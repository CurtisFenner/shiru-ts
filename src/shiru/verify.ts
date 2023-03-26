import * as builtin from "./builtin";
import { DefaultMap } from "./data";
import * as diagnostics from "./diagnostics";
import * as ir from "./ir";
import { displayType } from "./semantics";
import * as trace from "./trace";
import * as uf from "./uf";

type CallEdge<T> = {
	from: CallGraphNode;
	edge: CallGraphCall<T>;
	to: CallGraphNode;
};

class CallGraph<T> implements DirectedGraph<CallGraphCall<T>, CallGraphNode> {
	private callsByStatic = new DefaultMap<ir.FunctionID, { from: CallGraphNode, edges: CallEdge<T>[] }>(functionID => {
		return { from: { tag: "static", functionID }, edges: [] };
	});
	private callsByDynamic = new DefaultMap<ir.InterfaceID, DefaultMap<string, { from: CallGraphNode, edges: CallEdge<T>[] }>>(interfaceID => {
		return new DefaultMap(memberID => {
			return { from: { tag: "dynamic", interfaceID, memberID }, edges: [] };
		});
	});

	/**
	 * `initialize(node)` adds the given node to this graph so that it is
	 * included in subsequent calls to `this.getVertexes()`.
	 * 
	 * It also returns the canonical instance of the given `CallGraphNode`,
	 * enabling comparisons by identity.
	 */
	initialize(node: CallGraphNode): CallGraphNode {
		if (node.tag === "dynamic") {
			return this.callsByDynamic.get(node.interfaceID).get(node.memberID).from;
		} else {
			return this.callsByStatic.get(node.functionID).from;
		}
	}

	addCall(from: CallGraphNode, call: CallGraphCall<T>) {
		from = this.initialize(from);
		const to = this.initialize(call.calling);
		if (from.tag === "dynamic") {
			this.callsByDynamic.get(from.interfaceID).get(from.memberID).edges.push({
				from,
				edge: call,
				to,
			});
		} else {
			this.callsByStatic.get(from.functionID).edges.push({
				from,
				edge: call,
				to,
			});
		}
	}

	getOutgoing(from: CallGraphNode): Array<{
		from: CallGraphNode, edge: CallGraphCall<T>, to: CallGraphNode,
	}> {
		if (from.tag === "dynamic") {
			return this.callsByDynamic.get(from.interfaceID).get(from.memberID).edges;
		} else {
			return this.callsByStatic.get(from.functionID).edges;
		}
	}

	getVertexes(): CallGraphNode[] {
		const out = [];
		for (const [_, { from }] of this.callsByStatic) {
			out.push(from);
		}
		for (const [_, group] of this.callsByDynamic) {
			for (const [_, { from }] of group) {
				out.push(from);
			}
		}
		return out;
	}
}

type CallGraphNode = { tag: "static", functionID: ir.FunctionID }
	| { tag: "dynamic", interfaceID: ir.InterfaceID, memberID: string };

interface CallGraphCall<T> {
	/**
	 * `calling` indicates which function is being called.
	 */
	calling: CallGraphNode,

	/**
	 * `callLocation` indicates where in the source code the call is located.
	 */
	callLocation: ir.SourceLocation,

	/**
	 * Some data associated with this call.
	 */
	info: T,
}

class GlobalContext {
	program: ir.Program;
	interfaceSignaturesByImplFn: DefaultMap<ir.FunctionID, IndexedImpl[]>;

	decreasingCallGraph: CallGraph<"decreasing" | "non-decreasing"> = new CallGraph();

	/**
	 * Failure messages are accumulated in this list as failed verifications are
	 * discovered.
	 */
	failedVerifications: FailedVerification[] = [];

	constructor(program: ir.Program) {
		this.program = program;
		this.interfaceSignaturesByImplFn = indexInterfaceSignaturesByImplFn(program);
	}

	/**
	 * Fetch the symbolic interpreter associated with the foreign operation, if
	 * any.
	 */
	getForeignInterpreters(
		operation: string,
		state: VerificationState,
	): Pick<uf.Semantics<number>, "interpreter" | "generalInterpreter"> | undefined {
		const definition = builtin.foreignOperations[operation];
		if (definition === undefined) {
			throw new Error("GlobalContext.getForeignInterpreters: unknown operation `" + operation + "`");
		}

		return definition.getInterpreter && definition.getInterpreter(id => state.foreign.get(id));
	}
}

export function verifyProgram(
	program: ir.Program,
): FailedVerification[] {
	const context = new GlobalContext(program);
	// Verify each interface signature.
	for (const i in program.interfaces) {
		verifyInterface(context, i as ir.InterfaceID, program.interfaces[i]);
	}

	// Verify each function body.
	for (let f in program.functions) {
		const impls = context.interfaceSignaturesByImplFn.get(f as ir.FunctionID);
		verifyFunction(context, f as ir.FunctionID, program.functions[f], impls);
	}

	// Verify totality by inspecting the graph of non-decreasing calls.
	context.failedVerifications.push(...verifyCallGraphTotality(context.decreasingCallGraph));

	return context.failedVerifications;
}

function verifyInterface(
	context: GlobalContext,
	interfaceID: ir.InterfaceID,
	trait: ir.IRInterface,
): void {
	const state = new VerificationState(context);

	// Create the type scope for the interface's subjects.
	const interfaceTypeScope = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < trait.type_parameters.length; i++) {
		const typeVariable = trait.type_parameters[i];
		const typeID = state.smt.createVariable(ir.T_ANY, "#" + typeVariable + ".type");
		interfaceTypeScope.set(typeVariable, typeID);
	}
	state.pushTypeScope(interfaceTypeScope);

	// Validate that the interface's contracts are well-formed, in that
	// they explicitly guarantee their internal preconditions.
	for (const memberID in trait.signatures) {
		const signature = trait.signatures[memberID];

		// Create the type scope for this member's type parameters.
		const signatureTypeScope = new Map<ir.TypeVariableID, uf.ValueID>();
		for (let i = 0; i < signature.type_parameters.length; i++) {
			const typeVariable = signature.type_parameters[i];
			const typeID = state.smt.createVariable(ir.T_ANY, "#" + typeVariable + ".type");
			signatureTypeScope.set(typeVariable, typeID);
		}

		state.pushTypeScope(signatureTypeScope);
		const functionScope = state.pushVariableScope(true);

		// Create symbolic values for the arguments.
		const parameterTuple = [];
		for (const parameter of signature.parameters) {
			const symbolicParameter = state.smt.createVariable(parameter.type, parameter.variable);
			parameterTuple.push({ value: symbolicParameter, type: parameter.type });
			state.defineVariable(parameter, symbolicParameter);
		}

		const nonDecreasingCallSource: VerificationContext["nonDecreasingCallSource"] = {
			source: {
				tag: "dynamic",
				interfaceID,
				memberID,
			},
			limit: parameterTuple,
		};

		// Verify that preconditions explicitly state their own preconditions,
		// and assume that they hold for postconditions.
		for (const precondition of signature.preconditions) {
			traverseBlock(context, new Map(), precondition.block, state, {
				// Return ops within a precondition don't have their own
				// postconditions.
				verifyAtReturn: [],

				nonDecreasingCallSource,
			}, () => {
				state.assumeGuaranteedInPath(precondition.precondition);
			});
		}

		// Create symbolic values for the returns.
		const symbolicReturned = [];
		for (let i = 0; i < signature.return_types.length; i++) {
			const r = signature.return_types[i];
			symbolicReturned.push(state.smt.createVariable(r, "return." + i));
		}

		for (const postcondition of signature.postconditions) {
			const local = new Map<ir.VariableDefinition, uf.ValueID>();
			for (let i = 0; i < symbolicReturned.length; i++) {
				local.set(postcondition.returnedValues[i], symbolicReturned[i]);
			}
			traverseBlock(context, local, postcondition.block, state, {
				// Return ops within a postcondition don't have their own
				// postconditions.
				verifyAtReturn: [],

				nonDecreasingCallSource,
			}, () => {
				state.assumeGuaranteedInPath(postcondition.postcondition);
			});
		}

		state.popVariableScope(functionScope);
		state.popTypeScope();
	}

	state.popTypeScope();
}

interface IndexedImpl {
	implID: string,
	memberID: string,
}

function indexInterfaceSignaturesByImplFn(
	program: ir.Program,
): DefaultMap<ir.FunctionID, IndexedImpl[]> {
	const map = new DefaultMap<ir.FunctionID, IndexedImpl[]>(_ => []);

	// Add each implementation to the map.
	for (const implID in program.globalVTableFactories) {
		const impl = program.globalVTableFactories[implID];
		for (const memberID in impl.entries) {
			const implMember = impl.entries[memberID];
			map.get(implMember.implementation).push({ implID, memberID });
		}
	}
	return map;
}

function assumeStaticPreconditions(
	global: GlobalContext,
	callSource: CallGraphNode,
	signature: ir.FunctionSignature,
	valueArguments: uf.ValueID[],
	typeArguments: uf.ValueID[],
	state: VerificationState,
): void {
	if (signature.type_parameters.length !== typeArguments.length) {
		throw new Error("ICE: type argument count mismatch");
	} else if (signature.parameters.length !== valueArguments.length) {
		throw new Error("ICE: value argument count mismatch");
	}

	const typeScope = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < signature.type_parameters.length; i++) {
		typeScope.set(signature.type_parameters[i], typeArguments[i]);
	}

	const valueScope = new Map<ir.VariableDefinition, uf.ValueID>();
	for (let i = 0; i < signature.parameters.length; i++) {
		valueScope.set(signature.parameters[i], valueArguments[i]);
	}

	const hidingTypeScope = state.pushHidingTypeScope();
	state.pushTypeScope(typeScope);
	const variableScope = state.pushVariableScope(true);

	const objectArguments = [];
	for (let i = 0; i < valueArguments.length; i++) {
		objectArguments.push({
			value: valueArguments[i],
			type: signature.parameters[i].type,
		});
	}

	for (let i = 0; i < signature.preconditions.length; i++) {
		const precondition = signature.preconditions[i];
		traverseBlock(global, valueScope, precondition.block, state, {
			// Return ops within a precondition block do not have their own
			// postconditions.
			verifyAtReturn: [],

			nonDecreasingCallSource: {
				source: callSource,
				limit: objectArguments,
			},
		}, () => {
			state.assumeGuaranteedInPath(precondition.precondition);
		});
	}

	state.popVariableScope(variableScope);
	state.popTypeScope();
	state.popHidingTypeScope(hidingTypeScope);
}

/// implFnTypeArguments: The arguments to the impl fn. These are the impl's
/// "for_any" type parameters, followed by the interface-signature's type
/// parameters.
function assumeConstraintPreconditions(
	global: GlobalContext,
	valueArguments: uf.ValueID[],
	implFnTypeArguments: uf.ValueID[],
	implementing: IndexedImpl,
	state: VerificationState,
): void {
	const impl = global.program.globalVTableFactories[implementing.implID];
	const interfaceEntity = global.program.interfaces[impl.provides.interface];
	const interfaceSignature = interfaceEntity.signatures[implementing.memberID];

	if (implFnTypeArguments.length !== impl.for_any.length + interfaceSignature.type_parameters.length) {
		throw new Error("ICE: mismatching implFnTypeArguments.length");
	}

	const typeScope = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < interfaceEntity.type_parameters.length; i++) {
		const typeParameter = interfaceEntity.type_parameters[i];
		const typeArgument = state.getTypeID(impl.provides.subjects[i]);
		typeScope.set(typeParameter, typeArgument);
	}
	for (let i = 0; i < interfaceSignature.type_parameters.length; i++) {
		const typeParameter = interfaceSignature.type_parameters[i];
		const typeArgument = implFnTypeArguments[impl.for_any.length + i];
		typeScope.set(typeParameter, typeArgument);
	}

	const variableScope = new Map<ir.VariableDefinition, uf.ValueID>();
	for (let i = 0; i < valueArguments.length; i++) {
		variableScope.set(interfaceSignature.parameters[i], valueArguments[i]);
	}

	const hidingTypeScope = state.pushHidingTypeScope();
	state.pushTypeScope(typeScope);
	const hidingVariableScope = state.pushVariableScope(true);

	for (const precondition of interfaceSignature.preconditions) {
		traverseBlock(global, variableScope, precondition.block, state, {
			verifyAtReturn: [],

			// Any non-decreasing calls are attributed directly to the
			// interface.
			nonDecreasingCallSource: null,
		}, () => {
			state.assumeGuaranteedInPath(precondition.precondition);
		});
	}

	state.popVariableScope(hidingVariableScope);
	state.popTypeScope();
	state.popHidingTypeScope(hidingTypeScope);
}

function generateToVerifyFromConstraint(
	global: GlobalContext,
	valueArguments: uf.ValueID[],
	implFnTypeArguments: uf.ValueID[],
	implementing: IndexedImpl,
	state: VerificationState,
): VerifyAtReturn[] {
	const impl = global.program.globalVTableFactories[implementing.implID];
	const interfaceEntity = global.program.interfaces[impl.provides.interface];
	const interfaceSignature = interfaceEntity.signatures[implementing.memberID];

	if (implFnTypeArguments.length !== impl.for_any.length + interfaceSignature.type_parameters.length) {
		throw new Error("ICE: mismatching implFnTypeArguments.length");
	}

	const typeScope = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < interfaceEntity.type_parameters.length; i++) {
		const typeParameter = interfaceEntity.type_parameters[i];
		const typeArgument = state.getTypeID(impl.provides.subjects[i]);
		typeScope.set(typeParameter, typeArgument);
	}
	for (let i = 0; i < interfaceSignature.type_parameters.length; i++) {
		const typeParameter = interfaceSignature.type_parameters[i];
		const typeArgument = implFnTypeArguments[impl.for_any.length + i];
		typeScope.set(typeParameter, typeArgument);
	}

	const out: VerifyAtReturn[] = [];
	for (const postcondition of interfaceSignature.postconditions) {
		const variableScope = new Map<ir.VariableDefinition, VerifyAtReturnSource>();
		for (let i = 0; i < valueArguments.length; i++) {
			variableScope.set(interfaceSignature.parameters[i], { tag: "symbolic", symbolic: valueArguments[i] });
		}
		for (let i = 0; i < postcondition.returnedValues.length; i++) {
			variableScope.set(postcondition.returnedValues[i], { tag: "returned", returnedIndex: i });
		}

		out.push({
			postcondition,
			variableScope,
			typeIDScope: typeScope,
		});
	}
	return out;
}

function generateToVerifyFromStatic(
	signature: ir.FunctionSignature,
	valueArguments: uf.ValueID[],
	typeArguments: uf.ValueID[],
): VerifyAtReturn[] {
	if (signature.type_parameters.length !== typeArguments.length) {
		throw new Error("ICE: type argument count mismatch");
	} else if (signature.parameters.length !== valueArguments.length) {
		throw new Error("ICE: value argument count mismatch");
	}

	const typeScope = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < signature.type_parameters.length; i++) {
		typeScope.set(signature.type_parameters[i], typeArguments[i]);
	}

	const out: VerifyAtReturn[] = [];
	for (const postcondition of signature.postconditions) {
		// Setup verify-at-return for this postcondition.
		const variableScope = new Map<ir.VariableDefinition, VerifyAtReturnSource>();
		for (let i = 0; i < signature.parameters.length; i++) {
			variableScope.set(signature.parameters[i], { tag: "symbolic", symbolic: valueArguments[i] });
		}
		for (let i = 0; i < postcondition.returnedValues.length; i++) {
			variableScope.set(postcondition.returnedValues[i], { tag: "returned", returnedIndex: i });
		}
		out.push({
			postcondition,
			variableScope,
			typeIDScope: typeScope,
		});
	}
	return out;
}

function verifyPostconditionWellFormedness(
	global: GlobalContext,
	signature: ir.FunctionSignature,
	state: VerificationState,
	verifyAtReturns: VerifyAtReturn[],
): void {
	state.smt.pushScope();
	let symbolicReturned = [];
	for (let i = 0; i < signature.return_types.length; i++) {
		const r = signature.return_types[i];
		symbolicReturned.push(state.smt.createVariable(r, "return." + i));
	}
	for (const verifyAtReturn of verifyAtReturns) {
		const valueArgs = new Map<ir.VariableDefinition, uf.ValueID>();
		for (const [k, v] of verifyAtReturn.variableScope) {
			if (v.tag === "returned") {
				valueArgs.set(k, symbolicReturned[v.returnedIndex]);
			} else {
				valueArgs.set(k, v.symbolic);
			}
		}
		assumePostcondition(global, valueArgs, verifyAtReturn.typeIDScope, verifyAtReturn.postcondition, state);
	}
	state.smt.popScope();
}

/// interfaceSignaturesByImplFn: Explains which interface signatures each fn
/// implements. Any preconditions from the indicated interfaces should be
/// automatically assumed, and any postconditions should be automatically
/// checked.
function verifyFunction(
	global: GlobalContext,
	functionID: ir.FunctionID,
	f: ir.IRFunction,
	impls: IndexedImpl[],
): void {
	const state = new VerificationState(global);

	// Create the initial type scope, which maps each type parameter to an
	// unknown symbolic type ID constant.
	const typeScope = new Map<ir.TypeVariableID, uf.ValueID>();
	const typeArguments = [];
	for (let i = 0; i < f.signature.type_parameters.length; i++) {
		const typeParameter = f.signature.type_parameters[i];
		const typeArgument = state.smt.createVariable(ir.T_ANY, "#" + typeParameter + ".type");
		typeArguments.push(typeArgument);
		typeScope.set(typeParameter, typeArgument);
	}
	state.pushTypeScope(typeScope);

	// Initialize the function's arguments.
	const symbolicArguments = [];
	const objectArguments = [];
	for (let i = 0; i < f.signature.parameters.length; i++) {
		const parameter = f.signature.parameters[i];

		// Create a symbolic constant for the initial value of the parameter.
		const symbolic = state.smt.createVariable(parameter.type, parameter.variable);
		state.defineVariable(parameter, symbolic);
		symbolicArguments.push(symbolic);
		objectArguments.push({ value: symbolic, type: parameter.type });
	}

	// Execute and validate the function's preconditions.
	const nonDecreasingCallSource: VerificationContext["nonDecreasingCallSource"] = {
		source: {
			tag: "static",
			functionID,
		},
		limit: objectArguments,
	};
	assumeStaticPreconditions(
		global, nonDecreasingCallSource.source, f.signature, symbolicArguments, typeArguments, state);

	const verifyAtReturns: VerifyAtReturn[] = [];

	// Collect postconditions from an impl fn.
	for (const impl of impls) {
		if (f.signature.preconditions.length !== 0) {
			throw new Error("verifyFunction: impl function has explicit preconditions");
		}

		assumeConstraintPreconditions(global, symbolicArguments, typeArguments, impl, state);
		verifyAtReturns.push(...generateToVerifyFromConstraint(global, symbolicArguments, typeArguments, impl, state));
	}

	// Collect explicit postconditions from a fn.
	verifyAtReturns.push(...generateToVerifyFromStatic(f.signature, symbolicArguments, typeArguments));

	// Validate that the function's postconditions are well-formed, in that they
	// explicitly guarantee their internal preconditions.
	verifyPostconditionWellFormedness(global, f.signature, state, verifyAtReturns);

	// Check the function's body (including that each return op guarantees the
	// ensured postconditions).
	traverseBlock(global, new Map(), f.body, state, {
		verifyAtReturn: verifyAtReturns,

		nonDecreasingCallSource,
	});

	const lastOp = f.body.ops[f.body.ops.length - 1];
	if (!ir.opTerminates(lastOp)) {
		throw new Error("ICE: verifyFunction invoked on a function which does not obviously terminate");
	}
}

/// Describes what value to bind to a parameter of a postcondition block.
// "symbolic" values are used to supply the original arguments to the
// postcondition; these can be stored as a "closure".
// "returned" values are used to supply the operands of the op-return to the
// postcondition.
type VerifyAtReturnSource =
	{ tag: "symbolic", symbolic: uf.ValueID }
	| { tag: "returned", returnedIndex: number };

interface VerifyAtReturn {
	postcondition: ir.Postcondition,

	// The full (hiding) scope to use when executing the postcondition body.
	variableScope: Map<ir.VariableDefinition, VerifyAtReturnSource>,

	// The full (hiding) scope to use when determining the type-ID of a type
	// parameter that appears within the postcondition body.
	typeIDScope: Map<ir.TypeVariableID, uf.ValueID>,
}

interface VerificationContext {
	/// The post-conditions to verify at a ReturnStatement.
	verifyAtReturn: VerifyAtReturn[],

	/**
	 * `nonDecreasingCallSource` indicates the function to attribute
	 * non-decreasing calls to.
	 * 
	 * It is `null` when non-decreasingness ned not be checked (for example,
	 * when traversing a recursive contract, or when checking the body of a
	 * "partial" function).
	 */
	nonDecreasingCallSource: {
		source: CallGraphNode,
		limit: { value: uf.ValueID, type: ir.Type }[],
	} | null,
}

export type FailedVerification = FailedPreconditionVerification
	| FailedAssertVerification
	| FailedReturnVerification
	| FailedPostconditionValidation
	| FailedVariantVerification
	| FailedTotality;

export interface FailedPreconditionVerification {
	tag: "failed-precondition",
	callLocation: ir.SourceLocation,
	preconditionLocation: ir.SourceLocation,
}

export interface FailedPostconditionValidation {
	tag: "failed-postcondition",
	returnLocation: ir.SourceLocation,
	postconditionLocation: ir.SourceLocation,
}

export interface FailedAssertVerification {
	tag: "failed-assert",
	assertLocation: ir.SourceLocation,
}

export interface FailedReturnVerification {
	tag: "failed-return",
	blockEndLocation?: ir.SourceLocation,
}

export interface FailedVariantVerification {
	tag: "failed-variant",
	variant: string,
	enumType: string,
	accessLocation: ir.SourceLocation,
}

export interface FailedTotality {
	tag: "failed-totality",
	nonDecreasingCall: ir.SourceLocation,
	cycle: ir.SourceLocation[],
}

interface SignatureSet {
	blockedFunctions: Record<string, boolean>,
	blockedInterfaces: Record<string, Record<string, string>>,
}

interface VerificationScope {
	token: symbol,
	variableHiding: boolean,
	variables: Map<ir.VariableID, { type: ir.Type, value: uf.ValueID }>,
}

class DynamicFunctionMap {
	private map = new DefaultMap<ir.InterfaceID, DefaultMap<ir.FunctionID, uf.FnID[]>>(
		i => new DefaultMap(s => {
			const interfaceIR = this.program.interfaces[i];
			const signature = interfaceIR.signatures[s];

			const typeParameters = interfaceIR.type_parameters.concat(signature.type_parameters);
			const anys = [];
			for (let i = 0; i < typeParameters.length; i++) {
				anys.push(ir.T_ANY);
			}
			const map = ir.typeArgumentsMap(typeParameters, anys);
			const fnIDs = [];
			for (let i = 0; i < signature.return_types.length; i++) {
				const returnType = ir.typeSubstitute(signature.return_types[i], map);
				fnIDs[i] = this.smt.createFunction(returnType, { eq: signature.semantics?.eq },
					i + "." + s + (signature.return_types.length !== 0 ? "." + i : ""));
			}
			return fnIDs;
		}));

	constructor(private program: ir.Program, private smt: uf.UFTheory) { }

	/**
	 * Retreives the UF-theory representation of the given call of an interface
	 * function.
	 */
	call(
		interfaceID: ir.InterfaceID,
		signatureID: ir.FunctionID,
		args: { valueArgs: uf.ValueID[], interfaceTypeArgs: uf.ValueID[] },
	): uf.ValueID[] {
		const fnIDs = this.map.get(interfaceID).get(signatureID);
		const out = [];
		const allArgs = [...args.valueArgs, ...args.interfaceTypeArgs];
		for (const fnID of fnIDs) {
			out.push(this.smt.createApplication(fnID, allArgs));
		}
		return out;
	}
}

class StaticFunctionMap {
	private functions: DefaultMap<ir.FunctionID, uf.FnID[]> = new DefaultMap(fnID => {
		const fn = this.program.functions[fnID];
		if (fn === undefined) {
			throw new Error("VerificationState.functions.get: undefined `" + fnID + "`");
		}
		const instantiation = new Map<ir.TypeVariableID, ir.Type>();
		for (let i = 0; i < fn.signature.type_parameters.length; i++) {
			instantiation.set(fn.signature.type_parameters[i], ir.T_ANY);
		}

		const out = [];
		for (const r of fn.signature.return_types) {
			// Use a more generic "Any" type.
			const resultType = ir.typeSubstitute(r, instantiation);
			out.push(this.smt.createFunction(resultType, { eq: fn.signature.semantics?.eq }, fnID));
		}
		return out;
	});

	constructor(private program: ir.Program, private smt: uf.UFTheory) { }

	call(
		fn: ir.FunctionID,
		args: { valueArgs: uf.ValueID[], typeArgs: uf.ValueID[] },
	): uf.ValueID[] {
		const fnIDs = this.functions.get(fn);
		const out = [];
		const allArgs = [...args.valueArgs, ...args.typeArgs];
		for (let i = 0; i < fnIDs.length; i++) {
			out.push(this.smt.createApplication(fnIDs[i], allArgs));
		}
		return out;
	}
}

interface RecordFns {
	constructor: uf.FnID,
	fields: Record<string, uf.FnID>,

	// A function that takes in type arguments (as type IDs) and returns the
	// type ID for the "type application".
	typeID: uf.FnID,
}

class RecordMap {
	private map = new DefaultMap<ir.RecordID, RecordFns>(r => {
		const record = this.program.records[r];
		const fields: Record<string, uf.FnID> = {};
		for (const k in record.fields) {
			fields[k] = this.smt.createFunction(record.fields[k], {}, r + "." + k);
		}

		const recordType: ir.TypeCompound = {
			tag: "type-compound",
			base: r,
			type_arguments: record.type_parameters.map(x => ({ tag: "type-any" })),
		};
		return {
			constructor: this.smt.createFunction(recordType, {}, r + ".record"),
			fields,
			typeID: this.smt.createFunction(ir.T_INT, {}, r + ".type"),
		};
	});

	constructor(private program: ir.Program, private smt: uf.UFTheory) { }

	construct(recordID: ir.RecordID, initialization: Record<string, uf.ValueID>): uf.ValueID {
		const info = this.map.get(recordID);
		const f = info.constructor;
		const args = [];
		for (const field in info.fields) {
			args.push(initialization[field]);
		}
		return this.smt.createApplication(f, args);
	}

	extractField(recordID: ir.RecordID, field: string, obj: uf.ValueID): uf.ValueID {
		const f = this.map.get(recordID).fields[field];
		return this.smt.createApplication(f, [obj]);
	}

	typeID(recordID: ir.RecordID, typeArgumentTypeIDs: uf.ValueID[]): uf.ValueID {
		const info = this.map.get(recordID);
		return this.smt.createApplication(info.typeID, typeArgumentTypeIDs);
	}
}

interface EnumVariantFns {
	extractTag: uf.FnID,
	constructors: Record<string, uf.FnID>,
	destructors: Record<string, uf.FnID>,
	tagValues: Record<string, uf.ValueID>,

	// A function that takes in type arguments (as type IDs) and returns the
	// type ID for the "type application".
	typeID: uf.FnID,
};

class EnumMap {
	private map = new DefaultMap<ir.EnumID, EnumVariantFns>(enumID => {

		const constructors: Record<string, uf.FnID> = {};
		const destructors: Record<string, uf.FnID> = {};
		const tagValues: Record<string, uf.ValueID> = {};

		const enumEntity = this.program.enums[enumID];

		const instantiation = new Map<ir.TypeVariableID, ir.Type>();
		const enumType: ir.TypeCompound = {
			tag: "type-compound",
			base: enumID,
			type_arguments: [],
		};
		for (const parameter of enumEntity.type_parameters) {
			instantiation.set(parameter, ir.T_ANY);
			enumType.type_arguments.push(ir.T_ANY);
		}

		let tagIndex = 0;
		for (const variant in enumEntity.variants) {
			const variantType = ir.typeSubstitute(enumEntity.variants[variant], instantiation);
			constructors[variant] = this.smt.createFunction(enumType, {}, enumID + ".enum." + variant);
			destructors[variant] = this.smt.createFunction(variantType, {}, enumID + "." + variant);
			tagValues[variant] = this.smt.createConstant(ir.T_INT, tagIndex);
			tagIndex += 1;
		}

		return {
			extractTag: this.smt.createFunction(ir.T_INT, {}, enumID + ".enum.tag"),
			constructors,
			destructors,
			tagValues,
			typeID: this.smt.createFunction(ir.T_INT, {}, enumID + ".type"),
		};
	});

	constructor(
		private program: ir.Program,
		private smt: uf.UFTheory,
	) { }

	hasTag(
		enumID: ir.EnumID,
		enumValue: uf.ValueID,
		variant: string,
		eq: { eq(a: uf.ValueID, b: uf.ValueID): uf.ValueID },
	) {
		const info = this.map.get(enumID);
		const symbolicTag = this.smt.createApplication(info.extractTag, [enumValue]);
		const testTag = info.tagValues[variant];

		// Add a constraint that the tag takes on one of a small number of values.
		const finiteAlternativesClause = [];
		for (const variant in info.tagValues) {
			const tagConstant = info.tagValues[variant];
			finiteAlternativesClause.push(eq.eq(symbolicTag, tagConstant));
		}

		return {
			testResult: eq.eq(symbolicTag, testTag),
			finiteAlternativesClause,
		};
	}

	construct(
		enumID: ir.EnumID,
		variantValue: uf.ValueID,
		variant: string,
	): uf.ValueID {
		const info = this.map.get(enumID);
		return this.smt.createApplication(info.constructors[variant], [variantValue]);
	}

	destruct(
		enumID: ir.EnumID,
		enumValue: uf.ValueID,
		variant: string,
	): uf.ValueID {
		const info = this.map.get(enumID);
		return this.smt.createApplication(info.destructors[variant], [enumValue]);
	}

	typeID(enumID: ir.EnumID, typeArgumentTypeIDs: uf.ValueID[]): uf.ValueID {
		const info = this.map.get(enumID);
		return this.smt.createApplication(info.typeID, typeArgumentTypeIDs);
	}
}

class VerificationState {
	private context: GlobalContext;

	smt: uf.UFTheory = new uf.UFTheory();
	notF = this.smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");
	eqF = this.smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
	boundedByF = this.smt.createFunction(ir.T_BOOLEAN, { transitive: true, transitiveAcyclic: true }, "boundedBy");

	foreign = new DefaultMap<string, uf.FnID[]>(op => {
		const signature = this.context.program.foreign[op];
		if (signature === undefined) {
			throw new Error("VerificationState.foreign.get: undefined `" + op + "`");
		}
		const out = [];
		for (const r of signature.return_types) {
			// TODO: Distinguish interpreters for multi-return foreign
			// operations.
			const interpreters = this.context.getForeignInterpreters(op, this);
			out.push(this.smt.createFunction(r, {
				eq: signature.semantics?.eq,
				interpreter: interpreters?.interpreter,
				generalInterpreter: interpreters?.generalInterpreter,
				transitive: signature.semantics?.transitive,
				transitiveAcyclic: signature.semantics?.transitiveAcyclic,
			}, op));
		}
		return out;
	});

	dynamicFunctions: DynamicFunctionMap;
	staticFunctions: StaticFunctionMap;
	recordMap: RecordMap;
	enumMap: EnumMap;

	recursivePreconditions: SignatureSet = {
		blockedFunctions: {},
		blockedInterfaces: {},
	};

	recursivePostconditions: SignatureSet = {
		blockedFunctions: {},
		blockedInterfaces: {},
	};

	/// `varScopes` is a stack of variable mappings. SSA variables aren't
	/// reassigned, but can be shadowed (including within the same block).
	private varScopes: Array<VerificationScope> = [
		{
			token: Symbol("root-scope"),
			variableHiding: true,
			variables: new Map(),
		}
	];

	/// `typeScopes` is a stack of type parameter --> TypeID values.
	private typeScopes: Array<Map<ir.TypeVariableID, uf.ValueID> | symbol> = [];

	/// Pushing a hiding scope hides all previous associations, allowing errors
	/// to be noticed more easily.
	pushHidingTypeScope(): symbol {
		const token = Symbol("hiding-type-scope");
		this.typeScopes.push(token);
		return token;
	}

	pushTypeScope(scope: Map<ir.TypeVariableID, uf.ValueID>) {
		this.typeScopes.push(scope);
	}

	popTypeScope() {
		const top = this.typeScopes.pop();
		if (top === undefined) {
			throw new Error("popTypeScope: no scope open");
		} else if (!(top instanceof Map)) {
			throw new Error("popTypeScope: hiding scope open; expected call to popHidingTypeScope().");
		}
	}

	popHidingTypeScope(expected: symbol) {
		const top = this.typeScopes.pop();
		if (top !== expected) {
			throw new Error("popHidingTypeScope: did not find expected hiding type scope");
		}
	}

	private unitTypeID = this.smt.createConstant(ir.T_INT, 21);
	private booleanTypeID = this.smt.createConstant(ir.T_INT, 22);
	private intTypeID = this.smt.createConstant(ir.T_INT, 23);
	private bytesTypeID = this.smt.createConstant(ir.T_INT, 24);
	private anyTypeID = this.smt.createConstant(ir.T_INT, 25);

	/// `getTypeID` generates a symbolic constant representing the given type.
	getTypeID(t: ir.Type): uf.ValueID {
		if (t.tag === "type-any") {
			return this.anyTypeID;
		} else if (t.tag === "type-primitive") {
			if (t.primitive === "Unit") {
				return this.unitTypeID;
			} else if (t.primitive === "Boolean") {
				return this.booleanTypeID;
			} else if (t.primitive === "Int") {
				return this.intTypeID;
			} else if (t.primitive === "Bytes") {
				return this.bytesTypeID;
			} else {
				const un: never = t.primitive;
				throw new Error("getTypeID: unhandled primitive `" + un + "`");
			}
		} else if (t.tag === "type-variable") {
			for (let i = this.typeScopes.length - 1; i >= 0; i--) {
				const scope = this.typeScopes[i];
				if (typeof scope === "symbol") {
					throw new Error("getTypeID: unmapped type-variable within hiding scope: `" + t.id + "`");
				}
				const mapping = scope.get(t.id);
				if (mapping !== undefined) {
					return mapping;
				}
			}
			throw new Error("getTypeID: unmapped type-variable `" + t.id + "`");
		} else if (t.tag === "type-compound") {
			const args = t.type_arguments.map(x => this.getTypeID(x));
			const base = t.base;
			if (this.context.program.records[base] !== undefined) {
				return this.recordMap.typeID(base as ir.RecordID, args);
			} else {
				return this.enumMap.typeID(base as ir.EnumID, args);
			}
		} else {
			const un: never = t;
			throw new Error("getTypeID: unhandled type tag `" + un["tag"] + "`");
		}
	}

	/**
	 * `pathConstraints` is the stack of conditional constraint-clauses that
	 * must be true to reach the current position in the program.
	 * 
	 * Each clause is a disjunction of boolean-sorted constraints.
	 */
	private pathConstraints: uf.ValueID[][] = [];

	constructor(
		context: GlobalContext,
	) {
		this.context = context;
		this.dynamicFunctions = new DynamicFunctionMap(context.program, this.smt);
		this.staticFunctions = new StaticFunctionMap(context.program, this.smt);
		this.recordMap = new RecordMap(context.program, this.smt);
		this.enumMap = new EnumMap(context.program, this.smt);

		// SMT requires at least one constraint.
		this.smt.addConstraint([
			this.smt.createConstant(ir.T_BOOLEAN, true),
		]);
	}

	negate(bool: uf.ValueID): uf.ValueID {
		return this.smt.createApplication(this.notF, [bool]);
	}

	eq(left: uf.ValueID, right: uf.ValueID): uf.ValueID {
		return this.smt.createApplication(this.eqF, [left, right]);
	}

	pushVariableScope(variableHiding: boolean): symbol {
		const token = Symbol("variable-scope");
		this.varScopes.push({
			token,
			variableHiding,
			variables: new Map(),
		});
		return token;
	}

	popVariableScope(expected: symbol): void {
		const top = this.varScopes.pop();
		if (!top || top.token !== expected) {
			throw new Error("popVariableScope: did not find expected scope");
		}
	}

	/// Modifies this state so that it assumes the given condition is always
	/// true when at this path in the program.
	assumeGuaranteedInPath(condition: ir.VariableID): void {
		this.pushPathConstraint(this.negate(this.getValue(condition).value));
		this.markPathUnreachable();
		this.popPathConstraint();
	}

	pushPathConstraint(c: uf.ValueID) {
		this.pathConstraints.push([c]);
	}

	popPathConstraint() {
		this.pathConstraints.pop();
	}

	/// Determines whether or not the given condition is possibly false given
	/// the current path constraints.
	/// Returns `"refuted"` when it is not possible for the condition to be
	/// false.
	checkPossiblyFalseInPath(
		condition: ir.VariableID,
		reason: FailedVerification,
	): uf.UFCounterexample | "refuted" {
		this.pushPathConstraint(this.negate(this.getValue(condition).value));
		const reply = this.checkReachable(reason);
		this.popPathConstraint();
		return reply;
	}

	checkPossiblyNonDecreasingInPath(
		left: { value: uf.ValueID, type: ir.Type }[],
		right: { value: uf.ValueID, type: ir.Type }[],
		reason: FailedVerification,
	): uf.UFCounterexample | "refuted" {
		const clausified = clausifyNotSmallerThan(this.smt, {
			ltF: this.boundedByF,
			eqF: this.eqF,
			negF: this.notF,
		}, left.map(x => x.value), right.map(x => x.value));

		for (let i = 0; i < left.length && i < right.length; i++) {
			// Add type-specific postconditions for comparisons.
			createBoundedByComparison(this, left[i], right[i]);
		}

		for (const clause of clausified) {
			this.pathConstraints.push(clause);
		}

		const reply = this.checkReachable(reason);

		for (const clause of clausified) {
			this.pathConstraints.pop();
		}

		return reply;
	}

	/// `checkReachable` checks whether or not the conjunction of current path
	/// constraints, combined with all other constraints added to the `smt`
	/// solver, is reachable or not.
	checkReachable(reason: FailedVerification): uf.UFCounterexample | "refuted" {
		trace.start("checkReachable");
		this.smt.pushScope();
		for (const constraint of this.pathConstraints) {
			this.smt.addConstraint(constraint);
		}
		trace.mark([reason]);
		const model = this.smt.attemptRefutation();
		this.smt.popScope();
		trace.stop("checkReachable");
		return model;
	}

	/// `markPathUnreachable` ensures that the conjunction of the current path
	/// constraints is considered not satisfiable in subsequent invocations of
	/// the `smt` solver.
	markPathUnreachable() {
		const pathUnreachable = this.pathConstraints.map(e => {
			if (e.length !== 1) {
				throw new Error("VerificationState.markPathUnreachable: every path constraint must be a unit clause");
			}
			return this.negate(e[0]);
		});
		this.smt.addConstraint(pathUnreachable);
	}

	/// `defineVariable` associates the given symbolic value with the given
	/// name for the remainder of the current innermost scope.
	defineVariable(variable: ir.VariableDefinition, value: uf.ValueID) {
		const scope = this.varScopes[this.varScopes.length - 1];
		scope.variables.set(variable.variable, {
			type: variable.type,
			value: value,
		});
	}

	/// `getValue` retrieves the value associated with the given name from the
	/// innermost scope that defines it.
	getValue(variable: ir.VariableID) {
		for (let i = this.varScopes.length - 1; i >= 0; i--) {
			const scope = this.varScopes[i];
			const value = scope.variables.get(variable);
			if (value !== undefined) {
				return value;
			} else if (scope.variableHiding) {
				throw new Error("getValue: variable `" + variable + "` is not defined within the containing hiding scope");
			}
		}
		throw new Error("getValue: variable `" + variable + "` is not defined");
	}
}

function traverseBlock(
	global: GlobalContext,
	locals: Map<ir.VariableDefinition, uf.ValueID>,
	block: ir.OpBlock,
	state: VerificationState,
	context: VerificationContext,
	then?: () => unknown,
) {
	// Blocks bound variable scopes, so variables must be cleared after.
	const variableScope = state.pushVariableScope(false);

	for (const [k, v] of locals) {
		state.defineVariable(k, v);
	}

	for (let subop of block.ops) {
		traverse(global, subop, state, context);
	}

	// Execute the final computation before exiting this scope.
	if (then !== undefined) {
		then();
	}

	// Clear variables defined within this block.
	state.popVariableScope(variableScope);
}

/*
 * MUTATES the verification state parameter, to add additional clauses that are
 * ensured after the execution (and termination) of this operation.
 */
function traverse(
	global: GlobalContext,
	op: ir.Op,
	state: VerificationState,
	context: VerificationContext,
): void {
	if (op.tag === "op-branch") {
		const symbolicCondition: uf.ValueID = state.getValue(op.condition).value;

		const phis: uf.ValueID[] = [];
		for (const destination of op.destinations) {
			phis.push(state.smt.createVariable(
				destination.destination.type, destination.destination.variable));
		}

		state.pushPathConstraint(symbolicCondition);
		traverseBlock(global, new Map(), op.trueBranch, state, context, () => {
			for (let i = 0; i < op.destinations.length; i++) {
				const destination = op.destinations[i];
				const source = destination.trueSource;
				if (source === "undef") continue;
				state.smt.addUnscopedConstraint([
					state.negate(symbolicCondition),
					state.eq(phis[i], state.getValue(source.variable).value),
				]);
			}
		})
		state.popPathConstraint();

		state.pushPathConstraint(state.negate(symbolicCondition));
		traverseBlock(global, new Map(), op.falseBranch, state, context, () => {
			for (let i = 0; i < op.destinations.length; i++) {
				const destination = op.destinations[i];
				const source = destination.falseSource;
				if (source === "undef") continue;
				state.smt.addUnscopedConstraint([
					symbolicCondition,
					state.eq(phis[i], state.getValue(source.variable).value),
				]);
			}
		});
		state.popPathConstraint();

		for (let i = 0; i < op.destinations.length; i++) {
			state.defineVariable(op.destinations[i].destination, phis[i]);
		}

		return;
	} else if (op.tag === "op-const") {
		// Like assignment, this requires no manipulation of constraints, only
		// the state of variables.
		let constant: uf.ValueID;
		if (op.type === "Int") {
			constant = state.smt.createConstant(op.destination.type, BigInt(op.int));
		} else if (op.type === "Boolean") {
			constant = state.smt.createConstant(op.destination.type, op.boolean);
		} else if (op.type === "Bytes") {
			constant = state.smt.createConstant(op.destination.type, op.bytes);
		} else {
			const _: never = op;
			throw new Error("traverse: unexpected op-const type `" + op["type"] + "`");
		}
		state.defineVariable(op.destination, constant);
		return;
	} else if (op.tag === "op-copy") {
		for (const copy of op.copies) {
			state.defineVariable(copy.destination, state.getValue(copy.source).value);
		}
		return;
	} else if (op.tag === "op-field") {
		const object = state.getValue(op.object);
		const baseType = object.type as ir.TypeCompound & { base: ir.RecordID };
		const fieldValue = state.recordMap.extractField(baseType.base, op.field, object.value);
		const bounding = state.smt.createApplication(state.boundedByF, [fieldValue, object.value]);
		state.smt.addUnscopedConstraint([bounding]);
		state.defineVariable(op.destination, fieldValue);
		return;
	} else if (op.tag === "op-is-variant") {
		const object = state.getValue(op.base);
		const baseType = object.type as ir.TypeCompound & { base: ir.EnumID };

		const tagInfo = state.enumMap.hasTag(baseType.base, object.value, op.variant, state);
		state.smt.addUnscopedConstraint(tagInfo.finiteAlternativesClause);
		state.defineVariable(op.destination, tagInfo.testResult);
		return;
	} else if (op.tag === "op-variant") {
		const object = state.getValue(op.object);
		const baseType = object.type as ir.TypeCompound & { base: ir.EnumID };

		const tagInfo = state.enumMap.hasTag(baseType.base, object.value, op.variant, state);
		state.smt.addUnscopedConstraint(tagInfo.finiteAlternativesClause);

		// Check that the symbolic tag definitely matches this variant.
		state.pushPathConstraint(
			state.negate(tagInfo.testResult)
		);
		const reason: FailedVariantVerification = {
			tag: "failed-variant",
			enumType: baseType.base + "[???]",
			variant: op.variant,
			accessLocation: op.diagnostic_location,
		};
		const refutation = state.checkReachable(reason);
		if (refutation !== "refuted") {
			reason.enumType = displayType(baseType);
			global.failedVerifications.push(reason);
		}

		state.markPathUnreachable();
		state.popPathConstraint();

		// Extract the field.
		const variantValue = state.enumMap.destruct(baseType.base, object.value, op.variant);
		const bounding = state.smt.createApplication(state.boundedByF, [variantValue, object.value]);
		state.smt.addUnscopedConstraint([bounding]);
		state.defineVariable(op.destination, variantValue);
		return;
	} else if (op.tag === "op-new-record") {
		const fields: Record<string, uf.ValueID> = {}
		for (const field in op.fields) {
			fields[field] = state.getValue(op.fields[field]).value;
		}
		const recordType = op.destination.type as ir.TypeCompound & { base: ir.RecordID };
		const recordValue = state.recordMap.construct(recordType.base, fields);
		state.defineVariable(op.destination, recordValue);
		return;
	} else if (op.tag === "op-new-enum") {
		const enumType = op.destination.type as ir.TypeCompound & { base: ir.EnumID };
		const variantValue = state.getValue(op.variantValue).value;
		const enumValue = state.enumMap.construct(enumType.base, variantValue, op.variant);
		state.defineVariable(op.destination, enumValue);

		const tagInfo = state.enumMap.hasTag(enumType.base, enumValue, op.variant, state);
		state.smt.addUnscopedConstraint([tagInfo.testResult]);

		const destruction = state.enumMap.destruct(enumType.base, enumValue, op.variant);
		state.smt.addUnscopedConstraint([state.eq(destruction, variantValue)]);
		return;
	} else if (op.tag === "op-proof") {
		return traverseBlock(global, new Map(), op.body, state, context);
	} else if (op.tag === "op-return") {
		if (context.verifyAtReturn.length !== 0) {
			// Check that the postconditions from the context are satisfied by
			// this return.
			const returnedValues = [];
			for (let i = 0; i < op.sources.length; i++) {
				returnedValues.push(state.getValue(op.sources[i]).value);
			}
			checkVerifyAtReturns(global, state, returnedValues, context.verifyAtReturn, op.diagnostic_return_site);
		}

		// Subsequently, this path is treated as unreachable, since the function
		// exited.
		state.markPathUnreachable();
		return;
	} else if (op.tag === "op-foreign") {
		traverseForeignCall(global, op, state, context);
		return;
	} else if (op.tag === "op-static-call") {
		traverseStaticCall(global, op, state, context);
		return;
	} else if (op.tag === "op-dynamic-call") {
		traverseDynamicCall(global, op, state, context);
		return;
	} else if (op.tag === "op-unreachable") {
		// TODO: Better classify verification failures.
		const reason: FailedVerification = op.diagnostic_kind === "return"
			? {
				tag: "failed-return",
				blockEndLocation: op.diagnostic_location,
			}
			: {
				tag: "failed-assert",
				assertLocation: op.diagnostic_location,
			};

		if (state.checkReachable(reason) !== "refuted") {
			global.failedVerifications.push(reason);
		}

		// Like a return statement, this path is subsequently treated as
		// unreachable.
		state.markPathUnreachable();
		return;
	} else if (op.tag === "op-proof-eq") {
		const leftObject = state.getValue(op.left);
		const rightObject = state.getValue(op.right);

		state.defineVariable(op.destination, state.eq(leftObject.value, rightObject.value));
		return;
	} else if (op.tag === "op-proof-bounds") {
		const smallerObject = state.getValue(op.smaller);
		const largerObject = state.getValue(op.larger);
		state.defineVariable(op.destination, createBoundedByComparison(state, smallerObject, largerObject));
		return;
	}

	const _: never = op;
	throw new Error(`unhandled op ${op["tag"]}`);
}

function createBoundedByComparison(
	state: VerificationState,
	smallerObject: { value: uf.ValueID, type: ir.Type },
	largerObject: { value: uf.ValueID, type: ir.Type },
): uf.ValueID {
	const smaller = smallerObject.value;
	const larger = largerObject.value;

	// Compare using the structural comparison.
	const boundsComparison = state.smt.createApplication(state.boundedByF, [smaller, larger]);

	if (ir.equalTypes(ir.T_INT, smallerObject.type) && ir.equalTypes(ir.T_INT, largerObject.type)) {
		// Use a more specific definition for integers in terms of `Int<`:
		// `a bounds b` means `b is strictly between -a and a`.
		// For now, this will be restricted to the simpler condition
		// `b between 0 and a`:
		// `(0 < b < a) or (a < b < 0) or (a != 0 and b = 0).
		const lessThanFns = state.foreign.get("Int<");
		if (lessThanFns.length !== 1) {
			throw new Error("verify: Expected `Int<` to have exactly one return");
		}
		const lessThanFn = lessThanFns[0];

		const zero = state.smt.createConstant(ir.T_INT, BigInt(0));

		// (smaller == 0 and larger != 0) implies cmp
		// (smaller != 0 or larger == 0) or cmp
		state.smt.addUnscopedConstraint([
			state.negate(state.eq(smaller, zero)),
			state.eq(larger, zero),
			boundsComparison,
		]);

		// (0 < smaller and smaller < larger) implies cmp
		// (0 !< smaller or smaller !< larger) or cmp
		state.smt.addUnscopedConstraint([
			state.negate(state.smt.createApplication(lessThanFn, [zero, smaller])),
			state.negate(state.smt.createApplication(lessThanFn, [smaller, larger])),
			boundsComparison,
		]);

		// (larger < smaller and smaller < 0) implies cmp
		// (larger !< smaller or smaller !< 0) or cmp
		state.smt.addUnscopedConstraint([
			state.negate(state.smt.createApplication(lessThanFn, [larger, smaller])),
			state.negate(state.smt.createApplication(lessThanFn, [smaller, zero])),
			boundsComparison,
		]);
	}

	return boundsComparison;
}

/**
 * `checkPrecondition` inspects the state and ensures that the precondition
 * invoked with the given arguments is satisfied.
 */
function checkPrecondition(
	global: GlobalContext,
	valueArgs: Map<ir.VariableDefinition, uf.ValueID>,
	typeArgs: Map<ir.TypeVariableID, uf.ValueID>,
	precondition: ir.Precondition,
	state: VerificationState,
	reason: FailedVerification,
): void {
	// When contracts of `fn` refer to a type parameter like `#T`, its symbolic
	// type ID will be retrieved from only the `typeArgs` map:
	const hidingTypeScope = state.pushHidingTypeScope();
	state.pushTypeScope(typeArgs);

	traverseBlock(global, valueArgs, precondition.block, state, {
		// Return ops within a precondition do not have their own
		// postconditions.
		verifyAtReturn: [],

		// The non-decreasingness of a call within a precondition is check where
		// the precondition is defined, rather than where it is invoked.
		nonDecreasingCallSource: null,
	}, () => {
		if (state.checkPossiblyFalseInPath(precondition.precondition, reason) !== "refuted") {
			global.failedVerifications.push(reason);
		}
	});

	state.popTypeScope();
	state.popHidingTypeScope(hidingTypeScope);
}

/**
 * `assumePostCondition` modifies the `state` so that subsequent inspections can
 * assume that this postcondition, invoked with the given arguments, is
 * satisfied.
 */
function assumePostcondition(
	global: GlobalContext,
	valueArgs: Map<ir.VariableDefinition, uf.ValueID>,
	typeArgs: Map<ir.TypeVariableID, uf.ValueID>,
	postcondition: ir.Postcondition,
	state: VerificationState,
): void {
	// When contracts of `fn` refer to a type parameter like `#T`, its symbolic
	// type ID will be retrieved from only the `subscope` map:
	const hidingTypeScope = state.pushHidingTypeScope();
	state.pushTypeScope(typeArgs);
	const postconditionScope = state.pushVariableScope(true);

	traverseBlock(global, valueArgs, postcondition.block, state, {
		// Return ops within a postcondition do not have their own postconditions.
		verifyAtReturn: [],

		// The non-decreasingness of a call within a postcondition is checked
		// where the postcondition is defined, rather than where it is invoked.
		nonDecreasingCallSource: null,
	}, () => {
		state.assumeGuaranteedInPath(postcondition.postcondition);
	});

	state.popVariableScope(postconditionScope);
	state.popTypeScope();
	state.popHidingTypeScope(hidingTypeScope);
}

/**
 * `checkVerifyAtReturns` inspects the current `state` to determine whether each
 * postcondition is satisfied by the given returned values.
 */
function checkVerifyAtReturns(
	global: GlobalContext,
	state: VerificationState,
	returnedValues: uf.ValueID[],
	verifyAtReturns: VerifyAtReturn[],
	diagnosticReturnLocation: ir.SourceLocation,
): void {
	for (const verifyAtReturn of verifyAtReturns) {
		// Bind the necessary inputs (parameters, returned values) for
		// the postcondition.
		const locals = new Map<ir.VariableDefinition, uf.ValueID>();
		for (const [key, spec] of verifyAtReturn.variableScope) {
			if (spec.tag === "returned") {
				locals.set(key, returnedValues[spec.returnedIndex]);
			} else {
				const symbolicSource = spec.symbolic;
				locals.set(key, symbolicSource);
			}
		}

		const postconditionTypeScope = state.pushHidingTypeScope();
		state.pushTypeScope(verifyAtReturn.typeIDScope);
		const postconditionVariableScope = state.pushVariableScope(true);

		traverseBlock(global, locals, verifyAtReturn.postcondition.block, state, {
			// Return ops within a postcondition do not have their own
			// postconditions.
			verifyAtReturn: [],

			// The non-decreasingness of calls within the postcondition must be
			// established without specific access to the values being returned.
			// It is checked along with the well-formedness of the
			// postconditions, rather than at the return site.
			nonDecreasingCallSource: null,
		}, () => {
			const reason: FailedVerification = {
				tag: "failed-postcondition",
				returnLocation: diagnosticReturnLocation,
				postconditionLocation: verifyAtReturn.postcondition.location,
			};

			// Check if it's possible for the indicated boolean to be
			// false.
			const refutation = state.checkPossiblyFalseInPath(verifyAtReturn.postcondition.postcondition, reason);
			if (refutation !== "refuted") {
				global.failedVerifications.push(reason);
			}
		});

		state.popVariableScope(postconditionVariableScope);
		state.popTypeScope();
		state.popHidingTypeScope(postconditionTypeScope);
	}
}

function traverseStaticCall(
	global: GlobalContext,
	op: ir.OpStaticCall,
	state: VerificationState,
	context: VerificationContext,
): void {
	const fn = op.function;
	const signature = global.program.functions[fn].signature;
	if (global.interfaceSignaturesByImplFn.get(fn).length !== 0) {
		throw new Error("impl functions cannot be invoked directly by static calls");
	}

	const valueArgs = [];
	const objectArgs = [];
	for (let i = 0; i < op.arguments.length; i++) {
		const object = state.getValue(op.arguments[i]);
		objectArgs.push(object);
		valueArgs.push(object.value);
	}

	if (context.nonDecreasingCallSource !== null) {
		const refutation = state.checkPossiblyNonDecreasingInPath(objectArgs, context.nonDecreasingCallSource.limit, {
			tag: "failed-totality",
		} as any);

		global.decreasingCallGraph.addCall(context.nonDecreasingCallSource.source, {
			calling: {
				tag: "static",
				functionID: op.function,
			},
			callLocation: op.diagnostic_callsite,
			info: refutation === "refuted" ? "decreasing" : "non-decreasing",
		});
	}

	const typeArgs = [];
	const typeArgsMap = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < op.type_arguments.length; i++) {
		const typeParameter = signature.type_parameters[i];
		const typeArgument = op.type_arguments[i];
		typeArgsMap.set(typeParameter, state.getTypeID(typeArgument));
		typeArgs.push(state.getTypeID(typeArgument));
	}

	if (state.recursivePreconditions.blockedFunctions[fn] !== undefined) {
		throw new diagnostics.RecursivePreconditionErr({
			callsite: op.diagnostic_callsite,
			fn: fn,
		});
	} else {
		state.recursivePreconditions.blockedFunctions[fn] = true;

		const valueArgsMap = new Map<ir.VariableDefinition, uf.ValueID>();
		for (let i = 0; i < valueArgs.length; i++) {
			valueArgsMap.set(signature.parameters[i], valueArgs[i]);
		}

		for (const precondition of signature.preconditions) {
			const reason: FailedVerification = {
				tag: "failed-precondition",
				callLocation: op.diagnostic_callsite,
				preconditionLocation: precondition.location,
			};

			checkPrecondition(global, valueArgsMap, typeArgsMap, precondition, state, reason);
		}

		delete state.recursivePreconditions.blockedFunctions[fn];
	}

	const results = state.staticFunctions.call(fn, {
		valueArgs,
		typeArgs,
	});
	for (let i = 0; i < op.destinations.length; i++) {
		state.defineVariable(op.destinations[i], results[i]);
	}

	if (state.recursivePostconditions.blockedFunctions[fn] !== true) {
		state.recursivePostconditions.blockedFunctions[fn] = true;

		for (const postcondition of signature.postconditions) {
			const valueArgsMap = new Map<ir.VariableDefinition, uf.ValueID>();
			for (let i = 0; i < op.arguments.length; i++) {
				const variable = signature.parameters[i];
				valueArgsMap.set(variable, valueArgs[i]);
			}
			for (let i = 0; i < op.destinations.length; i++) {
				const variable = postcondition.returnedValues[i];
				valueArgsMap.set(variable, results[i]);
			}

			assumePostcondition(global, valueArgsMap, typeArgsMap, postcondition, state);
		}

		delete state.recursivePostconditions.blockedFunctions[fn];
	}
}

function traverseDynamicCall(
	global: GlobalContext,
	op: ir.OpDynamicCall,
	state: VerificationState,
	context: VerificationContext,
): void {
	const constraint = global.program.interfaces[op.constraint.interface];
	const signature = constraint.signatures[op.signature_id];

	const typeArgsMap = new Map<ir.TypeVariableID, uf.ValueID>();
	const typeArgsList = [];
	for (let i = 0; i < op.constraint.subjects.length; i++) {
		const t = op.constraint.subjects[i];
		const id = state.getTypeID(t);
		typeArgsMap.set(constraint.type_parameters[i], id);
		typeArgsList.push(id);
	}
	for (let i = 0; i < op.signature_type_arguments.length; i++) {
		const t = op.signature_type_arguments[i];
		const id = state.getTypeID(t);
		typeArgsMap.set(signature.type_parameters[i], id);
		typeArgsList.push(id);
	}

	const objectArgs = op.arguments.map(v => state.getValue(v));
	const valueArgs = objectArgs.map(x => x.value);

	if (context.nonDecreasingCallSource !== null) {
		const refutation = state.checkPossiblyNonDecreasingInPath(objectArgs, context.nonDecreasingCallSource.limit, {
			tag: "failed-totality",
		} as any);

		global.decreasingCallGraph.addCall(context.nonDecreasingCallSource.source, {
			calling: {
				tag: "dynamic",
				interfaceID: op.constraint.interface,
				memberID: op.signature_id,
			},
			callLocation: op.diagnostic_callsite,
			info: refutation === "refuted" ? "decreasing" : "non-decreasing",
		});
	}

	for (const precondition of signature.preconditions) {
		throw new Error("TODO");
	}

	const results = state.dynamicFunctions.call(op.constraint.interface, op.signature_id as ir.FunctionID, {
		valueArgs,
		interfaceTypeArgs: typeArgsList,
	});
	for (let i = 0; i < op.destinations.length; i++) {
		state.defineVariable(op.destinations[i], results[i]);
	}

	for (const postcondition of signature.postconditions) {
		throw new Error("TODO");
	}

	if (signature.semantics?.eq === true) {
		throw new Error("TODO");
	}
}

function traverseForeignCall(
	global: GlobalContext,
	op: ir.OpForeign,
	state: VerificationState,
	context: VerificationContext,
): void {
	const signature = global.program.foreign[op.operation];

	for (let precondition of signature.preconditions) {
		throw new Error("TODO: Check precondition of op-foreign");
	}

	const valueArgs = [];
	for (let i = 0; i < op.arguments.length; i++) {
		valueArgs.push(state.getValue(op.arguments[i]).value);
	}

	const typeArgsMap: Map<ir.TypeVariableID, uf.ValueID> = new Map();
	if (signature.type_parameters.length !== 0) {
		throw new Error("TODO: allow type-parameters in foreign functions");
	}

	const results = [];
	if (signature.semantics?.eq === true) {
		if (op.arguments.length !== 2) {
			throw new Error("Foreign signature with `eq` semantics"
				+ " must take exactly 2 arguments (" + op.operation + ")");
		} else if (op.destinations.length !== 1) {
			throw new Error("Foreign signature with `eq` semantics"
				+ " must return exactly 1 value");
		}
		const destination = op.destinations[0];
		const result = state.eq(valueArgs[0], valueArgs[1]);
		results.push(result);
		state.defineVariable(destination, result);
	} else {
		const fIDs = state.foreign.get(op.operation);
		for (let i = 0; i < op.destinations.length; i++) {
			const result = state.smt.createApplication(fIDs[i], valueArgs);
			results.push(result);
			state.defineVariable(op.destinations[i], result);
		}
	}

	const fnKey = "foreign{{" + op.operation + "}}";
	if (state.recursivePostconditions.blockedFunctions[fnKey] !== true) {
		state.recursivePostconditions.blockedFunctions[fnKey] = true;

		for (const postcondition of signature.postconditions) {
			const valueArgsMap = new Map<ir.VariableDefinition, uf.ValueID>();
			for (let i = 0; i < op.arguments.length; i++) {
				const variable = signature.parameters[i];
				valueArgsMap.set(variable, valueArgs[i]);
			}
			for (let i = 0; i < op.destinations.length; i++) {
				const variable = postcondition.returnedValues[i];
				valueArgsMap.set(variable, results[i]);
			}

			assumePostcondition(global, valueArgsMap, typeArgsMap, postcondition, state);
		}

		delete state.recursivePostconditions.blockedFunctions[fnKey];
	}
}

interface DirectedGraph<E, V> {
	/**
	 * `getOutgoing(from)` returns the set of edges originating at vertex
	 * `from`.
	 * 
	 * Each `to` is guaranteed to have the same identity when representing the
	 * same vertex.
	 */
	getOutgoing(from: V): { from: V, edge: E, to: V }[];

	getVertexes(): V[];
}

function verifyCallGraphTotality(
	callGraph: CallGraph<"decreasing" | "non-decreasing">,
): FailedVerification[] {
	const nonTerminatingCycles: FailedVerification[] = [];

	// throw new Error("TODO");

	return nonTerminatingCycles;
}

/// RETURNS a CNF clausification restricting solutions to those where the
/// lexicographic comparison `lefts < rights` is NOT true.
/// Note that when one tuple is a preifx of the other, the shorter tuple is
/// considered to be smaller.
export function clausifyNotSmallerThan(
	smt: uf.UFTheory,
	{ eqF, ltF, negF }: { eqF: uf.FnID, ltF: uf.FnID, negF: uf.FnID },
	lefts: uf.ValueID[],
	rights: uf.ValueID[],
): uf.ValueID[][] {
	const out: uf.ValueID[][] = [];
	const neqs: uf.ValueID[] = [];
	for (let i = 0; i <= lefts.length; i++) {
		const left = lefts[i];
		const right = rights[i];
		let cmp: uf.ValueID;
		if (left !== undefined && right !== undefined) {
			cmp = smt.createApplication(ltF, [left, right]);
		} else if (left === undefined && right === undefined) {
			break;
		} else if (left === undefined) {
			cmp = smt.createConstant(ir.T_BOOLEAN, true);
		} else if (right === undefined) {
			cmp = smt.createConstant(ir.T_BOOLEAN, false);
		} else {
			throw new Error("clausifyNotSmallerThan: unreachable");
		}

		const ncmp = smt.createApplication(negF, [cmp]);
		out.push([ncmp, ...neqs]);
		if (left === undefined || right === undefined) {
			break;
		}
		const eq = smt.createApplication(eqF, [left, right]);
		const neq = smt.createApplication(negF, [eq]);
		neqs.push(neq);
	}
	return out;
}
