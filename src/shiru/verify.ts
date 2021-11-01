import { DefaultMap } from "./data";
import * as diagnostics from "./diagnostics";
import * as ir from "./ir";
import { displayType } from "./semantics";
import * as uf from "./uf";

export function verifyProgram(
	program: ir.Program,
): FailedVerification[] {
	const problems = [];

	// 1) Verify each function body,
	for (let f in program.functions) {
		problems.push(...verifyFunction(program, f));
	}

	// 2) Verify that each interface implementation
	for (let v in program.globalVTableFactories) {
		// 2a) has weaker preconditions
		// 2b) has stronger postconditions
		problems.push(...verifyImpl(program, v));
	}

	return problems;
}

const foreignInterpeters = {
	"Int+": {
		f(a: unknown | null, b: unknown | null): unknown | null {
			if (a === null || b === null) {
				return null;
			} else if (typeof a !== "bigint") {
				throw new Error("foreignInterpreters['Int+']: got non bigint `" + a + "`");
			} else if (typeof b !== "bigint") {
				throw new Error("foreignInterpreters['Int+']: got non bigint `" + b + "`");
			}
			return (a as bigint) + (b as bigint);
		},
	},
};

function verifyFunction(
	program: ir.Program,
	fName: string,
): FailedVerification[] {
	const state = new VerificationState(program, foreignInterpeters);

	const f = program.functions[fName];

	// Create the initial type scope, which maps each type parameter to an
	// unknown symbolic type ID constant.
	const typeScope = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < f.signature.type_parameters.length; i++) {
		const typeParameter = f.signature.type_parameters[i];
		typeScope.set(typeParameter, state.smt.createVariable(ir.T_ANY));
	}
	state.pushTypeScope(typeScope);

	// Initialize the function's arguments.
	const contextParameters = [];
	for (let i = 0; i < f.signature.parameters.length; i++) {
		const parameter = f.signature.parameters[i];

		// Create a symbolic constant for the initial value of the parameter.
		const symbolic = state.smt.createVariable(parameter.type);
		state.defineVariable(parameter, symbolic);
		contextParameters.push({
			definition: parameter,
			symbolic,
		});
	}

	// Execute and validate the function's preconditions.
	for (let i = 0; i < f.signature.preconditions.length; i++) {
		const precondition = f.signature.preconditions[i];
		traverseBlock(program, new Map(), precondition.block, state, {
			// Return statements do not return a value.
			returnsPostConditions: [],
			parameters: contextParameters,
		}, () => {
			const bool = state.getValue(precondition.precondition).value;
			state.pushPathConstraint(state.negate(bool));
			state.markPathUnreachable();
			state.popPathConstraint();
		});
	}

	// Validate that the function's postconditions explicitly guarantee their
	// requirements.
	state.smt.pushScope();
	let symbolicReturned = [];
	for (const r of f.signature.return_types) {
		symbolicReturned.push(state.smt.createVariable(r));
	}
	for (const postcondition of f.signature.postconditions) {
		const local = new Map<ir.VariableDefinition, uf.ValueID>();
		for (let i = 0; i < symbolicReturned.length; i++) {
			local.set(postcondition.returnedValues[i], symbolicReturned[i]);
		}
		traverseBlock(program, local, postcondition.block, state, {
			returnsPostConditions: [],
			parameters: contextParameters,
		}, () => {
			const bool = state.getValue(postcondition.postcondition).value;
			state.pushPathConstraint(state.negate(bool));
			state.markPathUnreachable();
			state.popPathConstraint();
		});
	}
	state.smt.popScope();

	// Check the function's body (including that each return op guarantees the
	// ensured postconditions).
	traverseBlock(program, new Map(), f.body, state, {
		returnsPostConditions: f.signature.postconditions,
		parameters: contextParameters,
	});

	// The IR type-checker verifies that functions must end with a op-return or
	// op-unreachable.
	return state.failedVerifications;
}

function verifyImpl(
	program: ir.Program,
	implName: string,
): FailedVerification[] {
	const state = new VerificationState(program, foreignInterpeters);

	const impl = program.globalVTableFactories[implName];
	const specification = program.interfaces[impl.provides.interface];

	throw new Error("TODO: implement verifyImpl");
}

interface VerificationContext {
	/// The post-conditions to verify at a ReturnStatement.
	returnsPostConditions: ir.Postcondition[],

	/// The number of function parameters.
	parameters: { definition: ir.VariableDefinition, symbolic: uf.ValueID }[],
}

export type FailedVerification = FailedPreconditionVerification
	| FailedAssertVerification
	| FailedReturnVerification
	| FailedPostconditionValidation
	| FailedVariantVerification;

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

interface SignatureSet {
	blockedFunctions: Record<string, boolean>,
	blockedInterfaces: Record<string, Record<string, string>>,
}

interface VerificationScope {
	variables: Map<ir.VariableID, { type: ir.Type, value: uf.ValueID }>,
}

// TODO: Optimize this to not do linear scans.
class TypeArgumentsDefaultMap<V> {
	private entries: { key: ir.Type[], value: V }[] = [];

	constructor(private f: (key: ir.Type[]) => V) { }

	get(key: ir.Type[]) {
		for (const entry of this.entries) {
			let all = true;
			for (let i = 0; i < key.length; i++) {
				if (!ir.equalTypes(key[i], entry.key[i])) {
					all = false;
					break;
				}
			}
			if (all) {
				return entry.value;
			}
		}
		const value = this.f(key);
		this.entries.push({ key: key.slice(0), value });
		return value;
	}
}

class DynamicFunctionMap {
	private map = new DefaultMap<ir.InterfaceID, DefaultMap<ir.FunctionID, TypeArgumentsDefaultMap<uf.FnID[]>>>(
		i => new DefaultMap(s => new TypeArgumentsDefaultMap(ts => {
			const interfaceIR = this.program.interfaces[i];
			const signature = interfaceIR.signatures[s];
			const map = ir.typeArgumentsMap(interfaceIR.type_parameters.concat(signature.type_parameters), ts);
			const rs = signature.return_types.map(r => ir.typeSubstitute(r, map));
			return rs.map(r => this.smt.createFunction(r, { eq: signature.semantics?.eq }));
		})));

	constructor(private program: ir.Program, private smt: uf.UFTheory) { }

	get(interfaceID: ir.InterfaceID, signatureID: ir.FunctionID, typeArguments: ir.Type[]) {
		return this.map.get(interfaceID).get(signatureID).get(typeArguments);
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
			fields[k] = this.smt.createFunction(record.fields[k], {});
		}

		const recordType: ir.TypeCompound = {
			tag: "type-compound",
			base: r,
			type_arguments: record.type_parameters.map(x => ({ tag: "type-any" })),
		};
		return {
			constructor: this.smt.createFunction(recordType, {}),
			fields,
			typeID: this.smt.createFunction(ir.T_INT, {}),
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
			constructors[variant] = this.smt.createFunction(enumType, {});
			destructors[variant] = this.smt.createFunction(variantType, {});
			tagValues[variant] = this.smt.createConstant(ir.T_INT, tagIndex);
			tagIndex += 1;
		}

		return {
			extractTag: this.smt.createFunction(ir.T_INT, {}),
			constructors,
			destructors,
			tagValues,
			typeID: this.smt.createFunction(ir.T_INT, {}),
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
	private program: ir.Program;
	private foreignInterpreters: Record<string, uf.Semantics["interpreter"]>;

	smt: uf.UFTheory = new uf.UFTheory();
	notF = this.smt.createFunction(ir.T_BOOLEAN, { not: true });
	eqF = this.smt.createFunction(ir.T_BOOLEAN, { eq: true });

	/// Generates a SMT function for each return of each Shiru fn.
	/// The first parameters are the type arguments (type id).
	functions: DefaultMap<ir.FunctionID, uf.FnID[]> = new DefaultMap(fnID => {
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
			out.push(this.smt.createFunction(resultType, { eq: fn.signature.semantics?.eq }));
		}
		return out;
	});

	foreign = new DefaultMap<string, uf.FnID[]>(op => {
		const fn = this.program.foreign[op];
		if (fn === undefined) {
			throw new Error("VerificationState.foreign.get: undefined `" + op + "`");
		}
		const out = [];
		for (const r of fn.return_types) {
			out.push(this.smt.createFunction(r, {
				eq: fn.semantics?.eq,
				interpreter: this.foreignInterpreters[op],
			}));
		}
		return out;
	});

	dynamicFunctions: DynamicFunctionMap;
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
	private varScopes: VerificationScope[] = [
		{
			variables: new Map(),
		}
	];

	/// `typeScopes` is a stack of type parameter --> TypeID values.
	private typeScopes: Map<ir.TypeVariableID, uf.ValueID>[] = [];

	pushTypeScope(scope: Map<ir.TypeVariableID, uf.ValueID>) {
		this.typeScopes.push(scope);
	}

	popTypeScope() {
		this.typeScopes.pop();
	}

	private unitTypeID = this.smt.createConstant(ir.T_INT, 21);
	private booleanTypeID = this.smt.createConstant(ir.T_INT, 22);
	private intTypeID = this.smt.createConstant(ir.T_INT, 23);
	private bytesTypeID = this.smt.createConstant(ir.T_INT, 24);
	private anyTypeID = this.smt.createConstant(ir.T_INT, 25);

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
				const _: never = t.primitive;
				throw new Error("getTypeID: unhandled primitive `" + t["primitive"] + "`");
			}
		} else if (t.tag === "type-variable") {
			for (let i = this.typeScopes.length - 1; i >= 0; i--) {
				const scope = this.typeScopes[i];
				const mapping = scope.get(t.id);
				if (mapping !== undefined) {
					return mapping;
				}
			}
			throw new Error("getTypeID: unmapped type-variable `" + t.id + "`");
		} else if (t.tag === "type-compound") {
			const args = t.type_arguments.map(x => this.getTypeID(x));
			const base = t.base;
			if (this.program.records[base] !== undefined) {
				return this.recordMap.typeID(base as ir.RecordID, args);
			} else {
				return this.enumMap.typeID(base as ir.EnumID, args);
			}
		} else {
			const _: never = t;
			throw new Error("getTypeID: unhandled type tag `" + t["tag"] + "`");
		}
	}

	/// `pathConstraints` is the stack of conditional constraints that must be
	/// true to reach a position in the program.
	private pathConstraints: uf.ValueID[] = [];

	// Verification adds failure messages to this stack as they are encountered.
	// Multiple failures can be returned.
	failedVerifications: FailedVerification[] = [];

	constructor(
		program: ir.Program,
		foreignInterpeters: Record<string, uf.Semantics["interpreter"]>,
	) {
		this.program = program;
		this.foreignInterpreters = foreignInterpeters;
		this.dynamicFunctions = new DynamicFunctionMap(this.program, this.smt);
		this.recordMap = new RecordMap(this.program, this.smt);
		this.enumMap = new EnumMap(this.program, this.smt);

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

	pushDefinitionScope() {
		this.varScopes.push({
			variables: new Map(),
		});
	}

	popDefinitionScope() {
		this.varScopes.pop();
	}

	pushPathConstraint(c: uf.ValueID) {
		this.pathConstraints.push(c);
	}

	popPathConstraint() {
		this.pathConstraints.pop();
	}

	/// `checkReachable` checks whether or not the conjunction of current path
	/// constraints, combined with all other constraints added to the `smt`
	/// solver, is reachable or not.
	checkReachable(reason: FailedVerification): uf.UFCounterexample | "refuted" {
		this.smt.pushScope();
		for (const constraint of this.pathConstraints) {
			this.smt.addConstraint([constraint]);
		}
		const model = this.smt.attemptRefutation();
		this.smt.popScope();
		return model;
	}

	/// `markPathUnreachable` ensures that the conjunction of the current path
	/// constraints is not considered satisfiable in subsequent invocations of
	/// the `smt` solver.
	markPathUnreachable() {
		const pathUnreachable = this.pathConstraints.map(e => this.negate(e));
		this.smt.addConstraint(pathUnreachable);
	}

	defineVariable(variable: ir.VariableDefinition, value: uf.ValueID) {
		const scope = this.varScopes[this.varScopes.length - 1];
		scope.variables.set(variable.variable, {
			type: variable.type,
			value: value,
		});
	}

	getValue(variable: ir.VariableID) {
		for (let i = this.varScopes.length - 1; i >= 0; i--) {
			const scope = this.varScopes[i];
			const value = scope.variables.get(variable);
			if (value !== undefined) {
				return value;
			}
		}
		throw new Error("variable `" + variable + "` is not defined");
	}
}

function traverseBlock(
	program: ir.Program,
	locals: Map<ir.VariableDefinition, uf.ValueID>,
	block: ir.OpBlock,
	state: VerificationState,
	context: VerificationContext,
	then?: () => unknown,
) {
	// Blocks bound variable scopes, so variables must be cleared after.
	state.pushDefinitionScope();

	for (const [k, v] of locals) {
		state.defineVariable(k, v);
	}

	for (let subop of block.ops) {
		traverse(program, subop, state, context);
	}

	// Execute the final computation before exiting this scope.
	if (then !== undefined) {
		then();
	}

	// Clear variables defined within this block.
	state.popDefinitionScope();
}

// MUTATES the verification state parameter, to add additional clauses that are
// ensured after the execution (and termination) of this operation.
function traverse(program: ir.Program, op: ir.Op, state: VerificationState, context: VerificationContext): void {
	if (op.tag === "op-branch") {
		const symbolicCondition: uf.ValueID = state.getValue(op.condition).value;

		const phis: uf.ValueID[] = [];
		for (const destination of op.destinations) {
			phis.push(state.smt.createVariable(destination.destination.type));
		}

		state.pushPathConstraint(symbolicCondition);
		traverseBlock(program, new Map(), op.trueBranch, state, context, () => {
			for (let i = 0; i < op.destinations.length; i++) {
				const destination = op.destinations[i];
				const source = destination.trueSource;
				if (source === "undef") continue;
				state.smt.addConstraint([
					state.negate(symbolicCondition),
					state.eq(phis[i], state.getValue(source).value),
				]);
			}
		})
		state.popPathConstraint();

		state.pushPathConstraint(state.negate(symbolicCondition));
		traverseBlock(program, new Map(), op.falseBranch, state, context, () => {
			for (let i = 0; i < op.destinations.length; i++) {
				const destination = op.destinations[i];
				const source = destination.falseSource;
				if (source === "undef") continue;
				state.smt.addConstraint([
					symbolicCondition,
					state.eq(phis[i], state.getValue(source).value),
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
		state.defineVariable(op.destination, fieldValue);
		return;
	} else if (op.tag === "op-is-variant") {
		const object = state.getValue(op.base);
		const baseType = object.type as ir.TypeCompound & { base: ir.EnumID };

		const tagInfo = state.enumMap.hasTag(baseType.base, object.value, op.variant, state);
		state.smt.addConstraint(tagInfo.finiteAlternativesClause);
		state.defineVariable(op.destination, tagInfo.testResult);
		return;
	} else if (op.tag === "op-variant") {
		const object = state.getValue(op.object);
		const baseType = object.type as ir.TypeCompound & { base: ir.EnumID };

		// Check that the symbolic tag definitely matches this variant.
		const tagInfo = state.enumMap.hasTag(baseType.base, object.value, op.variant, state);
		state.smt.addConstraint(tagInfo.finiteAlternativesClause);

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
			state.failedVerifications.push(reason);
		}

		state.markPathUnreachable();
		state.popPathConstraint();

		// Extract the field.
		const variantValue = state.enumMap.destruct(baseType.base, object.value, op.variant);
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
		state.smt.addConstraint([tagInfo.testResult]);

		const destruction = state.enumMap.destruct(enumType.base, enumValue, op.variant);
		state.smt.addConstraint([state.eq(destruction, variantValue)]);
		return;
	} else if (op.tag === "op-proof") {
		return traverseBlock(program, new Map(), op.body, state, context);
	} else if (op.tag === "op-return") {
		if (context.returnsPostConditions.length !== 0) {
			for (let postcondition of context.returnsPostConditions) {
				// The original parameters might have been shadowed, so they
				// need to be redeclared.
				const locals = new Map<ir.VariableDefinition, uf.ValueID>();
				for (const parameter of context.parameters) {
					locals.set(parameter.definition, parameter.symbolic);
				}
				for (let i = 0; i < postcondition.returnedValues.length; i++) {
					locals.set(postcondition.returnedValues[i], state.getValue(op.sources[i]).value);
				}

				traverseBlock(program, locals, postcondition.block, state, context, () => {
					const reason: FailedVerification = {
						tag: "failed-postcondition",
						returnLocation: op.diagnostic_return_site,
						postconditionLocation: postcondition.location,
					};

					// Check if it's possible for the indicated boolean to be
					// false.
					const bool = state.getValue(postcondition.postcondition).value;
					state.pushPathConstraint(state.negate(bool));
					const refutation = state.checkReachable(reason);
					state.popPathConstraint();
					if (refutation !== "refuted") {
						state.failedVerifications.push(reason);
					}
				});
			}
		}

		// Subsequently, this path is treated as unreachable, since the function
		// exited.
		state.markPathUnreachable();
		return;
	} else if (op.tag === "op-foreign") {
		const signature = program.foreign[op.operation];

		for (let precondition of signature.preconditions) {
			throw new Error("TODO: Check precondition of op-foreign");
		}

		for (let postcondition of signature.postconditions) {
			throw new Error("TODO: Assume postcondition of op-foreign");
		}

		const args = [];
		for (let i = 0; i < op.arguments.length; i++) {
			args.push(state.getValue(op.arguments[i]).value);
		}

		if (signature.semantics?.eq === true) {
			if (op.arguments.length !== 2) {
				throw new Error("Foreign signature with `eq` semantics"
					+ " must take exactly 2 arguments (" + op.operation + ")");
			} else if (op.destinations.length !== 1) {
				throw new Error("Foreign signature with `eq` semantics"
					+ " must return exactly 1 value");
			}
			const destination = op.destinations[0];
			state.defineVariable(destination, state.eq(args[0], args[1]));
		} else {
			const fIDs = state.foreign.get(op.operation);
			for (let i = 0; i < op.destinations.length; i++) {
				state.defineVariable(op.destinations[i], state.smt.createApplication(fIDs[i], args));
			}
		}
		return;
	} else if (op.tag === "op-static-call") {
		traverseStaticCall(program, op, state, context);
		return;
	} else if (op.tag === "op-dynamic-call") {
		const typeArguments = op.constraint.subjects.concat(op.signature_type_arguments);
		const fs = state.dynamicFunctions.get(op.constraint.interface, op.signature_id as ir.FunctionID, typeArguments);
		const constraint = program.interfaces[op.constraint.interface];
		const signature = constraint.signatures[op.signature_id];

		for (let precondition of signature.preconditions) {
			throw new Error("TODO");
		}

		for (let postcondition of signature.postconditions) {
			throw new Error("TODO");
		}

		if (signature.semantics?.eq === true) {
			throw new Error("TODO");
		}

		throw new Error("traverse: TODO: op-dynamic-call");
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
			state.failedVerifications.push(reason);
		}

		// Like a return statement, this path is subsequently treated as
		// unreachable.
		state.markPathUnreachable();
		return;
	}

	const _: never = op;
	throw new Error(`unhandled op ${op["tag"]}`);
}

function traverseStaticCall(
	program: ir.Program,
	op: ir.OpStaticCall,
	state: VerificationState,
	context: VerificationContext,
) {
	const fn = op.function;
	const signature = program.functions[fn].signature;

	const args = [];
	for (let i = 0; i < op.arguments.length; i++) {
		args.push(state.getValue(op.arguments[i]).value);
	}

	const subscope = new Map<ir.TypeVariableID, uf.ValueID>();
	for (let i = 0; i < op.type_arguments.length; i++) {
		const typeParameter = signature.type_parameters[i];
		const typeArgument = op.type_arguments[i];
		subscope.set(typeParameter, state.getTypeID(typeArgument));
		args.push(state.getTypeID(typeArgument));
	}

	// When contracts refer to a type parameter like `#T`, its symbolic type ID
	// will be retrieved from this map:
	state.pushTypeScope(subscope);

	if (state.recursivePreconditions.blockedFunctions[fn] !== undefined) {
		throw new diagnostics.RecursivePreconditionErr({
			callsite: op.diagnostic_callsite,
			fn: fn,
		});
	} else {
		state.recursivePreconditions.blockedFunctions[fn] = true;

		for (const precondition of signature.preconditions) {
			const recursiveContext: VerificationContext = {
				returnsPostConditions: [],
				parameters: [],
			};
			const locals = new Map<ir.VariableDefinition, uf.ValueID>();
			for (let i = 0; i < op.arguments.length; i++) {
				locals.set(signature.parameters[i], args[i]);
				recursiveContext.parameters.push({
					definition: signature.parameters[i],
					symbolic: args[i],
				});
			}

			traverseBlock(program, locals, precondition.block, state, recursiveContext, () => {
				const reason: FailedVerification = {
					tag: "failed-precondition",
					callLocation: op.diagnostic_callsite,
					preconditionLocation: precondition.location,
				};

				const bool = state.getValue(precondition.precondition).value;
				state.pushPathConstraint(state.negate(bool));
				const refutation = state.checkReachable(reason);
				if (refutation !== "refuted") {
					state.failedVerifications.push(reason);
				}
				state.popPathConstraint();
			});
		}

		delete state.recursivePreconditions.blockedFunctions[fn];
	}

	const smtFns = state.functions.get(fn);
	for (let i = 0; i < op.destinations.length; i++) {
		const result = state.smt.createApplication(smtFns[i], args);
		state.defineVariable(op.destinations[i], result);
	}

	if (state.recursivePostconditions.blockedFunctions[fn] !== true) {
		for (const postcondition of signature.postconditions) {
			state.recursivePostconditions.blockedFunctions[fn] = true;
			const locals = new Map<ir.VariableDefinition, uf.ValueID>();
			for (let i = 0; i < op.arguments.length; i++) {
				const variable = signature.parameters[i];
				const value = state.getValue(op.arguments[i]).value;
				locals.set(variable, value);
			}
			for (let i = 0; i < op.destinations.length; i++) {
				const variable = postcondition.returnedValues[i];
				const value = state.getValue(op.destinations[i].variable).value;
				locals.set(variable, value);
			}

			// TODO: Do we need a different context?
			traverseBlock(program, locals, postcondition.block, state, context, () => {
				const bool = state.getValue(postcondition.postcondition).value;
				state.pushPathConstraint(state.negate(bool));
				state.markPathUnreachable();
				state.popPathConstraint();
			});

			delete state.recursivePostconditions.blockedFunctions[fn];
		}
	}

	state.popTypeScope();
}
