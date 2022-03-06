import { DefaultMap } from "./data";
import * as diagnostics from "./diagnostics";
import * as ir from "./ir";
import { displayType } from "./semantics";
import * as uf from "./uf";

export function verifyProgram(
	program: ir.Program,
): FailedVerification[] {
	const problems = [];

	// Index impls by their interface signatures.
	const interfaceSignaturesByImplFn = indexInterfaceSignaturesByImplFn(program);

	// Verify each interface signature.
	for (const i in program.interfaces) {
		problems.push(...verifyInterface(program, i, interfaceSignaturesByImplFn));
	}

	// Verify each function body.
	for (let f in program.functions) {
		problems.push(...verifyFunction(program, f, interfaceSignaturesByImplFn));
	}

	return problems;
}

function verifyInterface(
	program: ir.Program,
	interfaceName: string,
	interfaceSignaturesByImplFn: DefaultMap<ir.FunctionID, IndexedImpl[]>,
): FailedVerification[] {
	const state = new VerificationState(program, interfaceSignaturesByImplFn);
	const trait = program.interfaces[interfaceName];

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
	for (const member in trait.signatures) {
		const signature = trait.signatures[member];

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
		for (const parameter of signature.parameters) {
			state.defineVariable(parameter,
				state.smt.createVariable(parameter.type, parameter.variable));
		}

		// Verify that preconditions explicitly state their own preconditions,
		// and assume that they hold for postconditions.
		for (const precondition of signature.preconditions) {
			traverseBlock(program, new Map(), precondition.block, state, {
				// Return ops within a precondition don't have their own
				// postconditions.
				verifyAtReturn: [],
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
			traverseBlock(program, local, postcondition.block, state, {
				// Return ops within a postcondition don't have their own
				// postconditions.
				verifyAtReturn: [],
			}, () => {
				state.assumeGuaranteedInPath(postcondition.postcondition);
			});
		}

		state.popVariableScope(functionScope);
		state.popTypeScope();
	}

	state.popTypeScope();

	return state.failedVerifications;
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

function getForeignInterpreters(
	state: VerificationState,
): Record<string, {
	interpreter?: (...args: (unknown | null)[]) => unknown | null,
	generalInterpreter?: (
		matcher: uf.EMatcher<number>,
		id: uf.ValueID,
		operands: uf.ValueID[],
	) => "change" | "no-change",
}> {
	return {
		"Int-unary": {
			interpreter(a: unknown): unknown | null {
				if (a === null) {
					return null;
				} else if (typeof a !== "bigint") {
					return null;
				} else {
					return -(a as bigint);
				}
			},
		},
		"Int+": {
			interpreter(a: unknown | null, b: unknown | null): unknown | null {
				if (a === null || b === null) {
					return null;
				} else if (typeof a !== "bigint") {
					return null;
				} else if (typeof b !== "bigint") {
					return null;
				}

				return (a as bigint) + (b as bigint);
			},

			generalInterpreter(
				matcher: uf.EMatcher<number>,
				id: uf.ValueID,
				operands: uf.ValueID[],
			): "change" | "no-change" {
				const sum = state.foreign.get("Int+")[0];
				const left = operands[0];
				const right = operands[1];

				let change: "change" | "no-change" = "no-change";

				// Resolve commutativity by swapping all sums.
				const swapped = matcher.hasApplication(sum, [right, left]);
				if (swapped !== null) {
					let freshCommutative = matcher.merge(id, swapped, new Set());
					if (freshCommutative) {
						change = "change";
					}
				}

				// Resolve associativity by canonicalizing all left sums to
				// be left-leaning.
				const rightSums = matcher.matchAsApplication(right, sum);
				for (const rightSum of rightSums) {
					const a = rightSum.operands[0];
					const b = rightSum.operands[1];

					const leftASum = matcher.hasApplication(sum, [left, a]);
					if (leftASum !== null) {
						const leftLeaning = matcher.hasApplication(sum, [
							leftASum, b,
						]);

						if (leftLeaning !== null) {
							const freshAssociative = matcher.merge(id, leftLeaning, rightSum.reason);
							if (freshAssociative) {
								change = "change";
							}
						}
					}
				}

				return change;
			}
		},
		"Int<": {
			interpreter(a: unknown | null, b: unknown | null): unknown | null {
				if (a === null || b === null) {
					return null;
				} else if (typeof a !== "bigint") {
					return null;
				} else if (typeof b !== "bigint") {
					return null;
				}
				return (a as bigint) < (b as bigint);
			},

			generalInterpreter(
				matcher: uf.EMatcher<number>,
				id: uf.ValueID,
				operands: uf.ValueID[],
			): "change" | "no-change" {
				const sum = state.foreign.get("Int+")[0];
				const lt = state.foreign.get("Int<")[0];
				const left = operands[0];
				const right = operands[1];

				const leftSums = matcher.matchAsApplication(left, sum);
				const rightSums = matcher.matchAsApplication(right, sum);

				// TODO: Improve performance by indexing sums by their terms
				// instead of doing a quadratic scan when many are equal.
				// Search for the pattern 
				// a + k1 < b + k2 where k1 = k2.
				let change: "change" | "no-change" = "no-change";
				for (const leftSum of leftSums) {
					for (const rightSum of rightSums) {
						const kQuery = matcher.query(leftSum.operands[1], rightSum.operands[1]);
						if (kQuery !== null) {
							// Equate this with `a < b`, using the reason
							// which is why
							// left == (a+k1) and right == (b+k2)
							// and k1 == k2.
							const newLt = matcher.hasApplication(lt, [
								leftSum.operands[0],
								rightSum.operands[0],
							]);
							if (newLt === null) {
								continue;
							}
							const reason = new Set([
								...leftSum.reason,
								...rightSum.reason,
								...kQuery,
							]);
							const fresh = matcher.merge(id, newLt, reason);
							if (fresh) {
								change = "change";
							}
						}
					}
				}

				return change;
			},
		},
	};
}

function assumeStaticPreconditions(
	program: ir.Program,
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

	for (let i = 0; i < signature.preconditions.length; i++) {
		const precondition = signature.preconditions[i];
		traverseBlock(program, valueScope, precondition.block, state, {
			// Return ops within a precondition block do not have their own
			// postconditions.
			verifyAtReturn: [],
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
	program: ir.Program,
	valueArguments: uf.ValueID[],
	implFnTypeArguments: uf.ValueID[],
	implementing: IndexedImpl,
	state: VerificationState,
): void {
	const impl = program.globalVTableFactories[implementing.implID];
	const interfaceEntity = program.interfaces[impl.provides.interface];
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
		traverseBlock(program, variableScope, precondition.block, state, {
			verifyAtReturn: [],
		}, () => {
			state.assumeGuaranteedInPath(precondition.precondition);
		});
	}

	state.popVariableScope(hidingVariableScope);
	state.popTypeScope();
	state.popHidingTypeScope(hidingTypeScope);
}

function generateToVerifyFromConstraint(
	program: ir.Program,
	valueArguments: uf.ValueID[],
	implFnTypeArguments: uf.ValueID[],
	implementing: IndexedImpl,
	state: VerificationState,
): VerifyAtReturn[] {
	const impl = program.globalVTableFactories[implementing.implID];
	const interfaceEntity = program.interfaces[impl.provides.interface];
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
	program: ir.Program,
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
		assumePostcondition(program, valueArgs, verifyAtReturn.typeIDScope, verifyAtReturn.postcondition, state);
	}
	state.smt.popScope();
}

/// interfaceSignaturesByImplFn: Explains which interface signatures each fn
/// implements. Any preconditions from the indicated interfaces should be
/// automatically assumed, and any postconditions should be automatically
/// checked.
function verifyFunction(
	program: ir.Program,
	fName: string,
	interfaceSignaturesByImplFn: DefaultMap<ir.FunctionID, IndexedImpl[]>,
): FailedVerification[] {
	const interfaceSignatures = interfaceSignaturesByImplFn.get(fName as ir.FunctionID);
	const state = new VerificationState(program, interfaceSignaturesByImplFn);

	const f = program.functions[fName];

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
	for (let i = 0; i < f.signature.parameters.length; i++) {
		const parameter = f.signature.parameters[i];

		// Create a symbolic constant for the initial value of the parameter.
		const symbolic = state.smt.createVariable(parameter.type, parameter.variable);
		state.defineVariable(parameter, symbolic);
		symbolicArguments.push(symbolic);
	}

	// Execute and validate the function's preconditions.
	assumeStaticPreconditions(program, f.signature, symbolicArguments, typeArguments, state);

	const verifyAtReturns: VerifyAtReturn[] = [];

	// Collect postconditions from an impl fn.
	for (const interfaceSignatureReference of interfaceSignatures) {
		if (f.signature.preconditions.length !== 0) {
			throw new Error("impl function `" + fName + "` must not impose explicit preconditions");
		}

		assumeConstraintPreconditions(program, symbolicArguments, typeArguments, interfaceSignatureReference, state);
		verifyAtReturns.push(...generateToVerifyFromConstraint(program, symbolicArguments, typeArguments, interfaceSignatureReference, state));
	}

	// Collect explicit postconditions from a fn.
	verifyAtReturns.push(...generateToVerifyFromStatic(f.signature, symbolicArguments, typeArguments));

	// Validate that the function's postconditions are well-formed, in that they
	// explicitly guarantee their internal preconditions.
	verifyPostconditionWellFormedness(program, f.signature, state, verifyAtReturns);

	// Check the function's body (including that each return op guarantees the
	// ensured postconditions).
	traverseBlock(program, new Map(), f.body, state, {
		verifyAtReturn: verifyAtReturns,
	});

	const lastOp = f.body.ops[f.body.ops.length - 1];
	if (!ir.opTerminates(lastOp)) {
		throw new Error("ICE: verifyFunction invoked on a function which does not obviously terminate");
	}

	return state.failedVerifications;
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
			const rs = signature.return_types.map(r => ir.typeSubstitute(r, map));
			const fnIDs = [];
			for (let i = 0; i < signature.return_types.length; i++) {
				const returnType = ir.typeSubstitute(signature.return_types[i], map);
				fnIDs[i] = this.smt.createFunction(returnType, { eq: signature.semantics?.eq },
					i + "." + s + (signature.return_types.length !== 0 ? "." + i : ""));
			}
			return fnIDs;
		}));

	constructor(private program: ir.Program, private smt: uf.UFTheory) { }

	/// Retrieves the single function identity across all implementations of the
	/// interface.
	/// Invocations of the function in the SMT engine take
	/// value arguments ++ interface type arguments ++ signature type arguments.
	get(interfaceID: ir.InterfaceID, signatureID: ir.FunctionID) {
		return this.map.get(interfaceID).get(signatureID);
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
	private program: ir.Program;
	private foreignInterpreters: Record<string, Pick<uf.Semantics<number>, "interpreter" | "generalInterpreter">>;

	smt: uf.UFTheory = new uf.UFTheory();
	notF = this.smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");
	eqF = this.smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
	containsF = this.smt.createFunction(ir.T_BOOLEAN, { transitive: true, transitiveAcyclic: true }, "bounds");

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
			out.push(this.smt.createFunction(resultType, { eq: fn.signature.semantics?.eq }, fnID));
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
				interpreter: this.foreignInterpreters[op]?.interpreter,
				generalInterpreter: this.foreignInterpreters[op]?.generalInterpreter,
			}, op));
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
			if (this.program.records[base] !== undefined) {
				return this.recordMap.typeID(base as ir.RecordID, args);
			} else {
				return this.enumMap.typeID(base as ir.EnumID, args);
			}
		} else {
			const un: never = t;
			throw new Error("getTypeID: unhandled type tag `" + un["tag"] + "`");
		}
	}

	/// `pathConstraints` is the stack of conditional constraints that must be
	/// true to reach a position in the program.
	private pathConstraints: uf.ValueID[] = [];

	// Verification adds failure messages to this stack as they are encountered.
	// Multiple failures can be returned.
	failedVerifications: FailedVerification[] = [];

	interfaceSignaturesByImplFn: DefaultMap<ir.FunctionID, IndexedImpl[]>;

	constructor(
		program: ir.Program,
		interfaceSignaturesByImplFn: DefaultMap<ir.FunctionID, IndexedImpl[]>,
	) {
		this.program = program;
		this.dynamicFunctions = new DynamicFunctionMap(this.program, this.smt);
		this.recordMap = new RecordMap(this.program, this.smt);
		this.enumMap = new EnumMap(this.program, this.smt);
		this.interfaceSignaturesByImplFn = interfaceSignaturesByImplFn;

		// SMT requires at least one constraint.
		this.smt.addConstraint([
			this.smt.createConstant(ir.T_BOOLEAN, true),
		]);

		this.foreignInterpreters = getForeignInterpreters(this);
	}

	negate(bool: uf.ValueID): uf.ValueID {
		return this.smt.createApplication(this.notF, [bool]);
	}

	eq(left: uf.ValueID, right: uf.ValueID): uf.ValueID {
		return this.smt.createApplication(this.eqF, [left, right]);
	}


	isSmallerThan(left: uf.ValueID, right: uf.ValueID): uf.ValueID {
		return this.smt.createApplication(this.containsF, [left, right]);
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
		this.pathConstraints.push(c);
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
	/// constraints is considered not satisfiable in subsequent invocations of
	/// the `smt` solver.
	markPathUnreachable() {
		const pathUnreachable = this.pathConstraints.map(e => this.negate(e));
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
	program: ir.Program,
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
		traverse(program, subop, state, context);
	}

	// Execute the final computation before exiting this scope.
	if (then !== undefined) {
		then();
	}

	// Clear variables defined within this block.
	state.popVariableScope(variableScope);
}

// MUTATES the verification state parameter, to add additional clauses that are
// ensured after the execution (and termination) of this operation.
function traverse(program: ir.Program, op: ir.Op, state: VerificationState, context: VerificationContext): void {
	if (op.tag === "op-branch") {
		const symbolicCondition: uf.ValueID = state.getValue(op.condition).value;

		const phis: uf.ValueID[] = [];
		for (const destination of op.destinations) {
			phis.push(state.smt.createVariable(
				destination.destination.type, destination.destination.variable));
		}

		state.pushPathConstraint(symbolicCondition);
		traverseBlock(program, new Map(), op.trueBranch, state, context, () => {
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
		traverseBlock(program, new Map(), op.falseBranch, state, context, () => {
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
		state.smt.addUnscopedConstraint([state.isSmallerThan(fieldValue, object.value)]);
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
			state.failedVerifications.push(reason);
		}

		state.markPathUnreachable();
		state.popPathConstraint();

		// Extract the field.
		const variantValue = state.enumMap.destruct(baseType.base, object.value, op.variant);
		state.smt.addUnscopedConstraint([state.isSmallerThan(variantValue, object.value)]);
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
		return traverseBlock(program, new Map(), op.body, state, context);
	} else if (op.tag === "op-return") {
		if (context.verifyAtReturn.length !== 0) {
			// Check that the postconditions from the context are satisfied by
			// this return.
			const returnedValues = [];
			for (let i = 0; i < op.sources.length; i++) {
				returnedValues.push(state.getValue(op.sources[i]).value);
			}
			checkVerifyAtReturns(program, state, returnedValues, context.verifyAtReturn, op.diagnostic_return_site);
		}

		// Subsequently, this path is treated as unreachable, since the function
		// exited.
		state.markPathUnreachable();
		return;
	} else if (op.tag === "op-foreign") {
		traverseForeignCall(program, op, state, context);
		return;
	} else if (op.tag === "op-static-call") {
		traverseStaticCall(program, op, state);
		return;
	} else if (op.tag === "op-dynamic-call") {
		traverseDynamicCall(program, op, state);
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
	} else if (op.tag === "op-proof-eq") {
		const leftObject = state.getValue(op.left);
		const rightObject = state.getValue(op.right);

		state.defineVariable(op.destination, state.eq(leftObject.value, rightObject.value));
		return;
	}

	const _: never = op;
	throw new Error(`unhandled op ${op["tag"]}`);
}

/// checkPrecondition inspects the state and ensures that the precondition
/// invoked with the given scope is satisfied.
function checkPrecondition(
	program: ir.Program,
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

	traverseBlock(program, valueArgs, precondition.block, state, {
		// Return ops within a precondition do not have their own
		// postconditions.
		verifyAtReturn: [],
	}, () => {
		if (state.checkPossiblyFalseInPath(precondition.precondition, reason) !== "refuted") {
			state.failedVerifications.push(reason);
		}
	});

	state.popTypeScope();
	state.popHidingTypeScope(hidingTypeScope);
}

/// assumePostcondition modifies the state so that subsequent inspections can
/// assume that this postcondition, invoked with the given scope, is satisfied.
function assumePostcondition(
	program: ir.Program,
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

	traverseBlock(program, valueArgs, postcondition.block, state, {
		// Return ops within a postcondition do not have their own postconditions.
		verifyAtReturn: [],
	}, () => {
		state.assumeGuaranteedInPath(postcondition.postcondition);
	});

	state.popVariableScope(postconditionScope);
	state.popTypeScope();
	state.popHidingTypeScope(hidingTypeScope);
}

/// checkVerifyAtReturns inspects the current state to determine whether or not
/// each postcondition is satisfied by the given returned values.
function checkVerifyAtReturns(
	program: ir.Program,
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

		traverseBlock(program, locals, verifyAtReturn.postcondition.block, state, {
			// Return ops within a postcondition do not have their own
			// postconditions.
			verifyAtReturn: [],
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
				state.failedVerifications.push(reason);
			}
		});

		state.popVariableScope(postconditionVariableScope);
		state.popTypeScope();
		state.popHidingTypeScope(postconditionTypeScope);
	}
}

function traverseStaticCall(
	program: ir.Program,
	op: ir.OpStaticCall,
	state: VerificationState,
): void {
	const fn = op.function;
	const signature = program.functions[fn].signature;
	if (state.interfaceSignaturesByImplFn.get(fn).length !== 0) {
		throw new Error("impl functions cannot be invoked directly by static calls");
	}

	const valueArgs = [];
	for (let i = 0; i < op.arguments.length; i++) {
		valueArgs.push(state.getValue(op.arguments[i]).value);
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

			checkPrecondition(program, valueArgsMap, typeArgsMap, precondition, state, reason);
		}

		delete state.recursivePreconditions.blockedFunctions[fn];
	}

	const smtFns = state.functions.get(fn);
	const results = [];
	for (let i = 0; i < op.destinations.length; i++) {
		const result = state.smt.createApplication(smtFns[i], [...valueArgs, ...typeArgs]);
		results.push(result);
		state.defineVariable(op.destinations[i], result);
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

			assumePostcondition(program, valueArgsMap, typeArgsMap, postcondition, state);
		}

		delete state.recursivePostconditions.blockedFunctions[fn];
	}
}

function traverseDynamicCall(
	program: ir.Program,
	op: ir.OpDynamicCall,
	state: VerificationState,
): void {
	const constraint = program.interfaces[op.constraint.interface];
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

	const valueArgs = op.arguments.map(v => state.getValue(v).value);

	for (const precondition of signature.preconditions) {
		throw new Error("TODO");
	}

	const smtFns = state.dynamicFunctions.get(op.constraint.interface, op.signature_id as ir.FunctionID);
	const results = [];
	for (let i = 0; i < op.destinations.length; i++) {
		const result = state.smt.createApplication(smtFns[i], [...valueArgs, ...typeArgsList]);
		results.push(result);
		state.defineVariable(op.destinations[i], result);
	}

	for (const postcondition of signature.postconditions) {
		throw new Error("TODO");
	}

	if (signature.semantics?.eq === true) {
		throw new Error("TODO");
	}
}

function traverseForeignCall(
	program: ir.Program,
	op: ir.OpForeign,
	state: VerificationState,
	context: VerificationContext,
): void {
	const signature = program.foreign[op.operation];

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

			assumePostcondition(program, valueArgsMap, typeArgsMap, postcondition, state);
		}

		delete state.recursivePostconditions.blockedFunctions[fnKey];
	}
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
		const eq = smt.createApplication(eqF, [left, right]);
		const neq = smt.createApplication(negF, [eq]);
		neqs.push(neq);
	}
	return out;
}
