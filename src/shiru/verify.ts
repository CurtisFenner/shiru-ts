import * as diagnostics from "./diagnostics";
import * as ir from "./ir";
import * as smt from "./smt";

/// Represents a constraint solver. The `meta` is used to associated the query
/// with a "reason" the query is being asked.
export type ConstraintSolver = (
	meta: FailedVerification,
	state: VerificationState,
	additionalConstraints: smt.UFConstraint[],
) => "refuted" | {};

export function verifyProgram(
	program: ir.Program,
	constraintSolver: ConstraintSolver = (_, state, cons) => checkUnreachableSMT(state, cons),
): FailedVerification[] {
	const problems = [];

	// 1) Verify each function body,
	for (let f in program.functions) {
		problems.push(...verifyFunction(program, f, constraintSolver));
	}

	// 2) Verify that each interface implementation
	for (let v in program.globalVTableFactories) {
		// 2a) has weaker preconditions
		// 2b) has stronger postconditions
		throw new Error("TODO");
	}

	return problems;
}

function sortOf(t: ir.Type): smt.UFSort {
	if (t.tag === "type-primitive" && t.primitive === "Boolean") {
		return "bool";
	} else {
		// This is obviously wrong, but will work OK at the beginning.
		// TODO: This really needs to be stateful.
		return 17;
	}
}

function verifyFunction(
	program: ir.Program,
	fName: string,
	constraintSolver: ConstraintSolver,
): FailedVerification[] {
	const state = new VerificationState();

	const f = program.functions[fName];

	// Initialize the function's arguments.
	for (let i = 0; i < f.signature.parameters.length; i++) {
		const parameter = f.signature.parameters[i];

		// Define a symbolic constant for the initial value of the parameter.
		const p = `sh_arg_${parameter.id.variable_id}`;
		const sort = sortOf(parameter.type);
		state.constantSorts[p] = sort;

		// Update the stack.
		state.stackInitialize(parameter.type, p, parameter.id);
	}

	// Execute and validate the function's preconditions.
	for (let i = 0; i < f.signature.preconditions.length; i++) {
		const precondition = f.signature.preconditions[i];
		traverseBlock(program, precondition.block, state, {
			// Return statements do not return a value.
			returnsPostConditions: [],
			parameters: f.signature.parameters.map(p => p.id),
			constraintSolver,
		}, () => {
			state.clauses.push([
				{
					tag: "predicate",
					predicate: state.getVariable(precondition.precondition).symbolicAssignment,
				},
			]);
		});
	}

	traverseBlock(program, f.body, state, {
		returnsPostConditions: f.signature.postconditions,
		parameters: f.signature.parameters.map(p => p.id),
		constraintSolver,
	});

	// The IR type-checker verifies that functions must end with a op-return or
	// op-unreachable.
	return state.failedVerifications;
}

interface VerificationContext {
	/// The post-conditions to verify at a ReturnStatement.
	returnsPostConditions: ir.Postcondition[],

	/// The number of function parameters. The first entries in the stack are
	/// the parameters.
	parameters: ir.VariableID[],

	/// The constraint solver.
	constraintSolver: ConstraintSolver,
}

export type FailedVerification = FailedPreconditionVerification
	| FailedAssertVerification
	| FailedReturnVerification
	| FailedPostconditionValidation;

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

interface SignatureSet {
	blockedFunctions: Record<string, boolean>,
	blockedInterfaces: Record<string, Record<string, string>>,
}

interface VerificationVariable {
	t: ir.Type,
	sort: smt.UFSort,
	symbolicAssignment: smt.UFValue,
}

class VerificationState {
	constantSorts: Record<string, smt.UFSort> = {};
	functionSorts: Record<string, smt.UFSort> = {};

	recursivePreconditions: SignatureSet = {
		blockedFunctions: {},
		blockedInterfaces: {},
	};

	recursivePostconditions: SignatureSet = {
		blockedFunctions: {},
		blockedInterfaces: {},
	};

	private nextConstant: number = 1000;

	// LIFO ordering of keys of `variables`.
	stack: string[] = [];

	/// Mapping from Shiru local variable to value/type/sort.
	variables: Record<string, VerificationVariable> = {};

	// An append-only set of constraints that grow, regardless of path.
	clauses: smt.UFConstraint[][] = [];

	// A stack of constraints that are managed by conditional control
	// structures.
	pathConstraints: smt.UFConstraint[] = [];

	// Verification adds failure messages to this stack as they are encountered.
	// Multiple failures can be returned.
	failedVerifications: FailedVerification[] = [];

	defaultInhabitant(sort: smt.UFSort) {
		// TODO: Instead of doing this, do an analysis that ensures all
		// variables are assigned before use, and simply allow no references.
		const name = "_default_inhabitant_" + sort;
		if (this.constantSorts[name] === undefined) {
			this.constantSorts[name] = sort;
		}
		return name;
	}

	stackInitialize(t: ir.Type, value: smt.UFValue, id: ir.VariableID) {
		if (this.variables[id.variable_id] !== undefined) {
			throw new Error("VerificationState.stackInitialize: `"
				+ id.variable_id + "` is already defined.");
		}
		this.stack.push(id.variable_id);
		this.variables[id.variable_id] = {
			t,
			sort: sortOf(t),
			symbolicAssignment: value,
		};
	}

	getVariable(v: ir.VariableID) {
		const variable = this.variables[v.variable_id];
		if (variable === undefined) {
			throw new Error("VerificationState.getCurrentSymbolicAssignment: `"
				+ v.variable_id + "` has not been defined.");
		}
		return variable;
	}

	vendConstant(sort: smt.UFSort, hint: string = "v") {
		const n = `sh_var_${this.nextConstant}_${hint}`;
		this.nextConstant += 1;
		this.constantSorts[n] = sort;
		return n;
	}

	updateSymbolicAssignment(destination: ir.VariableID, value: smt.UFValue) {
		const variable = this.getVariable(destination);
		variable.symbolicAssignment = value;
	}

	getStackSize() {
		return this.stack.length;
	}

	truncateStackToSize(size: number) {
		for (const variable of this.stack.splice(size)) {
			delete this.variables[variable];
		}
	}

	maskStack(map: Record<string, VerificationVariable>, callback: () => void) {
		const oldStack = this.stack;
		const oldVariables = this.variables;
		this.variables = {};
		this.stack = [];
		for (const k in map) {
			this.stack.push(k);
			const v = map[k];
			this.variables[k] = {
				t: v.t,
				sort: v.sort,
				symbolicAssignment: v.symbolicAssignment,
			};
		}
		const expectStackLength = this.stack.length;
		callback();
		if (this.stack.length !== expectStackLength) {
			throw new Error("VerificationState.maskStack: invariant violation");
		}
		this.stack = oldStack;
		this.variables = oldVariables;
	}
}

/// conditionConjunction: a conjunction (and) of constraints
/// impliedDisjunction: a disjunction (or) of constraints
/// RETURNS a clause representing (conditionConjunction implies impliedDisjunction).
function conjunctionImplication(conditionConjunction: smt.UFConstraint[], impliedDisjunction: smt.UFConstraint[]) {
	return impliedDisjunction.concat(conditionConjunction.map(x => ({ tag: "not", constraint: x })));
}

function negate(constraint: smt.UFConstraint): smt.UFConstraint {
	return { tag: "not", constraint };
}

function showType(t: ir.Type): string {
	if (t.tag === "type-compound") {
		return t.record.record_id + "[" + t.type_arguments.map(showType).join(",") + "]";
	} else if (t.tag === "type-primitive") {
		return t.primitive;
	} else if (t.tag === "type-variable") {
		return "#" + t.id.type_variable_id;
	}
	throw new Error(`unhandled ${t}`);
}

/// RETURNS an array of strings, being the SMT function names for each of the
/// given function's return values.
/// TODO: A better way to encode generic functions is to treat type constraint
/// parameters as arguments.
function createFunctionIDs(state: VerificationState, destinations: ir.VariableID[], f: string, signature: ir.FunctionSignature, typeArguments: ir.Type[]): string[] {
	const args = typeArguments.map(showType);
	const prefix = `sh_f_${f}[${args.join(",")}]`;
	const fs = [];
	for (let i = 0; i < signature.return_types.length; i++) {
		const f = `${prefix}:${i}`;
		fs.push(f);
		if (state.functionSorts[f] === undefined) {
			state.functionSorts[f] = state.getVariable(destinations[i]).sort;
		}
	}
	return fs;
}

function createDynamicFunctionID(state: VerificationState, op: ir.OpDynamicCall): string[] {
	const args = op.subjects.concat(op.signature_type_arguments).map(showType);
	// TODO: This is a bad way to do this, particularly because it makes
	// encoding parametricity relationships harder.
	const prefix = `dyn_${op.constraint.interface_id}:${op.signature_id}[${args.join(",")}]`;
	const fs = [];
	for (let i = 0; i < op.destinations.length; i++) {
		const f = `${prefix}:${i}`;
		fs.push(f);
		if (state.functionSorts[f] == undefined) {
			state.functionSorts[f] = state.getVariable(op.destinations[i]).sort;
		}
	}
	return fs;
}

function createFieldFunctionID(state: VerificationState, base: ir.Type, field: string, fieldType: ir.Type): string {
	const t = showType(base);
	const name = `field_${t}:${field}`;
	if (state.functionSorts[name] === undefined) {
		state.functionSorts[name] = sortOf(fieldType);
	}
	return name;
}

function createConstructorFunctionID(state: VerificationState, base: ir.Type) {
	const t = showType(base);
	const name = `new_${t}`;
	if (state.functionSorts[name] === undefined) {
		state.functionSorts[name] = sortOf(base);
	}
	return name;
}

function addConditionalClause(state: VerificationState, clause: smt.UFConstraint[]) {
	state.clauses.push(conjunctionImplication(state.pathConstraints, clause));
}

function learnEquality(
	state: VerificationState,
	left: smt.UFValue,
	right: smt.UFValue,
	destination: ir.VariableID,
) {
	const result = state.vendConstant("bool", "eq");
	state.updateSymbolicAssignment(destination, result);

	// Create a two-way implication between the destination variable and the
	// abstract result of comparison.
	// This is necessary because comparison is only a UFConstraint, not a
	// UFValue.
	const resultCon: smt.UFConstraint = {
		tag: "predicate", predicate: result
	};
	const eqCon: smt.UFConstraint = { tag: "=", left, right };
	addConditionalClause(state, [
		negate(resultCon),
		eqCon,
	]);
	addConditionalClause(state, [
		resultCon,
		negate(eqCon),
	]);
}

function traverseBlock(
	program: ir.Program,
	block: ir.OpBlock,
	state: VerificationState,
	context: VerificationContext,
	then?: () => unknown,
) {
	// Blocks bound variable scopes, so variables must be cleared after.
	const stackAtBeginning = state.getStackSize();

	for (let subop of block.ops) {
		traverse(program, subop, state, context);
	}

	// Execute the final computation before exiting this scope.
	if (then !== undefined) {
		then();
	}

	// Clear variables defined within this block.
	state.truncateStackToSize(stackAtBeginning);
}

// MUTATES the verification state parameter, to add additional clauses that are
// ensured after the execution (and termination) of this operation.
function traverse(program: ir.Program, op: ir.Op, state: VerificationState, context: VerificationContext): void {
	if (op.tag === "op-assign") {
		// Update the last assignment.
		// NOTE that since this creates no new objects, this does not require
		// any manipulation of constraints.
		state.updateSymbolicAssignment(op.destination,
			state.getVariable(op.source).symbolicAssignment);
		return;
	} else if (op.tag === "op-branch") {
		const conditionVariable = state.getVariable(op.condition).symbolicAssignment;
		const trueCondition: smt.UFConstraint = {
			tag: "predicate", predicate: conditionVariable
		};
		state.pathConstraints.push(trueCondition);
		traverseBlock(program, op.trueBranch, state, context);
		state.pathConstraints.pop();

		state.pathConstraints.push({ tag: "not", constraint: trueCondition })
		traverseBlock(program, op.falseBranch, state, context);
		state.pathConstraints.pop();
		return;
	} else if (op.tag === "op-const") {
		// Like assignment, this requires no manipulation of constraints, only
		// the state of variables.
		const sort = state.getVariable(op.destination).sort;
		state.updateSymbolicAssignment(op.destination, {
			tag: "const", value: op.value, sort
		});
		return;
	} else if (op.tag === "op-field") {
		const baseType = state.getVariable(op.object).t;
		const dstType = state.getVariable(op.destination).t;
		const f = createFieldFunctionID(state, baseType, op.field, dstType);
		state.updateSymbolicAssignment(op.destination, {
			tag: "app",
			f,
			args: [state.getVariable(op.object).symbolicAssignment],
		});
		return;
	} else if (op.tag === "op-new-record") {
		const fieldNames = Object.keys(op.fields).sort();
		const fields = [];
		for (let field of fieldNames) {
			fields.push(state.getVariable(op.fields[field]).symbolicAssignment);
		}
		const dstType = state.getVariable(op.destination).t;
		const f = createConstructorFunctionID(state, dstType);
		const app: smt.UFValue = {
			tag: "app",
			f,
			args: fields,
		};
		state.updateSymbolicAssignment(op.destination, app);
		for (let i = 0; i < fields.length; i++) {
			const fieldType = state.getVariable(op.fields[fieldNames[i]]).t;
			const f = createFieldFunctionID(state, dstType, fieldNames[i], fieldType);
			addConditionalClause(state, [
				{
					tag: "=",
					left: { tag: "app", f, args: [app] },
					right: fields[i],
				},
			]);
		}
		return;
	} else if (op.tag === "op-proof") {
		return traverseBlock(program, op.body, state, context);
	} else if (op.tag === "op-return") {
		if (context.returnsPostConditions.length !== 0) {
			for (let postcondition of context.returnsPostConditions) {
				const substate: Record<string, VerificationVariable> = {};
				for (let i = 0; i < context.parameters.length; i++) {
					const parameter = context.parameters[i];
					substate[parameter.variable_id] = state.getVariable(parameter);
				}
				for (let i = 0; i < op.sources.length; i++) {
					substate[postcondition.returnedValues[i].variable_id] = state.getVariable(op.sources[i]);
				}
				state.maskStack(substate, () => {
					traverseBlock(program, postcondition.block, state, context, () => {
						const reason: FailedVerification = {
							tag: "failed-postcondition",
							returnLocation: op.diagnostic_return_site,
							postconditionLocation: postcondition.location,
						};
						const refutation = context.constraintSolver(reason, state, [{
							tag: "not",
							constraint: {
								tag: "predicate",
								predicate: state.getVariable(postcondition.postcondition).symbolicAssignment,
							},
						}]);
						if (refutation !== "refuted") {
							state.failedVerifications.push(reason);
						}
					});
				});
			}
		}

		// Subsequently, this path is treated as unreachable, since the function
		// exited.
		state.clauses.push(state.pathConstraints.map(negate));
		return;
	} else if (op.tag === "op-foreign") {
		const signature = program.foreign[op.operation];

		for (let precondition of signature.preconditions) {
			throw new Error("TODO: Check precondition of op-foreign");
		}

		for (let postcondition of signature.postconditions) {
			throw new Error("TODO: Assume postcondition of op-foreign");
		}

		if (signature.semantics?.eq === true) {
			if (op.arguments.length !== 2) {
				throw new Error("Foreign signature with `eq` semantics"
					+ " must take exactly 2 arguments (" + op.operation + ")");
			}
			const left = state.getVariable(op.arguments[0]).symbolicAssignment;
			const right = state.getVariable(op.arguments[1]).symbolicAssignment;
			if (op.destinations.length !== 1) {
				throw new Error("Foreign signature with `eq` semantics"
					+ " must return exactly 1 value");
			}
			const destination = op.destinations[0];
			learnEquality(state, left, right, destination);
		}
		return;
	} else if (op.tag === "op-static-call") {
		const fn = op.function.function_id;
		const signature = program.functions[fn].signature;

		const args = [];
		for (let i = 0; i < op.arguments.length; i++) {
			args.push(state.getVariable(op.arguments[i]).symbolicAssignment);
		}

		if (state.recursivePreconditions.blockedFunctions[fn] !== undefined) {
			throw new diagnostics.RecursivePreconditionErr({
				callsite: op.diagnostic_callsite,
				fn: fn,
			});
		} else {
			state.recursivePreconditions.blockedFunctions[fn] = true;

			const substate: Record<string, VerificationVariable> = {};
			for (let i = 0; i < op.arguments.length; i++) {
				const p = signature.parameters[i].id;
				const v = state.getVariable(op.arguments[i]);
				substate[p.variable_id] = v;
			}
			state.maskStack(substate, () => {
				for (let precondition of signature.preconditions) {
					traverseBlock(program, precondition.block, state, {
						...context,
					}, () => {
						const reason: FailedVerification = {
							tag: "failed-precondition",
							callLocation: op.diagnostic_callsite,
							preconditionLocation: precondition.location,
						};
						const refutation = context.constraintSolver(reason, state, [{
							tag: "not",
							constraint: {
								tag: "predicate",
								predicate: state.getVariable(precondition.precondition).symbolicAssignment,
							},
						}]);
						if (refutation !== "refuted") {
							state.failedVerifications.push(reason);
						}
					});
				}
			});

			delete state.recursivePreconditions.blockedFunctions[fn];
		}

		const smtFnID = createFunctionIDs(state, op.destinations, fn, signature, op.type_arguments);
		for (let i = 0; i < op.destinations.length; i++) {
			state.updateSymbolicAssignment(op.destinations[i], {
				tag: "app",
				f: smtFnID[i],
				args,
			});
		}

		for (let postcondition of signature.postconditions) {
			throw new Error("TODO: Assume postcondition of op-static-call");
		}

		// Handle the special semantics of functions.
		if (signature.semantics?.eq === true) {
			if (op.arguments.length !== 2) {
				throw new Error("Function signature with `eq` semantics must take exactly 2 arguments (" + fn + ")");
			}
			const left = state.getVariable(op.arguments[0]).symbolicAssignment;
			const right = state.getVariable(op.arguments[1]).symbolicAssignment;
			if (op.destinations.length !== 1) {
				throw new Error("Function signatures with `eq` semantics must return exactly 1 value (" + fn + ")");
			}
			const destination = op.destinations[0];
			learnEquality(state, left, right, destination);
		}

		return;
	} else if (op.tag === "op-dynamic-call") {
		const fs = createDynamicFunctionID(state, op);
		const constraint = program.interfaces[op.constraint.interface_id];
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

		throw new Error("TODO");
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
		if (context.constraintSolver(reason, state, []) !== "refuted") {
			state.failedVerifications.push(reason);
		}

		// Like a return statement, this path is subsequently treated as
		// unreachable.
		state.clauses.push(state.pathConstraints.map(negate));
		return;
	} else if (op.tag === "op-var") {
		state.stackInitialize(op.type, state.defaultInhabitant(sortOf(op.type)), op.id);
		return;
	}

	const _: never = op;
	throw new Error(`unhandled op ${op["tag"]}`);
}

export function checkUnreachableSMT(
	state: VerificationState,
	additionalConstraints: smt.UFConstraint[],
): "refuted" | {} {
	const theory = new smt.UFTheory();
	for (let variable in state.constantSorts) {
		theory.defineVariable(variable, state.constantSorts[variable]);
	}
	for (let func in state.functionSorts) {
		theory.defineFunction(func, state.functionSorts[func]);
	}
	for (let clause of state.clauses) {
		if (clause.length === 0) {
			return "refuted";
		}
		theory.addConstraint(clause);
	}
	for (let clause of state.pathConstraints) {
		theory.addConstraint([clause]);
	}
	for (let c of additionalConstraints) {
		theory.addConstraint([c]);
	}

	return theory.attemptRefutation();
}
