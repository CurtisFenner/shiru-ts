import * as ir from "./ir";
import * as smt from "./smt";

export function verifyProgram(program: ir.Program): FailedVerification[] {
	const problems = [];

	// 1) Verify each function body,
	for (let f in program.functions) {
		problems.push(...verifyFunction(program, f));
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

function verifyFunction(program: ir.Program, fName: string): FailedVerification[] {
	const state = new VerificationState();

	const f = program.functions[fName];

	// Initialize the function's arguments.
	for (let i = 0; i < f.signature.parameters.length; i++) {
		// Define a constant for the parameter.
		const p = `sh_arg_${i}`;
		const sort = sortOf(f.signature.parameters[i]);
		state.variableSorts[p] = sort;

		// Update the stack.
		state.stackInitialize(sort, p, i);
	}

	// Execute and validate the function's preconditions.
	for (let i = 0; i < f.signature.preconditions.length; i++) {
		let preconditionEvaluation = `sh_pre_${i}`;
		state.variableSorts[preconditionEvaluation] = "bool";
		traverse(program, f.signature.preconditions[i], state, {
			returnToVariables: [preconditionEvaluation],
			postconditionReadReturns: null,

			// "Returns" inside the preconditions are just the boolean to 
			// require; no verification needs to be done at them.
			returnsPostConditions: [],
		});
		state.clauses.push([{ tag: "predicate", predicate: preconditionEvaluation }]);
	}

	// Prepare the return variables for the function's body and postconditions.
	const returnVariables = [];
	for (let i = 0; i < f.signature.return_types.length; i++) {
		const v = `sh_ret_${i}`;
		state.variableSorts[v] = sortOf(f.signature.return_types[i]);
		returnVariables.push(v);
	}

	// Execute and validate the function's body.
	traverseBlock(program, f.body, state, {
		returnToVariables: returnVariables,
		postconditionReadReturns: null,
		returnsPostConditions: f.signature.postconditions,
	});

	// The IR type-checker verifies that functions must end with a op-return or
	// op-unreachable.
	return state.failedVerifications;
}

interface VerificationContext {
	/// The variables to return to (via assignment clauses), and to inspect in
	/// postconditions.
	returnToVariables: string[],

	/// The variables that a "return expression" reads from. This is only set in
	/// post-conditions.
	postconditionReadReturns: string[] | null,

	/// The post-conditions to verify at a ReturnStatement.
	returnsPostConditions: ir.Op[],
}

type FailedVerification = FailedPreconditionVerification
	| FailedAssertVerification
	| FailedReturnVerification;

interface FailedPreconditionVerification {
	tag: "failed-precondition",
	callLocation: ir.SourceLocation,
	preconditionLocation: ir.SourceLocation,
}

interface FailedAssertVerification {
	tag: "failed-assert",
	assertLocation?: ir.SourceLocation,
}

interface FailedReturnVerification {
	tag: "failed-return",
	blockEndLocation?: ir.SourceLocation,
}

class VerificationState {
	variableSorts: Record<string, smt.UFSort> = {};
	functionSorts: Record<string, smt.UFSort> = {};

	private nextConstant: number = 1000;

	/// Mapping from Shiru local variable to UFTheory sort.
	private stackSorts: smt.UFSort[] = [];

	/// Mapping from Shiru local variable to UFTheory variable.
	private lastAssignment: smt.UFValue[] = [];

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
		if (this.variableSorts[name] === undefined) {
			this.variableSorts[name] = sort;
		}
		return name;
	}

	stackInitialize(sort: smt.UFSort, value: smt.UFValue, expectedIndex?: number | undefined) {
		const id = this.stackSorts.length;
		if (expectedIndex !== undefined) {
			if (expectedIndex !== id) {
				throw new Error("bad expectedIndex");
			}
		}

		if (this.stackSorts.length !== this.lastAssignment.length) {
			throw new Error("bad state");
		}
		this.stackSorts.push(sort);
		this.lastAssignment.push(value);
		return id;
	}

	getStackSort(v: number): smt.UFSort {
		if (this.stackSorts[v] === undefined) {
			throw new Error("out of bounds");
		}
		return this.stackSorts[v];
	}

	vendConstant(sort: smt.UFSort, hint: string = "v") {
		const n = `sh_var_${this.nextConstant}_${hint}`;
		this.nextConstant += 1;
		this.variableSorts[n] = sort;
		return n;
	}

	updateAssignment(destination: number, value: smt.UFValue) {
		if (this.lastAssignment[destination] === undefined) {
			throw new Error("out of bounds");
		}
		this.lastAssignment[destination] = value;
	}

	getAssignment(source: number): smt.UFValue {
		const v = this.lastAssignment[source];
		if (v === undefined) {
			console.log("Attempted to get assignment of #" + source);
			for (let i = 0; i < this.stackSorts.length; i++) {
				console.log("\t#" + i + " ::", this.stackSorts[i]);
				console.log("\t\t=", this.lastAssignment[i]);
			}
			throw new Error("out of bounds");
		}
		return v;
	}

	getStackSize() {
		return this.lastAssignment.length;
	}

	truncateStackToSize(size: number) {
		this.lastAssignment.splice(size);
		this.stackSorts.splice(size);
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
			state.functionSorts[f] = state.getStackSort(destinations[i].variable_id);
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
			state.functionSorts[f] = state.getStackSort(op.destinations[i].variable_id);
		}
	}
	return fs;
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
	state.updateAssignment(destination.variable_id, result);

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
) {
	// Blocks bound variable scopes, so variables must be cleared after.
	const stackAtBeginning = state.getStackSize();

	for (let subop of block.ops) {
		traverse(program, subop, state, context);
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
		state.updateAssignment(op.destination.variable_id,
			state.getAssignment(op.source.variable_id));
		return;
	} else if (op.tag === "op-branch") {
		const conditionVariable = state.getAssignment(op.condition.variable_id)
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
		const sort = state.getStackSort(op.destination.variable_id);
		state.updateAssignment(op.destination.variable_id, {
			tag: "const", value: op.value, sort
		});
		return;
	} else if (op.tag === "op-field") {
	} else if (op.tag === "op-new-record") {

	} else if (op.tag === "op-proof") {
		return traverseBlock(program, op.body, state, context);
	} else if (op.tag === "op-return") {
		for (let i = 0; i < op.sources.length; i++) {
			addConditionalClause(state, [
				{
					tag: "=",
					left: state.getAssignment(op.sources[i].variable_id),
					right: context.returnToVariables[i],
				},
			]);
		}

		for (let post of context.returnsPostConditions) {
			throw new Error("TODO: Verify postcondition at op-return");
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
			const left = state.getAssignment(op.arguments[0].variable_id);
			const right = state.getAssignment(op.arguments[1].variable_id);
			if (op.destinations.length !== 1) {
				throw new Error("Foreign signature with `eq` semantics"
					+ " must return exactly 1 value");
			}
			const destination = op.destinations[0];
			learnEquality(state, left, right, destination);
		}
		return;
	} else if (op.tag === "op-static-call") {
		const sf = op.function.function_id;
		const signature = program.functions[sf].signature;
		const fs = createFunctionIDs(state, op.destinations, sf, signature, op.type_arguments);

		for (let precondition of signature.preconditions) {
			throw new Error("TODO: Check precondition of op-static-call");
		}

		const args = [];
		for (let i = 0; i < op.arguments.length; i++) {
			args.push(state.getAssignment(op.arguments[i].variable_id));
		}

		for (let i = 0; i < op.destinations.length; i++) {
			const dst = op.destinations[i].variable_id;
			state.updateAssignment(dst, { tag: "app", f: fs[i], args });
		}

		for (let postcondition of signature.postconditions) {
			throw new Error("TODO: Assume postcondition of op-static-call");
		}

		// Handle the special semantics of functions.
		if (signature.semantics?.eq === true) {
			if (op.arguments.length !== 2) {
				throw new Error("Function signature with `eq` semantics must take exactly 2 arguments (" + sf + ")");
			}
			const left = state.getAssignment(op.arguments[0].variable_id);
			const right = state.getAssignment(op.arguments[1].variable_id);
			if (op.destinations.length !== 1) {
				throw new Error("Function signatures with `eq` semantics must return exactly 1 value (" + sf + ")");
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
		return;
	} else if (op.tag === "op-unreachable") {
		if (checkUnreachable(state) !== "refuted") {
			// TODO: Better classify verification failures.
			if (op.diagnostic_kind === "return") {
				state.failedVerifications.push({
					tag: "failed-return",
					blockEndLocation: op.diagnostic_location,
				});
			} else {
				state.failedVerifications.push({
					tag: "failed-assert",
					assertLocation: op.diagnostic_location,
				});
			}
		}

		// Like a return statement, this path is subsequently treated as
		// unreachable.
		state.clauses.push(state.pathConstraints.map(negate));
		return;
	} else if (op.tag === "op-var") {
		const sort = sortOf(op.type);
		state.stackInitialize(sort, state.defaultInhabitant(sort));
		return;
	}

	const _: never = op;
	throw new Error(`unhandled op ${op["tag"]}`);
}

function checkUnreachable(state: VerificationState) {
	const theory = new smt.UFTheory();
	for (let variable in state.variableSorts) {
		theory.defineVariable(variable, state.variableSorts[variable]);
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

	return theory.attemptRefutation();
}
