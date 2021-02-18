import * as ir from "./ir";
import * as smt from "./smt";

export function verifyProgram(program: ir.Program) {
	// 1) Verify each function body,
	for (let f in program.functions) {
		verifyFunction(program, program.functions[f]);
	}

	// 2) Verify that each interface implementation
	// 2a) has weaker preconditions
	// 2b) has stronger postconditions
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

function verifyFunction(program: ir.Program, f: ir.IRFunction) {
	const state: VerificationState = {
		variableSorts: {},
		functionSorts: {},

		nextLocal: 0,

		stackSorts: [],
		lastAssignment: [],

		clauses: [],
		pathConstraints: [],

		failedVerifications: [],
	};

	// Initialize the function's arguments.
	for (let i = 0; i < f.signature.parameters.length; i++) {
		const p = `sh_arg_${i}`;
		const sort = sortOf(f.signature.parameters[i]);
		state.variableSorts[p] = sort;
		state.stackSorts.push(sort);
		state.lastAssignment.push(p);
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
	traverse(program, f.body, state, {
		returnToVariables: returnVariables,
		postconditionReadReturns: null,
		returnsPostConditions: f.signature.postconditions,
	});

	// TODO: Ensure the function has definitely exited by checking that the
	// current state is unreachable.
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
	| FailedAssertVerification;

interface FailedPreconditionVerification {
	tag: "failed-precondition",
	callLocation: ir.SourceLocation,
	preconditionLocation: ir.SourceLocation,
}

interface FailedAssertVerification {
	tag: "failed-assert",
	assertLocation?: ir.SourceLocation,
}

interface VerificationState {
	variableSorts: Record<string, smt.UFSort>,
	functionSorts: Record<string, smt.UFSort>,

	nextLocal: number,

	stackSorts: smt.UFSort[],

	// Mapping from Shiru variable to UFTheory variable.
	lastAssignment: smt.UFValue[],

	// An append-only set of constraints that grow, regardless of path.
	clauses: smt.UFConstraint[][],

	// A stack of constraints that are managed by conditional control 
	// structures.
	pathConstraints: smt.UFConstraint[],

	// Verification adds failure messages to this stack as they are encountered.
	// Multiple failures can be returned.
	failedVerifications: FailedVerification[],
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
	if (t.tag === "type-class") {
		return t.class.class_id + "[" + t.parameter.map(showType).join(",") + "]";
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
			state.functionSorts[f] = state.stackSorts[destinations[i].variable_id];
		}
	}
	return fs;
}

function createDynamicFunctionID(state: VerificationState, op: ir.OpDynamicCall): string[] {
	const args = op.interface_arguments.concat(op.signature_type_arguments).map(showType);
	// TODO: This is a bad way to do this, particularly because it makes 
	// encoding parametricity relationships harder.
	const prefix = `dyn_${op.interface.interface_id}:${op.signature_id}[${args.join(",")}]`;
	const fs = [];
	for (let i = 0; i < op.destinations.length; i++) {
		const f = `${prefix}:${i}`;
		fs.push(f);
		if (state.functionSorts[f] == undefined) {
			state.functionSorts[f] = state.stackSorts[op.destinations[i].variable_id];
		}
	}
	return fs;
}

function vendVariable(state: VerificationState, s: smt.UFSort, hint: string = "v") {
	const n = `sh_var_${state.nextLocal}_${hint}`;
	state.nextLocal += 1;
	state.variableSorts[n] = s;
	return n;
}

function addConditionalClause(state: VerificationState, clause: smt.UFConstraint[]) {
	state.clauses.push(conjunctionImplication(state.pathConstraints, clause));
}

// MUTATES the verification state parameter, to add additional clauses that are 
// ensured after the execution (and termination) of this operation.
function traverse(program: ir.Program, op: ir.Op, state: VerificationState, context: VerificationContext): void {
	if (op.tag === "op-assign") {
		// Update the last assignment.
		// NOTE that since this creates no new objects, this does not require
		// any manipulation of constraints.
		state.lastAssignment[op.destination.variable_id] = state.lastAssignment[op.source.variable_id];
		return;
	} else if (op.tag === "op-block") {
		// Blocks bound variable scopes, so variables must be cleared after.
		const stackAtBeginning = state.stackSorts.length;

		for (let subop of op.ops) {
			traverse(program, op, state, context);
		}

		// Clear variables defined within this block.
		state.stackSorts.splice(stackAtBeginning);
		return;
	} else if (op.tag === "op-branch") {
		const conditionVariable = state.lastAssignment[op.condition.variable_id];
		const trueCondition: smt.UFConstraint = {
			tag: "predicate", predicate: conditionVariable
		};
		state.pathConstraints.push(trueCondition);
		traverse(program, op.trueBranch, state, context);
		state.pathConstraints.pop();

		state.pathConstraints.push({ tag: "not", constraint: trueCondition })
		traverse(program, op.falseBranch, state, context);
		state.pathConstraints.pop();
		return;
	} else if (op.tag === "op-const") {
		// Like assignment, this requires no manipulation of constraints, only
		// the state of variables.
		const sort = state.stackSorts[op.destination.variable_id];
		state.lastAssignment[op.destination.variable_id] = {
			tag: "const", value: op.value, sort
		};
		return;
	} else if (op.tag === "op-dynamic-call") {
		const fs = createDynamicFunctionID(state, op);
		throw new Error("TODO: op-dynamic-call");
	} else if (op.tag === "op-eq") {
		const result = vendVariable(state, "bool", "eq");
		const left = state.lastAssignment[op.left.variable_id];
		const right = state.lastAssignment[op.right.variable_id];
		state.lastAssignment[op.destination.variable_id] = result;

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
		return;
	} else if (op.tag === "op-field") {
	} else if (op.tag === "op-foreign") {

	} else if (op.tag === "op-new-class") {

	} else if (op.tag === "op-proof") {
		return traverse(program, op.body, state, context);
	} else if (op.tag === "op-return") {
		for (let i = 0; i < op.sources.length; i++) {
			addConditionalClause(state, [
				{
					tag: "=",
					left: state.lastAssignment[op.sources[i].variable_id],
					right: context.returnToVariables[i],
				},
			]);
		}

		// TODO: Verify all postconditions.

		// Subsequently, this path is treated as unreachable, since the function
		// exited.
		state.clauses.push(state.pathConstraints.map(negate));
	} else if (op.tag === "op-static-call") {
		const sf = op.function.function_id;
		const signature = program.functions[sf].signature;
		const fs = createFunctionIDs(state, op.destinations, sf, signature, op.type_arguments);

		for (let precondition of signature.preconditions) {
			throw new Error("TODO: Check precondition of op-static-call");
		}

		const args = [];
		for (let i = 0; i < op.arguments.length; i++) {
			args.push(state.lastAssignment[op.arguments[i].variable_id]);
		}

		for (let i = 0; i < op.destinations.length; i++) {
			const dst = op.destinations[i].variable_id;
			state.lastAssignment[dst] = { tag: "app", f: fs[i], args };
		}

		for (let postcondition of signature.postconditions) {
			throw new Error("TODO: Assuem postcondition of op-static-call");
		}
	} else if (op.tag === "op-unreachable") {
		if (checkUnreachable(state) !== "refuted") {
			// TODO: Better classify verification failures.
			state.failedVerifications.push({
				tag: "failed-assert",
				assertLocation: op.diagnostic_location,
			});
		}
		return;
	} else if (op.tag === "op-var") {

	}
	throw new Error(`unhandled op ${op}`);
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
		theory.addConstraint(clause);
	}
	for (let clause of state.pathConstraints) {
		theory.addConstraint([clause]);
	}

	return theory.attemptRefutation();
}
