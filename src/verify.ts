import { RecursivePreconditionErr } from "./diagnostics";
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
		state.constantSorts[p] = sort;

		// Update the stack.
		state.stackInitialize(f.signature.parameters[i], p, i);
	}

	// Execute and validate the function's preconditions.
	for (let i = 0; i < f.signature.preconditions.length; i++) {
		const precondition = f.signature.preconditions[i];
		traverseBlock(program, precondition.block, state, {
			// Return statements do not return a value.
			returnsPostConditions: [],
		}, () => {
			state.clauses.push([
				{
					tag: "predicate",
					predicate: state.getLocal(precondition.result.variable_id).assignment,
				},
			]);
		});
	}

	traverseBlock(program, f.body, state, {
		returnsPostConditions: f.signature.postconditions,
	});

	// The IR type-checker verifies that functions must end with a op-return or
	// op-unreachable.
	return state.failedVerifications;
}

interface VerificationContext {
	/// The post-conditions to verify at a ReturnStatement.
	returnsPostConditions: { block: ir.OpBlock, result: ir.VariableID }[],
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
	assertLocation: ir.SourceLocation,
}

interface FailedReturnVerification {
	tag: "failed-return",
	blockEndLocation?: ir.SourceLocation,
}

interface SignatureSet {
	blockedFunctions: Record<string, boolean>,
	blockedInterfaces: Record<string, Record<string, string>>,
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

	/// Mapping from Shiru local variable to value/type/sort.
	stack: { sort: smt.UFSort, assignment: smt.UFValue, t: ir.Type }[] = [];

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

	stackInitialize(t: ir.Type, value: smt.UFValue, expectedIndex?: number | undefined) {
		const id = this.stack.length;
		if (expectedIndex !== undefined) {
			if (expectedIndex !== id) {
				throw new Error("bad expectedIndex");
			}
		}

		this.stack.push({
			sort: sortOf(t),
			assignment: value,
			t,
		});
		return id;
	}

	getLocal(v: number) {
		if (this.stack[v] === undefined) {
			throw new Error(`Local ${v} is out of bounds for read in stack [${this.stack.map((x, i) => i + ": " + showType(x.t)).join(", ")}]`);
		}
		return this.stack[v];
	}

	vendConstant(sort: smt.UFSort, hint: string = "v") {
		const n = `sh_var_${this.nextConstant}_${hint}`;
		this.nextConstant += 1;
		this.constantSorts[n] = sort;
		return n;
	}

	updateAssignment(destination: number, value: smt.UFValue) {
		if (this.stack[destination] === undefined) {
			throw new Error(`Local ${destination} is out of bounds for write in stack [${this.stack.map((x, i) => i + ": " + showType(x.t)).join(", ")}]`);
		}
		this.stack[destination].assignment = value;
	}

	getStackSize() {
		return this.stack.length;
	}

	truncateStackToSize(size: number) {
		this.stack.splice(size);
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
			state.functionSorts[f] = state.getLocal(destinations[i].variable_id).sort;
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
			state.functionSorts[f] = state.getLocal(op.destinations[i].variable_id).sort;
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
		state.updateAssignment(op.destination.variable_id,
			state.getLocal(op.source.variable_id).assignment);
		return;
	} else if (op.tag === "op-branch") {
		const conditionVariable = state.getLocal(op.condition.variable_id).assignment;
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
		const sort = state.getLocal(op.destination.variable_id).sort;
		state.updateAssignment(op.destination.variable_id, {
			tag: "const", value: op.value, sort
		});
		return;
	} else if (op.tag === "op-field") {
		const baseType = state.getLocal(op.object.variable_id).t;
		const dstType = state.getLocal(op.destination.variable_id).t;
		const f = createFieldFunctionID(state, baseType, op.field, dstType);
		state.updateAssignment(op.destination.variable_id, {
			tag: "app",
			f,
			args: [state.getLocal(op.object.variable_id).assignment],
		});
		return;
	} else if (op.tag === "op-new-record") {
		const fieldNames = Object.keys(op.fields).sort();
		const fields = [];
		for (let field of fieldNames) {
			fields.push(state.getLocal(op.fields[field].variable_id).assignment);
		}
		const dstType = state.getLocal(op.destination.variable_id).t;
		const f = createConstructorFunctionID(state, dstType);
		const app: smt.UFValue = {
			tag: "app",
			f,
			args: fields,
		};
		state.updateAssignment(op.destination.variable_id, app);
		for (let i = 0; i < fields.length; i++) {
			const fieldType = state.getLocal(op.fields[fieldNames[i]].variable_id).t;
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
			const left = state.getLocal(op.arguments[0].variable_id).assignment;
			const right = state.getLocal(op.arguments[1].variable_id).assignment;
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
			args.push(state.getLocal(op.arguments[i].variable_id).assignment);
		}

		if (state.recursivePreconditions.blockedFunctions[fn] !== undefined) {
			throw new RecursivePreconditionErr({
				callsite: op.diagnostic_callsite,
				fn: fn,
			});
		} else {
			state.recursivePreconditions.blockedFunctions[fn] = true;
			const oldStack = state.stack;
			state.stack = [];
			for (let i = 0; i < op.arguments.length; i++) {
				const local = oldStack[op.arguments[i].variable_id];
				state.stack.push({
					sort: local.sort,
					assignment: local.assignment,
					t: local.t,
				});
			}
			for (let precondition of signature.preconditions) {
				traverseBlock(program, precondition.block, state, {
					...context,
				}, () => {
					const r = checkUnreachable(state, [{
						tag: "not",
						constraint: {
							tag: "predicate",
							predicate: state.getLocal(precondition.result.variable_id).assignment,
						},
					}]);
					if (r !== "refuted") {
						state.failedVerifications.push({
							tag: "failed-precondition",
							callLocation: op.diagnostic_callsite,
							preconditionLocation: precondition.location,
						});
					}
				});
			}
			state.stack = oldStack;
			delete state.recursivePreconditions.blockedFunctions[fn];
		}

		const smtFnID = createFunctionIDs(state, op.destinations, fn, signature, op.type_arguments);
		for (let i = 0; i < op.destinations.length; i++) {
			const dst = op.destinations[i].variable_id;
			state.updateAssignment(dst, { tag: "app", f: smtFnID[i], args });
		}

		for (let postcondition of signature.postconditions) {
			throw new Error("TODO: Assume postcondition of op-static-call");
		}

		// Handle the special semantics of functions.
		if (signature.semantics?.eq === true) {
			if (op.arguments.length !== 2) {
				throw new Error("Function signature with `eq` semantics must take exactly 2 arguments (" + fn + ")");
			}
			const left = state.getLocal(op.arguments[0].variable_id).assignment;
			const right = state.getLocal(op.arguments[1].variable_id).assignment;
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
		state.stackInitialize(op.type, state.defaultInhabitant(sortOf(op.type)));
		return;
	}

	const _: never = op;
	throw new Error(`unhandled op ${op["tag"]}`);
}

function checkUnreachable(state: VerificationState, additionalConstraints?: smt.UFConstraint[]): "refuted" | {} {
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
	if (additionalConstraints !== undefined) {
		for (let c of additionalConstraints) {
			theory.addConstraint([c]);
		}
	}

	return theory.attemptRefutation();
}
