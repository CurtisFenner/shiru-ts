import * as diagnostics from "./diagnostics";
import * as ir from "./ir";
import * as smt from "./smt";

/// Represents a constraint solver. The `meta` is used to associated the query
/// with a "reason" the query is being asked.
export type ConstraintSolver = (
	meta: FailedVerification,
	constantSorts: Record<string, smt.UFSort>,
	functionSorts: Record<string, smt.UFSort>,
	clauses: smt.UFConstraint[][],
) => "refuted" | {};

export function verifyProgram(
	program: ir.Program,
	constraintSolver: ConstraintSolver = checkUnreachableSMT,
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
	const contextParameters = [];
	for (let i = 0; i < f.signature.parameters.length; i++) {
		const parameter = f.signature.parameters[i];

		// Create a symbolic constant for the initial value of the parameter.
		const sort = sortOf(parameter.type);
		const constant = state.vendConstant(sort)
		state.defineVariable(parameter, constant);
		contextParameters.push({
			definition: parameter,
			constant,
		});
	}

	// Execute and validate the function's preconditions.
	for (let i = 0; i < f.signature.preconditions.length; i++) {
		const precondition = f.signature.preconditions[i];
		traverseBlock(program, precondition.block, state, {
			// Return statements do not return a value.
			returnsPostConditions: [],
			parameters: contextParameters,
			constraintSolver,
		}, () => {
			const bool = state.getValue(precondition.precondition).value;
			state.pushConstraint(negate({ tag: "predicate", predicate: bool }));
			state.markPathUnreachable();
			state.popConstraint();
		});
	}

	traverseBlock(program, f.body, state, {
		returnsPostConditions: f.signature.postconditions,
		parameters: contextParameters,
		constraintSolver,
	});

	// The IR type-checker verifies that functions must end with a op-return or
	// op-unreachable.
	return state.failedVerifications;
}

interface VerificationContext {
	/// The post-conditions to verify at a ReturnStatement.
	returnsPostConditions: ir.Postcondition[],

	/// The number of function parameters.
	parameters: { definition: ir.VariableDefinition, constant: smt.UFValue }[],

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

interface VerificationScope {
	variables: Map<ir.VariableID, { type: ir.Type, value: smt.UFValue }>,
}

class VerificationState {
	private constantSorts: Record<string, smt.UFSort> = {};
	functionSorts: Record<string, smt.UFSort> = {};

	recursivePreconditions: SignatureSet = {
		blockedFunctions: {},
		blockedInterfaces: {},
	};

	recursivePostconditions: SignatureSet = {
		blockedFunctions: {},
		blockedInterfaces: {},
	};

	/// `scopes` is a stack of variable mappings. SSA variables aren't
	/// reassigned, but can be shadowed (including within the same block).
	private scopes: VerificationScope[] = [
		{
			variables: new Map(),
		}
	];

	// An append-only set of constraints that grow, regardless of path.
	private clauses: smt.UFConstraint[][] = [];

	/// `pathConstraints` is the stack of conditional constraints that must be
	/// true to reach a position in the program.
	private pathConstraints: smt.UFConstraint[] = [];

	// Verification adds failure messages to this stack as they are encountered.
	// Multiple failures can be returned.
	failedVerifications: FailedVerification[] = [];

	private nextConstant: number = 1000;

	addTautology(clause: smt.UFConstraint[]) {
		this.clauses.push(clause);
	}

	pushScope() {
		this.scopes.push({
			variables: new Map(),
		});
	}

	popScope() {
		this.scopes.pop();
	}

	markPathUnreachable() {
		this.clauses.push(this.pathConstraints.map(negate));
	}

	checkReachable(reason: FailedVerification, solver: ConstraintSolver) {
		const clauses = this.clauses.slice();
		for (const element of this.pathConstraints) {
			clauses.push([element]);
		}
		return solver(reason, this.constantSorts, this.functionSorts, clauses);
	}

	pushConstraint(constraint: smt.UFConstraint) {
		this.pathConstraints.push(constraint);
	}

	popConstraint() {
		this.pathConstraints.pop();
	}

	vendConstant(sort: smt.UFSort, hint: string = "v"): smt.UFVariable {
		const n = `c'${this.nextConstant}'${hint}`;
		this.nextConstant += 1;
		this.constantSorts[n] = sort;
		return n as smt.UFVariable;
	}

	defineVariable(variable: ir.VariableDefinition, value: smt.UFValue) {
		const scope = this.scopes[this.scopes.length - 1];
		scope.variables.set(variable.variable, {
			type: variable.type,
			value: value,
		});
	}

	getValue(variable: ir.VariableID) {
		for (let i = this.scopes.length - 1; i >= 0; i--) {
			const scope = this.scopes[i];
			const value = scope.variables.get(variable);
			if (value !== undefined) {
				return value;
			}
		}
		throw new Error("variable is not defined");
	}
}

function negate(constraint: smt.UFConstraint): smt.UFConstraint {
	return { tag: "not", constraint };
}

function showType(t: ir.Type): string {
	if (t.tag === "type-compound") {
		return t.record + "[" + t.type_arguments.map(showType).join(",") + "]";
	} else if (t.tag === "type-primitive") {
		return t.primitive;
	} else if (t.tag === "type-variable") {
		return "#" + t.id;
	}
	throw new Error(`unhandled ${t}`);
}

/// RETURNS an array of strings, being the SMT function names for each of the
/// given function's return values.
/// TODO: A better way to encode generic functions is to treat type constraint
/// parameters as arguments.
function createFunctionIDs(
	state: VerificationState,
	destinations: ir.VariableDefinition[],
	f: string,
	signature: ir.FunctionSignature,
	typeArguments: ir.Type[],
): smt.UFFunction[] {
	const args = typeArguments.map(showType);
	const prefix = `sh_f_${f}[${args.join(",")}]`;
	const fs = [];
	for (let i = 0; i < signature.return_types.length; i++) {
		const f = `${prefix}:${i}`;
		fs.push(f as smt.UFFunction);
		if (state.functionSorts[f] === undefined) {
			state.functionSorts[f] = sortOf(destinations[i].type);
		}
	}
	return fs;
}

function createDynamicFunctionID(state: VerificationState, op: ir.OpDynamicCall): string[] {
	const args = op.subjects.concat(op.signature_type_arguments).map(showType);
	// TODO: This is a bad way to do this, particularly because it makes
	// encoding parametricity relationships harder.
	const prefix = `dyn_${op.constraint}:${op.signature_id}[${args.join(",")}]`;
	const fs = [];
	for (let i = 0; i < op.destinations.length; i++) {
		const f = `${prefix}:${i}`;
		fs.push(f);
		if (state.functionSorts[f] == undefined) {
			state.functionSorts[f] = sortOf(op.destinations[i].type);
		}
	}
	return fs;
}

function createFieldFunctionID(
	state: VerificationState,
	base: ir.Type,
	field: string,
	fieldType: ir.Type,
): smt.UFFunction {
	const t = showType(base);
	const name = `field_${t}:${field}`;
	if (state.functionSorts[name] === undefined) {
		state.functionSorts[name] = sortOf(fieldType);
	}
	return name as smt.UFFunction;
}

function createConstructorFunctionID(state: VerificationState, base: ir.Type): smt.UFFunction {
	const t = showType(base);
	const name = `new_${t}`;
	if (state.functionSorts[name] === undefined) {
		state.functionSorts[name] = sortOf(base);
	}
	return name as smt.UFFunction;
}

function learnEquality(
	state: VerificationState,
	left: smt.UFValue,
	right: smt.UFValue,
	equalityVariable: smt.UFVariable,
) {
	const resultCon: smt.UFConstraint = {
		tag: "predicate",
		predicate: equalityVariable,
	};

	// Create a two-way implication between the destination variable and the
	// abstract result of comparison.
	// This is necessary because comparison is only a UFConstraint, not a
	// UFValue.
	const eqCon: smt.UFConstraint = { tag: "=", left, right };
	state.addTautology([negate(resultCon), eqCon]);
	state.addTautology([resultCon, negate(eqCon)]);
}

function traverseBlock(
	program: ir.Program,
	block: ir.OpBlock,
	state: VerificationState,
	context: VerificationContext,
	then?: () => unknown,
) {
	// Blocks bound variable scopes, so variables must be cleared after.
	state.pushScope();

	for (let subop of block.ops) {
		traverse(program, subop, state, context);
	}

	// Execute the final computation before exiting this scope.
	if (then !== undefined) {
		then();
	}

	// Clear variables defined within this block.
	state.popScope();
}

// MUTATES the verification state parameter, to add additional clauses that are
// ensured after the execution (and termination) of this operation.
function traverse(program: ir.Program, op: ir.Op, state: VerificationState, context: VerificationContext): void {
	if (op.tag === "op-branch") {
		const symbolicCondition: smt.UFConstraint = {
			tag: "predicate",
			predicate: state.getValue(op.condition).value,
		}

		const definedConstants: smt.UFVariable[] = [];
		for (const destination of op.destinations) {
			const sort = sortOf(destination.destination.type);
			definedConstants.push(state.vendConstant(sort, "branch"));
		}

		state.pushScope();
		state.pushConstraint(symbolicCondition);
		traverseBlock(program, op.trueBranch, state, context, () => {
			for (let i = 0; i < op.destinations.length; i++) {
				const destination = op.destinations[i];
				const source = destination.trueSource;
				if (source === "undef") continue;
				state.addTautology([
					negate(symbolicCondition),
					{
						tag: "=",
						left: definedConstants[i],
						right: state.getValue(source).value,
					},
				]);
			}
		})
		state.popConstraint();
		state.popScope();

		state.pushScope();
		state.pushConstraint(negate(symbolicCondition));
		traverseBlock(program, op.falseBranch, state, context, () => {
			for (let i = 0; i < op.destinations.length; i++) {
				const destination = op.destinations[i];
				const source = destination.falseSource;
				if (source === "undef") continue;
				state.addTautology([
					symbolicCondition,
					{
						tag: "=",
						left: definedConstants[i],
						right: state.getValue(source).value,
					},
				]);
			}
		});
		state.popConstraint();
		state.popScope();

		for (let i = 0; i < op.destinations.length; i++) {
			state.defineVariable(op.destinations[i].destination, definedConstants[i]);
		}

		return;
	} else if (op.tag === "op-const") {
		// Like assignment, this requires no manipulation of constraints, only
		// the state of variables.
		const literal: smt.UFLiteralValue = {
			tag: "literal",
			literal: op.value,
			sort: sortOf(op.destination.type),
		};
		state.defineVariable(op.destination, literal);
		return;
	} else if (op.tag === "op-field") {
		const object = state.getValue(op.object);
		const baseType = object.type;
		const f = createFieldFunctionID(state, baseType, op.field, op.destination.type);
		const fieldValue: smt.UFValue = {
			tag: "app",
			f,
			args: [object.value],
		};
		state.defineVariable(op.destination, fieldValue);
		return;
	} else if (op.tag === "op-new-record") {
		const fieldNames = Object.keys(op.fields).sort();
		const fields = [];
		for (let field of fieldNames) {
			fields.push(state.getValue(op.fields[field]).value);
		}
		const constructor = createConstructorFunctionID(state, op.destination.type);
		const recordValue: smt.UFValue = {
			tag: "app",
			f: constructor,
			args: fields,
		};
		state.defineVariable(op.destination, recordValue);
		for (let i = 0; i < fields.length; i++) {
			const fieldType = state.getValue(op.fields[fieldNames[i]]).type;
			const getField = createFieldFunctionID(state, op.destination.type, fieldNames[i], fieldType);
			state.addTautology([
				{
					tag: "=",
					left: { tag: "app", f: getField, args: [recordValue] },
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
				state.pushScope();
				const values = [];
				for (const source of op.sources) {
					values.push(state.getValue(source));
				}

				// The original parameters might have been shadowed, so they
				// need to be redeclared.
				for (const parameter of context.parameters) {
					state.defineVariable(parameter.definition, parameter.constant);
				}
				for (let i = 0; i < postcondition.returnedValues.length; i++) {
					state.defineVariable(postcondition.returnedValues[i], values[i].value);
				}

				traverseBlock(program, postcondition.block, state, context, () => {
					const reason: FailedVerification = {
						tag: "failed-postcondition",
						returnLocation: op.diagnostic_return_site,
						postconditionLocation: postcondition.location,
					};

					// Check if it's possible for the indicated boolean to be
					// false.
					const bool: smt.UFConstraint = {
						tag: "predicate",
						predicate: state.getValue(postcondition.postcondition).value,
					};
					state.pushConstraint(negate(bool));
					const refutation = state.checkReachable(reason, context.constraintSolver);
					state.popConstraint();
					if (refutation !== "refuted") {
						state.failedVerifications.push(reason);
					}
				});

				state.popScope();
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

		if (signature.semantics?.eq === true) {
			if (op.arguments.length !== 2) {
				throw new Error("Foreign signature with `eq` semantics"
					+ " must take exactly 2 arguments (" + op.operation + ")");
			}
			const left = state.getValue(op.arguments[0]).value;
			const right = state.getValue(op.arguments[1]).value;
			if (op.destinations.length !== 1) {
				throw new Error("Foreign signature with `eq` semantics"
					+ " must return exactly 1 value");
			}
			const destination = op.destinations[0];
			const eqConstant = state.vendConstant(sortOf(destination.type), "eq");
			learnEquality(state, left, right, eqConstant);
			state.defineVariable(destination, eqConstant);
		}
		return;
	} else if (op.tag === "op-static-call") {
		traverseStaticCall(program, op, state, context);
		return;
	} else if (op.tag === "op-dynamic-call") {
		const fs = createDynamicFunctionID(state, op);
		const constraint = program.interfaces[op.constraint];
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
		if (state.checkReachable(reason, context.constraintSolver) !== "refuted") {
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

	if (state.recursivePreconditions.blockedFunctions[fn] !== undefined) {
		throw new diagnostics.RecursivePreconditionErr({
			callsite: op.diagnostic_callsite,
			fn: fn,
		});
	} else {
		state.recursivePreconditions.blockedFunctions[fn] = true;

		for (const precondition of signature.preconditions) {
			state.pushScope();

			const recursiveContext: VerificationContext = {
				returnsPostConditions: [],
				parameters: [],
				constraintSolver: context.constraintSolver,
			};
			for (let i = 0; i < op.arguments.length; i++) {
				state.defineVariable(signature.parameters[i], args[i]);
				recursiveContext.parameters.push({
					definition: signature.parameters[i],
					constant: args[i],
				});
			}

			traverseBlock(program, precondition.block, state, recursiveContext, () => {
				const reason: FailedVerification = {
					tag: "failed-precondition",
					callLocation: op.diagnostic_callsite,
					preconditionLocation: precondition.location,
				};

				const bool: smt.UFConstraint = {
					tag: "predicate",
					predicate: state.getValue(precondition.precondition).value,
				};

				state.pushConstraint(negate(bool));
				const refutation = state.checkReachable(reason, context.constraintSolver);
				if (refutation !== "refuted") {
					state.failedVerifications.push(reason);
				}
				state.popConstraint();
			});
			state.popScope();
		}

		delete state.recursivePreconditions.blockedFunctions[fn];
	}

	const smtFnID = createFunctionIDs(state, op.destinations, fn, signature, op.type_arguments);
	for (let i = 0; i < op.destinations.length; i++) {
		state.defineVariable(op.destinations[i], {
			tag: "app",
			f: smtFnID[i],
			args,
		});
	}

	for (const postcondition of signature.postconditions) {
		state.recursivePostconditions.blockedFunctions[fn] = true;
		state.pushScope();

		const parameters = [];
		for (let i = 0; i < op.arguments.length; i++) {
			parameters.push({
				variable: signature.parameters[i],
				value: state.getValue(op.arguments[i]).value,
			});
		}
		for (let i = 0; i < op.destinations.length; i++) {
			parameters.push({
				variable: postcondition.returnedValues[i],
				value: state.getValue(op.destinations[i].variable).value,
			});
		}

		for (const parameter of parameters) {
			state.defineVariable(parameter.variable, parameter.value);
		}

		// TODO: Do we need a different context?
		traverseBlock(program, postcondition.block, state, context, () => {
			const bool: smt.UFConstraint = {
				tag: "predicate",
				predicate: state.getValue(postcondition.postcondition).value,
			};
			state.pushConstraint(negate(bool));
			state.markPathUnreachable();
			state.popConstraint();
		});

		state.popScope();
		delete state.recursivePostconditions.blockedFunctions[fn];
	}

	// Handle the special semantics of functions.
	if (signature.semantics?.eq === true) {
		if (op.arguments.length !== 2) {
			throw new Error("Function signature with `eq` semantics must take exactly 2 arguments (" + fn + ")");
		}
		const left = state.getValue(op.arguments[0]).value;
		const right = state.getValue(op.arguments[1]).value;
		if (op.destinations.length !== 1) {
			throw new Error("Function signatures with `eq` semantics must return exactly 1 value (" + fn + ")");
		}
		const destination = op.destinations[0];
		const constant = state.vendConstant(sortOf(destination.type), "feq");
		learnEquality(state, left, right, constant);
		state.defineVariable(op.destinations[0], constant);
	}
}

export function checkUnreachableSMT(
	_: FailedVerification,
	constantSorts: Record<string, smt.UFSort>,
	functionSorts: Record<string, smt.UFSort>,
	clauses: smt.UFConstraint[][],
): "refuted" | {} {
	const theory = new smt.UFTheory();
	for (let variable in constantSorts) {
		theory.defineVariable(variable, constantSorts[variable]);
	}
	for (let func in functionSorts) {
		theory.defineFunction(func, functionSorts[func]);
	}
	for (let clause of clauses) {
		if (clause.length === 0) {
			return "refuted";
		}
		theory.addConstraint(clause);
	}

	return theory.attemptRefutation();
}
