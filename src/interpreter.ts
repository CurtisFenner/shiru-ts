import * as ir from "./ir";

export type Value = ClassValue | BooleanValue | StringValue | IntValue;
export type ClassValue = {
	sort: "class",
	fields: {
		[field: string]: Value,
	},
};
export type BooleanValue = {
	sort: "boolean",
	boolean: boolean,
};
export type StringValue = {
	sort: "string",
	string: string,
};
export type IntValue = {
	sort: "int",
	int: number,
};

interface VTable {
	tag: "dictionary",
	entries: VTableEntry[],
}

interface VTableEntry {
	implementation: ir.FunctionID,
	closureConstraints: (VTable | { tag: "callsite", callsite: number })[],
}

function matchTypeSingle(variables: Map<number, ir.Type | null>, pattern: ir.Type, subject: ir.Type): boolean {
	if (pattern.tag === "type-variable") {
		const existing = variables.get(pattern.id.type_variable_id);
		if (existing !== undefined) {
			if (existing === null || ir.equalTypes(existing, subject)) {
				variables.set(pattern.id.type_variable_id, subject);
				return true;
			}
			return false;
		} else {
			// Literally references a type-variable, which must match the subject.
			if (subject.tag !== "type-variable") {
				return false;
			}
			return pattern.id.type_variable_id === subject.id.type_variable_id;
		}
	} else if (pattern.tag === "type-compound" && subject.tag === "type-compound") {
		if (pattern.record.record_id !== subject.record.record_id) {
			return false;
		}

		if (pattern.type_arguments.length !== subject.type_arguments.length) {
			throw new Error(`Arity of type \`${pattern.record.record_id}\` is inconsistent.`);
		}

		for (let i = 0; i < pattern.type_arguments.length; i++) {
			if (!matchTypeSingle(variables, pattern.type_arguments[i], subject.type_arguments[i])) {
				return false;
			}
		}
		return true;
	} else if (pattern.tag === "type-primitive" && subject.tag === "type-primitive") {
		return pattern.primitive === subject.primitive;
	} else {
		return false;
	}
}

/// `matchTypes` compares a `subject` to a particular `pattern`, returning a
/// possible instantiation of the variables named in `forAny` such that the
/// subject is equal to the instantiated pattern, or `null` if there is no such
/// instantiation.
function matchTypes(forAny: ir.TypeVariable[], pattern: ir.Type[], subject: ir.Type[]): Map<number, ir.Type> | null {
	if (pattern.length !== subject.length) {
		throw new Error("invalid");
	}

	let mapping: Map<number, ir.Type | null> = new Map();
	for (let t of forAny) {
		mapping.set(t.id.type_variable_id, null);
	}

	for (let i = 0; i < pattern.length; i++) {
		if (!matchTypeSingle(mapping, pattern[i], subject[i])) {
			return null;
		}
	}

	for (let [k, v] of mapping) {
		if (!v) {
			// All variables must be referenced in the pattern.
			console.error("mapping:", mapping);
			console.error("Illegal pattern in matchTypes:", pattern);
			throw new Error("pattern variable `" + k + "` is not referenced in pattern.");
		}
	}

	return mapping as Map<number, ir.Type>;
}

function isTruthy(value: Value): boolean {
	if (value.sort !== "boolean") throw new Error("bad value sort for isTruthy `" + value.sort + "`");
	return value.boolean;
}

function satisfyConstraint(
	globalVTableFactories: Record<string, ir.VTableFactory>,
	constraint: ir.InterfaceID,
	subjects: ir.Type[],
	availableSignatures: ir.ConstraintParameter[],
	// TODO: Separate this parameter so that this function's search can be
	// memoized.
	availableVTables: VTable[],
): VTable {
	// TODO: This is a very inefficient scan that is repeated at each call.
	// It should instead be precomputed for each distinct callsite.

	for (let i = 0; i < availableSignatures.length; i++) {
		const signature = availableSignatures[i];
		if (signature.constraint.interface_id !== constraint.interface_id) {
			continue;
		}
		const match = matchTypes([], signature.subjects, subjects);
		if (match !== null) {
			return availableVTables[i];
		}
	}

	for (let global in globalVTableFactories) {
		const factory = globalVTableFactories[global];
		const match = matchTypes(factory.for_any, factory.subjects, subjects);
		if (match !== null) {
			// Collect the entries to use in the v-table.
			const vtable: VTable = { tag: "dictionary", entries: [] };
			for (let entryPattern of factory.entries) {
				const entry: VTableEntry = {
					implementation: entryPattern.implementation,
					closureConstraints: [],
				};
				for (let c of entryPattern.constraint_parameters) {
					if (typeof c === "number") {
						entry.closureConstraints.push({
							tag: "callsite",
							callsite: c,
						});
					} else {
						const subSubjects = c.subjects.map(a => ir.typeSubstitute(a, match));
						const subVTableReference = satisfyConstraint(
							globalVTableFactories, c.constraint, subSubjects,
							availableSignatures, availableVTables);
						entry.closureConstraints.push(subVTableReference);
					}
				}
				vtable.entries.push(entry);
			}
			return vtable;
		}
	}

	throw new Error("Could not find an implementation of `"
		+ constraint.interface_id
		+ "` for " + JSON.stringify(subjects));
}

export type ForeignImpl = (args: Value[]) => Value[];

interface Context {
	program: ir.Program,
	foreign: Record<string, ForeignImpl>,

	/// `availableConstraints` describes the elements of `availableVTables`.
	/// These are separated because `availableConstraints` remains constant as
	/// execution evolves, but `availableVTables` may change constantly.
	availableVTables: VTable[],
	availableConstraints: ir.ConstraintParameter[],
}

interface Slot {
	value: Value,
	t: ir.Type,
}

export function interpret(
	fn: string,
	args: Value[],
	program: ir.Program,
	foreign: Record<string, ForeignImpl>): Value[] {
	const context: Context = {
		program,
		foreign,
		availableVTables: [],
		availableConstraints: [],
	};

	const iter = interpretCall(fn, args, [], context);
	while (true) {
		const x = iter.next();
		if (x.done) {
			return x.value;
		}
	}
}

/// Execute a Shiru program until termination, returning the result from the 
/// given `entry` function.
export function* interpretCall(
	fnName: string,
	args: Value[],
	vtables: VTable[],
	context: Context,
): Generator<{}, Value[], unknown> {
	if (!context.program.functions[fnName]) {
		throw new Error("The program has no function named `" + fnName + "`");
	}

	const fn = context.program.functions[fnName];
	if (fn.signature.constraint_parameters.length !== vtables.length) {
		throw new Error("interpretCall: Wrong number of constraint parameters");
	}
	const newContext: Context = {
		...context,
		availableConstraints: fn.signature.constraint_parameters,
		availableVTables: vtables,
	};

	const stack = args.map((value, i) => ({ value, t: fn.signature.parameters[i] }));
	const result = yield* interpretBlock(fn.body, stack, newContext);
	if (result === null) {
		throw new Error("Function `" + fn + "` failed to return a result");
	}
	return result;
}

function* interpretBlock(
	block: ir.OpBlock,
	stack: Slot[],
	context: Context,
): Generator<{}, Value[] | null, unknown> {
	const initialStack = stack.length;
	for (let op of block.ops) {
		const result = yield* interpretOp(op, stack, context);
		if (result !== null) {
			return result;
		}
	}
	stack.splice(initialStack);
	return null;
}

function* interpretOp(
	op: ir.Op,
	stack: Slot[],
	context: Context,
): Generator<{}, Value[] | null, unknown> {
	yield {};
	if (op.tag === "op-return") {
		return op.sources.map(({ variable_id }) => stack[variable_id].value);
	} else if (op.tag === "op-var") {
		stack.push({ t: op.type, value: null as any });
		return null;
	} else if (op.tag === "op-assign") {
		stack[op.destination.variable_id].value = stack[op.source.variable_id].value;
		return null;
	} else if (op.tag === "op-const") {
		let value: Value;
		if (typeof op.value === "boolean") {
			value = { sort: "boolean", boolean: op.value };
		} else if (typeof op.value === "number") {
			value = { sort: "int", int: op.value };
		} else {
			const _: never = op.value;
			throw new Error("interpretOp: unhandled op-const value");
		}
		stack[op.destination.variable_id].value = value;
		return null;
	} else if (op.tag === "op-static-call") {
		const args = op.arguments.map(({ variable_id }) => stack[variable_id].value);

		const constraintArgs: VTable[] = [];
		const fn = context.program.functions[op.function.function_id];
		const instantiation: Map<number, ir.Type> = new Map();
		for (let i = 0; i < op.type_arguments.length; i++) {
			instantiation.set(i, op.type_arguments[i]);
		}
		for (let constraintTemplate of fn.signature.constraint_parameters) {
			const subjects = constraintTemplate.subjects.map(t => ir.typeSubstitute(t, instantiation));
			const vtable = satisfyConstraint(
				context.program.globalVTableFactories,
				constraintTemplate.constraint, subjects,
				context.availableConstraints, context.availableVTables);
			constraintArgs.push(vtable);
		}

		const result = yield* interpretCall(op.function.function_id, args, constraintArgs, context);
		for (let i = 0; i < result.length; i++) {
			stack[op.destinations[i].variable_id].value = result[i];
		}
		return null;
	} else if (op.tag === "op-foreign") {
		const args = op.arguments.map(({ variable_id }) => stack[variable_id].value);
		const f = context.foreign[op.operation];
		if (f === undefined) {
			throw new Error("interpretOp: no implementation for `" + op.operation + "`");
		}
		const result = f(args);
		for (let i = 0; i < op.destinations.length; i++) {
			stack[op.destinations[i].variable_id].value = result[i];
		}
		return null;
	} else if (op.tag === "op-branch") {
		const condition = isTruthy(stack[op.condition.variable_id].value);
		const branch = condition ? op.trueBranch : op.falseBranch;
		const result = yield* interpretBlock(branch, stack, context);
		return result;
	} else if (op.tag === "op-dynamic-call") {
		const args = op.arguments.map(({ variable_id }) => stack[variable_id].value);
		const vtable = satisfyConstraint(context.program.globalVTableFactories,
			op.constraint, op.subjects,
			context.availableConstraints, context.availableVTables);

		const spec = vtable.entries[op.signature_id];
		const constraintArgs = [];
		for (let constraint of spec.closureConstraints) {
			if (constraint.tag === "callsite") {
				throw new Error("TODO: Retrieve callsite constraint like static call");
			} else {
				constraintArgs.push(constraint);
			}
		}

		const result = yield* interpretCall(spec.implementation.function_id, args, constraintArgs, context);
		for (let i = 0; i < result.length; i++) {
			stack[op.destinations[i].variable_id].value = result[i];
		}
		return null;
	}

	const _: never = op;
	throw new Error("interpretOp: unhandled op tag `" + op["tag"] + "`");
}
