import * as ir from "./ir";
import { ErrorElement } from "./lexer";

export type Value = RecordValue | BooleanValue | BytesValue | IntValue;
export type RecordValue = {
	sort: "record",
	fields: {
		[field: string]: Value,
	},
};
export type BooleanValue = {
	sort: "boolean",
	boolean: boolean,
};
export type BytesValue = {
	sort: "bytes",
	bytes: string,
};
export type IntValue = {
	sort: "int",
	int: number,
};

interface VTable {
	tag: "dictionary",
	entries: Record<string, VTableEntry>,
}

interface VTableEntry {
	implementation: ir.FunctionID,
	closureConstraints: (VTable | { tag: "callsite", callsite: number })[],
}

function matchTypeSingle(variables: Map<ir.TypeVariableID, ir.Type | null>, pattern: ir.Type, subject: ir.Type): boolean {
	if (pattern.tag === "type-variable") {
		const existing = variables.get(pattern.id);
		if (existing !== undefined) {
			if (existing === null || ir.equalTypes(existing, subject)) {
				variables.set(pattern.id, subject);
				return true;
			}
			return false;
		} else {
			// Literally references a type-variable, which must match the subject.
			if (subject.tag !== "type-variable") {
				return false;
			}
			return pattern.id === subject.id;
		}
	} else if (pattern.tag === "type-compound" && subject.tag === "type-compound") {
		if (pattern.record !== subject.record) {
			return false;
		}

		if (pattern.type_arguments.length !== subject.type_arguments.length) {
			throw new Error(`Arity of type \`${pattern.record}\` is inconsistent.`);
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
function matchTypes(forAny: ir.TypeVariable[], pattern: ir.Type[], subject: ir.Type[]): Map<ir.TypeVariableID, ir.Type> | null {
	if (pattern.length !== subject.length) {
		throw new Error("invalid");
	}

	let mapping: Map<ir.TypeVariableID, ir.Type | null> = new Map();
	for (let t of forAny) {
		mapping.set(t.id, null);
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

	return mapping as Map<ir.TypeVariableID, ir.Type>;
}

function isTruthy(value: Value): boolean {
	if (value.sort !== "boolean") {
		throw new Error("bad value sort for isTruthy `" + value.sort + "`");
	}
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
		if (signature.interface !== constraint) {
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
			const vtable: VTable = { tag: "dictionary", entries: {} };
			for (let key in factory.entries) {
				const entryPattern = factory.entries[key];
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
							globalVTableFactories, c.interface, subSubjects,
							availableSignatures, availableVTables);
						entry.closureConstraints.push(subVTableReference);
					}
				}
				vtable.entries[key] = entry;
			}
			return vtable;
		}
	}

	throw new Error("Could not find an implementation of `"
		+ constraint + "` for " + JSON.stringify(subjects));
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

class Frame {
	private stack: { name: ir.VariableID, t: ir.Type, value: Value, previous: undefined | number }[] = [];
	private variables: Map<ir.VariableID, number> = new Map();

	define(definition: ir.VariableDefinition, value: Value) {
		const slot = this.stack.length;
		this.stack.push({
			name: definition.variable,
			t: definition.type,
			value,
			previous: this.variables.get(definition.variable)
		});
		this.variables.set(definition.variable, slot);
	}

	load(name: ir.VariableID): Value {
		const v = this.variables.get(name);
		if (v === undefined) {
			throw new Error("variable `" + name + "` is not defined");
		}
		return this.stack[v].value;
	}

	stackSize(): number {
		return this.stack.length;
	}

	pop(slice: number) {
		const removed = this.stack.splice(slice);
		for (let i = removed.length - 1; i >= 0; i--) {
			const e = removed[i];
			if (e.previous === undefined) {
				this.variables.delete(e.name);
			} else {
				this.variables.set(e.name, e.previous);
			}
		}
	}
}

export function interpret(
	fn: ir.FunctionID,
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
	fnName: ir.FunctionID,
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

	const frame: Frame = new Frame();
	for (let i = 0; i < args.length; i++) {
		frame.define(fn.signature.parameters[i], args[i]);
	}
	const result = yield* interpretBlock(fn.body, frame, newContext);
	if (result === null) {
		throw new Error("Function `" + fnName + "` failed to return a result");
	}
	return result;
}

function* interpretBlock(
	block: ir.OpBlock,
	frame: Frame,
	context: Context,
	callback?: () => void,
): Generator<{}, Value[] | null, unknown> {
	const initialStack = frame.stackSize();
	for (let op of block.ops) {
		const result = yield* interpretOp(op, frame, context);
		if (result !== null) {
			return result;
		}
	}
	if (callback !== undefined) {
		callback();
	}
	frame.pop(initialStack);
	return null;
}

function* interpretOp(
	op: ir.Op,
	frame: Frame,
	context: Context,
): Generator<{}, Value[] | null, unknown> {
	yield {};
	if (op.tag === "op-return") {
		return op.sources.map(variable => frame.load(variable));
	} else if (op.tag === "op-const") {
		let value: Value;
		if (typeof op.value === "boolean") {
			value = { sort: "boolean", boolean: op.value };
		} else if (typeof op.value === "number") {
			value = { sort: "int", int: op.value };
		} else if (typeof op.value === "string") {
			value = { sort: "bytes", bytes: op.value };
		} else {
			const _: never = op.value;
			throw new Error("interpretOp: unhandled op-const value");
		}
		frame.define(op.destination, value);
		return null;
	} else if (op.tag === "op-static-call") {
		const args = op.arguments.map(variable => frame.load(variable));

		const constraintArgs: VTable[] = [];
		const fn = context.program.functions[op.function];
		const instantiation: Map<number, ir.Type> = new Map();
		for (let i = 0; i < op.type_arguments.length; i++) {
			instantiation.set(i, op.type_arguments[i]);
		}
		for (let constraintTemplate of fn.signature.constraint_parameters) {
			const subjects = constraintTemplate.subjects.map(t => ir.typeSubstitute(t, instantiation));
			const vtable = satisfyConstraint(
				context.program.globalVTableFactories,
				constraintTemplate.interface, subjects,
				context.availableConstraints, context.availableVTables);
			constraintArgs.push(vtable);
		}

		const result = yield* interpretCall(op.function, args, constraintArgs, context);
		for (let i = 0; i < result.length; i++) {
			frame.define(op.destinations[i], result[i]);
		}
		return null;
	} else if (op.tag === "op-foreign") {
		const args = op.arguments.map(source => frame.load(source));
		const f = context.foreign[op.operation];
		if (f === undefined) {
			throw new Error("interpretOp: no implementation for `" + op.operation + "`");
		}
		const result = f(args);
		for (let i = 0; i < op.destinations.length; i++) {
			frame.define(op.destinations[i], result[i]);
		}
		return null;
	} else if (op.tag === "op-branch") {
		const conditionValue = frame.load(op.condition);
		const condition = isTruthy(conditionValue);
		const branch = condition ? op.trueBranch : op.falseBranch;
		const result = yield* interpretBlock(branch, frame, context);
		return result;
	} else if (op.tag === "op-dynamic-call") {
		const args = op.arguments.map(arg => frame.load(arg));
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

		const result = yield* interpretCall(spec.implementation, args, constraintArgs, context);
		for (let i = 0; i < result.length; i++) {
			frame.define(op.destinations[i], result[i]);
		}
		return null;
	} else if (op.tag === "op-proof") {
		// Do nothing.
		return null;
	} else if (op.tag === "op-new-record") {
		const recordValue: RecordValue = {
			sort: "record",
			fields: {},
		};
		for (let f in op.fields) {
			recordValue.fields[f] = frame.load(op.fields[f]);
		}
		frame.define(op.destination, recordValue);
		return null;
	} else if (op.tag === "op-field") {
		const recordValue = frame.load(op.object);
		if (recordValue.sort !== "record") {
			throw new Error("bad value sort for field access");
		}
		frame.define(op.destination, recordValue.fields[op.field]);
		return null;
	} else if (op.tag === "op-unreachable") {
		throw new RuntimeErr([
			"Hit unreachable op at",
			op.diagnostic_location || " (unknown location)",
		]);
	}

	const _: never = op;
	throw new Error("interpretOp: unhandled op tag `" + op["tag"] + "`");
}

export class RuntimeErr {
	constructor(public message: ErrorElement[]) { }
}

function showType(t: ir.Type, context: { typeVariables: string[] }): string {
	if (t.tag === "type-compound") {
		const generics = "[" + t.type_arguments.map(x => showType(x, context)).join(", ") + "]";
		return t.record + generics;
	} else if (t.tag === "type-primitive") {
		return t.primitive;
	} else {
		return "#" + context.typeVariables[t.id];
	}
}

export function printProgram(program: ir.Program, lines: string[]) {
	for (let fnName in program.functions) {
		printFn(program, fnName, lines);
	}
}

export function printFn(program: ir.Program, fnName: string, lines: string[]) {
	const fn = program.functions[fnName];
	const context = { typeVariables: [] as string[] };
	for (let i = 0; i < fn.signature.type_parameters.length; i++) {
		context.typeVariables[i] = "T" + i;
	}
	const parameters = [];
	for (const parameter of fn.signature.parameters) {
		parameters.push(parameter.variable + ": " + showType(parameter.type, context));
	}
	const typeParameters = context.typeVariables.map(x => "#" + x).join(", ");
	lines.push("fn " + fnName + "[" + typeParameters + "](" + parameters.join(", ") + ")");
	for (const pre of fn.signature.preconditions) {
		lines.push("precondition (" + pre.precondition + ") {");
		printBlockContents(pre.block, "", context, lines);
		lines.push("}");
	}
	for (const post of fn.signature.postconditions) {
		lines.push("postcondition ("
			+ post.returnedValues.join(", ")
			+ " -> " + post.postcondition + ") {");
		printBlockContents(post.block, "", context, lines);
		lines.push("}");
	}
	lines.push("body {");
	printBlockContents(fn.body, "", context, lines);
	lines.push("}");
	lines.push("");
}

export function printBlockContents(
	block: ir.OpBlock,
	indent: string,
	context: { typeVariables: string[] },
	lines: string[],
) {
	for (let op of block.ops) {
		printOp(op, indent + "\t", context, lines);
	}
}

export function printOp(
	op: ir.Op,
	indent: string,
	context: { typeVariables: string[] },
	lines: string[],
) {
	if (op.tag === "op-branch") {
		const cond = op.condition;
		lines.push(indent + "if " + cond + " {");
		printBlockContents(op.trueBranch, indent, context, lines);
		lines.push(indent + "} else {");
		printBlockContents(op.falseBranch, indent, context, lines);
		lines.push(indent + "}");
		// TODO: Format destinations?
		return;
	} else if (op.tag === "op-return") {
		lines.push(indent + "return " + op.sources.join(", ") + ";");
		return;
	} else if (op.tag === "op-const") {
		const lhs = "var " + op.destination.variable;
		lines.push(indent + lhs + " = " + op.value + ";");
		return;
	} else if (op.tag === "op-foreign") {
		const lhs = op.destinations.map(x => "var " + x).join(", ");
		const rhs = op.operation + "(" + op.arguments.join(", ") + ");";
		lines.push(indent + lhs + " = " + rhs);
		return;
	} else if (op.tag === "op-unreachable") {
		lines.push(indent + "unreachable; // " + op.diagnostic_kind);
		return;
	} else if (op.tag === "op-static-call") {
		const targs = op.type_arguments.map(x => showType(x, context));
		const lhs = op.destinations.map(x => "var " + x.variable).join(", ");
		const rhs = op.function + "[" + targs.join(", ") + "](" + op.arguments.join(", ") + ");";
		lines.push(indent + lhs + " = " + rhs);
		return;
	} else if (op.tag === "op-proof") {
		lines.push(indent + "proof {");
		printBlockContents(op.body, indent, context, lines);
		lines.push("}");
		return;
	} else if (op.tag === "op-dynamic-call") {
		const f = op.constraint + "." + op.signature_id;
		const targs = op.signature_type_arguments.map(x => showType(x, context));
		const lhs = op.destinations.map(x => "var " + x.variable).join(", ");
		const rhs = f + "[" + targs.join(", ") + "](" + op.arguments.join(", ") + ")";
		lines.push(indent + lhs + " = " + rhs + ";");
		return;
	} else if (op.tag === "op-field") {
		const lhs = "var " + op.destination.variable;
		const rhs = op.object + "." + op.field;
		lines.push(indent + lhs + " = " + rhs + ";");
		return;
	} else if (op.tag === "op-new-record") {
		const lhs = "var " + op.destination.variable;
		const args = [];
		for (let k in op.fields) {
			args.push(k + " = " + op.fields[k]);
		}
		const recordType = showType(op.destination.type, context);
		const recordLiteral = recordType + "{" + args.join(", ") + "}";
		lines.push(indent + lhs + " = " + recordLiteral + ";");
		return;
	}

	const _: never = op;
	lines.push(indent + "??? " + op["tag"] + " ???");
}
