import * as ir from "./ir";
import { ErrorElement } from "./lexer";

export type Value = RecordValue | EnumValue | BooleanValue | BytesValue | IntValue;

export type RecordValue = {
	sort: "record",
	fields: Record<string, Value>,
};

export type EnumValue = {
	sort: "enum",
	field: Record<string, Value>,
}

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
	int: bigint,
};

interface VTable {
	tag: "dictionary",
	entries: Record<string, VTableEntry>,
}

interface VTableEntry {
	implementation: ir.FunctionID,
	closureConstraints: VTable[],
}

interface ConstraintsContext {
	// search:
	global: Map<ir.InterfaceID, Record<string, ir.VTableFactory>>,

	local: Map<ir.InterfaceID, {
		// runtime:
		vtable: VTable,
		// search:
		provides: ir.ConstraintParameter,
	}[]>,
}

// N.B.: Only uses "runtime" fields.
type VTableProducer = (c: ConstraintsContext, callsite: VTable[]) => VTable;

/// `makeVTableProducer` scans the "search" fields of the context, and produces
/// a `VTableProducer` that only consumes the "runtime" fields of the context.j
/// The returned producer can thus be cached, avoiding the expensive search
/// process, for subsequent calls which have different runtime contexts but the
/// same search context.
function makeVTableProducer(
	// N.B.: Only uses "search" fields.
	context: ConstraintsContext,
	constraint: ir.ConstraintParameter,
): VTableProducer {
	const locals = context.local.get(constraint.interface);
	if (locals !== undefined) {
		for (let i = 0; i < locals.length; i++) {
			const ti = i;
			const local = locals[ti];
			const matched = matchTypes([], local.provides.subjects, constraint.subjects);
			if (matched !== null) {
				return (runtimeCtx, callsite) => {
					return runtimeCtx.local.get(constraint.interface)![ti].vtable;
				};
			}
		}
	}

	const globals = context.global.get(constraint.interface);
	if (globals !== undefined) {
		for (const k in globals) {
			const global = globals[k];
			const matched = matchTypes(global.for_any, global.provides.subjects, constraint.subjects);
			if (matched !== null) {
				const entrySchema: Record<string, {
					implementation: ir.FunctionID,
					closureConstraints: (number | VTableProducer)[],
				}> = {};
				for (const s in global.entries) {
					const entry = global.entries[s];
					entrySchema[s] = {
						implementation: entry.implementation,
						closureConstraints: entry.constraint_parameters.map(x => {
							if (typeof x === "number") {
								return x;
							}
							return makeVTableProducer(context, {
								interface: x.interface,
								subjects: x.subjects.map(t => ir.typeSubstitute(t, matched)),
							});
						}),
					};
				}

				return (runtimeCtx, callsite) => {
					const entries: Record<string, VTableEntry> = {};
					for (const s in entrySchema) {
						const schema = entrySchema[s];
						entries[s] = {
							implementation: schema.implementation,
							closureConstraints: schema.closureConstraints.map(x => {
								if (typeof x === "number") {
									return callsite[x];
								} else {
									return x(runtimeCtx, callsite);
								}
							}),
						};
					}

					return {
						tag: "dictionary",
						entries,
					};
				};
			}
		}
	}

	throw new Error("Could not find an implementation of `"
		+ JSON.stringify(constraint) + "`");
}

function matchTypeSingle(
	variables: Map<ir.TypeVariableID, ir.Type | null>,
	pattern: ir.Type,
	subject: ir.Type,
): boolean {
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
		if (pattern.base !== subject.base) {
			return false;
		}

		if (pattern.type_arguments.length !== subject.type_arguments.length) {
			throw new Error(`Arity of type \`${pattern.base}\` is inconsistent.`);
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
function matchTypes(
	forAny: ir.TypeVariableID[],
	pattern: ir.Type[],
	subject: ir.Type[],
): Map<ir.TypeVariableID, ir.Type> | null {
	if (pattern.length !== subject.length) {
		throw new Error("invalid");
	}

	let mapping: Map<ir.TypeVariableID, ir.Type | null> = new Map();
	for (let t of forAny) {
		mapping.set(t, null);
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

export type ForeignImpl = (args: Value[]) => Value[];

interface Context {
	program: ir.Program,
	foreign: Record<string, ForeignImpl>,
	constraintContext: ConstraintsContext,
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
	foreign: Record<string, ForeignImpl>,
): Value[] {
	const constraintContext: ConstraintsContext = {
		global: new Map(),
		local: new Map(),
	};
	for (const k in program.globalVTableFactories) {
		const factory = program.globalVTableFactories[k];

		let group = constraintContext.global.get(factory.provides.interface);
		if (group === undefined) {
			group = {};
			constraintContext.global.set(factory.provides.interface, group);
		}
		group[k] = factory;
	}

	const context: Context = {
		program,
		foreign,
		constraintContext,
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
function* interpretCall(
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
		constraintContext: {
			global: context.constraintContext.global,
			local: new Map(),
		},
	};
	for (let i = 0; i < vtables.length; i++) {
		const vtable = vtables[i];
		const constraint = fn.signature.constraint_parameters[i];
		let group = newContext.constraintContext.local.get(constraint.interface);
		if (group === undefined) {
			group = [];
			newContext.constraintContext.local.set(constraint.interface, group);
		}
		group.push({
			vtable,
			provides: constraint,
		});
	}

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
		if (op.type === "Boolean") {
			value = { sort: "boolean", boolean: op.boolean };
		} else if (op.type === "Int") {
			value = { sort: "int", int: BigInt(op.int) };
		} else if (op.type === "Bytes") {
			value = { sort: "bytes", bytes: op.bytes };
		} else {
			const _: never = op;
			throw new Error("interpretOp: unhandled op-const value");
		}
		frame.define(op.destination, value);
		return null;
	} else if (op.tag === "op-copy") {
		for (const copy of op.copies) {
			const sourceValue = frame.load(copy.source);
			frame.define(copy.destination, sourceValue);
		}
		return null;
	} else if (op.tag === "op-static-call") {
		const args = op.arguments.map(variable => frame.load(variable));

		const constraintArgs: VTable[] = [];
		const signature = context.program.functions[op.function].signature;
		const instantiation = ir.typeArgumentsMap(signature.type_parameters, op.type_arguments);
		for (let constraintTemplate of signature.constraint_parameters) {
			const subjects = constraintTemplate.subjects.map(t => ir.typeSubstitute(t, instantiation));
			const constraint: ir.ConstraintParameter = {
				interface: constraintTemplate.interface,
				subjects,
			}

			const vtableProducer = makeVTableProducer(context.constraintContext, constraint);
			const vtable = vtableProducer(context.constraintContext, []);
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
		const destinations = new Map<ir.VariableDefinition, Value>();
		const result = yield* interpretBlock(branch, frame, context, () => {
			for (const phi of op.destinations) {
				const source = condition ? phi.trueSource : phi.falseSource;
				if (source !== "undef") {
					destinations.set(phi.destination, frame.load(source.variable));
				}
			}
		});

		for (const [destination, value] of destinations) {
			frame.define(destination, value);
		}
		return result;
	} else if (op.tag === "op-dynamic-call") {
		const args = op.arguments.map(arg => frame.load(arg));
		const vtableProducer = makeVTableProducer(context.constraintContext, op.constraint);
		const int = context.program.interfaces[op.constraint.interface];
		const signature = int.signatures[op.signature_id];

		const interfaceMap = ir.typeArgumentsMap(int.type_parameters, op.constraint.subjects);
		const signatureMap = ir.typeArgumentsMap(signature.type_parameters, op.signature_type_arguments);
		const substitutionMap = new Map([...interfaceMap.entries(), ...signatureMap.entries()]);

		const callsite: VTable[] = [];
		for (const genericConstraint of signature.constraint_parameters) {
			const neededConstraint = ir.constraintSubstitute(genericConstraint, substitutionMap);
			const argumentProducer = makeVTableProducer(context.constraintContext, neededConstraint);
			const callsiteVTable = argumentProducer(context.constraintContext, []);
			callsite.push(callsiteVTable);
		}
		const vtable = vtableProducer(context.constraintContext, callsite);

		const spec = vtable.entries[op.signature_id];
		const constraintArgs = spec.closureConstraints;

		const result = yield* interpretCall(spec.implementation, args, constraintArgs, context);
		for (let i = 0; i < result.length; i++) {
			frame.define(op.destinations[i], result[i]);
		}
		return null;
	} else if (op.tag === "op-proof") {
		// Do nothing.
		return null;
	} else if (op.tag === "op-proof-eq") {
		throw new Error("unexpected op-proof-eq");
	} else if (op.tag === "op-proof-bounds") {
		throw new Error("unexpected op-proof-bounds");
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
	} else if (op.tag === "op-new-enum") {
		const enumValue: EnumValue = {
			sort: "enum",
			field: {},
		};
		enumValue.field[op.variant] = frame.load(op.variantValue);
		frame.define(op.destination, enumValue);
		return null;
	} else if (op.tag === "op-field") {
		const recordValue = frame.load(op.object);
		if (recordValue.sort !== "record") {
			throw new Error("bad value sort for field access");
		}
		frame.define(op.destination, recordValue.fields[op.field]);
		return null;
	} else if (op.tag === "op-variant") {
		const compoundValue = frame.load(op.object);
		if (compoundValue.sort !== "enum") {
			throw new Error("bad value sort for variant access");
		}
		const variant = compoundValue.field[op.variant];
		if (variant === undefined) {
			throw new RuntimeErr([
				"Retrieve uninitialized variant at",
				op.diagnostic_location || " (unknown location)",
			]);
		}
		frame.define(op.destination, variant);
		return null;
	} else if (op.tag === "op-unreachable") {
		throw new RuntimeErr([
			"Hit unreachable op at",
			op.diagnostic_location || " (unknown location)",
		]);
	} else if (op.tag === "op-is-variant") {
		const base = frame.load(op.base);
		if (base.sort !== "enum") {
			throw new Error("bad value sort for is-variant");
		}
		const contains = op.variant in base.field;
		frame.define(op.destination, { sort: "boolean", boolean: contains });
		return null;
	}

	const _: never = op;
	throw new Error("interpretOp: unhandled op tag `" + op["tag"] + "`");
}

export class RuntimeErr {
	constructor(public message: ErrorElement[]) { }
}

function showType(t: ir.Type): string {
	if (t.tag === "type-compound") {
		const generics = "[" + t.type_arguments.map(x => showType(x)).join(", ") + "]";
		return t.base + generics;
	} else if (t.tag === "type-primitive") {
		return t.primitive;
	} else if (t.tag === "type-variable") {
		return "#" + t.id;
	} else if (t.tag === "type-any") {
		return "Any";
	}

	const _: never = t;
	throw new Error("showType: unknown tag `" + t["tag"] + "`");
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
		parameters.push(parameter.variable + ": " + showType(parameter.type));
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
			+ post.returnedValues.map(printVariable).join(", ")
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

function printVariable(variable: ir.VariableDefinition) {
	return "var " + variable.variable + ": " + showType(variable.type);
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
		lines.push(indent + "}");
		for (const phi of op.destinations) {
			lines.push(indent + "\t" + phi.destination.variable + " := " + (phi.trueSource as any).variable);
		}
		lines.push(indent + "else {");
		printBlockContents(op.falseBranch, indent, context, lines);
		lines.push(indent + "}");
		for (const phi of op.destinations) {
			lines.push(indent + "\t" + phi.destination.variable + " := " + (phi.falseSource as any).variable);
		}
		// TODO: Format destinations?
		return;
	} else if (op.tag === "op-return") {
		lines.push(indent + "return " + op.sources.join(", ") + ";");
		return;
	} else if (op.tag === "op-const") {
		const lhs = printVariable(op.destination);
		if (op.type === "Int") {
			lines.push(indent + lhs + " = " + op.int + ";");
		} else if (op.type === "Boolean") {
			lines.push(indent + lhs + " = " + op.boolean + ";");
		} else if (op.type === "Bytes") {
			lines.push(indent + lhs + " = " + JSON.stringify(op.bytes) + ";");
		} else {
			const _: never = op;
			throw new Error("printOp: unrecognized const type");
		}
		return;
	} else if (op.tag === "op-copy") {
		const lhs = op.copies.map(x => printVariable(x.destination));
		const rhs = op.copies.map(x => x.source);
		lines.push(indent + lhs.join(", ") + " = " + rhs.join(", ") + ";");
		return;
	} else if (op.tag === "op-foreign") {
		const lhs = op.destinations.map(printVariable).join(", ");
		const rhs = op.operation + "(" + op.arguments.join(", ") + ");";
		lines.push(indent + lhs + " = " + rhs);
		return;
	} else if (op.tag === "op-unreachable") {
		lines.push(indent + "unreachable; // " + op.diagnostic_kind);
		return;
	} else if (op.tag === "op-static-call") {
		const targs = op.type_arguments.map(x => showType(x));
		const lhs = op.destinations.map(x => printVariable).join(", ");
		const rhs = op.function + "[" + targs.join(", ") + "](" + op.arguments.join(", ") + ");";
		lines.push(indent + lhs + " = " + rhs);
		return;
	} else if (op.tag === "op-proof") {
		lines.push(indent + "proof {");
		printBlockContents(op.body, indent, context, lines);
		lines.push(indent + "}");
		return;
	} else if (op.tag === "op-dynamic-call") {
		const f = op.constraint + "." + op.signature_id;
		const targs = op.signature_type_arguments.map(x => showType(x));
		const lhs = op.destinations.map(x => printVariable(x)).join(", ");
		const rhs = f + "[" + targs.join(", ") + "](" + op.arguments.join(", ") + ")";
		lines.push(indent + lhs + " = " + rhs + ";");
		return;
	} else if (op.tag === "op-field") {
		const lhs = printVariable(op.destination);
		const rhs = op.object + "." + op.field;
		lines.push(indent + lhs + " = " + rhs + ";");
		return;
	} else if (op.tag === "op-new-record") {
		const lhs = printVariable(op.destination);
		const args = [];
		for (let k in op.fields) {
			args.push(k + " = " + op.fields[k]);
		}
		const recordType = showType(op.destination.type);
		const recordLiteral = recordType + "{" + args.join(", ") + "}";
		lines.push(indent + lhs + " = " + recordLiteral + ";");
		return;
	} else if (op.tag === "op-new-enum") {
		const lhs = printVariable(op.destination);
		const enumType = showType(op.destination.type);
		const arg = op.variant + " = " + op.variantValue;
		const enumLiteral = enumType + "{" + arg + "}";
		lines.push(indent + lhs + " = " + enumLiteral + ";");
		return;
	} else if (op.tag === "op-is-variant") {
		const lhs = printVariable(op.destination);
		lines.push(indent + lhs + " = " + op.base + " is " + op.variant + ";");
		return;
	} else if (op.tag === "op-variant") {
		const lhs = printVariable(op.destination);
		lines.push(indent + lhs + " = " + op.object + "." + op.variant + ";");
		return;
	} else if (op.tag === "op-proof-eq") {
		const lhs = printVariable(op.destination);
		lines.push(indent + lhs + " = " + op.left + " proof== " + op.right + ";");
		return;
	} else if (op.tag === "op-proof-bounds") {
		const lhs = printVariable(op.destination);
		const rhs = op.larger + " proofbounds " + op.smaller;
		lines.push(indent + lhs + " = " + rhs + ";");
		return;
	}

	const _: never = op;
	lines.push(indent + "??? " + op["tag"] + " ???");
}
