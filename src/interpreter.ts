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
	interfaceID: ir.InterfaceID,
	interfaceArguments: ir.Type[],
	entries: VTableEntry[],
};

interface VTableEntry {
	implementation: ir.FunctionID,
	closureConstraints: VTable[],
};

/// Replace all occurrences of the specified type-variables in the constraint 
/// parameter.
function constraintSubstitute(c: ir.ConstraintParameter, map: Map<number, ir.Type>): ir.ConstraintParameter {
	const args = c.subjects.map(t => ir.typeSubstitute(t, map));
	return {
		constraint: c.constraint,
		subjects: args,
	};
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

class StackFrame {
	variables: (Value | null)[] = [];

	/// `scopes[i]` indicates the size of the `variables` stack at the moment
	/// the `i`th scope opened.
	scopes: number[] = [];

	/// `ip` indicates the 'path' into the `op` of this function.
	/// For a block, a value `k` indicates index `k` into the `ops` array, or a
	/// "cleanup" instruction.
	/// For a branch, a value `THEN_INDEX` indicates the truthy branch and
	/// `FALSE_INDEX` indicates the falsy branch.
	ip: number[] = [];

	constructor(
		private program: ir.Program,
		public function_id: string,
		public constraintArguments: VTable[]) {
	}

	resolveVTableFromConstraint(constraint: ir.ConstraintParameter): VTable {
		return this.resolveVTable(
			constraint.constraint,
			constraint.subjects);
	}

	resolveVTable(interfaceID: ir.InterfaceID, interfaceArguments: ir.Type[]): VTable {
		// Search in this stack frame for constraint parameters.
		for (let vtable of this.constraintArguments) {
			if (vtable.interfaceID.interface_id !== interfaceID.interface_id) {
				continue;
			}

			const instantiationMapping = matchTypes([], vtable.interfaceArguments, interfaceArguments);
			if (!instantiationMapping) {
				continue;
			}

			// Found a matching v-table!
			return vtable;
		}

		// Search in the list of global v-table factories.
		const availableVTables = Object.values(this.program.globalVTableFactories);
		for (let vtableFactory of availableVTables) {
			if (vtableFactory.interface.interface_id !== interfaceID.interface_id) {
				continue;
			}

			// Match v-table's arguments against the query.
			const instantiationMapping = matchTypes(vtableFactory.for_any, vtableFactory.interface_arguments, interfaceArguments);
			if (!instantiationMapping) {
				continue;
			}

			// Found a matching v-table in the global list of v-tables.
			// Substitute its types with the instantiation mapping.
			return {
				interfaceID: interfaceID,
				interfaceArguments: interfaceArguments,
				entries: vtableFactory.implementations.map(entry => {
					const mappedParameters = entry.constraint_parameters.map(c => {
						const resolved = this.resolveVTableFromConstraint(constraintSubstitute(c, instantiationMapping));

						return {
							interfaceID: resolved.interfaceID,
							// Use the form of the interface arguments that the callee expects.
							interfaceArguments: c.subjects,
							entries: resolved.entries,
						};
					});
					return {
						implementation: entry.implementation,
						closureConstraints: mappedParameters,
					};
				}),
			};
		}

		console.error("Failing call resolveVTable(", interfaceID, interfaceArguments, ")");
		throw new Error("No vtable found");
	}

	getVariable(variable: ir.VariableID): Value {
		const value = this.variables[variable.variable_id];
		if (value === null || value === undefined) {
			throw new Error("attempting to read undefined variable `" + variable.variable_id + "`");
		}
		return value;
	}

	setVariable(variable: ir.VariableID, value: Value) {
		const id = variable.variable_id;
		if (this.variables[id] === undefined) {
			throw new Error("attempting to write to undefined variable `" + id + "`");
		}
		this.variables[id] = value;
	}
}

export type ForeignImpl = (args: Value[]) => Value[];

/// Execute a Shiru program until termination, returning the result from the 
/// given `entry` function.
export function interpret(entry: string, program: ir.Program, foreign: Record<string, ForeignImpl>): Value[] {
	if (!program.functions[entry]) {
		throw new Error("The program has no function named `" + entry + "`");
	} else if (program.functions[entry].signature.parameters.length !== 0) {
		throw new Error("Function `" + entry + "` cannot be used as an entry point because it expects arguments.");
	}

	const stack: StackFrame[] = [new StackFrame(program, entry, [])];
	while (true) {
		const result = interpretStep(program, stack, foreign);
		if (result) {
			return result;
		}
	}
}

const THEN_INDEX = 1;
const ELSE_INDEX = 2;

function interpretStep(program: ir.Program, stack: StackFrame[], foreign: Record<string, ForeignImpl>): undefined | Value[] {
	const frame = stack[stack.length - 1];
	const func = program.functions[frame.function_id];
	const op = getOp(func.body, frame.ip);

	if (op.tag == "op-assign") {
		frame.setVariable(op.destination, frame.getVariable(op.source));
		frame.ip[frame.ip.length - 1] += 1;
		return;
	} else if (op.tag == "op-block") {
		if (op.ops.length === 0) {
			// No-op.
			frame.ip[frame.ip.length - 1] += 1;
			return;
		} else {
			frame.ip.push(0);
			return;
		}
	} else if (op.tag == "op-branch") {
		const condition = frame.getVariable(op.condition);
		frame.ip.push(isTruthy(condition) ? THEN_INDEX : ELSE_INDEX);
		return;
	} else if (op.tag == "op-field") {
		const instance = frame.getVariable(op.object);
		if (instance.sort !== "class") {
			throw new Error("op-field requires instance of sort 'class'");
		}
		frame.setVariable(op.destination, instance.fields[op.field]);
		frame.ip[frame.ip.length - 1] += 1;
		return;
	} else if (op.tag == "op-new-record") {
		let instance: ClassValue = {
			sort: "class",
			fields: {},
		};
		for (let field in op.fields) {
			instance.fields[field] = frame.getVariable(op.fields[field]);
		}
		frame.setVariable(op.destination, instance);
		frame.ip[frame.ip.length - 1] += 1;
		return;
	} else if (op.tag == "op-proof") {
		// Proof statements are a no-op at runtime.
		frame.ip[frame.ip.length - 1] += 1;
		return;
	} else if (op.tag == "op-return") {
		stack.pop();
		const lastFrame = stack[stack.length - 1];
		if (!lastFrame) {
			// The entry-point function is returning.
			return op.sources.map(v => frame.getVariable(v));
		} else {
			const callerFunc = program.functions[lastFrame.function_id];
			const call = getOp(callerFunc.body, lastFrame.ip);
			if (call.tag === "op-static-call") {
				for (let i = 0; i < call.destinations.length; i++) {
					lastFrame.setVariable(call.destinations[i], frame.getVariable(op.sources[i]));
				}
				lastFrame.ip[lastFrame.ip.length - 1] += 1;
			} else if (call.tag === "op-dynamic-call") {
				for (let i = 0; i < call.destinations.length; i++) {
					lastFrame.setVariable(call.destinations[i], frame.getVariable(op.sources[i]));
				}
				lastFrame.ip[lastFrame.ip.length - 1] += 1;
			} else {
				throw new Error("Invalid call state");
			}
			return;
		}
	} else if (op.tag == "op-dynamic-call") {
		const invoking = frame.resolveVTable(op.interface, op.interface_arguments);
		const vtableEntry = invoking.entries[op.signature_id];

		// N.B.: Though the interface may add additional type-parameters, it 
		// cannot actually  demand any constraint arguments,only the underlying
		// implementation can.
		const functionID = vtableEntry.implementation.function_id;
		const constraintArguments = vtableEntry.closureConstraints;
		const newFrame = new StackFrame(program, functionID, constraintArguments);
		for (let arg of op.arguments) {
			newFrame.variables.push(frame.getVariable(arg));
		}
		stack.push(newFrame);
		return;
	} else if (op.tag == "op-static-call") {
		const signature = program.functions[op.function.function_id].signature;
		const parameterMapping: Map<number, ir.Type> = new Map();
		for (let i = 0; i < op.type_arguments.length; i++) {
			parameterMapping.set(i, op.type_arguments[i]);
		}

		const constraintArguments: VTable[] = [];
		for (let constraintParameter of signature.constraint_parameters) {
			const interfaceElements = constraintParameter.subjects;

			const concreteInterfaceArguments = interfaceElements.map(u => ir.typeSubstitute(u, parameterMapping));
			const resolved = frame.resolveVTable(constraintParameter.constraint, concreteInterfaceArguments);

			// For the purpose of identification within the new stack-frame, the
			// interface-parameters should be in the original uninstantiated 
			// form.
			constraintArguments.push({
				interfaceID: constraintParameter.constraint,
				// This v-table must be identifiable within the local 
				// type-context of the called function.
				interfaceArguments: constraintParameter.subjects,
				// The identifications of these v-table entries can be 
				// instantiated, since they will be overridden elsewhere.
				entries: resolved.entries,
			});
		}

		const newFrame = new StackFrame(program, op.function.function_id, constraintArguments);
		for (let arg of op.arguments) {
			newFrame.variables.push(frame.getVariable(arg));
		}
		stack.push(newFrame);
		return;
	} else if (op.tag == "op-unreachable") {
		throw new Error("unreachable code was reached! This indicates a bug in the verifier.");
	} else if (op.tag == "op-var") {
		frame.variables.push(null);
		frame.ip[frame.ip.length - 1] += 1;
		return;
	} else if (op.tag === "op-const") {
		if (typeof op.value === "number") {
			frame.setVariable(op.destination, {
				sort: "int",
				int: op.value as number,
			});
		} else {
			throw new Error("unrecognized constant value `" + op.value + "`");
		}
		frame.ip[frame.ip.length - 1] += 1;
		return;
	} else if (op.tag === "op-foreign") {
		if (!foreign[op.operation]) {
			throw new Error("missing implementation for foreign operation `" + op.operation + "`");
		}
		const argumentValues = op.arguments.map(arg => frame.getVariable(arg));
		const results = foreign[op.operation](argumentValues);
		if (results.length !== op.destinations.length) {
			throw new Error("operation `" + op.operation + "` returned "
				+ results.length + " values but the instruction expected "
				+ op.destinations.length);
		}
		for (let i = 0; i < op.destinations.length; i++) {
			frame.setVariable(op.destinations[i], results[i]);
		}
		frame.ip[frame.ip.length - 1] += 1;
		return;
	}
	throw new Error(`TODO: ${op.tag}`);
}

function isTruthy(value: Value): boolean {
	if (value.sort !== "boolean") throw new Error("bad value sort for isTruthy `" + value.sort + "`");
	return value.boolean;
}

interface SyntheticCloseScope {
	tag: "synth-close-scope",
}

/// isLast: appended to for each visited element of ip, whether or not that
///         index can be incremented without leaving bounds.
function getOp(base: ir.Op | ir.OpBlock, ip: number[], from: number = 0): ir.Op | ir.OpBlock | SyntheticCloseScope {
	if (from >= ip.length) {
		return base;
	}
	const index = ip[from];
	if (base.tag == "op-block") {
		if (index === base.ops.length) {
			// Generate a synthetic "close block" operation.
			return { tag: "synth-close-scope" };
		} else {
			return getOp(base.ops[index], ip, from + 1);
		}
	} else if (base.tag == "op-branch") {
		if (index == ELSE_INDEX) {
			return getOp(base.falseBranch, ip, from + 1);
		} else if (index == THEN_INDEX) {
			return getOp(base.trueBranch, ip, from + 1);
		}
	}
	throw new Error(`cannot access ${index} in ${base.tag}`);
}
