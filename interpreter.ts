import * as IR from "./ir";

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

class VTable {
	interface(): IR.InterfaceID {
		throw new Error("TODO");
	}

	resolve(signature: number): IR.FunctionID {
		throw new Error("TODO");
	}
}

class StackFrame {
	function_id: string;
	variables: (Value | null)[];
	constraintArguments: VTable[];

	/// `scopes[i]` indicates the size of the `variables` stack at the moment
	/// the `i`th scope opened.
	scopes: number[];

	/// `ip` indicates the 'path' into the `op` of this function.
	/// For a block, a value `k` indicates index `k` into the `ops` array, or a
	/// "cleanup" instruction.
	/// For a branch, a value `THEN_INDEX` indicates the truthy branch and
	/// `FALSE_INDEX` indicates the falsy branch.
	ip: number[];

	constructor(function_id: string) {
		this.function_id = function_id;
		this.variables = [];
		this.constraintArguments = [];
		this.ip = [];
		this.scopes = [];
	}

	getVariable(variable: IR.VariableID): Value {
		const value = this.variables[variable.variable_id];
		if (value === null) {
			throw new Error("attempting to read undefined variable `" + variable.variable_id + "`");
		}
		return value;
	}

	setVariable(variable: IR.VariableID, value: Value) {
		this.variables[variable.variable_id] = value;
	}

	getVTable(constraint: IR.ConstraintParameter, implementer: IR.Type): VTable {
		throw new Error("TODO");
	}
}

export type ForeignImpl = (args: Value[]) => Value[];

/// Execute a Smol program until termination, returning the result from the 
/// given `entry` function.
export function interpret(entry: string, program: IR.Program, foreign: Record<string, ForeignImpl>): Value[] {
	if (!program.functions[entry]) {
		throw new Error("The program has no function named `" + entry + "`");
	} else if (program.functions[entry].signature.parameters.length !== 0) {
		throw new Error("Function `" + entry + "` cannot be used as an entry point because it expects arguments.");
	}

	const stack: StackFrame[] = [new StackFrame(entry)];
	while (true) {
		const result = interpretStep(program, stack, foreign);
		if (result) {
			return result;
		}
	}
}

const THEN_INDEX = 1;
const ELSE_INDEX = 2;

function interpretStep(program: IR.Program, stack: StackFrame[], foreign: Record<string, ForeignImpl>): undefined | Value[] {
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
	} else if (op.tag == "op-dynamic-call") {
		const f = frame.getVTable(op.constraint, op.constraint_implementer).resolve(op.signature_id);
		// TODO: May need constraint arguments from vtable to be passed to new frame.
		const newFrame = new StackFrame(f.function_id);
		for (let arg of op.arguments) {
			newFrame.variables.push(frame.getVariable(arg));
		}
		stack.push(newFrame);
	} else if (op.tag == "op-field") {
		const instance = frame.getVariable(op.object);
		if (instance.sort !== "class") {
			throw new Error("op-field requires instance of sort 'class'");
		}
		frame.setVariable(op.destination, instance.fields[op.field]);
		frame.ip[frame.ip.length - 1] += 1;
		return;
	} else if (op.tag == "op-new-class") {
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
	} else if (op.tag == "op-static-call") {
		const newFrame = new StackFrame(op.function.function_id);
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
			frame.variables[op.destination.variable_id] = {
				sort: "int",
				int: op.value as number,
			};
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
function getOp(base: IR.Op, ip: number[], from: number = 0): IR.Op | SyntheticCloseScope {
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
