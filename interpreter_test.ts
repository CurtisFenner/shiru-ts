
import { assert } from "./test";
import * as IR from "./ir";
import type { IntValue, Value } from "./interpreter"
import { interpret } from "./interpreter";

const T_INT: IR.Type = { tag: "type-primitive", primitive: "Int" } as const;
const T_BOOL: IR.Type = { tag: "type-primitive", primitive: "Boolean" } as const;

type SOp = ["block", SOp[]]
	| ["local", IR.Type, string | undefined]
	| ["if", number, SOp[], SOp[]]
	| ["bool", number, boolean]
	| ["int", number, number]
	| ["foreign", string, number[], number[]]
	| ["return", number[]]
	| ["call", string, number[], number[], IR.Type[]];

function op(...args: SOp): IR.Op {
	if (args[0] === "local") {
		return {
			tag: "op-var",
			type: args[1],
			debug_name: args[2],
		};
	} else if (args[0] === "if") {
		return {
			tag: "op-branch",
			condition: { variable_id: args[1] },
			trueBranch: op("block", args[2]) as IR.OpBlock,
			falseBranch: op("block", args[3]) as IR.OpBlock,
		};
	} else if (args[0] === "block") {
		return {
			tag: "op-block",
			ops: args[1].map(x => op(...x)),
		};
	} else if (args[0] === "bool") {
		return {
			tag: "op-const",
			destination: { variable_id: args[1] },
			value: args[2],
		};
	} else if (args[0] === "int") {
		return {
			tag: "op-const",
			destination: { variable_id: args[1] },
			value: args[2],
		};
	} else if (args[0] === "foreign") {
		return {
			tag: "op-foreign",
			operation: args[1],
			destinations: args[2].map(x => ({ variable_id: x })),
			arguments: args[3].map(x => ({ variable_id: x })),
		};
	} else if (args[0] === "return") {
		return {
			tag: "op-return",
			sources: args[1].map(x => ({ variable_id: x })),
		};
	} else if (args[0] === "call") {
		return {
			tag: "op-static-call",
			function: { function_id: args[1] },
			destinations: args[2].map(x => ({ variable_id: x })),
			arguments: args[3].map(x => ({ variable_id: x })),
			type_arguments: args[4],
		};
	} else {
		throw new Error("unhandled args: `" + args + "`");
	}
}

// Tests for interpreter.ts.
export const tests = {
	"basic-arithmetic"() {
		const program: IR.Program = {
			classes: {},
			interfaces: {},
			functions: {
				"main": {
					// fib5: () -> Int
					signature: {
						parameters: [],
						return_types: [T_INT],
						type_parameters: [],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "n: #0"],
						["int", 0, 5],
						["call", "fib", [0], [0], []],
						["return", [0]],
					]),
				},
				"fib": {
					signature: {
						parameters: [T_INT],
						return_types: [T_INT],
						type_parameters: [],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "zero: #1"],
						["int", 1, 0],
						["local", T_BOOL, "arg == 0: #2"],
						["foreign", "int=", [2], [0, 1]],
						["local", T_INT, "1: #3"],
						["int", 3, 1],
						["if", 2,
							[["return", [3]]],
							[
								["foreign", "int=", [2], [0, 3]],
								["if", 2,
									[["return", [3]]],
									[
										["local", T_INT, "arg - 1: #4"],
										["local", T_INT, "arg - 2: #5"],
										["local", T_INT, "2: #6"],
										["int", 6, 2],
										["foreign", "int-", [4], [0, 3]],
										["foreign", "int-", [5], [0, 6]],
										["call", "fib", [4], [4], []],
										["call", "fib", [5], [5], []],
										["foreign", "int+", [4], [4, 5]],
										["return", [4]],
									],
								],
							],
						],
					]),
				},
			},
			foreign: {
				"int=": {
					// Equality
					parameters: [T_INT, T_INT],
					return_types: [T_BOOL],
					type_parameters: [],
					preconditions: [],
					postconditions: [
						{
							tag: "op-eq",
							left: { variable_id: 0 },
							right: { variable_id: 1 },
							destination: { variable_id: 2 },
						}
					],
				},
				"int+": {
					// Addition
					parameters: [T_INT, T_INT],
					return_types: [T_INT],
					type_parameters: [],
					preconditions: [],
					postconditions: [],
				},
				"int-": {
					// Addition
					parameters: [T_INT, T_INT],
					return_types: [T_INT],
					type_parameters: [],
					preconditions: [],
					postconditions: [],
				},
			},
		};

		const [returned] = interpret("main", program, {
			"int+": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int + b.int }];
			},
			"int-": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int - b.int }];
			},
			"int=": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "boolean", boolean: a.int == b.int }];
			},
		});
		assert(returned.sort, "is equal to", "int");
		assert((returned as IntValue).int, "is equal to", 8);
	},
};
