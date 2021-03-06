import { assert } from "./test";
import * as IR from "./ir";
import type { Value } from "./interpreter"
import { interpret } from "./interpreter";

const T_INT: IR.Type = { tag: "type-primitive", primitive: "Int" } as const;
const T_BOOL: IR.Type = { tag: "type-primitive", primitive: "Boolean" } as const;

export type SOp = ["block", SOp[]]
	| ["local", IR.Type, string | undefined]
	| ["if", number, SOp[], SOp[]]
	| ["bool", number, boolean]
	| ["int", number, number]
	| ["foreign", { f: string, dst: number[], arg: number[] }]
	| ["return", number[]]
	| ["call", { f: string, dst: number[], arg: number[], ts: IR.Type[] }]
	| ["dyncall", { i: string, it: IR.Type[], f: number, dst: number[], arg: number[], ts: IR.Type[] }];


export function classType(name: string, ...args: IR.Type[]): IR.Type {
	return {
		tag: "type-class",
		class: { class_id: name },
		type_arguments: args,
	};
}

export function variableType(n: number): IR.TypeVariable {
	return {
		tag: "type-variable",
		id: { type_variable_id: n },
	};
}

export function op(...args: SOp): IR.Op {
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
			operation: args[1].f,
			destinations: args[1].dst.map(x => ({ variable_id: x })),
			arguments: args[1].arg.map(x => ({ variable_id: x })),
		};
	} else if (args[0] === "return") {
		return {
			tag: "op-return",
			sources: args[1].map(x => ({ variable_id: x })),
		};
	} else if (args[0] === "call") {
		return {
			tag: "op-static-call",
			function: { function_id: args[1].f },
			destinations: args[1].dst.map(x => ({ variable_id: x })),
			arguments: args[1].arg.map(x => ({ variable_id: x })),
			type_arguments: args[1].ts,
		};
	} else if (args[0] === "dyncall") {
		return {
			tag: "op-dynamic-call",
			interface: { interface_id: args[1].i },
			interface_arguments: args[1].it,
			signature_id: args[1].f,
			signature_type_arguments: args[1].ts,
			destinations: args[1].dst.map(x => ({ variable_id: x })),
			arguments: args[1].arg.map(x => ({ variable_id: x })),
		};
	} else {
		throw new Error("unhandled args: `" + args + "`");
	}
}

const foreign: Record<string, IR.FunctionSignature> = {
	"int=": {
		// Equality
		parameters: [T_INT, T_INT],
		return_types: [T_BOOL],
		type_parameters: [],
		constraint_parameters: [],
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
		constraint_parameters: [],
		preconditions: [],
		postconditions: [],
	},
	"int-": {
		// Addition
		parameters: [T_INT, T_INT],
		return_types: [T_INT],
		type_parameters: [],
		constraint_parameters: [],
		preconditions: [],
		postconditions: [],
	},
};

// Tests for interpreter.ts.
export const tests = {
	"basic-arithmetic"() {
		const program: IR.Program = {
			globalVTableFactories: {},
			classes: {},
			interfaces: {},
			functions: {
				"main": {
					// fib5: () -> Int
					signature: {
						parameters: [],
						return_types: [T_INT],
						type_parameters: [],
						constraint_parameters: [],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "n: #0"],
						["int", 0, 5],
						["call", { f: "fib", dst: [0], arg: [0], ts: [] }],
						["return", [0]],
					]),
				},
				"fib": {
					signature: {
						parameters: [T_INT],
						return_types: [T_INT],
						type_parameters: [],
						constraint_parameters: [],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "zero: #1"],
						["int", 1, 0],
						["local", T_BOOL, "arg == 0: #2"],
						["foreign", { f: "int=", dst: [2], arg: [0, 1] }],
						["local", T_INT, "1: #3"],
						["int", 3, 1],
						["if", 2,
							[["return", [3]]],
							[
								["foreign", { f: "int=", dst: [2], arg: [0, 3] }],
								["if", 2,
									[["return", [3]]],
									[
										["local", T_INT, "arg - 1: #4"],
										["local", T_INT, "arg - 2: #5"],
										["local", T_INT, "2: #6"],
										["int", 6, 2],
										["foreign", { f: "int-", dst: [4], arg: [0, 3] }],
										["foreign", { f: "int-", dst: [5], arg: [0, 6] }],
										["call", { f: "fib", dst: [4], arg: [4], ts: [] }],
										["call", { f: "fib", dst: [5], arg: [5], ts: [] }],
										["foreign", { f: "int+", dst: [4], arg: [4, 5] }],
										["return", [4]],
									],
								],
							],
						],
					]),
				},
			},
			foreign: foreign,
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
		assert(returned.sort, "is equal to", "int" as const);
		assert(returned.int, "is equal to", 8);
	},
	"dynamic-dispatch-from-global-vtable-factory"() {
		const program: IR.Program = {
			globalVTableFactories: {
				"FortyTwoIsFavorite": {
					interface: { interface_id: "Favorite" },
					interface_arguments: [classType("FortyTwo")],
					for_any: [],
					implementations: [
						{
							implementation: { "function_id": "fortyTwo" },
							constraint_parameters: [],
						}
					],
				},
			},
			functions: {
				"fortyTwo": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "fortytwo: #0"],
						["int", 0, 42],
						["return", [0]],
					]),
				},
				"main": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],

					},
					body: op("block", [
						["local", T_INT, "favorite: #0"],
						// Invoke op-dynamic-call.
						// No constraints are passed in this invocation.
						["dyncall", { i: "Favorite", it: [classType("FortyTwo")], f: 0, arg: [], dst: [0], ts: [] }],
						["return", [0]],
					]),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This"],
					signatures: [
						{
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [T_INT],
							preconditions: [],
							postconditions: [],
						},
					]
				},
			},
			classes: {
				"FortyTwo": {
					parameters: [],
					fields: {},
				},
			},
			foreign: {},
		};

		const [returned] = interpret("main", program, {});
		assert(returned, "is equal to", {
			sort: "int",
			int: 42,
		});
	},
	"dynamic-dispatch-from-type-parameter"() {
		const program: IR.Program = {
			globalVTableFactories: {
				"ThirteenIsFavorite": {
					interface: { interface_id: "Favorite" },
					interface_arguments: [classType("Thirteen")],
					for_any: [],
					implementations: [
						{
							implementation: { "function_id": "thirteen" },
							constraint_parameters: [],
						},
					],
				},
			},
			functions: {
				"thirteen": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "thirteen: #0"],
						["int", 0, 13],
						["return", [0]],
					]),
				},
				"favoriteOf": {
					signature: {
						// Takes one type parameter, which can have a favorite
						// extracted.
						// The Favorite v-table will be a runtime argument to
						// this function.
						type_parameters: ["#T"],
						constraint_parameters: [
							{
								interface: { interface_id: "Favorite" },
								interface_arguments: [variableType(0)],
							}
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "favorite: #0"],
						[
							"dyncall", {
								i: "Favorite", it: [variableType(0)],
								f: 0, arg: [], dst: [0], ts: []
							},
						],
						["return", [0]],
					]),
				},
				"main": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],

					},
					body: op("block", [
						["local", T_INT, "favorite: #0"],
						// No constraints are passed in this invocation.
						["call", { f: "favoriteOf", dst: [0], arg: [], ts: [classType("Thirteen")] }],
						["return", [0]],
					]),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This"],
					signatures: [
						{
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [T_INT],
							preconditions: [],
							postconditions: [],
						},
					]
				},
			},
			classes: {
				"Thirteen": {
					parameters: [],
					fields: {},
				},
			},
			foreign: {},
		};

		const [returned] = interpret("main", program, {});
		assert(returned, "is equal to", {
			sort: "int",
			int: 13,
		});
	},
	"dynamic-dispatch-from-type-constraint-closure"() {
		const program: IR.Program = {
			globalVTableFactories: {
				"SevenIsFavorite": {
					interface: { interface_id: "Favorite" },
					interface_arguments: [classType("Seven")],
					for_any: [],
					implementations: [
						{
							implementation: { "function_id": "seven" },
							constraint_parameters: [],
						},
					],
				},
				"SquarerIsFavorite": {
					interface: { interface_id: "Favorite" },
					interface_arguments: [classType("Squarer", variableType(0))],
					for_any: [variableType(0)],
					implementations: [
						{
							implementation: { function_id: "squareFavorite" },
							constraint_parameters: [
								{
									interface: { interface_id: "Favorite" },
									interface_arguments: [variableType(0)]
								},
							],
						},
					],
				},
			},
			functions: {
				"squareFavorite": {
					signature: {
						type_parameters: ["#F"],
						constraint_parameters: [
							{
								interface: { interface_id: "Favorite" },
								interface_arguments: [variableType(0)],
							}
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "fav: #0"],
						[
							"dyncall",
							{
								i: "Favorite", it: [variableType(0)],
								f: 0, dst: [0], arg: [], ts: []
							},
						],
						["foreign", { f: "int*", dst: [0], arg: [0, 0] }],
						["return", [0]],
					]),
				},
				"seven": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "seven: #0"],
						["int", 0, 7],
						["return", [0]],
					]),
				},
				"favoriteOf": {
					signature: {
						// Takes one type parameter, which can have a favorite
						// extracted.
						// The Favorite v-table will be a runtime argument to
						// this function.
						type_parameters: ["#T"],
						constraint_parameters: [
							{
								interface: { interface_id: "Favorite" },
								interface_arguments: [variableType(0)],
							},
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "favorite: #0"],
						[
							"dyncall",
							{
								i: "Favorite", it: [variableType(0)],
								f: 0, arg: [], dst: [0], ts: []
							},
						],
						["return", [0]],
					]),
				},
				"main": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: op("block", [
						["local", T_INT, "favorite: #0"],
						// No constraints are passed in this invocation.
						["call", { f: "favoriteOf", dst: [0], arg: [], ts: [classType("Squarer", classType("Seven"))] }],
						["return", [0]],
					]),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This"],
					signatures: [
						{
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [T_INT],
							preconditions: [],
							postconditions: [],
						},
					]
				},
			},
			classes: {
				"Seven": {
					parameters: [],
					fields: {},
				},
				"FavoriteSquarer": {
					parameters: ["#X"],
					fields: {},
				},
			},
			foreign: foreign,
		};

		const [returned] = interpret("main", program, {
			"int*": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int * b.int }];
			},
		});
		assert(returned, "is equal to", {
			sort: "int",
			int: 49,
		});
	},
};
