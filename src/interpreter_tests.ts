import { assert } from "./test";
import * as ir from "./ir";
import type { Value } from "./interpreter"
import { interpret } from "./interpreter";
import { parseSource } from "./grammar";
import { compileSources } from "./semantics";

const T_INT: ir.Type = ir.T_INT;
const T_BOOL: ir.Type = ir.T_BOOLEAN;

export function classType(name: string, ...args: ir.Type[]): ir.Type {
	return {
		tag: "type-compound",
		record: { record_id: name },
		type_arguments: args,
	};
}

export function variableType(n: number): ir.TypeVariable {
	return {
		tag: "type-variable",
		id: { type_variable_id: n },
	};
}

export function opVar(t: ir.Type, name: string): ir.OpVar {
	return {
		tag: "op-var",
		type: t,
		debug_name: name,
	};
}

export function opBlock(...ops: ir.Op[]): ir.OpBlock {
	return {
		ops,
	};
}

export function opBranch(condition: number, trueBranch: ir.OpBlock, falseBranch: ir.OpBlock): ir.OpBranch {
	return {
		tag: "op-branch",
		condition: { variable_id: condition },
		trueBranch,
		falseBranch,
	};
}

export function opConst(destination: number, value: number | boolean): ir.OpConst {
	return {
		tag: "op-const",
		destination: { variable_id: destination },
		value,
	};
}

export function opForeign({ dst, args, f }: { dst: number[], args: number[], f: string }): ir.OpForeign {
	return {
		tag: "op-foreign",
		operation: f,
		destinations: dst.map(x => ({ variable_id: x })),
		arguments: args.map(x => ({ variable_id: x })),
	};
}

export function opReturn(...srcs: number[]): ir.OpReturn {
	return {
		tag: "op-return",
		sources: srcs.map(x => ({ variable_id: x })),
	};
}

export function opStaticCall({ f, dst, args, ts }: { f: string, dst: number[], args: number[], ts: ir.Type[] }): ir.OpStaticCall {
	return {
		tag: "op-static-call",
		function: { function_id: f },
		destinations: dst.map(x => ({ variable_id: x })),
		arguments: args.map(x => ({ variable_id: x })),
		type_arguments: ts,
		diagnostic_callsite: { fileID: "unknown", offset: 0, length: 0 },
	};
}

export function opDynamicCall({ i, its, f, ts, dst, args }: { i: string, its: ir.Type[], f: number, ts: ir.Type[], dst: number[], args: number[] }): ir.OpDynamicCall {
	return {
		tag: "op-dynamic-call",
		constraint: { interface_id: i },
		subjects: its,
		signature_id: f,
		signature_type_arguments: ts,
		destinations: dst.map(x => ({ variable_id: x })),
		arguments: args.map(x => ({ variable_id: x })),
	};
}

const foreign: Record<string, ir.FunctionSignature> = {
	"Int==": {
		// Equality
		parameters: [T_INT, T_INT],
		return_types: [T_BOOL],
		type_parameters: [],
		constraint_parameters: [],
		preconditions: [],
		postconditions: [],
		semantics: {
			eq: true,
		},
	},
	"Int+": {
		// Addition
		parameters: [T_INT, T_INT],
		return_types: [T_INT],
		type_parameters: [],
		constraint_parameters: [],
		preconditions: [],
		postconditions: [],
	},
	"Int-": {
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
		const program: ir.Program = {
			globalVTableFactories: {},
			records: {},
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
					body: opBlock(
						opVar(T_INT, "n: #0"),
						opConst(0, 5),
						opStaticCall({ f: "fib", dst: [0], args: [0], ts: [] }),
						opReturn(0),
					),
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
					body: opBlock(
						opVar(T_INT, "zero: #1"),
						opConst(1, 0),
						opVar(T_BOOL, "arg == 0: #2"),
						opForeign({ f: "Int==", dst: [2], args: [0, 1] }),
						opVar(T_INT, "1: #3"),
						opConst(3, 1),
						opBranch(2,
							opBlock(
								opReturn(3),
							),
							opBlock(
								opForeign({ f: "Int==", dst: [2], args: [0, 3] }),
								opBranch(2,
									opBlock(
										opReturn(3),
									),
									opBlock(
										opVar(T_INT, "arg - 1: #4"),
										opVar(T_INT, "arg - 2: #5"),
										opVar(T_INT, "2: #6"),
										opConst(6, 2),
										opForeign({ f: "Int-", dst: [4], args: [0, 3] }),
										opForeign({ f: "Int-", dst: [5], args: [0, 6] }),
										opStaticCall({ f: "fib", dst: [4], args: [4], ts: [] }),
										opStaticCall({ f: "fib", dst: [5], args: [5], ts: [] }),
										opForeign({ f: "Int+", dst: [4], args: [4, 5] }),
										opReturn(4),
									),
								),
							),
						),
					),
				},
			},
			foreign: foreign,
		};

		const [returned] = interpret("main", [], program, {
			"Int+": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int + b.int }];
			},
			"Int-": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int - b.int }];
			},
			"Int==": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "boolean", boolean: a.int == b.int }];
			},
		});
		assert(returned.sort, "is equal to", "int" as const);
		assert(returned.int, "is equal to", 8);
	},
	"dynamic-dispatch-from-global-vtable-factory"() {
		const program: ir.Program = {
			globalVTableFactories: {
				"FortyTwoIsFavorite": {
					interface: { interface_id: "Favorite" },
					subjects: [classType("FortyTwo")],
					for_any: [],
					entries: [
						{
							implementation: { function_id: "fortyTwo" },
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
					body: opBlock(
						opVar(T_INT, "fortytwo: #0"),
						opConst(0, 42),
						opReturn(0),
					),
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
					body: opBlock(
						opVar(T_INT, "favorite: #0"),
						// Invoke op-dynamic-call.
						// No constraints are passed in this invocation.
						opDynamicCall({ i: "Favorite", its: [classType("FortyTwo")], f: 0, args: [], dst: [0], ts: [] }),
						opReturn(0),
					),
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
			records: {
				"FortyTwo": {
					type_parameters: [],
					fields: {},
				},
			},
			foreign: {},
		};

		const [returned] = interpret("main", [], program, {});
		assert(returned, "is equal to", {
			sort: "int",
			int: 42,
		});
	},
	"dynamic-dispatch-from-type-parameter"() {
		const program: ir.Program = {
			globalVTableFactories: {
				"ThirteenIsFavorite": {
					interface: { interface_id: "Favorite" },
					subjects: [classType("Thirteen")],
					for_any: [],
					entries: [
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
					body: opBlock(
						opVar(T_INT, "thirteen: #0"),
						opConst(0, 13),
						opReturn(0),
					),
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
								constraint: { interface_id: "Favorite" },
								subjects: [variableType(0)],
							}
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opVar(T_INT, "favorite: #0"),
						opDynamicCall({
							i: "Favorite", its: [variableType(0)],
							f: 0, args: [], dst: [0], ts: [],
						}),
						opReturn(0),
					),
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
					body: opBlock(
						opVar(T_INT, "favorite: #0"),
						// No constraints are passed in this invocation.
						opStaticCall({ f: "favoriteOf", dst: [0], args: [], ts: [classType("Thirteen")] }),
						opReturn(0),
					),
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
			records: {
				"Thirteen": {
					type_parameters: [],
					fields: {},
				},
			},
			foreign: {},
		};

		const [returned] = interpret("main", [], program, {});
		assert(returned, "is equal to", {
			sort: "int",
			int: 13,
		});
	},
	"dynamic-dispatch-from-type-constraint-closure"() {
		const program: ir.Program = {
			globalVTableFactories: {
				"SevenIsFavorite": {
					interface: { interface_id: "Favorite" },
					subjects: [classType("Seven")],
					for_any: [],
					entries: [
						{
							implementation: { "function_id": "seven" },
							constraint_parameters: [],
						},
					],
				},
				"SquarerIsFavorite": {
					interface: { interface_id: "Favorite" },
					subjects: [classType("Squarer", variableType(0))],
					for_any: [variableType(0)],
					entries: [
						{
							implementation: { function_id: "squareFavorite" },
							constraint_parameters: [
								{
									constraint: { interface_id: "Favorite" },
									subjects: [variableType(0)]
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
								constraint: { interface_id: "Favorite" },
								subjects: [variableType(0)],
							}
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opVar(T_INT, "fav: #0"),
						opDynamicCall({
							i: "Favorite", its: [variableType(0)],
							f: 0, dst: [0], args: [], ts: [],
						}),
						opForeign({ f: "int*", dst: [0], args: [0, 0] }),
						opReturn(0),
					),
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
					body: opBlock(
						opVar(T_INT, "seven: #0"),
						opConst(0, 7),
						opReturn(0),
					),
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
								constraint: { interface_id: "Favorite" },
								subjects: [variableType(0)],
							},
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opVar(T_INT, "favorite: #0"),
						opDynamicCall({
							i: "Favorite", its: [variableType(0)],
							f: 0, args: [], dst: [0], ts: [],
						}),
						opReturn(0),
					),
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
					body: opBlock(
						opVar(T_INT, "favorite: #0"),
						// No constraints are passed in this invocation.
						opStaticCall({
							f: "favoriteOf", dst: [0], args: [], ts: [classType("Squarer", classType("Seven"))],
						}),
						opReturn(0),
					),
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
			records: {
				"Seven": {
					type_parameters: [],
					fields: {},
				},
				"FavoriteSquarer": {
					type_parameters: ["#X"],
					fields: {},
				},
			},
			foreign: foreign,
		};

		const [returned] = interpret("main", [], program, {
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
	"end-to-end"() {
		const text = `
		package example;
		record Main {
			fn lucas(n: Int): Int {
				if n == 0 {
					return 2;
				} else if n == 1 {
					return 1;
				}
				return Main.lucas(n - 1) + Main.lucas(n - 2);
			}

			fn main(): Int, Int, Int, Int, Int, Int, Int {
				return Main.lucas(1), Main.lucas(2), Main.lucas(3), Main.lucas(4), Main.lucas(5), Main.lucas(6), Main.lucas(7);
			}
		}`;
		const ast = parseSource(text, "test-file");
		const program = compileSources([ast]);
		const result = interpret("example.Main.main", [], program, {
			"Int+": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int + b.int }];
			},
			"Int-": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int - b.int }];
			},
			"Int==": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "boolean", boolean: a.int == b.int }];
			},
		});
		assert(result, "is equal to", [
			{ sort: "int", int: 1 },
			{ sort: "int", int: 3 },
			{ sort: "int", int: 4 },
			{ sort: "int", int: 7 },
			{ sort: "int", int: 11 },
			{ sort: "int", int: 18 },
			{ sort: "int", int: 29 },
		]);
	},
};
