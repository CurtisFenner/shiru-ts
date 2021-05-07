import { assert } from "./test";
import * as ir from "./ir";
import type { Value } from "./interpreter"
import { interpret } from "./interpreter";
import * as grammar from "./grammar";
import * as semantics from "./semantics";

const T_INT: ir.Type = ir.T_INT;
const T_BOOL: ir.Type = ir.T_BOOLEAN;

export const UNKNOWN_LOCATION: ir.SourceLocation = { fileID: "unknown", offset: 0, length: 0 };

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
		id: { variable_id: name },
		sourceLocation: UNKNOWN_LOCATION,
	};
}

export function opBlock(...ops: ir.Op[]): ir.OpBlock {
	return {
		ops,
	};
}

export function opBranch(condition: string, trueBranch: ir.OpBlock, falseBranch: ir.OpBlock): ir.OpBranch {
	return {
		tag: "op-branch",
		condition: { variable_id: condition },
		trueBranch,
		falseBranch,
	};
}

export function opConst(destination: string, value: number | boolean): ir.OpConst {
	return {
		tag: "op-const",
		destination: { variable_id: destination },
		value,
	};
}

export function opForeign({ dst, args, f }: { dst: string[], args: string[], f: string }): ir.OpForeign {
	return {
		tag: "op-foreign",
		operation: f,
		destinations: dst.map(x => ({ variable_id: x })),
		arguments: args.map(x => ({ variable_id: x })),
	};
}

export function opReturn(...srcs: string[]): ir.OpReturn {
	return {
		tag: "op-return",
		sources: srcs.map(x => ({ variable_id: x })),
		diagnostic_return_site: UNKNOWN_LOCATION,
	};
}

export function opStaticCall({ f, dst, args, ts }: { f: string, dst: string[], args: string[], ts: ir.Type[] }): ir.OpStaticCall {
	return {
		tag: "op-static-call",
		function: { function_id: f },
		destinations: dst.map(x => ({ variable_id: x })),
		arguments: args.map(x => ({ variable_id: x })),
		type_arguments: ts,
		diagnostic_callsite: UNKNOWN_LOCATION,
	};
}

export function opDynamicCall({ i, its, f, ts, dst, args }: { i: string, its: ir.Type[], f: string, ts: ir.Type[], dst: string[], args: string[] }): ir.OpDynamicCall {
	return {
		tag: "op-dynamic-call",
		constraint: { interface_id: i },
		subjects: its,
		signature_id: f,
		signature_type_arguments: ts,
		destinations: dst.map(x => ({ variable_id: x })),
		arguments: args.map(x => ({ variable_id: x })),
		diagnostic_callsite: UNKNOWN_LOCATION,
	};
}

const foreign: Record<string, ir.FunctionSignature> = {
	"Int==": {
		// Equality
		parameters: [
			{ id: { variable_id: "left" }, type: ir.T_INT },
			{ id: { variable_id: "right" }, type: ir.T_INT },
		],
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
		parameters: [
			{ id: { variable_id: "left" }, type: ir.T_INT },
			{ id: { variable_id: "right" }, type: ir.T_INT },
		],
		return_types: [T_INT],
		type_parameters: [],
		constraint_parameters: [],
		preconditions: [],
		postconditions: [],
	},
	"Int-": {
		// Addition
		parameters: [
			{ id: { variable_id: "left" }, type: ir.T_INT },
			{ id: { variable_id: "right" }, type: ir.T_INT },
		],
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
						opVar(T_INT, "n"),
						opConst("n", 5),
						opStaticCall({ f: "fib", dst: ["n"], args: ["n"], ts: [] }),
						opReturn("n"),
					),
				},
				"fib": {
					signature: {
						parameters: [{ id: { variable_id: "k" }, type: T_INT }],
						return_types: [T_INT],
						type_parameters: [],
						constraint_parameters: [],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opVar(T_INT, "zero"),
						opConst("zero", 0),
						opVar(T_BOOL, "e"),
						opForeign({ f: "Int==", dst: ["e"], args: ["k", "zero"] }),
						opVar(T_INT, "one"),
						opConst("one", 1),
						opBranch("e",
							opBlock(
								opReturn("one"),
							),
							opBlock(
								opForeign({ f: "Int==", dst: ["e"], args: ["k", "one"] }),
								opBranch("e",
									opBlock(
										opReturn("one"),
									),
									opBlock(
										opVar(T_INT, "k1"),
										opVar(T_INT, "k2"),
										opForeign({ f: "Int-", dst: ["k1"], args: ["k", "one"] }),
										opForeign({ f: "Int-", dst: ["k2"], args: ["k1", "one"] }),
										opStaticCall({ f: "fib", dst: ["k1"], args: ["k1"], ts: [] }),
										opStaticCall({ f: "fib", dst: ["k2"], args: ["k2"], ts: [] }),
										opForeign({ f: "Int+", dst: ["k1"], args: ["k1", "k2"] }),
										opReturn("k1"),
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
					entries: {
						"get": {
							implementation: { function_id: "fortyTwo" },
							constraint_parameters: [],
						}
					},
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
						opVar(T_INT, "fortytwo"),
						opConst("fortytwo", 42),
						opReturn("fortytwo"),
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
						opVar(T_INT, "favorite"),
						// Invoke op-dynamic-call.
						// No constraints are passed in this invocation.
						opDynamicCall({ i: "Favorite", its: [classType("FortyTwo")], f: "get", args: [], dst: ["favorite"], ts: [] }),
						opReturn("favorite"),
					),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This"],
					signatures: {
						"get": {
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [T_INT],
							preconditions: [],
							postconditions: [],
						},
					},
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
					entries: {
						"get": {
							implementation: { "function_id": "thirteen" },
							constraint_parameters: [],
						},
					},
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
						opVar(T_INT, "thirteen"),
						opConst("thirteen", 13),
						opReturn("thirteen"),
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
								interface: { interface_id: "Favorite" },
								subjects: [variableType(0)],
							}
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opVar(T_INT, "favorite"),
						opDynamicCall({
							i: "Favorite", its: [variableType(0)],
							f: "get", args: [], dst: ["favorite"], ts: [],
						}),
						opReturn("favorite"),
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
						opVar(T_INT, "favorite"),
						// No constraints are passed in this invocation.
						opStaticCall({ f: "favoriteOf", dst: ["favorite"], args: [], ts: [classType("Thirteen")] }),
						opReturn("favorite"),
					),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This"],
					signatures: {
						"get": {
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [T_INT],
							preconditions: [],
							postconditions: [],
						},
					},
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
					entries: {
						"get": {
							implementation: { "function_id": "seven" },
							constraint_parameters: [],
						},
					},
				},
				"SquarerIsFavorite": {
					interface: { interface_id: "Favorite" },
					subjects: [classType("Squarer", variableType(0))],
					for_any: [variableType(0)],
					entries: {
						"get": {
							implementation: { function_id: "squareFavorite" },
							constraint_parameters: [
								{
									interface: { interface_id: "Favorite" },
									subjects: [variableType(0)]
								},
							],
						},
					},
				},
			},
			functions: {
				"squareFavorite": {
					signature: {
						type_parameters: ["#F"],
						constraint_parameters: [
							{
								interface: { interface_id: "Favorite" },
								subjects: [variableType(0)],
							}
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opVar(T_INT, "fav"),
						opDynamicCall({
							i: "Favorite", its: [variableType(0)],
							f: "get", dst: ["fav"], args: [], ts: [],
						}),
						opForeign({ f: "int*", dst: ["fav"], args: ["fav", "fav"] }),
						opReturn("fav"),
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
						opVar(T_INT, "seven"),
						opConst("seven", 7),
						opReturn("seven"),
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
								interface: { interface_id: "Favorite" },
								subjects: [variableType(0)],
							},
						],
						parameters: [],
						return_types: [T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opVar(T_INT, "favorite"),
						opDynamicCall({
							i: "Favorite", its: [variableType(0)],
							f: "get", args: [], dst: ["favorite"], ts: [],
						}),
						opReturn("favorite"),
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
						opVar(T_INT, "favorite"),
						// No constraints are passed in this invocation.
						opStaticCall({
							f: "favoriteOf", dst: ["favorite"], args: [], ts: [classType("Squarer", classType("Seven"))],
						}),
						opReturn("favorite"),
					),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This"],
					signatures: {
						"get": {
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [T_INT],
							preconditions: [],
							postconditions: [],
						},
					},
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
		const ast = grammar.parseSource(text, "test-file");
		const program = semantics.compileSources({ ast });
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
	"construct-record-literal"() {
		const source = `
		package example;

		record V {
			var x: Int;
			var y: Int;

			fn make(x: Int, y: Int): V {
				return V{
					x = x,
					y = y,
				};
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });

		const inputs: Value[] = [
			{ sort: "int", int: 13 },
			{ sort: "int", int: 17 },
		];
		const result = interpret("example.V.make", inputs, program, {});
		assert(result, "is equal to", [
			{
				sort: "record",
				fields: {
					x: { sort: "int", int: 13 },
					y: { sort: "int", int: 17 },
				},
			}
		]);
	},
	"access-fields-of-record"() {
		const source = `
		package example;

		record V {
			var x: Int;
			var y: Int;

			fn unmake(v: V): Int, Int {
				return v.x, v.y;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const inputs: Value[] = [
			{
				sort: "record",
				fields: {
					x: { sort: "int", int: 13 },
					y: { sort: "int", int: 17 },
				},
			},
		];
		const result = interpret("example.V.unmake", inputs, program, {});
		assert(result, "is equal to", [
			{ sort: "int", int: 13 },
			{ sort: "int", int: 17 },
		]);
	},
};
