import { assert } from "./test.js";
import * as ir from "./ir.js";
import type { Value } from "./interpreter.js"
import { interpret } from "./interpreter.js";
import * as grammar from "./grammar.js";
import * as semantics from "./semantics.js";

export const UNKNOWN_LOCATION: ir.SourceLocation = { fileID: "unknown", offset: 0, length: 0 };

export function typeCompound(name: string, ...args: ir.Type[]): ir.Type {
	return {
		tag: "type-compound",
		base: name as ir.RecordID,
		type_arguments: args,
	};
}

export function typeVariable(n: string): ir.TypeVariable {
	return {
		tag: "type-variable",
		id: n as ir.TypeVariableID,
	};
}

export function opBlock(...ops: ir.Op[]): ir.OpBlock {
	return {
		ops,
	};
}

export function opConst(destination: string, value: number | boolean): ir.OpConst {
	if (typeof value === "number") {
		return {
			tag: "op-const",
			destination: {
				variable: destination as ir.VariableID,
				type: typeof value === "number" ? ir.T_INT : ir.T_BOOLEAN,
				location: UNKNOWN_LOCATION,
			},
			type: "Int",
			int: value.toFixed(0),
		};
	} else {
		return {
			tag: "op-const",
			destination: {
				variable: destination as ir.VariableID,
				type: typeof value === "number" ? ir.T_INT : ir.T_BOOLEAN,
				location: UNKNOWN_LOCATION,
			},
			type: "Boolean",
			boolean: value,
		};
	}
}

export function opForeign({ dst, args, f }: { dst: [string, ir.Type][], args: string[], f: string }): ir.OpForeign {
	return {
		tag: "op-foreign",
		operation: f,
		destinations: dst.map(x => ({
			variable: x[0] as ir.VariableID,
			type: x[1],
			location: UNKNOWN_LOCATION,
		})),
		arguments: args as ir.VariableID[],
	};
}

export function opReturn(...srcs: string[]): ir.OpReturn {
	return {
		tag: "op-return",
		sources: srcs as ir.VariableID[],
		diagnostic_return_site: UNKNOWN_LOCATION,
	};
}

export function opStaticCall({ f, dst, args, ts }: { f: string, dst: [string, ir.Type][], args: string[], ts: ir.Type[] }): ir.OpStaticCall {
	return {
		tag: "op-static-call",
		function: f as ir.FunctionID,
		destinations: dst.map(x => ({
			variable: x[0] as ir.VariableID,
			type: x[1],
			location: UNKNOWN_LOCATION,
		})),
		arguments: args as ir.VariableID[],
		type_arguments: ts,
		diagnostic_callsite: UNKNOWN_LOCATION,
	};
}

export function opDynamicCall(
	{ i, its, f, ts, dst, args }: {
		i: string,
		its: ir.Type[],
		f: string,
		ts: ir.Type[],
		dst: [string, ir.Type][],
		args: string[]
	},
): ir.OpDynamicCall {
	return {
		tag: "op-dynamic-call",
		constraint: {
			interface: i as ir.InterfaceID,
			subjects: its,
		},
		signature_id: f,
		signature_type_arguments: ts,
		destinations: dst.map(x => ({
			variable: x[0] as ir.VariableID,
			type: x[1],
			location: UNKNOWN_LOCATION,
		})),
		arguments: args as ir.VariableID[],
		diagnostic_callsite: UNKNOWN_LOCATION,
	};
}

const foreign: Record<string, ir.FunctionSignature> = {
	"Int==": {
		// Equality
		parameters: [
			{
				variable: "left" as ir.VariableID,
				type: ir.T_INT,
				location: UNKNOWN_LOCATION,
			},
			{
				variable: "right" as ir.VariableID,
				type: ir.T_INT,
				location: UNKNOWN_LOCATION,
			},
		],
		return_types: [ir.T_BOOLEAN],
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
			{
				variable: "left" as ir.VariableID,
				type: ir.T_INT,
				location: UNKNOWN_LOCATION,
			},
			{
				variable: "right" as ir.VariableID,
				type: ir.T_INT,
				location: UNKNOWN_LOCATION,
			},
		],
		return_types: [ir.T_INT],
		type_parameters: [],
		constraint_parameters: [],
		preconditions: [],
		postconditions: [],
	},
	"Int-": {
		// Addition
		parameters: [
			{
				variable: "left" as ir.VariableID,
				type: ir.T_INT,
				location: UNKNOWN_LOCATION,
			},
			{
				variable: "right" as ir.VariableID,
				type: ir.T_INT,
				location: UNKNOWN_LOCATION,
			},
		],
		return_types: [ir.T_INT],
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
			enums: {},
			interfaces: {},
			functions: {
				"main": {
					// fib5: () -> Int
					signature: {
						parameters: [],
						return_types: [ir.T_INT],
						type_parameters: [],
						constraint_parameters: [],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opConst("n", 5),
						opStaticCall({ f: "fib", dst: [["n", ir.T_INT]], args: ["n"], ts: [] }),
						opReturn("n"),
					),
				},
				"fib": {
					signature: {
						parameters: [{
							variable: "k" as ir.VariableID,
							type: ir.T_INT,
							location: UNKNOWN_LOCATION,
						}],
						return_types: [ir.T_INT],
						type_parameters: [],
						constraint_parameters: [],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opConst("zero", 0),
						opForeign({ f: "Int==", dst: [["k_eq_zero", ir.T_BOOLEAN]], args: ["k", "zero"] }),
						opConst("one", 1),
						{
							tag: "op-branch",
							condition: "k_eq_zero" as ir.VariableID,
							trueBranch: opBlock(
								opReturn("one"),
							),
							falseBranch: opBlock(
								opForeign({ f: "Int==", dst: [["k_eq_one", ir.T_BOOLEAN]], args: ["k", "one"] }),
								{
									tag: "op-branch",
									condition: "k_eq_one" as ir.VariableID,
									trueBranch: opBlock(
										opReturn("one"),
									),
									falseBranch: opBlock(
										opForeign({ f: "Int-", dst: [["k1", ir.T_INT]], args: ["k", "one"] }),
										opForeign({ f: "Int-", dst: [["k2", ir.T_INT]], args: ["k1", "one"] }),
										opStaticCall({ f: "fib", dst: [["k1", ir.T_INT]], args: ["k1"], ts: [] }),
										opStaticCall({ f: "fib", dst: [["k2", ir.T_INT]], args: ["k2"], ts: [] }),
										opForeign({ f: "Int+", dst: [["k1", ir.T_INT]], args: ["k1", "k2"] }),
										opReturn("k1"),
									),
									destinations: [],
								},
							),
							destinations: [],
						},
					),
				},
			},
			foreign: foreign,
		};

		const [returned] = interpret("main" as ir.FunctionID, [], program, {
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
		assert(returned.int, "is equal to", BigInt(8));
	},
	"dynamic-dispatch-from-global-vtable-factory"() {
		const program: ir.Program = {
			globalVTableFactories: {
				"FortyTwoIsFavorite": {
					provides: {
						interface: "Favorite" as ir.InterfaceID,
						subjects: [typeCompound("FortyTwo")],
					},
					for_any: [],
					closures: [],
					entries: {
						"get": {
							implementation: "fortyTwo" as ir.FunctionID,
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
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opConst("fortytwo", 42),
						opReturn("fortytwo"),
					),
				},
				"main": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],

					},
					body: opBlock(
						// Invoke op-dynamic-call.
						// No constraints are passed in this invocation.
						opDynamicCall({
							i: "Favorite",
							its: [typeCompound("FortyTwo")],
							f: "get",
							ts: [],
							args: [],
							dst: [["favorite", ir.T_INT]],
						}),
						opReturn("favorite"),
					),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This" as ir.TypeVariableID],
					signatures: {
						"get": {
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [ir.T_INT],
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
			enums: {},
			foreign: {},
		};

		const [returned] = interpret("main" as ir.FunctionID, [], program, {});
		assert(returned, "is equal to", {
			sort: "int",
			int: BigInt(42),
		});
	},
	"dynamic-dispatch-from-type-parameter"() {
		const program: ir.Program = {
			globalVTableFactories: {
				"ThirteenIsFavorite": {
					provides: {
						interface: "Favorite" as ir.InterfaceID,
						subjects: [typeCompound("Thirteen")],
					},
					for_any: [],
					closures: [],
					entries: {
						"get": {
							implementation: "thirteen" as ir.FunctionID,
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
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
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
						type_parameters: ["T" as ir.TypeVariableID],
						constraint_parameters: [
							{
								interface: "Favorite" as ir.InterfaceID,
								subjects: [typeVariable("T")],
							}
						],
						parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opDynamicCall({
							i: "Favorite",
							its: [typeVariable("T")],
							f: "get",
							ts: [],
							args: [],
							dst: [["favorite", ir.T_INT]],
						}),
						opReturn("favorite"),
					),
				},
				"main": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],

					},
					body: opBlock(
						// No constraints are passed in this invocation.
						opStaticCall({
							f: "favoriteOf",
							dst: [["favorite", ir.T_INT]],
							args: [],
							ts: [typeCompound("Thirteen")],
						}),
						opReturn("favorite"),
					),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This" as ir.TypeVariableID],
					signatures: {
						"get": {
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [ir.T_INT],
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
			enums: {},
			foreign: {},
		};

		const [returned] = interpret("main" as ir.FunctionID, [], program, {});
		assert(returned, "is equal to", {
			sort: "int",
			int: BigInt(13),
		});
	},
	"dynamic-dispatch-from-type-constraint-closure"() {
		const program: ir.Program = {
			globalVTableFactories: {
				"SevenIsFavorite": {
					provides: {
						interface: "Favorite" as ir.InterfaceID,
						subjects: [typeCompound("Seven")],
					},
					for_any: [],
					closures: [],
					entries: {
						"get": {
							implementation: "seven" as ir.FunctionID,
							constraint_parameters: [],
						},
					},
				},
				"SquarerIsFavorite": {
					for_any: ["T" as ir.TypeVariableID],
					provides: {
						interface: "Favorite" as ir.InterfaceID,
						subjects: [typeCompound("Squarer", typeVariable("T"))],
					},
					closures: [
						{
							interface: "Favorite" as ir.InterfaceID,
							subjects: [typeVariable("T")]
						},
					],
					entries: {
						"get": {
							implementation: "squareFavorite" as ir.FunctionID,
							constraint_parameters: [
								{
									source: "closure",
									closureIndex: 0,
								},
							],
						},
					},
				},
			},
			functions: {
				"squareFavorite": {
					signature: {
						type_parameters: ["#F" as ir.TypeVariableID],
						constraint_parameters: [
							{
								interface: "Favorite" as ir.InterfaceID,
								subjects: [typeVariable("#F")],
							}
						],
						parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opDynamicCall({
							i: "Favorite", its: [typeVariable("#F")],
							f: "get", dst: [["fav", ir.T_INT]], args: [], ts: [],
						}),
						opForeign({ f: "int*", dst: [["fav", ir.T_INT]], args: ["fav", "fav"] }),
						opReturn("fav"),
					),
				},
				"seven": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
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
						type_parameters: ["#T" as ir.TypeVariableID],
						constraint_parameters: [
							{
								interface: "Favorite" as ir.InterfaceID,
								subjects: [typeVariable("#T")],
							},
						],
						parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						opDynamicCall({
							i: "Favorite",
							its: [typeVariable("#T")],
							f: "get",
							ts: [],
							args: [],
							dst: [["favorite", ir.T_INT]],
						}),
						opReturn("favorite"),
					),
				},
				"main": {
					signature: {
						type_parameters: [],
						constraint_parameters: [],
						parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: opBlock(
						// No constraints are passed in this invocation.
						opStaticCall({
							f: "favoriteOf",
							ts: [typeCompound("Squarer", typeCompound("Seven"))],
							args: [],
							dst: [["favorite", ir.T_INT]],
						}),
						opReturn("favorite"),
					),
				},
			},
			interfaces: {
				"Favorite": {
					type_parameters: ["#This" as ir.TypeVariableID],
					signatures: {
						"get": {
							type_parameters: [],
							constraint_parameters: [],
							parameters: [],
							return_types: [ir.T_INT],
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
					type_parameters: ["#X" as ir.TypeVariableID],
					fields: {},
				},
			},
			enums: {},
			foreign: foreign,
		};

		const [returned] = interpret("main" as ir.FunctionID, [], program, {
			"int*": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int * b.int }];
			},
		});
		assert(returned, "is equal to", {
			sort: "int",
			int: BigInt(49),
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
		const result = interpret("example.Main.main" as ir.FunctionID, [], program, {
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
			{ sort: "int", int: BigInt(1) },
			{ sort: "int", int: BigInt(3) },
			{ sort: "int", int: BigInt(4) },
			{ sort: "int", int: BigInt(7) },
			{ sort: "int", int: BigInt(11) },
			{ sort: "int", int: BigInt(18) },
			{ sort: "int", int: BigInt(29) },
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
			{ sort: "int", int: BigInt(13) },
			{ sort: "int", int: BigInt(17) },
		];
		const result = interpret("example.V.make" as ir.FunctionID, inputs, program, {});
		assert(result, "is equal to", [
			{
				sort: "record",
				fields: {
					x: { sort: "int", int: BigInt(13) },
					y: { sort: "int", int: BigInt(17) },
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
					x: { sort: "int", int: BigInt(13) },
					y: { sort: "int", int: BigInt(17) },
				},
			},
		];
		const result = interpret("example.V.unmake" as ir.FunctionID, inputs, program, {});
		assert(result, "is equal to", [
			{ sort: "int", int: BigInt(13) },
			{ sort: "int", int: BigInt(17) },
		]);
	},
	"callsite-dyn-call"() {
		const program: ir.Program = {
			interfaces: {
				"AbstractProducer": {
					type_parameters: ["This" as ir.TypeVariableID],
					signatures: {
						"abstractProduce": {
							type_parameters: ["X" as ir.TypeVariableID, "T" as ir.TypeVariableID],
							constraint_parameters: [
								{
									interface: "Producer" as ir.InterfaceID,
									subjects: [typeVariable("X"), typeVariable("T")],
								},
							],
							parameters: [],
							return_types: [typeVariable("T")],
							preconditions: [],
							postconditions: [],
						},
					},
				},
				"Producer": {
					type_parameters: ["X" as ir.TypeVariableID, "T" as ir.TypeVariableID],
					signatures: {
						"produce": {
							type_parameters: [],
							constraint_parameters: [],
							return_types: [typeVariable("T")],
							parameters: [],
							preconditions: [],
							postconditions: [],
						},
					},
				},
			},
			globalVTableFactories: {
				"AbstractProducerImpl_is_AbstractProducer": {
					for_any: [],
					provides: {
						interface: "AbstractProducer" as ir.InterfaceID,
						subjects: [typeCompound("AbstractProducerImpl")],
					},
					closures: [],
					entries: {
						"abstractProduce": {
							implementation: "abstractProducer" as ir.FunctionID,
							constraint_parameters: [{ source: "signature", signatureIndex: 0 }],
						},
					},
				},
				"IntProducer_is_Producer": {
					for_any: [],
					provides: {
						interface: "Producer" as ir.InterfaceID,
						subjects: [typeCompound("IntProducer"), ir.T_INT],
					},
					closures: [],
					entries: {
						"produce": {
							implementation: "produceInt" as ir.FunctionID,
							constraint_parameters: [],
						},
					},
				},
			},
			records: {
				"AbstractProducerImpl": {
					type_parameters: [],
					fields: {},
				},
				"IntProducer": {
					type_parameters: [],
					fields: {},
				},
			},
			enums: {},
			functions: {
				"produceInt": {
					signature: {
						type_parameters: [],
						parameters: [],
						constraint_parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: {
						ops: [
							opConst("r", 17),
							opReturn("r"),
						],
					},
				},
				"abstractProducer": {
					signature: {
						type_parameters: ["X" as ir.TypeVariableID, "T" as ir.TypeVariableID],
						parameters: [],
						constraint_parameters: [
							{
								interface: "Producer" as ir.InterfaceID,
								subjects: [typeVariable("X"), typeVariable("T")],
							},
						],
						return_types: [typeVariable("T")],
						preconditions: [],
						postconditions: [],
					},
					body: {
						ops: [
							opDynamicCall({
								i: "Producer",
								its: [typeVariable("X"), typeVariable("T")],
								f: "produce",
								ts: [],
								dst: [["r", typeVariable("T")]],
								args: [],
							}),
							opReturn("r"),
						],
					},
				},
				"main": {
					signature: {
						type_parameters: [],
						parameters: [],
						constraint_parameters: [],
						return_types: [ir.T_INT],
						preconditions: [],
						postconditions: [],
					},
					body: {
						ops: [
							opDynamicCall({
								i: "AbstractProducer",
								its: [typeCompound("AbstractProducerImpl")],
								f: "abstractProduce",
								ts: [typeCompound("IntProducer"), ir.T_INT],
								args: [],
								dst: [["r", ir.T_INT]],
							}),
							opReturn("r"),
						],
					},
				},
			},
			foreign: {},
		};

		const result = interpret("main" as ir.FunctionID, [], program, {});
		assert(result, "is equal to", [{ sort: "int", int: BigInt(17) }]);
	},
	"basic-static-method"() {
		const source = `
		package example;

		record V2 {
			var x: Int;
			var y: Int;

			fn add(self: V2, other: V2): V2 {
				return V2{
					x = self.x + other.x,
					y = self.y + other.y,
				};
			}

			fn main(a: V2, b: V2): Int, Int {
				var sum: V2 = a.add(b);
				return sum.x, sum.y;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const inputs: Value[] = [
			{
				sort: "record",
				fields: {
					x: { sort: "int", int: BigInt(1) },
					y: { sort: "int", int: BigInt(2) },
				},
			},
			{
				sort: "record",
				fields: {
					x: { sort: "int", int: BigInt(30) },
					y: { sort: "int", int: BigInt(40) },
				},
			},
		];
		const result = interpret("example.V2.main" as ir.FunctionID, inputs, program, {
			"Int+": ([a, b]: Value[]) => {
				if (a.sort !== "int") throw new Error("bad argument");
				if (b.sort !== "int") throw new Error("bad argument");
				return [{ sort: "int", int: a.int + b.int }];
			},
		});
		assert(result, "is equal to", [
			{ sort: "int", int: BigInt(31) },
			{ sort: "int", int: BigInt(42) },
		]);
	},
	"invoke-concrete-impl"() {
		const source = `
		package example;

		interface I {
			fn get(): Int;
		}

		record R {
			fn main(): Int {
				return (R is I).get();
			}
		}

		impl R is I {
			fn get(): Int {
				return 32;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });

		const inputs: Value[] = [];
		const result = interpret("example.R.main" as ir.FunctionID, inputs, program, {});

		assert(result, "is equal to", [
			{ sort: "int", int: BigInt(32) },
		]);
	},
	"invoke-type-parameter-impl"() {
		const source = `
		package example;

		interface Convertible[#To] {
			fn convert(t: This): #To;
		}

		record R {
			var r: Int;
		}

		record S {
			var s: Int;
		}

		impl R is Convertible[S] {
			fn convert(r: R): S {
				return S{s = r.r};
			}
		}

		record Delegating[#A, #B | #A is Convertible[#B]] {
			fn convert(a: #A): #B {
				return (#A is Convertible[#B]).convert(a);
			}
		}

		record Main {
			fn main(): S {
				var r: R = R{r = 17};
				return Delegating[R, S].convert(r);
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });

		const inputs: Value[] = [];
		const result = interpret("example.Main.main" as ir.FunctionID, inputs, program, {});

		assert(result, "is equal to", [
			{
				sort: "record",
				fields: {
					s: { sort: "int", int: BigInt(17) },
				},
			},
		]);
	},
	"basic-enum-construct-and-extract"() {
		const source = `
		package example;

		enum Either {
			var bool: Boolean;
			var int: Int;
		}

		record Main {
			fn main(): Either, Boolean, Boolean, Int {
				var obj: Either = Either{int = 3};
				return obj, obj is int, obj is bool, obj.int;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });

		const inputs: Value[] = [];
		const result = interpret("example.Main.main" as ir.FunctionID, inputs, program, {});

		assert(result, "is equal to", [
			{
				sort: "enum",
				field: {
					int: { sort: "int", int: BigInt(3) },
				},
			},
			{
				sort: "boolean",
				boolean: true,
			},
			{
				sort: "boolean",
				boolean: false,
			},
			{
				sort: "int",
				int: BigInt(3),
			}
		]);
	},
	"logical-operations"() {
		const source = `
		package example;

		record Main {
			fn andTable(): Boolean, Boolean, Boolean, Boolean {
				return false and false,
					false and true,
					true and false,
					true and true;
			}

			fn impliesTable(): Boolean, Boolean, Boolean, Boolean {
				return false implies false,
					false implies true,
					true implies false,
					true implies true;
			}

			fn orTable(): Boolean, Boolean, Boolean, Boolean {
				return false or false,
					false or true,
					true or false,
					true or true;
			}

			fn notTable(): Boolean, Boolean {
				return not false, not true;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });

		const inputs: Value[] = [];
		const andTable = interpret("example.Main.andTable" as ir.FunctionID, inputs, program, {});
		assert(andTable, "is equal to", [
			{ sort: "boolean", boolean: false },
			{ sort: "boolean", boolean: false },
			{ sort: "boolean", boolean: false },
			{ sort: "boolean", boolean: true },
		]);

		const impliesTable = interpret("example.Main.impliesTable" as ir.FunctionID, inputs, program, {});
		assert(impliesTable, "is equal to", [
			{ sort: "boolean", boolean: true },
			{ sort: "boolean", boolean: true },
			{ sort: "boolean", boolean: false },
			{ sort: "boolean", boolean: true },
		]);

		const orTable = interpret("example.Main.orTable" as ir.FunctionID, inputs, program, {});
		assert(orTable, "is equal to", [
			{ sort: "boolean", boolean: false },
			{ sort: "boolean", boolean: true },
			{ sort: "boolean", boolean: true },
			{ sort: "boolean", boolean: true },
		]);

		const notTable = interpret("example.Main.notTable" as ir.FunctionID, inputs, program, {});
		assert(notTable, "is equal to", [
			{ sort: "boolean", boolean: true },
			{ sort: "boolean", boolean: false },
		]);
	},
};
