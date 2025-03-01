import * as ir from "./ir.js";
import * as uf from "./uf.js";

function varDef(name: string, t: ir.Type): ir.VariableDefinition {
	return {
		variable: name as ir.VariableID,
		type: t,
		location: ir.NONE,
	};
}

export const foreignOperations: Record<string, {
	signature: ir.FunctionSignature,
	getInterpreter?(foreignFns: (name: string) => uf.FnID[]): {
		interpreter?: (...args: (unknown | null)[]) => unknown | null,
	},
}> = {
	// Integer equality function.
	"Int==": {
		signature: {
			parameters: [
				varDef("left", ir.T_INT),
				varDef("right", ir.T_INT),
			],
			return_types: [ir.T_BOOLEAN],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [],
			semantics: {
				eq: true,
			},
		}
	},
	// Boolean equality function.
	"Boolean==": {
		signature: {
			parameters: [
				varDef("left", ir.T_BOOLEAN),
				varDef("right", ir.T_BOOLEAN),
			],
			return_types: [ir.T_BOOLEAN],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [],
			semantics: {
				eq: true,
			},
		}
	},
	"Boolean.not": {
		signature: {
			parameters: [
				varDef("value", ir.T_BOOLEAN),
			],
			return_types: [ir.T_BOOLEAN],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [
				{
					returnedValues: [varDef("returns", ir.T_BOOLEAN)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-branch",
								condition: "value" as ir.VariableID,
								trueBranch: {
									ops: [
										{
											tag: "op-const",
											type: "Boolean",
											boolean: false,
											destination: varDef("false", ir.T_BOOLEAN),
										},
										{
											tag: "op-foreign",
											operation: "Boolean==",
											arguments: ["false", "returns"] as ir.VariableID[],
											destinations: [varDef("cmp", ir.T_BOOLEAN)],
										},
									],
								},
								falseBranch: {
									ops: [
										{
											tag: "op-const",
											type: "Boolean",
											boolean: true,
											destination: varDef("true", ir.T_BOOLEAN),
										},
										{
											tag: "op-foreign",
											operation: "Boolean==",
											arguments: ["true", "returns"] as ir.VariableID[],
											destinations: [varDef("cmp", ir.T_BOOLEAN)],
										},
									],
								},
								destinations: [
									{
										trueSource: {
											tag: "variable",
											variable: "cmp" as ir.VariableID,
										},
										falseSource: {
											tag: "variable",
											variable: "cmp" as ir.VariableID,
										},
										destination: varDef("post", ir.T_BOOLEAN),
									},
								],
							},
						],
					},
					location: ir.NONE,
				},
			],
			semantics: {
				not: true,
			},
		},
	},
	// Integer less-than function.
	"Int<": {
		signature: {
			parameters: [
				varDef("left", ir.T_INT),
				varDef("right", ir.T_INT),
			],
			return_types: [ir.T_BOOLEAN],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [
				{
					// left < right ifandonlyif left <= right - 1
					returnedValues: [varDef("returns", ir.T_BOOLEAN)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-const",
								type: "Int",
								int: "1",
								destination: varDef("one", ir.T_INT),
							},
							{
								tag: "op-foreign",
								operation: "Int-",
								arguments: [
									"right" as ir.VariableID,
									"one" as ir.VariableID,
								],
								destinations: [varDef("rightMinusOne", ir.T_INT)],
							},
							{
								tag: "op-foreign",
								operation: "Int<=",
								arguments: [
									"left" as ir.VariableID,
									"rightMinusOne" as ir.VariableID,
								],
								destinations: [varDef("lessThanEqual", ir.T_INT)],
							},
							{
								tag: "op-proof-eq",
								left: "lessThanEqual" as ir.VariableID,
								right: "returns" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
				{
					// `<` forms a total order:
					// (left < right) implies not (right < left)
					// not (left < right) implies (right <= left).
					returnedValues: [varDef("returns", ir.T_BOOLEAN)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-branch",
								condition: "returns" as ir.VariableID,
								trueBranch: {
									ops: [
										{
											tag: "op-foreign",
											operation: "Int<",
											arguments: [
												"right" as ir.VariableID,
												"left" as ir.VariableID,
											],
											destinations: [varDef("reverse", ir.T_BOOLEAN)],
										},
										{
											tag: "op-foreign",
											operation: "Boolean.not",
											arguments: ["reverse" as ir.VariableID],
											destinations: [varDef("notReverse", ir.T_BOOLEAN)],
										},
									],
								},
								falseBranch: {
									ops: [
										{
											tag: "op-foreign",
											operation: "Int<=",
											arguments: ["right", "left"] as ir.VariableID[],
											destinations: [varDef("post", ir.T_BOOLEAN)],
										},
									],
								},
								destinations: [
									{
										trueSource: {
											tag: "variable",
											variable: "notReverse" as ir.VariableID,
										},
										falseSource: {
											tag: "variable",
											variable: "post" as ir.VariableID,
										},
										destination: varDef("post", ir.T_BOOLEAN),
									},
								],
							},
						],
					},
					location: ir.NONE,
				},
			],
			semantics: {
				transitive: true,
				transitiveAcyclic: true,
			},
		},
		getInterpreter(foreignFns) {
			return {
				interpreter(a: unknown | null, b: unknown | null): unknown | null {
					if (a === null || b === null) {
						return null;
					} else if (typeof a !== "bigint") {
						return null;
					} else if (typeof b !== "bigint") {
						return null;
					}
					return (a as bigint) < (b as bigint);
				},
			};
		},
	},
	// Integer less-than-or-equal function.
	"Int<=": {
		signature: {
			parameters: [
				varDef("left", ir.T_INT),
				varDef("right", ir.T_INT),
			],
			return_types: [ir.T_BOOLEAN],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [
				{
					// return == (left < right or left == right)
					returnedValues: [varDef("returns", ir.T_BOOLEAN)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-proof-eq",
								left: "left" as ir.VariableID,
								right: "right" as ir.VariableID,
								destination: varDef("eq", ir.T_BOOLEAN),
							},
							{
								tag: "op-branch",
								condition: "eq" as ir.VariableID,
								trueBranch: {
									ops: [],
								},
								falseBranch: {
									ops: [
										{
											tag: "op-foreign",
											operation: "Int<",
											arguments: [
												"left" as ir.VariableID,
												"right" as ir.VariableID,
											],
											destinations: [varDef("lt", ir.T_BOOLEAN)],
										},
									],
								},
								destinations: [
									{
										trueSource: { tag: "variable", variable: "eq" as ir.VariableID },
										falseSource: { tag: "variable", variable: "lt" as ir.VariableID },
										destination: varDef("lte", ir.T_BOOLEAN),
									},
								],
							},
							{
								tag: "op-proof-eq",
								left: "lte" as ir.VariableID,
								right: "returns" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
			],
			semantics: {
				transitive: true,
			},

		},
		getInterpreter(foreignFns) {
			return {
				interpreter(a: unknown | null, b: unknown | null): unknown | null {
					if (a === null || b === null) {
						return null;
					} else if (typeof a !== "bigint") {
						return null;
					} else if (typeof b !== "bigint") {
						return null;
					}
					return (a as bigint) <= (b as bigint);
				},
			}
		},
	},
	// Integer addition function.
	"Int+": {
		signature: {
			parameters: [
				varDef("left", ir.T_INT),
				varDef("right", ir.T_INT),
			],
			return_types: [ir.T_INT],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [
				{
					// right == 0 ifandonlyif return == left
					returnedValues: [varDef("sum", ir.T_INT)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-const",
								destination: varDef("zero", ir.T_INT),
								type: "Int",
								int: "0",
							},
							{
								tag: "op-proof-eq",
								left: "right" as ir.VariableID,
								right: "zero" as ir.VariableID,
								destination: varDef("rightIsZero", ir.T_BOOLEAN),
							},
							{
								tag: "op-proof-eq",
								left: "left" as ir.VariableID,
								right: "sum" as ir.VariableID,
								destination: varDef("sumIsLeft", ir.T_BOOLEAN),
							},
							{
								tag: "op-proof-eq",
								left: "rightIsZero" as ir.VariableID,
								right: "sumIsLeft" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
				{
					// left == 0 ifandonlyif return == right
					returnedValues: [varDef("sum", ir.T_INT)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-const",
								destination: varDef("zero", ir.T_INT),
								type: "Int",
								int: "0",
							},
							{
								tag: "op-proof-eq",
								left: "left" as ir.VariableID,
								right: "zero" as ir.VariableID,
								destination: varDef("leftIsZero", ir.T_BOOLEAN),
							},
							{
								tag: "op-proof-eq",
								left: "right" as ir.VariableID,
								right: "sum" as ir.VariableID,
								destination: varDef("sumIsRight", ir.T_BOOLEAN),
							},
							{
								tag: "op-proof-eq",
								left: "leftIsZero" as ir.VariableID,
								right: "sumIsRight" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
				{
					// right < 0 ifandonlyif sum < left
					returnedValues: [varDef("sum", ir.T_INT)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-const",
								destination: varDef("zero", ir.T_INT),
								type: "Int",
								int: "0",
							},
							{
								tag: "op-foreign",
								operation: "Int<",
								arguments: [
									"right" as ir.VariableID,
									"zero" as ir.VariableID,
								],
								destinations: [varDef("rightIsLessThanZero", ir.T_BOOLEAN)],
							},
							{
								tag: "op-foreign",
								operation: "Int<",
								arguments: [
									"sum" as ir.VariableID,
									"left" as ir.VariableID,
								],
								destinations: [varDef("sumIsLessThanLeft", ir.T_BOOLEAN)],
							},
							{
								tag: "op-proof-eq",
								left: "rightIsLessThanZero" as ir.VariableID,
								right: "sumIsLessThanLeft" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
				{
					// 0 < right ifandonlyif left < sum
					returnedValues: [varDef("sum", ir.T_INT)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-const",
								destination: varDef("zero", ir.T_INT),
								type: "Int",
								int: "0",
							},
							{
								tag: "op-foreign",
								operation: "Int<",
								arguments: [
									"zero" as ir.VariableID,
									"right" as ir.VariableID,
								],
								destinations: [varDef("zeroIsLessThanRight", ir.T_BOOLEAN)],
							},
							{
								tag: "op-foreign",
								operation: "Int<",
								arguments: [
									"left" as ir.VariableID,
									"sum" as ir.VariableID,
								],
								destinations: [varDef("leftIsLessThanSum", ir.T_BOOLEAN)],
							},
							{
								tag: "op-proof-eq",
								left: "zeroIsLessThanRight" as ir.VariableID,
								right: "leftIsLessThanSum" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
			],
		},
		getInterpreter(foreignFns) {
			return {
				interpreter(a: unknown | null, b: unknown | null): unknown | null {
					if (a === null || b === null) {
						return null;
					} else if (typeof a !== "bigint") {
						return null;
					} else if (typeof b !== "bigint") {
						return null;
					}

					return (a as bigint) + (b as bigint);
				},
			};
		},
	},
	// Integer subtraction function.
	"Int-": {
		signature: {
			parameters: [
				varDef("left", ir.T_INT),
				varDef("right", ir.T_INT),
			],
			return_types: [ir.T_INT],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [
				{
					// difference == left + (-right)
					returnedValues: [varDef("difference", ir.T_INT)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-foreign",
								operation: "Int-unary",
								arguments: ["right" as ir.VariableID],
								destinations: [varDef("negation", ir.T_INT)],
							},
							{
								tag: "op-foreign",
								operation: "Int+",
								arguments: [
									"left" as ir.VariableID,
									"negation" as ir.VariableID,
								],
								destinations: [varDef("sum", ir.T_INT)],
							},
							{
								tag: "op-proof-eq",
								left: "sum" as ir.VariableID,
								right: "difference" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
			],
		},
		getInterpreter(foreignFns) {
			return {
				interpreter(a: unknown | null, b: unknown | null): unknown | null {
					if (a === null || b === null) {
						return null;
					} else if (typeof a !== "bigint") {
						return null;
					} else if (typeof b !== "bigint") {
						return null;
					}

					return (a as bigint) - (b as bigint);
				},
			};
		},
	},
	// Integer additive inverse function.
	"Int-unary": {
		signature: {
			parameters: [
				varDef("value", ir.T_INT),
			],
			return_types: [ir.T_INT],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [
				{
					// value + negation == 0
					returnedValues: [varDef("negation", ir.T_INT)],
					postcondition: "post" as ir.VariableID,
					block: {
						ops: [
							{
								tag: "op-foreign",
								operation: "Int+",
								arguments: [
									"value" as ir.VariableID,
									"negation" as ir.VariableID,
								],
								destinations: [varDef("sum", ir.T_INT)],
							},
							{
								tag: "op-const",
								destination: varDef("zero", ir.T_INT),
								type: "Int",
								int: "0",
							},
							{
								tag: "op-proof-eq",
								left: "sum" as ir.VariableID,
								right: "zero" as ir.VariableID,
								destination: varDef("post", ir.T_BOOLEAN),
							},
						],
					},
					location: ir.NONE,
				},
			],
		},
		getInterpreter(foreignFns) {
			return {
				interpreter(a: unknown): unknown | null {
					if (a === null) {
						return null;
					} else if (typeof a !== "bigint") {
						return null;
					} else {
						return -(a as bigint);
					}
				},
			};
		},
	},
	"Bytes++": {
		signature: {
			parameters: [
				varDef("left", ir.T_BYTES),
				varDef("right", ir.T_BYTES),
			],
			return_types: [ir.T_BYTES],
			type_parameters: [],
			constraint_parameters: [],
			postconditions: [],
			preconditions: [],
		},
		getInterpreter() {
			return {
				interpreter(a: unknown, b: unknown): unknown | null {
					if (typeof a === "string" && typeof b === "string") {
						return a + b;
					}
					return null;
				},
			};
		}
	},
};
