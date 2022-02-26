import * as ir from "./ir";

function varDef(name: string, t: ir.Type): ir.VariableDefinition {
	return {
		variable: name as ir.VariableID,
		type: t,
		location: ir.NONE,
	};
}

export function getBasicForeign(): Record<string, ir.FunctionSignature> {
	return {
		"Int==": {
			// Equality
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
		},
		"Boolean==": {
			// Equality
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
		},
		"Int<": {
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
			],
			semantics: {
				transitive: true,
				transitiveAcyclic: true,
			},
		},
		"Int<=": {
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
		"Int+": {
			// Addition
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
		"Int-": {
			// Subtract
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
		"Int-unary": {
			// Negate
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
	};
}
