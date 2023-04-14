import { RecordID, Type, typeRecursiveSubstitute, typeSubstitute, TypeVariableID, unifyTypes } from "./ir.js";
import { assert } from "./test.js";

export const tests = {
	"basic-unification-fails"() {
		// `R[T, T]`
		const left: Type = {
			tag: "type-compound",
			base: "R" as RecordID,
			type_arguments: [
				{
					tag: "type-variable",
					id: "T" as TypeVariableID,
				},
				{
					tag: "type-variable",
					id: "T" as TypeVariableID,
				},
			],
		};

		// `R[X, Y]`
		const right: Type = {
			tag: "type-compound",
			base: "R" as RecordID,
			type_arguments: [
				{
					tag: "type-variable",
					id: "X" as TypeVariableID,
				},
				{
					tag: "type-variable",
					id: "Y" as TypeVariableID,
				},
			],
		};

		const vs = ["T" as TypeVariableID];
		const unifier = unifyTypes(vs, [left], vs, [right]);
		assert(unifier, "is equal to", null);
	},
	"basic-unification-succeeds"() {
		// `R[X, T]`
		const left: Type = {
			tag: "type-compound",
			base: "R" as RecordID,
			type_arguments: [
				{
					tag: "type-variable",
					id: "X" as TypeVariableID,
				},
				{
					tag: "type-variable",
					id: "T" as TypeVariableID,
				},
			],
		};

		// `R[T, Y]`
		const right: Type = {
			tag: "type-compound",
			base: "R" as RecordID,
			type_arguments: [
				{
					tag: "type-variable",
					id: "T" as TypeVariableID,
				},
				{
					tag: "type-variable",
					id: "Y" as TypeVariableID,
				},
			],
		};

		const vs = ["T" as TypeVariableID];
		const unifier = unifyTypes(vs, [left], vs, [right]);
		assert(unifier, "is not null");

		const leftSub = typeSubstitute(left, unifier.leftRenaming);
		const rightSub = typeSubstitute(right, unifier.rightRenaming);
		const leftFull = typeRecursiveSubstitute(leftSub, unifier.instantiations);
		const rightFull = typeRecursiveSubstitute(rightSub, unifier.instantiations);

		// `R[X, Y]`.
		assert(leftFull, "is equal to", {
			tag: "type-compound",
			base: "R" as RecordID,
			type_arguments: [
				{
					tag: "type-variable",
					id: "X" as TypeVariableID,
				},
				{
					tag: "type-variable",
					id: "Y" as TypeVariableID,
				},
			],
		});
		assert(rightFull, "is equal to", {
			tag: "type-compound",
			base: "R" as RecordID,
			type_arguments: [
				{
					tag: "type-variable",
					id: "X" as TypeVariableID,
				},
				{
					tag: "type-variable",
					id: "Y" as TypeVariableID,
				},
			],
		});
	},
};
