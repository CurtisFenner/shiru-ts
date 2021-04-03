import { SourceLocation } from "./ir";
import { ErrorElement } from "./lexer";

function pluralize(n: number, singular: string, plural = singular + "s"): string {
	if (n === 1) {
		return singular;
	}
	return plural;
}

function nth(n: number): string {
	if (n % 100 == 11) {
		return n + "th";
	} else if (n % 100 == 12) {
		return n + "th";
	} else if (n % 100 == 13) {
		return n + "th";
	} else if (n % 10 == 1) {
		return n + "st";
	} else if (n % 10 == 2) {
		return n + "nd";
	} else if (n % 10 == 3) {
		return n + "rd";
	}
	return n + "th";
}

export class SemanticError {
	constructor(public message: ErrorElement[]) { }

	toString() {
		return JSON.stringify(this.message);
	}
}

export class EntityRedefinedErr extends SemanticError {
	constructor(args: { name: string, firstBinding: SourceLocation, secondBinding: SourceLocation }) {
		super([
			"Entity `" + args.name + "` was defined for a second time at",
			args.secondBinding,
			"The first definition was at",
			args.firstBinding,
		]);
	}
}

export class NoSuchPackageErr extends SemanticError {
	constructor(args: { packageName: string, reference: SourceLocation }) {
		super([
			"Package `" + args.packageName + "` has not been defined, but it was reference at",
			args.reference,
		]);
	}
}

export class NoSuchEntityErr extends SemanticError {
	constructor(args: { entityName: string, reference: SourceLocation }) {
		super([
			"Entity `" + args.entityName + "` has not been defined, but it was referenced at",
			args.reference,
		]);
	}
}

export class NamespaceAlreadyDefinedErr extends SemanticError {
	constructor(args: { namespace: string, firstBinding: SourceLocation, secondBinding: SourceLocation }) {
		super([
			"The namespace `" + args.namespace + "` was defined for a second time at",
			args.secondBinding,
			"The first definition was at",
			args.firstBinding,
		]);
	}
}

export class InvalidThisTypeErr extends SemanticError {
	constructor(args: { referenced: SourceLocation }) {
		super([
			"The keyword `This` cannot be used at", args.referenced
		]);
	}
}

export class MemberRedefinedErr extends SemanticError {
	constructor(args: { memberName: string, secondBinding: SourceLocation, firstBinding: SourceLocation }) {
		super([
			"The member `" + args.memberName + "` was defined for a second time at",
			args.secondBinding,
			"The first definition of `" + args.memberName + "` was at",
			args.firstBinding,
		]);
	}
}

export class TypeVariableRedefinedErr extends SemanticError {
	constructor(args: { typeVariableName: string, firstBinding: SourceLocation, secondBinding: SourceLocation }) {
		super([
			"The type variable `#" + args.typeVariableName + "` was defined for a second time at",
			args.secondBinding,
			"The first definition was at",
			args.firstBinding,
		]);
	}
}

export class NonTypeEntityUsedAsTypeErr extends SemanticError {
	constructor(args: { entity: string, entityTag: "interface", entityBinding: SourceLocation, useLocation: SourceLocation }) {
		super([
			"The entity `" + args.entity + "` cannot be used a type as was attempted at",
			args.useLocation,
			"because it was defined as a " + args.entityTag + " at",
			args.entityBinding,
		]);
	}
}

export class TypeUsedAsConstraintErr extends SemanticError {
	constructor(args: { name?: string, kind: "record" | "keyword", typeLocation: SourceLocation }) {
		super([
			args.name === undefined
				? "A " + args.kind + " type "
				: "The " + args.kind + " type `" + args.name + "` ",
			"cannot be used as a constraint like it is at",
			args.typeLocation,
		]);
	}
}

export class VariableRedefinedErr extends SemanticError {
	constructor(args: { name: string, firstLocation: SourceLocation, secondLocation: SourceLocation }) {
		super([
			"The variable `" + args.name + "` was defined for a second time at",
			args.secondLocation,
			"The first definition was at",
			args.firstLocation,
		]);
	}
}

export class VariableNotDefinedErr extends SemanticError {
	constructor(args: { name: string, referencedAt: SourceLocation }) {
		super([
			"The variable `" + args.name + "` has not been defined, but it was referenced at",
			args.referencedAt,
		]);
	}
}

export class MultiExpressionGroupedErr extends SemanticError {
	constructor(args: {
		location: SourceLocation,
		valueCount: number,
		grouping: "parens" | "field" | "method" | "if" | "op" | "contract",
		op?: string,
	}) {
		const by = {
			parens: "parenthesization",
			field: "a field access",
			method: "a method access",
			if: "an `if` condition",
			op: "a `" + args.op + "` operation",
			contract: "a `" + args.op + "` contract",
		};
		super([
			"An expression has " + args.valueCount + " values and so cannot be grouped",
			"by " + by[args.grouping] + " at",
			args.location,
		]);
	}
}

export class ValueCountMismatchErr extends SemanticError {
	constructor(args: { actualCount: number, actualLocation: SourceLocation, expectedCount: number, expectedLocation: SourceLocation }) {
		super([
			"An expression has " + args.actualCount + " " + pluralize(args.actualCount, "value") + " at",
			args.actualLocation,
			"but " + args.expectedCount + " " + pluralize(args.expectedCount, "value was", "values were") + " expected at",
			args.expectedLocation,
		]);
	}
}

export class TypeMismatchErr extends SemanticError {
	constructor(args: {
		givenType: string,
		givenLocation: SourceLocation,
		givenIndex?: { index0: number, count: number },
		expectedType: string,
		expectedLocation: SourceLocation,
	}) {
		const value = args.givenIndex && args.givenIndex.count !== 1
			? `${nth(args.givenIndex.count + 1)} value (of ${args.givenIndex.count})`
			: "value";
		super([
			"A " + value + " with type `" + args.givenType + "` at",
			args.givenLocation,
			"cannot be converted to the type `" + args.expectedType + "` as expected at",
			args.expectedLocation,
		]);
	}
}

export class FieldAccessOnNonCompoundErr extends SemanticError {
	constructor(args: {
		accessedType: string,
		accessedLocation: SourceLocation,
	}) {
		super([
			"The type `" + args.accessedType + "` is not a compound type so a field access is illegal at",
			args.accessedLocation,
		]);
	}
}

export class BooleanTypeExpectedErr extends SemanticError {
	constructor(args: { givenType: string, location: SourceLocation } & (
		{ reason: "if" }
		| { reason: "logical-op", op: string, opLocation: SourceLocation }
		| { reason: "contract", contract: "requires" | "ensures" | "assert" })
	) {
		if (args.reason === "if") {
			super([
				"A condition expression with type `" + args.givenType + "` at",
				args.location,
				"cannot be converted to the type `Boolean` as required of ",
				"`if` conditions."
			]);
		} else if (args.reason === "contract") {
			super([
				"A contract expression with type `" + args.givenType + "` at",
				args.location,
				"cannot be converted to the type `Boolean` as required of ",
				"`" + args.contract + "` conditions."
			]);
		} else {
			super([
				"An expression with type `" + args.givenType + "` at",
				args.location,
				"cannot be converted to the type `Boolean` as required ",
				"by the `" + args.op + "` operator at",
				args.opLocation,
			]);
		}
	}
}

export class TypeDoesNotProvideOperatorErr extends SemanticError {
	constructor({ lhsType, operator, operatorLocation }: {
		lhsType: string,
		operatorLocation: SourceLocation,
		operator: string,
	}) {
		super([
			"The type `" + lhsType + "` does not have an operator `" + operator + "`,"
			+ " so an operation is illegal at",
			operatorLocation,
		]);
	}
}

export class OperatorTypeMismatchErr extends SemanticError {
	constructor(args: {
		lhsType: string,
		operator: string,
		givenRhsType: string,
		expectedRhsType: string,
		rhsLocation: SourceLocation
	}) {
		super([
			"The operator `" + args.operator + "`"
			+ " with type `" + args.lhsType
			+ "` on the left side expects a value with type `"
			+ args.expectedRhsType + "` on the right side, but one of type `"
			+ args.givenRhsType + "` was given at",
			args.rhsLocation
		]);
	}
}

export class CallOnNonCompoundErr extends SemanticError {
	constructor(args: {
		baseType: string,
		location: SourceLocation,
	}) {
		super([
			"TODO: CallOnNonCompoundErr",
		]);
	}
}

export class NoSuchFnErr extends SemanticError {
	constructor(args: {
		baseType: string,
		methodName: string,
		methodNameLocation: SourceLocation,
	}) {
		super([
			"TODO: NoSuchFnErr: " + args.baseType + " " + args.methodName + " ",
			args.methodNameLocation,
		]);
	}
}

export class OperationRequiresParenthesizationErr extends SemanticError {
	constructor(args: {
		op1: { str: string, location: SourceLocation },
		op2: { str: string, location: SourceLocation },
		reason: "unordered" | "non-associative",
	}) {
		super([
			"The operators `" + args.op1.str + "` and `" + args.op2.str + "` at",
			args.op1.location,
			"and at",
			args.op2.location,
			"have ambiguous precedence, and require parentheses to specify precedence."
		]);
	}
}

export class RecursivePreconditionErr extends SemanticError {
	constructor(args: {
		callsite?: SourceLocation,
		fn: string,
	}) {
		super([
			"The function `" + args.fn + "` was recursively invoked in a `requires` clause at",
			args.callsite || "???",
			"Try moving this reference to an `ensures` clause.",
		]);
	}
}
