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
	constructor(args: { name?: string, kind: "class" | "keyword", typeLocation: SourceLocation }) {
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
		grouping: "parens" | "field" | "method",
	}) {
		super([
			"An expression has " + args.valueCount + " values and so cannot be grouped",
			"by " + args.grouping + " at",
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
