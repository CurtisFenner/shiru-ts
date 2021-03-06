import { SourceLocation } from "./ir";
import { ErrorElement } from "./lexer";

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
