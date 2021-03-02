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
			"Object `" + args.name + "` was defined for a second time at",
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
			"Object `" + args.entityName + "` has not been defined, but it was referenced at",
			args.reference,
		]);
	}
}

export class NamespaceAlreadyDefined extends SemanticError {
	constructor(args: { namespace: string, firstBinding: SourceLocation, secondBinding: SourceLocation }) {
		super([
			"The namespace `" + args.namespace + "` was defined for a second time at",
			args.secondBinding,
			"The first definition was at",
			args.firstBinding,
		]);
	}
}

export class InvalidThisType extends SemanticError {
	constructor(args: { referenced: SourceLocation }) {
		super([
			"The keyword `This` cannot be used at", args.referenced
		]);
	}
}
