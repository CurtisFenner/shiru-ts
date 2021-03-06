import { SourceLocation } from "./ir";
import { ErrorElement, IdenToken, KeywordToken, PUNCTUATION, PunctuationToken, Token, tokenize, TypeIdenToken, TypeKeywordToken, TypeVarToken } from "./lexer";
import { RecordParserDescription, ConstParser, Parser, ParsersFor, RecordParser, RepeatParser, TokenParser, DebugContext, ParseResult, choice, ChoiceParser, TokenSpan, FailHandler } from "./parser";

function keywordParser<K extends KeywordToken["keyword"]>(keyword: K): Parser<Token, KeywordToken> {
	return new TokenParser((t) => {
		if (t.tag === "keyword") {
			if (t.keyword === keyword) {
				return t;
			}
		}
		return null;
	});
}

function tokenParser<T extends Token["tag"]>(tag: T): Parser<Token, Extract<Token, { tag: T }>> {
	return new TokenParser((t: Token) => {
		if (t.tag === tag) {
			return t as Extract<Token, { tag: T }>;
		}
		return null;
	});
}

function punctuationParser<K extends keyof typeof PUNCTUATION>(symbol: K): Parser<Token, PunctuationToken> {
	return new TokenParser((t: Token) => {
		if (t.tag === "punctuation" && t.symbol === symbol) {
			return t;
		}
		return null;
	});
}


const eofParser: Parser<Token, SourceLocation> = new TokenParser(t => t.tag === "eof" ? t.location : null);

/// `CommaParser` is a combinator that parses a comma-separated sequence of 
/// elements.
class CommaParser<T> extends Parser<Token, T[]> {
	constructor(private element: Parser<Token, T>, private expected: string) {
		super();
	}

	parse(stream: Token[], from: number, debugContext: Record<string, TokenSpan<Token>>): ParseResult<T[]> {
		let out = [];
		while (true) {
			const object = this.element.parse(stream, from, debugContext);
			if (object === null) {
				if (out.length === 0) {
					return { object: [], rest: from };
				}
				throw new ParseError([this.expected, stream[from].location]);
			} else if ("message" in object) {
				return object;
			} else {
				out.push(object.object);
				from = object.rest;
			}

			// Parse a comma.
			const comma = punctuation.comma.parse(stream, from, debugContext);
			if (comma === null) {
				return {
					object: out,
					rest: from,
				};
			} else if ("message" in comma) {
				throw new Error("unreachable");
			} else {
				from = comma.rest;
			}
		}
	}
}

class StructParser<T extends { location: SourceLocation }, R> extends Parser<T, R & { location: SourceLocation }> {
	parser: RecordParser<T, R>;

	constructor(spec: () => RecordParserDescription<T, R>) {
		super();
		this.parser = new RecordParser(spec);
	}

	parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<R & { location: SourceLocation }> {
		const firstToken = stream[from].location;

		const result = this.parser.parse(stream, from, debugContext);
		if (result === null || "message" in result) {
			return result;
		}

		const lastToken = stream[result.rest - 1].location;
		const location = {
			fileID: firstToken.fileID,
			offset: firstToken.offset,
			length: lastToken.offset + lastToken.length - firstToken.offset,
		};

		return {
			object: { ...result.object, location },
			rest: result.rest,
		};
	}
}

function requireAtLeastOne<T>(thing: string) {
	return (array: T[], tokens: Token[], from: number) => {
		if (array.length === 0) {
			throw new ParseError([
				"Expected at least one " + thing + " at",
				tokens[from].location,
			]);
		}
		return array;
	};
}

function parseProblem(...message: (ErrorElement | FailHandler<Token, ErrorElement | ErrorElement[]>)[]) {
	return (stream: Token[], from: number, context: DebugContext<Token>) => {
		const out = [];
		for (let e of message) {
			if (typeof e === "function") {
				const x = e(stream, from, context);
				if (Array.isArray(x)) {
					out.push(...x);
				} else {
					out.push(x);
				}
			} else {
				out.push(e);
			}
		}
		return new ParseError(out);
	};
}

export class ParseError {
	constructor(public message: ErrorElement[]) { }

	toString() {
		return JSON.stringify(this.message);
	}
}

function atReference(name: string) {
	return (stream: Token[], from: number, props: DebugContext<Token>): SourceLocation => {
		const token = props[name].first;
		if (token === null) {
			throw new Error("null first in atReference");
		} else {
			return token.location;
		}
	}
}

function atHead(stream: Token[], from: number): SourceLocation {
	const token = stream[from];
	if (token === undefined) {
		throw new Error("out of bounds");
	} else {
		return token.location;
	}
}

/// THROWS `LexError`
/// THROWS `ParseError`
export function parseSource(blob: string, fileID: string) {
	const tokens = tokenize(blob, fileID);
	const result = grammar.Source.parse(tokens, 0, {})!;
	// N.B.: The end-of parser in Source ensures no tokens are left afterwards.
	return result.object;
}


const tokens = {
	packageIden: tokenParser("iden"),
	typeIden: tokenParser("type-iden"),
	iden: tokenParser("iden"),
	typeVarIden: tokenParser("type-var"),
};

const keywords = {
	fn: keywordParser("fn"),
	import: keywordParser("import"),
	is: keywordParser("is"),
	interface: keywordParser("interface"),
	package: keywordParser("package"),
	proof: keywordParser("proof"),
	class: keywordParser("class"),
	var: keywordParser("var"),
};

const punctuation = {
	semicolon: punctuationParser(";"),
	comma: punctuationParser(","),
	colon: punctuationParser(":"),
	dot: punctuationParser("."),
	pipe: punctuationParser("|"),
	curlyOpen: punctuationParser("{"),
	curlyClose: punctuationParser("}"),
	roundOpen: punctuationParser("("),
	roundClose: punctuationParser(")"),
	squareOpen: punctuationParser("["),
	squareClose: punctuationParser("]"),
};

export interface Source {
	package: PackageDef,
	imports: Import[],
	definitions: Definition[],
}

export interface PackageDef {
	packageName: IdenToken,
}

export interface ImportOfObject {
	tag: "of-object",

	packageName: IdenToken,
	objectName: TypeIdenToken,

	location: SourceLocation,
}

export interface ImportOfPackage {
	tag: "of-package",

	packageName: IdenToken,

	location: SourceLocation,
}

export interface Import {
	imported: ImportOfObject | ImportOfPackage,
}

export type Definition = ClassDefinition;

export interface ClassDefinition {
	tag: "class-definition",
	entityName: TypeIdenToken,
	typeParameters: TypeParameters,
	fields: Field[],
	fns: Fn[],

	location: SourceLocation,
}

export interface InterfaceMember {
	signature: FnSignature,
}

export interface InterfaceDefinition {
	tag: "interface-definition",
	entityName: TypeIdenToken,
	typeParameters: TypeParameters,
	members: InterfaceMember[],
}

export interface Field {
	name: IdenToken,
	t: Type,
}

export interface FnParameters {
	parameters: FnParameter[],
}

export interface FnParameter {
	name: IdenToken,
	t: Type,
}

export interface FnSignature {
	proof: KeywordToken | false,
	name: IdenToken,
	parameters: FnParameter[],
	returns: Type[],
}

export interface Fn {
	signature: FnSignature,
}

// For bringing new type variables into a scope.
interface TypeParameters {
	parameters: TypeVarToken[],
	constraints: TypeConstraint[],
}

// For specifying arguments to some entity.
interface TypeArguments {
	arguments: Type[],
}

interface TypeConstraint {
	subject: TypeVarToken,
	constraint: Type,
}

interface TypeConstraints {
	constraints: TypeConstraint[],
}

export interface ClassType {
	tag: "class",
	packageQualification: PackageQualification | null,
	class: TypeIdenToken,
	arguments: Type[],
	location: SourceLocation,
}

export type KeywordType = {
	tag: "keyword",
	keyword: "Boolean" | "String" | "Unit" | "Int" | "This",
	location: SourceLocation,
};

export interface PackageQualification {
	package: IdenToken,

	location: SourceLocation,
}

export type Type = ClassType | KeywordType;

type ASTs = {
	Source: Source,
	PackageDef: PackageDef,
	ImportOfObject: ImportOfObject,
	ImportOfPackage: ImportOfPackage,
	Import: Import,
	Definition: Definition,
	ClassDefinition: ClassDefinition,
	Field: Field,
	FnParameters: FnParameters,
	FnParameter: FnParameter,
	FnSignature: FnSignature,
	Fn: Fn,
	InterfaceDefinition: InterfaceDefinition,
	InterfaceMember: InterfaceMember,
	KeywordType: KeywordType,
	PackageQualification: PackageQualification,
	TypeArguments: TypeArguments,
	TypeParameters: TypeParameters,
	TypeConstraint: TypeConstraint,
	TypeConstraints: TypeConstraints,
	ClassType: ClassType,
	Type: Type,
};

export const grammar: ParsersFor<Token, ASTs> = {
	Source: new RecordParser(() => ({
		package: grammar.PackageDef
			.required(parseProblem("Expected a package declaration to begin the source file at", atHead)),
		imports: new RepeatParser(grammar.Import),
		definitions: new RepeatParser(grammar.Definition),
		_eof: eofParser
			.required(parseProblem("Expected another definition at", atHead)),
	})),
	PackageDef: new RecordParser(() => ({
		_package: keywords.package,
		packageName: tokens.packageIden
			.required(parseProblem("Expected a package name after `package` at", atHead)),
		_semicolon: punctuation.semicolon
			.required(parseProblem("Expected a `;` to end the package declaration at", atHead)),
	})),
	ImportOfObject: new StructParser(() => ({
		tag: new ConstParser("of-object"),
		packageName: tokens.packageIden,
		_dot: punctuation.dot,
		objectName: tokens.typeIden
			.required(parseProblem("Expected an object name to import after `:` at", atHead)),
	})),
	ImportOfPackage: new StructParser(() => ({
		tag: new ConstParser("of-package"),
		packageName: tokens.packageIden,
	})),
	Import: new RecordParser(() => ({
		_import: keywords.import,
		imported: choice(() => grammar, "ImportOfObject", "ImportOfPackage")
			.required(parseProblem("Expected an entity or package to import after `import` at", atHead)),
		_semicolon: punctuation.semicolon
			.required(parseProblem("Expected a `;` to end the import at", atHead)),
	})),
	Definition: new ChoiceParser(() => [grammar.ClassDefinition]),
	ClassDefinition: new StructParser(() => ({
		_class: keywords.class,
		tag: new ConstParser("class-definition"),
		entityName: tokens.typeIden,
		typeParameters: grammar.TypeParameters
			.otherwise({ parameters: [], constraints: [] } as TypeParameters),
		_open: punctuation.curlyOpen,
		fields: new RepeatParser(grammar.Field),
		fns: new RepeatParser(grammar.Fn),
		_close: punctuation.curlyClose
			.required(parseProblem("Expected a `}` at", atHead,
				"to complete a class definition beginning at", atReference("_open"))),
	})),
	InterfaceMember: new RecordParser(() => ({
		signature: grammar.FnSignature,
		_semicolon: punctuation.semicolon
			.required(parseProblem("Expected a `;` to complete the interface member at", atHead)),
	})),
	InterfaceDefinition: new RecordParser(() => ({
		_interface: keywords.interface,
		tag: new ConstParser("interface-definition"),
		entityName: tokens.typeIden,
		typeParameters: grammar.TypeParameters
			.otherwise({ parameters: [], constraints: [] } as TypeParameters),
		_open: punctuation.curlyOpen,
		members: new RepeatParser(grammar.InterfaceMember),
		_close: punctuation.curlyClose
			.required(parseProblem("Expected a `}` at", atHead,
				"to complete an interface definition beginning at", atReference("_open"))),
	})),
	Field: new StructParser(() => ({
		_var: keywords.var,
		name: tokens.iden
			.required(parseProblem("Expected a field name after `var` at", atHead)),
		_colon: punctuation.colon
			.required(parseProblem("Expected a `;` after variable name at", atHead)),
		t: grammar.Type
			.required(parseProblem("Expected a type after `:` at", atHead)),
		_semicolon: punctuation.semicolon
			.required(parseProblem("Expected a `;` after field type at", atHead)),
	})),
	KeywordType: new TokenParser((t) => {
		if (t.tag !== "type-keyword") {
			return null;
		}
		if (t.keyword === "Never") {
			throw new ParseError([
				"Found `Never`, which is a reserved but unused keyword at",
				t.location,
			]);
		}
		return {
			tag: "keyword",
			keyword: t.keyword,
			location: t.location,
		}
	}),
	PackageQualification: new StructParser(() => ({
		package: tokens.iden,
		_dot: punctuation.dot
			.required(parseProblem("Expected a `.` after a package name at", atHead)),
	})),
	TypeConstraint: new RecordParser(() => ({
		subject: tokens.typeVarIden,
		_is: keywords.is
			.required(parseProblem("Expected `is` after type constraint subject at", atHead)),
		constraint: grammar.Type
			.required(parseProblem("Expected a constraint to be named after `is` at", atHead)),
	})),
	TypeConstraints: new RecordParser(() => ({
		_pipe: punctuation.pipe,
		constraints: new CommaParser(grammar.TypeConstraint, "Expected a type constraint at")
			.map(requireAtLeastOne("type constraint")),
	})),
	TypeParameters: new RecordParser(() => ({
		_open: punctuation.squareOpen,
		parameters: new CommaParser(tokens.typeVarIden, "Expected a type variable at")
			.map(requireAtLeastOne("type variable")),
		constraints: grammar.TypeConstraints.map(x => x.constraints),
		_close: punctuation.squareClose
			.required(parseProblem("Expected a `]` at", atHead,
				"to complete type parameters started at", atReference("_open"))),
	})),
	ClassType: new StructParser(() => ({
		packageQualification: grammar.PackageQualification
			.otherwise(null),
		class: tokens.typeIden,
		tag: new ConstParser("class"),
		arguments: grammar.TypeArguments.map(x => x.arguments).otherwise([]),
	})),
	TypeArguments: new RecordParser(() => ({
		_open: punctuation.squareOpen,
		arguments: new CommaParser(grammar.Type, "Expected a type argument at")
			.map(requireAtLeastOne("type argument")),
		_close: punctuation.squareClose
			.required(parseProblem("Expected a `]` at", atHead,
				"to complete type arguments started at", atReference("_open"))),
	})),
	Type: choice(() => grammar, "ClassType", "KeywordType"),
	FnParameter: new RecordParser(() => ({
		name: tokens.iden,
		_colon: punctuation.colon,
		t: grammar.Type,
	})),
	FnParameters: new RecordParser(() => ({
		_open: punctuation.roundOpen,
		parameters: new CommaParser(grammar.FnParameter,
			"Expected another function parameter after `,` at"),
		_close: punctuation.roundClose
			.required(parseProblem("Expected a `)` at", atHead,
				"to complete the parameter list started at", atReference("_open"))),
	})),
	FnSignature: new StructParser(() => ({
		proof: keywords.proof.otherwise(false as const),
		_fn: keywords.fn,
		name: tokens.iden
			.required(parseProblem("Expected a function name after `fn` at", atHead)),
		parameters: grammar.FnParameters.map(x => x.parameters)
			.required(parseProblem("Expected a `(` to begin function parameters at", atHead)),
		_colon: punctuation.colon
			.required(parseProblem("Expected a `:` after function parameters at", atHead)),
		returns: new CommaParser(grammar.Type, "Expected a return type at")
			.map(requireAtLeastOne("return type")),
	})),
	Fn: new StructParser(() => ({
		signature: grammar.FnSignature,
		_open: punctuation.curlyOpen
			.required(parseProblem("Expected a `{` to begin a function body at", atHead)),
		_close: punctuation.curlyClose
			.required(parseProblem("Expected a `}` to complete a function body at", atHead)),
	})),
};
