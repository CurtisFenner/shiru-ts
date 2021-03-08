import * as grammar from "./grammar";
import { Token, tokenize } from "./lexer";
import { assert } from "./test";


export const tests = {
	"lex-error"() {
		const source = `package alpha; $`;
		assert(() => grammar.parseSource(source, "test-file"), "throws", {
			message: [
				"Found an unexpected symbol at",
				{ fileID: "test-file", offset: 15, length: 1 },
			],
		});
	},
	"expect-package"() {
		const source = `something`;
		assert(() => grammar.parseSource(source, "test-file"), "throws", {
			message: [
				"Expected a package declaration to begin the source file at",
				{ fileID: "test-file", offset: 0, length: 9 },
			],
		});
	},
	"expect-package-name"() {
		const stream: Token[] = tokenize(`package`, "test-file");
		assert(() => grammar.grammar.Source.parse(stream, 0, {}), "throws", {
			message: [
				"Expected a package name after `package` at",
				{ fileID: "test-file", offset: 7, length: 0 },
			],
		});
	},
	"expect-package-semicolon"() {
		const source = `package mypackage`;
		assert(() => grammar.parseSource(source, "test-file"), "throws", {
			message: [
				"Expected a `;` to end the package declaration at",
				{ fileID: "test-file", offset: 17, length: 0 },
			],
		});
	},
	"parse-minimal-class"() {
		const code = `class A {}`;
		const tokens = tokenize(code, "test-file");
		const ast = grammar.grammar.ClassDefinition.parse(tokens, 0, {});

		assert(ast, "is equal to", {
			object: {
				tag: "class-definition",
				entityName: {
					tag: "type-iden",
					name: "A",
					location: { fileID: "test-file", offset: 6, length: 1 },
				},
				typeParameters: {
					parameters: [],
					constraints: [],
				},
				fields: [],
				fns: [],
				location: { fileID: "test-file", offset: 0, length: 10 },
			},
			rest: tokens.length - 1,
		});
	},
	"parse-minimal-source"() {
		const source = `package mypackage;`;
		const ast = grammar.parseSource(source, "test-file");
		assert(ast, "is equal to", {
			package: {
				packageName: {
					tag: "iden",
					name: "mypackage",
					location: { fileID: "test-file", offset: 8, length: 9 },
				},
			},
			imports: [],
			definitions: [],
		});
	},
	"parse-small-source"() {
		const source = `package mypackage; class A {} class B {}`;
		const ast = grammar.parseSource(source, "test-file");
		assert(ast.definitions.length, "is equal to", 2);
	},
	"expect-one-type-variable"() {
		const source = `package example; class A[] {}`;
		assert(() => grammar.parseSource(source, "test-a"), "throws", {
			message: [
				"Expected a type variable at",
				{ fileID: "test-a", offset: 25, length: 1 },
			],
		});
	},
	"expect-some-type-constraints"() {
		const source = `package example; class A[#X | ] {}`;
		assert(() => grammar.parseSource(source, "test-a"), "throws", {
			message: [
				"Expected at least one type constraint at",
				{ fileID: "test-a", offset: 30, length: 1 },
			],
		});
	},
	"expect-some-type-constraint-is"() {
		const source = `package example; class A[#X | #X] {}`;
		assert(() => grammar.parseSource(source, "test-a"), "throws", {
			message: [
				"Expected `is` after type constraint subject at",
				{ fileID: "test-a", offset: 32, length: 1 },
			],
		});
	},
	"expect-some-type-constraint-name"() {
		const source = `package example; class A[#X | #X is] {}`;
		assert(() => grammar.parseSource(source, "test-a"), "throws", {
			message: [
				"Expected a constraint to be named after `is` at",
				{ fileID: "test-a", offset: 35, length: 1 },
			],
		});
	},
};
