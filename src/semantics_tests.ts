import { SemanticError } from "./diagnostics";
import * as grammar from "./grammar";
import * as semantics from "./semantics";
import { assert } from "./test";

export const tests = {
	"redefine-class-same-source"() {
		const source = `package example; record A { } record A { }`;
		const ast = grammar.parseSource(source, "file-0");

		assert(() => semantics.compileSources([ast]), "throws", new SemanticError([
			"Entity `example.A` was defined for a second time at",
			{ fileID: "file-0", offset: 37, length: 1 },
			"The first definition was at",
			{ fileID: "file-0", offset: 24, length: 1 },
		]));
	},
	"redefine-class-different-sources"() {
		const source0 = `package example; record A { } `;
		const ast0 = grammar.parseSource(source0, "file-0");

		const source1 = `package example; record A { } `;
		const ast1 = grammar.parseSource(source1, "file-1");

		assert(() => semantics.compileSources([ast0, ast1]), "throws", new SemanticError([
			"Entity `example.A` was defined for a second time at",
			{ fileID: "file-1", offset: 24, length: 1 },
			"The first definition was at",
			{ fileID: "file-0", offset: 24, length: 1 },
		]));
	},
	"import-already-defined-name"() {
		const sourceA = `package alpha; record A {}`;
		const sourceB = `package beta; import alpha.A; record A {}`;
		const astA = grammar.parseSource(sourceA, "file-a");
		const astB = grammar.parseSource(sourceB, "file-b");

		assert(() => semantics.compileSources([astA, astB]), "throws", {
			message: [
				"Entity `A` was defined for a second time at",
				{ fileID: "file-b", offset: 27, length: 1 },
				"The first definition was at",
				{ fileID: "file-b", offset: 37, length: 1 },
			],
		});
	},
	"import-name-already-imported"() {
		const sourceA = `package alpha; record A {}`;
		const sourceB = `package beta; record A {}`;
		const sourceC = `package gamma; import alpha.A; import beta.A;`
		const astA = grammar.parseSource(sourceA, "file-a");
		const astB = grammar.parseSource(sourceB, "file-b");
		const astC = grammar.parseSource(sourceC, "file-c");

		assert(() => semantics.compileSources([astA, astB, astC]), "throws", {
			message: [
				"Entity `A` was defined for a second time at",
				{ fileID: "file-c", offset: 43, length: 1 },
				"The first definition was at",
				{ fileID: "file-c", offset: 28, length: 1 },
			],
		});
	},
	"trivial"() {
		const source = `package example;`;
		const ast = grammar.parseSource(source, "test-file");

		const program = semantics.compileSources([ast]);
		assert(program.records, "is equal to", {});
		assert(program.functions, "is equal to", {});
	},
	"redefined-field-in-record"() {
		const source = `package example; record A { var f1: A; var f1: A; }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources([ast]), "throws", {
			message: [
				"The member `f1` was defined for a second time at",
				{ fileID: "test-file", offset: 43, length: 2 },
				"The first definition of `f1` was at",
				{ fileID: "test-file", offset: 32, length: 2 },
			],
		});
	},
	"undefined-type-referenced-in-field"() {
		const source = `package example; record A { var b: B; }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources([ast]), "throws", {
			message: [
				"Entity `B` has not been defined, but it was referenced at",
				{ fileID: "test-file", offset: 35, length: 1 },
			],
		});
	},
	"access-field-in-int"() {
		const source = `package example; record A { fn f(): Unit { var a: Int = 1; var b: A = a; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources([ast]), "throws", {
			message: [
				"A value with type `Int` at",
				{ fileID: "test-file", offset: 70, length: 1 },
				"cannot be converted to the type `example.A` as expected at",
				{ fileID: "test-file", offset: 63, length: 1 },
			],
		});
	},
	"return-too-many-values"() {
		const source = `package example; record A { fn f(): Int { return 1, 1; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources([ast]), "throws", {
			message: [
				"An expression has 2 values at",
				{ fileID: "test-file", offset: 49, length: 4 },
				"but 1 value was expected at",
				{ fileID: "test-file", offset: 36, length: 3 },
			],
		});
	},
	"return-too-few-values"() {
		const source = `package example; record A { fn f(): Int, Int { return 1; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources([ast]), "throws", {
			message: [
				"An expression has 1 value at",
				{ fileID: "test-file", offset: 54, length: 1 },
				"but 2 values were expected at",
				{ fileID: "test-file", offset: 36, length: 8 },
			],
		});
	},
	"return-expression-illegal-in-requires"() {
		const source = `package example; record A { fn f(): Boolean requires return { return true; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources([ast]), "throws", {
			message: [
				"A `return` expression cannot be used outside an `ensures` clause like it is at",
				{ fileID: "test-file", offset: 53, length: 6 },
			]
		});
	},
	"return-expression-illegal-in-body"() {
		const source = `package example; record A { fn f(): Boolean { return return; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources([ast]), "throws", {
			message: [
				"A `return` expression cannot be used outside an `ensures` clause like it is at",
				{ fileID: "test-file", offset: 53, length: 6 },
			]
		});
	},
	"return-expression-legal-in-ensures"() {
		const source = `package example; record A { fn f(): Boolean ensures return { return true; } }`;
		const ast = grammar.parseSource(source, "test-file");

		semantics.compileSources([ast]);
	},
};
