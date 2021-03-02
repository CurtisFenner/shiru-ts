import { SemanticError } from "./diagnostics";
import * as grammar from "./grammar";
import * as semantics from "./semantics";
import { assert } from "./test";

export const tests = {
	"redefine-class-same-source"() {
		const source = `package example; class A { } class A { }`;
		const ast = grammar.parseSource(source, "file-0");

		assert(() => semantics.compileSources([ast]), "throws", new SemanticError([
			"Object `example.A` was defined for a second time at",
			{ fileID: "file-0", offset: 35, length: 1 },
			"The first definition was at",
			{ fileID: "file-0", offset: 23, length: 1 },
		]));
	},
	"redefine-class-different-sources"() {
		const source0 = `package example; class A { } `;
		const ast0 = grammar.parseSource(source0, "file-0");

		const source1 = `package example; class A { } `;
		const ast1 = grammar.parseSource(source1, "file-1");

		assert(() => semantics.compileSources([ast0, ast1]), "throws", new SemanticError([
			"Object `example.A` was defined for a second time at",
			{ fileID: "file-1", offset: 23, length: 1 },
			"The first definition was at",
			{ fileID: "file-0", offset: 23, length: 1 },
		]));
	},
	"import-already-defined-name"() {
		const sourceA = `package alpha; class A {}`;
		const sourceB = `package beta; import alpha.A; class A {}`;
		const astA = grammar.parseSource(sourceA, "file-a");
		const astB = grammar.parseSource(sourceB, "file-b");

		assert(() => semantics.compileSources([astA, astB]), "throws", {
			message: [
				"Object `A` was defined for a second time at",
				{ fileID: "file-b", offset: 27, length: 1 },
				"The first definition was at",
				{ fileID: "file-b", offset: 36, length: 1 },
			],
		});
	},
	"import-name-already-imported"() {
		const sourceA = `package alpha; class A {}`;
		const sourceB = `package beta; class A {}`;
		const sourceC = `package gamma; import alpha.A; import beta.A;`
		const astA = grammar.parseSource(sourceA, "file-a");
		const astB = grammar.parseSource(sourceB, "file-b");
		const astC = grammar.parseSource(sourceC, "file-c");

		assert(() => semantics.compileSources([astA, astB, astC]), "throws", {
			message: [
				"Object `A` was defined for a second time at",
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
		assert(program.classes, "is equal to", {});
		assert(program.functions, "is equal to", {});
	},
};
