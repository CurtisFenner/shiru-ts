import { SemanticError } from "./diagnostics.js";
import * as grammar from "./grammar.js";
import * as semantics from "./semantics.js";
import { assert } from "./test.js";

export const tests = {
	"redefine-class-same-source"() {
		const source = `package example; record A { } record A { }`;
		const ast = grammar.parseSource(source, "file-0");

		assert(() => semantics.compileSources({ ast }), "throws", new SemanticError([
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

		assert(() => semantics.compileSources({ ast0, ast1 }), "throws", new SemanticError([
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

		assert(() => semantics.compileSources({ astA, astB }), "throws", {
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

		assert(() => semantics.compileSources({ astA, astB, astC }), "throws", {
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

		const program = semantics.compileSources({ ast });
		assert(program.records, "is equal to", {});
		assert(program.functions, "is equal to", {});
	},
	"redefined-field-in-record"() {
		const source = `package example; record A { var f1: A; var f1: A; }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `f1` was defined for a second time at",
				{ fileID: "test-file", offset: 43, length: 2 },
				"The first definition of `f1` was at",
				{ fileID: "test-file", offset: 32, length: 2 },
			],
		});
	},
	"redefined-field-as-method-in-record"() {
		const source = `package example; record A { var f1: A; fn f1(): Int { return 1; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `f1` was defined for a second time at",
				{ fileID: "test-file", offset: 42, length: 2 },
				"The first definition of `f1` was at",
				{ fileID: "test-file", offset: 32, length: 2 },
			],
		});
	},
	"undefined-type-referenced-in-field"() {
		const source = `package example; record A { var b: B; }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"Entity `B` has not been defined, but it was referenced at",
				{ fileID: "test-file", offset: 35, length: 1 },
			],
		});
	},
	"assign-int-to-record"() {
		const source = `
		package example;
		record A {
			fn f(): Unit {
				var a: Int = 1;
				var b: A = a;
			}
		}`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"A value with type `Int` at",
				{ fileID: "test-file", offset: 86, length: 1 },
				"cannot be converted to the type `example.A` as expected at",
				{ fileID: "test-file", offset: 82, length: 1 },
			],
		});
	},
	"access-field-in-int"() {
		const source = `
		package example;
		record A {
			fn f(): Unit {
				var a: Int = 1;
				var b: Int = a.x;
			}
		}`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The type `Int` is not a compound type so a field access is illegal at",
				{ fileID: "test-file", offset: 90, length: 1 },
			],
		});
	},
	"return-too-many-values"() {
		const source = `package example; record A { fn f(): Int { return 1, 1; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
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

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"An expression has 1 value at",
				{ fileID: "test-file", offset: 54, length: 1 },
				"but 2 values were expected at",
				{ fileID: "test-file", offset: 36, length: 8 },
			],
		});
	},
	"return-expression-illegal-in-requires"() {
		const source = `
		package example;
		record A {
			fn f(): Boolean requires return { return true; }
		}
		`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"A `return` expression cannot be used outside an `ensures` clause like it is at",
				{ fileID: "test-file", offset: 61, length: 6 },
			]
		});
	},
	"return-expression-illegal-in-body"() {
		const source = `package example; record A { fn f(): Boolean { return return; } }`;
		const ast = grammar.parseSource(source, "test-file");

		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"A `return` expression cannot be used outside an `ensures` clause like it is at",
				{ fileID: "test-file", offset: 53, length: 6 },
			]
		});
	},
	"return-expression-legal-in-ensures"() {
		const source = `
		package example;
		record A { fn f(): Boolean ensures return { return true; } }
		`;
		const ast = grammar.parseSource(source, "test-file");

		semantics.compileSources({ ast });
	},
	"no-such-interface"() {
		const source = `
		package example;
		record X[#T | #T is NoSuchInt] {}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"Entity `NoSuchInt` has not been defined, but it was referenced at",
				{ fileID: "test-file", offset: 42, length: 9 },
			],
		});
	},
	"no-such-type-variable"() {
		const source = `
		package example;
		record Main {
			fn f(a: #A): Int {
				return 0;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"Type variable `#A` has not been defined, but it was referenced at",
				{ fileID: "test-file", offset: 47, length: 2 },
			],
		});
	},
	"function-parameter-type-argument-does-not-satisfy-constraint"() {
		const source = `
		package example;
		interface Good {
		}

		record A[#T | #T is Good] {
		}

		record Main {
			fn f(a: A[Int]): Int {
				return 0;
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"There is no impl for `Int is example.Good` at",
				{ fileID: "test-file", offset: 106, length: 6 },
				"This impl is required by the constraint at",
				{ fileID: "test-file", offset: 60, length: 10 },
			],
		});
	},
	"record-type-satisfies-constraint"() {
		const source = `
		package example;
		interface Good {}

		record A[#T | #T is Good] {}

		record B {}

		impl B is Good {}

		record Main {
			fn f(a: A[B]): Int {
				return 0;
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		const compiled = semantics.compileSources({ ast });
	},
	"conflicting-simple-impl"() {
		const source = `
		package example;
		interface Good {}

		record A[#T] {}

		impl A[Int] is Good {}
		impl A[Int] is Good {}
		`;
		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The impl `example.A[Int] is example.Good` given at",
				{ fileID: "test-file", offset: 87, length: 19 },
				"conflicts with the impl `example.A[Int] is example.Good` given at",
				{ fileID: "test-file", offset: 62, length: 19 },
			],
		});
	},
	"conflicting-impl-universal-with-argument"() {
		const source = `
		package example;
		interface Good {}

		record A[#T] {}

		impl [#X] A[#X] is Good {}
		impl A[Int] is Good {}
		`;
		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The impl `example.A[Int] is example.Good` given at",
				{ fileID: "test-file", offset: 91, length: 19 },
				"conflicts with the impl `[#X] example.A[#X] is example.Good` given at",
				{ fileID: "test-file", offset: 62, length: 23 },
			],
		});
	},
	"conflicting-impl-universal-with-universal"() {
		const source = `
		package example;
		interface Good {}

		record A[#T] {}

		impl [#X] A[#X] is Good {}
		impl [#Y] A[#Y] is Good {}
		`;
		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The impl `[#Y] example.A[#Y] is example.Good` given at",
				{ fileID: "test-file", offset: 91, length: 23 },
				"conflicts with the impl `[#X] example.A[#X] is example.Good` given at",
				{ fileID: "test-file", offset: 62, length: 23 },
			],
		});
	},
	"type-parameter-does-not-satisfy-constraint"() {
		const source = `
		package example;
		interface Good {}

		record A[#T | #T is Good] {}

		record Main[#Q] {
			fn f(a: A[#Q]): Int {
				return 0;
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"There is no impl for `#Q is example.Good` at",
				{ fileID: "test-file", offset: 104, length: 5 },
				"This impl is required by the constraint at",
				{ fileID: "test-file", offset: 57, length: 10 },
			],
		});
	},
	"type-parameter-satisfies-constraint"() {
		const source = `
		package example;
		interface Good {}

		record A[#T | #T is Good] {}

		record Main[#Q | #Q is Good] {
			fn f(a: A[#Q]): Int {
				return 0;
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		const compiled = semantics.compileSources({ ast });
	},
	"missing-type-arguments-in-record-literal"() {
		const source = `
		package example;

		record A[#T] {
			var field: #T;
		}

		record B[#T] {
			fn f(t: #T): Int {
				var x: A[Int] = A{ field = t };
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The record `A` was given ",
				"0 ",
				"type parameters at",
				{ fileID: "test-file", offset: 120, length: 1 },
				"but 1 ",
				"type parameter was ",
				"expected at",
				{ fileID: "test-file", offset: 32, length: 2 },
			],
		});
	},
	"missing-type-arguments-in-interface-constraint"() {
		const source = `
		package example;

		interface I[#T] { }

		record A {}
		
		impl A is I {}
		`;
		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The interface `example.I` was given ",
				"0 ",
				"type parameters at",
				{ fileID: "test-file", offset: 73, length: 1 },
				"but 1 ",
				"type parameter was ",
				"expected at",
				{ fileID: "test-file", offset: 35, length: 2 },
			],
		});
	},
	"wrong-field-type-when-instantiated"() {
		const source = `
		package example;

		record A[#T] {
			var f: #T;

			fn field(s: A[Int]): #T {
				return s.f;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"A value with type `Int` at",
				{ fileID: "test-file", offset: 93, length: 3 },
				"cannot be converted to the type `#T` as expected at",
				{ fileID: "test-file", offset: 77, length: 2 },
			],
		});
	},
	"missing-impl-for-constraint-call"() {
		const source = `
		package example;

		interface I {
			fn get(): Int;
		}

		record R {
			fn main(): Int {
				return (R is I).get();
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"There is no impl for `example.R is example.I` at",
				{ fileID: "test-file", offset: 104, length: 8 },
			],
		});
	},
	"missing-fn-for-constraint-call"() {
		const source = `
		package example;

		interface I {
		}

		record R {
			fn main(): Int {
				return (R is I).get();
			}
		}

		impl R is I {}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The type `example.R is example.I` ",
				"does not have a function member named `get` ",
				"so the function call is illegal at",
				{ fileID: "test-file", offset: 95, length: 3 },
			],
		});
	},
	"missing-function-in-impl"() {
		const source = `
		package example;

		interface I {
			fn get(): Int;
		}

		record R {
		}

		impl R is I {
			// Missing fn get
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The impl `example.R is example.I` ",
				"is missing member `get` at",
				{ fileID: "test-file", offset: 80, length: 11 },
				"However, the interface `example.I` requires a `get` member at",
				{ fileID: "test-file", offset: 43, length: 3 },
			],
		});
	},
	"extra-fn-in-impl"() {
		const source = `
		package example;

		interface I {
			fn get(): Int;
		}

		record R {
		}

		impl R is I {
			// Extra fn
			fn set(n: Int): Unit {
			}

			fn get(): Int {
				return 3;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The impl `example.R is example.I` ",
				"defines a member `set` at",
				{ fileID: "test-file", offset: 115, length: 3 },
				"However, the interface `example.I` defined at",
				{ fileID: "test-file", offset: 33, length: 1 },
				"does not have a member named `set`.",
			],
		});
	},
	"wrong-fn-signature-in-impl"() {
		const source = `
		package example;

		interface I {
			fn get(a: Int): Int;
		}

		record R {
		}

		impl R is I {
			// Wrong type
			fn get(a: Boolean): Int {
				return 42;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The type `Boolean` ",
				"of the 1st parameter ",
				"of the impl member `get` at",
				{ fileID: "test-file", offset: 130, length: 7 },
				"does not match the type `Int` ",
				"as required of a `example.R is example.I` by the interface member defined at",
				{ fileID: "test-file", offset: 50, length: 3 },
			],
		});
	},
	"body-must-type-check-in-impl"() {
		const source = `
		package example;

		interface I {
			fn get(): Int;
		}

		record R {
		}

		impl R is I {
			fn get(): Int {
				// bad type
				return "str";
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"A value with type `Bytes` at",
				{ fileID: "test-file", offset: 140, length: 5 },
				"cannot be converted to the type `Int` as expected at",
				{ fileID: "test-file", offset: 107, length: 3 },
			],
		});
	},
	"redefine-var-in-record"() {
		const source = `
		package example;

		record R {
			var field: Int;
			var field: Int;
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `field` was defined for a second time at",
				{ fileID: "test-file", offset: 60, length: 5 },
				"The first definition of `field` was at",
				{ fileID: "test-file", offset: 41, length: 5 },
			],
		});
	},
	"redefine-var-in-enum"() {
		const source = `
		package example;

		enum E {
			var variant: Int;
			var variant: Int;
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `variant` was defined for a second time at",
				{ fileID: "test-file", offset: 60, length: 7 },
				"The first definition of `variant` was at",
				{ fileID: "test-file", offset: 39, length: 7 },
			],
		});
	},
	"redefine-var-as-fn-in-record"() {
		const source = `
		package example;

		record R {
			var member: Int;
			fn member(): Int {
				return 1;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `member` was defined for a second time at",
				{ fileID: "test-file", offset: 60, length: 6 },
				"The first definition of `member` was at",
				{ fileID: "test-file", offset: 41, length: 6 },
			],
		});
	},
	"redefine-var-as-fn-in-enum"() {
		const source = `
		package example;

		enum E {
			var member: Int;
			fn member(): Int {
				return 1;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `member` was defined for a second time at",
				{ fileID: "test-file", offset: 58, length: 6 },
				"The first definition of `member` was at",
				{ fileID: "test-file", offset: 39, length: 6 },
			],
		});
	},
	"redefine-fn-in-record"() {
		const source = `
		package example;

		record R {
			fn get(): Int { return 1; }
			fn get(): Int { return 1; }
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `get` was defined for a second time at",
				{ fileID: "test-file", offset: 71, length: 3 },
				"The first definition of `get` was at",
				{ fileID: "test-file", offset: 40, length: 3 },
			],
		});
	},
	"redefine-fn-in-enum"() {
		const source = `
		package example;

		enum E {
			fn get(): Int { return 1; }
			fn get(): Int { return 1; }
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `get` was defined for a second time at",
				{ fileID: "test-file", offset: 69, length: 3 },
				"The first definition of `get` was at",
				{ fileID: "test-file", offset: 38, length: 3 },
			],
		});
	},
	"redefine-fn-in-interface"() {
		const source = `
		package example;

		interface I {
			fn alpha(): Int;
			fn alpha(): Int;
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `alpha` was defined for a second time at",
				{ fileID: "test-file", offset: 63, length: 5 },
				"The first definition of `alpha` was at",
				{ fileID: "test-file", offset: 43, length: 5 },
			],
		});
	},
	"redefine-fn-in-impl"() {
		const source = `
		package example;

		interface I {
			fn alpha(): Int;
		}

		record R {}

		impl R is I {
			fn alpha(): Int {
				return 1;
			}
			fn alpha(): Int {
				return 1;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `alpha` was defined for a second time at",
				{ fileID: "test-file", offset: 139, length: 5 },
				"The first definition of `alpha` was at",
				{ fileID: "test-file", offset: 99, length: 5 },
			],
		});
	},
	"impl-has-too-few-parameters"() {
		const source = `
		package example;

		interface I {
			fn alpha(p: Int): Int;
		}

		record R {}

		impl R is I {
			fn alpha(): Int {
				return 1;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The impl member `alpha` has ",
				"0 parameters at",
				{ fileID: "test-file", offset: 110, length: 2 },
				"However, `example.R is example.I` needs 1, as defined at",
				{ fileID: "test-file", offset: 48, length: 8 },
			],
		});
	},
	"record-literal-with-duplicated-field"() {
		const source = `
		package example;

		record R {
			var f: Int;
		}
		
		record Main {
			fn main(): R {
				return R{
					f = 1,
					f = 1,
				};
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The field `f` was initialized a second time at",
				{ fileID: "test-file", offset: 121, length: 1 },
				"The first initialization was at",
				{ fileID: "test-file", offset: 109, length: 1 },
			],
		});
	},
	"enum-literal-with-duplicated-variant"() {
		const source = `
		package example;

		enum E {
			var f: Int;
		}
		
		record Main {
			fn main(): E {
				return E{
					f = 1,
					f = 1,
				};
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The variant `f` was initialized a second time at",
				{ fileID: "test-file", offset: 119, length: 1 },
				"The first initialization was at",
				{ fileID: "test-file", offset: 107, length: 1 },
			],
		});
	},
	"enum-literal-with-multiple-variants"() {
		const source = `
		package example;

		enum E {
			var a: Int;
			var b: Int;
		}
		
		record Main {
			fn main(): E {
				return E{
					a = 1,
					b = 1,
				};
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The initialization of enum type `example.E` ",
				"includes a second variant `b` at",
				{ fileID: "test-file", offset: 134, length: 1 },
				"The first variant `a` is included at",
				{ fileID: "test-file", offset: 122, length: 1 },
			],
		});
	},
	"enum-literal-with-non-existent-variant"() {
		const source = `
		package example;

		enum E {
			var a: Int;
			var b: Int;
		}
		
		record Main {
			fn main(): E {
				return E{
					c = 1,
				};
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The enum type `example.E` ",
				"does not have a variant called `c`, ",
				"so the initialization is illegal at",
				{ fileID: "test-file", offset: 122, length: 1 },
			],
		});
	},
	"is-test-on-record"() {
		const source = `
		package example;

		record R {
			var f: Int;
		}
		
		record Main {
			fn main(): Boolean {
				return R{f = 1} is f;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The type `example.R` is not an enum type, ",
				"so the `is` test is illegal at",
				{ fileID: "test-file", offset: 116, length: 4 },
			],
		});
	},
	"is-test-on-multi-value"() {
		const source = `
		package example;

		enum E {
			var f: Int;
		}
		
		record Main {
			fn two(): E, E {
				return E{f = 1}, E{f = 1};
			}

			fn main(): Boolean {
				return Main.two() is f;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"An expression has 2 values and so cannot be grouped ",
				"by an `is` test at",
				{ fileID: "test-file", offset: 162, length: 10 },
			],
		});
	},
	"attempt-assert-non-integer"() {
		const source = `
		package example;
		
		record Main {
			fn main(): Boolean {
				assert 10;
				return true;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"A contract expression with type `Int` at",
				{ fileID: "test-file", offset: 74, length: 2 },
				"cannot be converted to the type `Boolean` as required of ",
				"`assert` conditions.",
			],
		});
	},
	"attempt-assert-tuple"() {
		const source = `
		package example;
		
		record Main {
			fn twoBooleans(): Boolean, Boolean {
				return true, true;
			}

			fn main(): Boolean {
				assert Main.twoBooleans();
				return true;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"An expression has 2 values and so cannot be grouped ",
				"by a `assert` operation at",
				{ fileID: "test-file", offset: 143, length: 18 },
			],
		});
	},
	"attempt-ensure-non-boolean-in-unused-interface"() {
		const source = `
		package example;
		
		interface I {
			fn f(): Int
			ensures 5;
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"A contract expression with type `Int` at",
				{ fileID: "test-file", offset: 65, length: 1 },
				"cannot be converted to the type `Boolean` as required of ",
				"`ensures` conditions.",
			],
		});
	},
	"attempt-require-in-impl-fn"() {
		const source = `
		package example;

		interface I {
			fn f(a: Int): Int;
		}

		record R {}

		impl R is I {
			fn f(a: Int): Int
			requires a == 1 {
				return a;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"The member `f` of impl `",
				"example.R is example.I` declares an additional precondition at",
				{ fileID: "test-file", offset: 128, length: 6 },
				"However, impls may not state additional preconditions; ",
				"preconditions on the interface are automatically applied.",
			],
		});
	},
	"attempt-impl-with-types-not-satisfying-interface-subject-constraints"() {
		const source = `
		package example;

		interface Good {}

		interface I[#X | #X is Good] {}

		record R {}

		impl R is I[R] {}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"There is no impl for `example.R is example.Good` at",
				{ fileID: "test-file", offset: 99, length: 9 },
				"This impl is required by the constraint at",
				{ fileID: "test-file", offset: 61, length: 10 },
			],
		});
	},
	"attempt-impl-with-this-subject-not-satisfying-interface-constraints"() {
		const source = `
		package example;

		interface Good {}

		interface I[This is Good] {}

		record R {}

		impl R is I {}
		`;

		const ast = grammar.parseSource(source, "test-file");
		assert(() => semantics.compileSources({ ast }), "throws", {
			message: [
				"There is no impl for `example.R is example.Good` at",
				{ fileID: "test-file", offset: 96, length: 6 },
				"This impl is required by the constraint at",
				{ fileID: "test-file", offset: 56, length: 12 },
			],
		});
	},
	"attempt-this-constraint-in-record-type-parameters"() {
		const source = `
		package example;

		interface I {}

		record R[#T, This is I] {}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"Expected a type variable at",
				{ fileID: "test-file", offset: 54, length: 4 },
			],
		});
	},
	"attempt-eq-on-records-outside-proof-context"() {
		const source = `
		package example;

		record R {
			fn main(): Int {
				// This is OK since assert introduces a proof context.
				assert R{} == R{};

				// This is NOT OK since there is no surrounding proof context.
				var b: Boolean = R{} == R{};
				return 1;
			}
		}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"The operation `==` ",
				"cannot be used outside a proof context as it is at",
				{
					fileID: "test-file",
					offset: 229,
					length: 2,
				},
			],
		});
	},
	"attempt-not-eq-on-records-outside-proof-context"() {
		const source = `
		package example;

		record R {
			fn main(): Int {
				// This is OK since assert introduces a proof context.
				assert R{} != R{};

				// This is NOT OK since there is no surrounding proof context.
				var b: Boolean = R{} != R{};
				return 1;
			}
		}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"The operation `!=` ",
				"cannot be used outside a proof context as it is at",
				{
					fileID: "test-file",
					offset: 229,
					length: 2,
				},
			],
		});
	},
	"attempt-arithmetic-with-multiple-values-lhs"() {
		const source = `
		package example;

		record R {
			fn two(): Int, Int {
				return 1, 2;
			}

			fn main(): Int {
				return R.two() + 3;
			}
		}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"An expression has 2 values and so cannot be grouped ",
				"by a `+` operation at",
				{ fileID: "test-file", offset: 112, length: 7 },
			],
		});
	},
	"attempt-arithmetic-with-multiple-values-rhs"() {
		const source = `
		package example;

		record R {
			fn two(): Int, Int {
				return 1, 2;
			}

			fn main(): Int {
				return 3 + R.two();
			}
		}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"An expression has 2 values and so cannot be grouped ",
				"by a `+` operation at",
				{ fileID: "test-file", offset: 116, length: 7 },
			],
		});
	},
	"attempt-to-add-boolean-to-int"() {
		const source = `
		package example;

		record R {
			fn main(): Int {
				return 1 + true;
			}
		}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"The operator `+` with type `Int` on the left side expects a value with type `Int` on the right side, but one of type `Boolean` was given at",
				{ fileID: "test-file", offset: 69, length: 4 },
			],
		});
	},
	"attempt-bounds-on-ints-outside-proof-context"() {
		const source = `
		package example;

		record R {
			fn f(a: Int, b: Int): Int {
				if a bounds b {
					return 1;
				} else {
					return 2;
				}
			}
		}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"The operation `bounds` ",
				"cannot be used outside a proof context as it is at",
				{ fileID: "test-file", offset: 74, length: 6 },
			],
		});
	},
	"impl-cannot-refer-to-interface-type-parameter"() {
		const source = `
			package example;
	
			interface Consumer[#X] {
				fn consume(t: #X): Int;
			}

			record FromAny[#T] {
				fn zero(): Int {
					return 0;
				}
			}

			record Empty {}

			impl Empty is Consumer[String] {
				fn consume(t: String): Int {
					return FromAny[#X].zero();
				}
			}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"Type variable `#X` has not been defined, but it was referenced at",
				{ fileID: "test-file", offset: 266, length: 2 },
			],
		});
	},
	"generic-impl"() {
		const source = `
		package example;

		interface Show {
			fn show(t: This): String;
		}
		
		record Empty {
		}
		
		impl Empty is Show {
			fn show(s: Empty): String {
				return "Empty{}";
			}
		}
		
		record Box[#T] {
			var boxed: #T;
		}
		
		impl [#T | #T is Show] Box[#T] is Show {
			fn show(s: Box[#T]): String {
				return "Box{boxed = " ++ ((#T is Show).show(s.boxed) ++ "}");
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		semantics.compileSources({ ast });
	},
	"comparison-has-higher-precedence-than-addition"() {
		const source = `
		package example;

		record R {
			fn f(): Boolean {
				return 1 + 2 == 3;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		semantics.compileSources({ ast });
	},
	"plus-requires-parentheses"() {
		const source = `
		package example;

		record R {
			fn f(): Boolean {
				return true and 3 < 4 > 5;
			}
		}
		`;

		assert(() => {
			const ast = grammar.parseSource(source, "test-file");
			semantics.compileSources({ ast })
		}, "throws", {
			message: [
				"The operators `<` and `>` at",
				{ fileID: "test-file", offset: 77, length: 1 },
				"and at",
				{ fileID: "test-file", offset: 81, length: 1 },
				"have ambiguous precedence, and require parentheses to specify precedence."
			],
		});
	},
};
