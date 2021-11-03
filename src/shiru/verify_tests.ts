import * as grammar from "./grammar";
import * as ir from "./ir";
import * as semantics from "./semantics";
import * as verify from "./verify";
import { assert } from "./test";

export const tests = {
	"empty-verification"() {
		const program: ir.Program = {
			records: {},
			enums: {},
			functions: {},
			interfaces: {},
			foreign: {},
			globalVTableFactories: {},
		};
		assert(verify.verifyProgram(program), "is equal to", []);
	},
	"basic-requires-fails"() {
		const source = `
		package example;
		record A {
			fn isGood(n: Int): Boolean {
				return n == 7;
			}

			fn picky(n: Int): Int
			requires A.isGood(n) {
				return n + n;
			}

			fn main(): Int {
				return A.picky(3);
			}
		}`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 196, length: 10 },
				preconditionLocation: { fileID: "test-file", offset: 127, length: 11 },
			}
		]);
	},
	"basic-requires-satisfied-by-if"() {
		const source = `
		package example;
		record A {
			fn isGood(n: Int): Boolean {
				return n == 7;
			}

			fn picky(n: Int): Int
			requires A.isGood(n) {
				return n + n;
			}

			fn main(x: Int): Int {
				if A.isGood(x) {
					return A.picky(x);
				}
				return 0;
			}
		}`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"basic-requires-satisfied-by-precondition"() {
		const source = `
		package example;
		record A {
			fn isGood(n: Int): Boolean {
				return n == 7;
			}

			fn picky(n: Int): Int
			requires A.isGood(n) {
				return n + n;
			}

			fn main(x: Int): Int
			requires A.isGood(x) {
				return A.picky(x);
			}
		}`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"basic-ensures-fails"() {
		const source = `
		package example;
		record A {
			fn isGood(n: Int): Boolean {
				return n == 7;
			}

			fn main(x: Int, y: Int): Int
			ensures A.isGood(return) {
				if A.isGood(x) {
					return x;
				}
				return y;
			}
		}`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-postcondition",
				returnLocation: { fileID: "test-file", offset: 198, length: 9 },
				postconditionLocation: { fileID: "test-file", offset: 133, length: 16 },
			},
		]);
	},
	"basic-ensures-satisfied-by-precondition"() {
		const source = `
		package example;
		record A {
			fn isGood(n: Int): Boolean {
				return n == 7;
			}

			fn main(x: Int, y: Int): Int
			requires A.isGood(x) or A.isGood(y)
			ensures A.isGood(return) {
				if A.isGood(x) {
					return x;
				}
				return y;
			}
		}`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"basic-ensures-satisfied-by-postcondition"() {
		const source = `
		package example;
		record A {
			fn isGood(n: Int): Boolean
			ensures n == 7 implies return {
				return n == 7;
			}

			fn m(x: Int): Int
			requires x == 7
			ensures A.isGood(return) {
				return x;
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"constant-arithmetic"() {
		const source = `
		package example;

		record Main {
			fn main(x: Int): Int
			requires x == 1
			ensures return == 3 {
				return x + 2;
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"ill-formed-ensures"() {
		const source = `
		package example;

		record Main {
			fn justOne(x: Int): Boolean
			requires x == 1
			ensures return {
				return true;
			}

			fn problematic(): Int
			// this call is not well-formed since the signature does not ensure
			// the precondition that return == 1
			ensures Main.justOne(return) {
				return 1;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 277, length: 20 },
				preconditionLocation: { fileID: "test-file", offset: 80, length: 6 },
			},
		]);
	},
	"precondition-in-ensures-satisfied-by-implictation"() {
		const source = `
		package example;

		record Main {
			fn justOne(x: Int): Boolean
			requires x == 1
			ensures return {
				return true;
			}

			fn problematic(): Int
			ensures return == 1 implies Main.justOne(return) {
				return 1;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"precondition-in-ensures-satisfied-by-previous-ensures"() {
		const source = `
		package example;

		record Main {
			fn justOne(x: Int): Boolean
			requires x == 1
			ensures return {
				return true;
			}

			fn problematic(): Int
			ensures return == 1
			// the precondition is satisfied by the previous ensures
			ensures Main.justOne(return) {
				return 1;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"recursive-ensures"() {
		const source = `
		package example;

		record R {
			fn dec(n: Int): Int
			ensures n < 0 or return == R.dec(n - 1) {
				if n < 0 {
					return 0;
				}
				return R.dec(n - 1);
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"empty-function-missing-return"() {
		const source = `
		package example;

		record Main {
			fn f(): Int {
			}
		}
		`

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-return",
				blockEndLocation: { fileID: "test-file", offset: 57, length: 1 },
			}
		]);
	},
	"fn-need-not-return-if-else-unreachable"() {
		const source = `
		package example;

		record Main {
			fn f(b: Boolean): Int
			requires b {
				if b {
					return 1;
				} else {
					unreachable;
				}
			}
		}
		`

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"fn-need-not-return-if-then-exhaustive"() {
		const source = `
		package example;

		record Main {
			fn f(): Int {
				if true {
					return 1;
				}
			}
		}
		`

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"ensures-enum-literal-variant"() {
		const source = `
		package example;

		enum E {
			var a: Int;
			var b: Boolean;

			fn makeInt(n: Int): E
			ensures return is a
			ensures return.a == n {
				return E{a = n};
			}
		}
		`;
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"accessing-variant-requires-variant-is-valid"() {
		const source = `
		package example;

		enum E {
			var a: Int;
			var b: Int;

			fn getB(e: E): Int {
				return e.b;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-variant",
				enumType: "example.E",
				variant: "b",
				accessLocation: { fileID: "test-file", offset: 100, length: 1 },
			},
		]);
	},
	"variant-tag-is-bounded"() {
		const source = `
		package example;

		enum E {
			var a: Int;
			var b: Int;
			
			fn getB(e: E): E
			ensures return is a or return is b {
				return e;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"all-variants-handled-by-if-branches"() {
		const source = `
		package example;

		enum E {
			var a: Int;
			var b: Int;
			
			fn getB(e: E): Int {
				if e is a {
					return 1;
				} else if e is b {
					return 2;
				}
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"single-variant-enum-requires-no-is-test"() {
		const source = `
		package example;

		enum E {
			var only: Int;
			
			fn getB(e: E): Int {
				// Since there is only one branch, this is legal:
				return e.only;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"simple-cons-list-with-head-and-tails-methods"() {
		const source = `
		package example;

		record Cons[#T] {
			var head: #T;
			var tail: List[#T];
		}

		enum List[#T] {
			var cons: Cons[#T];
			var nil: Unit;

			fn head(self: List[#T]): #T
			requires self is cons {
				return self.cons.head;
			}

			fn tail(self: List[#T]): List[#T]
			requires self is cons {
				return self.cons.tail;
			}

			fn concat(left: List[#T], right: List[#T]): List[#T] {
				if left is nil {
					return right;
				} else if right is nil {
					return left;
				}

				return List[#T]{
					cons = Cons[#T]{
						head = left.head(),
						tail = left.tail().concat(right),
					},
				};
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"fn-behavior-depends-on-type-argument"() {
		const source = `
		package example;

		record Gen[#T] {
			fn depends(): Int {
				// N.B.: The solver does not (yet?) know about parametricity,
				// so it cannot realize that this function must have the same
				// behavior regardless of the type argument #T.
				return 1;
			}
		}

		record Main {
			fn main(): Boolean {
				assert Gen[Int].depends() == 1 implies Gen[Int].depends() == 1;

				// This does not follow because Shiru's verifier does not assume
				// that functions are parametric; Int and Boolean could have
				// different behavior.
				assert Gen[Int].depends() == 1 implies Gen[Boolean].depends() == 1;

				return true;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-assert",
				assertLocation: { fileID: "test-file", offset: 545, length: 67 },
			},
		]);
	},
	"type-argument-not-opaque-in-requires"() {
		const source = `
		package example;

		record Gen[#T] {
			fn depends(): Int {
				// N.B.: The solver does not (yet?) know about parametricity,
				// so it cannot realize that this function must have the same
				// behavior regardless of the type argument #T.
				return 1;
			}
		}

		record Inspector[#T] {
			fn inspect(a: Int): Boolean
			requires Gen[#T].depends() == a {
				return false;
			}
		}

		record Main {
			fn main(): Boolean {
				return Inspector[Int].inspect(Gen[Int].depends());
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"type-argument-not-opaque-in-ensures"() {
		const source = `
		package example;

		record Gen[#T] {
			fn depends(): Int {
				// N.B.: The solver does not (yet?) know about parametricity,
				// so it cannot realize that this function must have the same
				// behavior regardless of the type argument #T.
				return 1;
			}
		}

		record Inspector[#T] {
			fn produce(): Int
			ensures return == Gen[#T].depends() {
				return Gen[#T].depends();
			}
		}

		record Main {
			fn main(): Boolean {
				assert Inspector[Int].produce() == Gen[Int].depends();
				return false;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
};
