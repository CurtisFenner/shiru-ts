import * as grammar from "./grammar";
import * as ir from "./ir";
import * as semantics from "./semantics";
import * as uf from "./uf";
import * as verify from "./verify";
import { assert, spec, specDescribe } from "./test";

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
	"impl-must-ensure-interface-postcondition"() {
		const source = `
		package example;

		record R {}

		interface I {
			fn f(): Boolean
			ensures return;
		}

		impl R is I {
			fn f(): Boolean {
				return false;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-postcondition",
				postconditionLocation: {
					fileID: "test-file", offset: 82, length: 6,
				},
				returnLocation: {
					fileID: "test-file", offset: 136, length: 13,
				},
			},
		]);
	},
	"impl-may-assume-interface-precondition"() {
		const source = `
		package example;

		record R {}

		interface I {
			fn f(a: Boolean): Boolean
			requires a;
		}

		impl R is I {
			fn f(b: Boolean): Boolean {
				assert b;
				return false;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"preconditions-of-calls-in-unimplemented-interface-requires-must-be-met"() {
		const source = `
		package example;

		record R {
			fn picky(n: Int): Boolean
			requires n == 32 {
				return true;
			}
		}

		interface I {
			fn i(k: Int): Int
			requires R.picky(k);
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 161, length: 10 },
				preconditionLocation: { fileID: "test-file", offset: 75, length: 7 },
			},
		]);
	},
	"preconditions-of-calls-in-unimplemented-interface-ensures-must-be-met"() {
		const source = `
		package example;

		record R {
			fn picky(n: Int): Boolean
			requires n == 32 {
				return true;
			}
		}

		interface I {
			fn i(): Int
			ensures R.picky(return);
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 154, length: 15 },
				preconditionLocation: { fileID: "test-file", offset: 75, length: 7 },
			},
		]);
	},
	"unimplemented-interface-may-assume-requires-in-ensures"() {
		const source = `
		package example;

		record R {
			fn picky(n: Int): Boolean
			requires n == 32 {
				return true;
			}
		}

		interface I {
			fn i(k: Int): Int
			requires k == 32
			ensures R.picky(k);
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"impl-may-assume-interface-using-type-arg-requires"() {
		const source = `
		package example;

		record R {}

		interface FavoriteInt {
			fn favoriteInt(): Int;
		}

		interface I[#T | #T is FavoriteInt] {
			fn f(a: Boolean): Boolean
			requires (#T is FavoriteInt).favoriteInt() == 10;
		}

		impl R is FavoriteInt {
			fn favoriteInt(): Int {
				return 7;
			}
		}

		impl R is I[R] {
			fn f(b: Boolean): Boolean {
				assert (R is FavoriteInt).favoriteInt() == 10;
				return false;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"refutes-recursive-object-containing-itself"() {
		const source = `
		package example;

		record Cons[#T] {
			var head: #T;
			var tail: List[#T];
		}

		enum List[#T] {
			var cons: Cons[#T];
			var nil: Unit;
		}

		record Main {
			fn t(a: List[Int]): Int {
				if a is cons {
					assert a.cons.tail != a;
				}
				return 5;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"attempt-to-claim-recursive-object-contains-itself"() {
		const source = `
		package example;

		record Cons[#T] {
			var head: #T;
			var tail: List[#T];
		}

		enum List[#T] {
			var cons: Cons[#T];
			var nil: Unit;
		}

		record Main {
			fn t(a: List[Int]): Int {
				if a is cons {
					// This is impossible.
					assert a.cons.tail == a;
				}
				return 5;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-assert",
				assertLocation: {
					fileID: "test-file",
					offset: 247,
					length: 24,
				},
			},
		]);
	},
	"clausifyNotSmallerThan-simple"() {
		const smt = new uf.UFTheory();
		smt.addConstraint([
			smt.createConstant(ir.T_BOOLEAN, true),
		]);
		const eqF = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const negF = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");
		const ltF = smt.createFunction(ir.T_BOOLEAN, {
			interpreter(...args: (unknown | null)[]): unknown | null {
				if (args.length !== 2) {
					throw new Error("unexpected");
				}
				const a = args[0];
				const b = args[1];
				if (a === null || b === null) {
					return null;
				}
				if (typeof a !== "number" || typeof b !== "number") {
					throw new Error("unexpected");
				}
				return a < b;
			},
		}, "<");

		const isSatisfiable = (clauses: uf.ValueID[][]): boolean => {
			smt.pushScope();
			for (let i = 0; i < clauses.length; i++) {
				smt.addConstraint(clauses[i]);
			}
			const result = smt.attemptRefutation();
			smt.popScope();
			return result !== "refuted";
		}

		const n1 = smt.createConstant(ir.T_INT, 1);
		const n2 = smt.createConstant(ir.T_INT, 2);
		const n3 = smt.createConstant(ir.T_INT, 3);

		assert(isSatisfiable([[smt.createApplication(ltF, [n1, n1])]]), "is equal to", false);
		assert(isSatisfiable([[smt.createApplication(ltF, [n2, n1])]]), "is equal to", false);
		assert(isSatisfiable([[smt.createApplication(ltF, [n1, n2])]]), "is equal to", true);
		assert(isSatisfiable([[smt.createApplication(ltF, [n1, n3])]]), "is equal to", true);

		const testCases = [
			{ lefts: [1, 2], rights: [1, 2], less: false },
			{ lefts: [1, 1], rights: [1, 1], less: false },
			{ lefts: [1, 1], rights: [2, 2], less: true },
			{ lefts: [1, 1], rights: [1, 2], less: true },
			{ lefts: [2, 1], rights: [1, 2], less: false },
			{ lefts: [], rights: [1], less: true },
			{ lefts: [1], rights: [], less: false },
		];

		assert(lexicographicComparison([1, 2, 3], [4]), "is equal to", -1);
		assert(lexicographicComparison([4], [1, 2, 3]), "is equal to", +1);
		assert(lexicographicComparison([1, 2, 3], [1, 2, 3]), "is equal to", 0);
		assert(lexicographicComparison([1, 2, 3], [1, 2]), "is equal to", +1);
		assert(lexicographicComparison([1, 2], [1, 2, 3]), "is equal to", -1);

		for (const testCase of testCases) {
			// Check that the test case expectation is correct.
			assert(testCase.less, "is equal to",
				specDescribe(lexicographicComparison(testCase.lefts, testCase.rights) === -1,
					JSON.stringify(testCase)));

			// Check that clausifyNotSmallerThan agrees with the direct check.
			const lefts = testCase.lefts.map(n => smt.createConstant(ir.T_INT, n));
			const rights = testCase.rights.map(n => smt.createConstant(ir.T_INT, n));
			const clauses = verify.clausifyNotSmallerThan(smt, { eqF, ltF, negF }, lefts, rights);
			assert(
				isSatisfiable(clauses),
				"is equal to",
				specDescribe(!testCase.less, "!testCase.less", "case(" + JSON.stringify(testCase) + ")"),
			);
		}
	},
	"add-zero-is-identify"() {
		const source = `
		package example;
		record Main {
			fn zeroIsRightIdentity(a: Int): Boolean
			ensures a + 0 == a {
				return true;
			}
			fn zeroIsLeftIdentity(a: Int): Boolean
			ensures 0 + a == a {
				return true;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"int-subtract-then-add-is-identity"() {
		const source = `
		package example;
		record Main {
			fn subtractThenAddIsIdentity(n: Int, k: Int): Boolean
			ensures (n - k) + k == n {
				assert (n - k) + k == ((n + 0) - k) + k;
				assert (n - k) + k == (n + (0 - k)) + k;
				assert (0 - k) + k == k + (0 - k);
				return true;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"int-addition-associative"() {
		const source = `
		package example;
		record Main {
			fn isAssociative(a: Int, b: Int, c: Int): Boolean
			ensures (a + b) + c == a + (b + c) {
				return true;
			}
		}
		`;

		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"logical-operations-short-circuit-okay"() {
		const source = `
		package example;

		record Main {
			fn evil(): Boolean
			requires false {
				return false;
			}

			fn andLeftFalse(): Boolean {
				return false and Main.evil();
			}

			fn orLeftTrue(): Boolean {
				return true or Main.evil();
			}

			fn impliesLeftFalse(): Boolean {
				return false implies Main.evil();
			}
		}
		`;

		// All of these operations have a short-circuit move which means the
		// precondition need not hold.
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", []);
	},
	"logical-operations-short-circuit-invalid"() {
		const source = `
		package example;

		record Main {
			fn evil(): Boolean
			requires false {
				return false;
			}

			fn andLeftFalse(): Boolean {
				return true and Main.evil();
			}

			fn orLeftTrue(): Boolean {
				return false or Main.evil();
			}

			fn impliesLeftFalse(): Boolean {
				return true implies Main.evil();
			}
		}
		`;

		// None of these can be shortcircuited.
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 155, length: 11 },
				preconditionLocation: { fileID: "test-file", offset: 71, length: 5 },
			},
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 224, length: 11 },
				preconditionLocation: { fileID: "test-file", offset: 71, length: 5 },
			},
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 303, length: 11 },
				preconditionLocation: { fileID: "test-file", offset: 71, length: 5 },
			},
		]);
	},
	"do-not-shortcircuit-implies-on-right"() {
		const source = `
		package example;

		record Main {
			fn evil(): Boolean
			requires false {
				return false;
			}

			fn impliesRightTrue(): Boolean {
				return Main.evil() implies true;
			}
		}
		`;

		// implies is only shortcircuited on the left operand, not the right.
		const ast = grammar.parseSource(source, "test-file");
		const program = semantics.compileSources({ ast });
		const failures = verify.verifyProgram(program);
		assert(failures, "is equal to", [
			{
				tag: "failed-precondition",
				callLocation: { fileID: "test-file", offset: 150, length: 11 },
				preconditionLocation: { fileID: "test-file", offset: 71, length: 5 },
			},
		]);
	},
};

function lexicographicComparison<T>(left: T[], right: T[]): -1 | 0 | 1 {
	for (let i = 0; true; i++) {
		if (i < left.length && i < right.length) {
			if (left[i] < right[i]) {
				return -1;
			} else if (right[i] < left[i]) {
				return +1;
			}
		} else {
			if (i < left.length) {
				return +1;
			} else if (i < right.length) {
				return -1;
			} else {
				return 0;
			}
		}
	}
}
