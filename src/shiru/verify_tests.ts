import * as grammar from "./grammar";
import * as ir from "./ir";
import * as semantics from "./semantics";
import * as verify from "./verify";
import { assert } from "./test";

export const tests = {
	"empty-verification"() {
		const program: ir.Program = {
			records: {},
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
};
