import * as grammar from "./grammar";
import * as ir from "./ir";
import * as semantics from "./semantics";
import * as verify from "./verify";
import { assert } from "./test";

export const tests = {
	"basic-verification"() {
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
};
