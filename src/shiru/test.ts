import * as data_tests from "./data_tests";
import * as egraph_tests from "./egraph_tests";
import * as grammar_tests from "./grammar_tests";
import * as interpreter_tests from "./interpreter_tests";
import * as lexer_tests from "./lexer_tests";
import * as parser_tests from "./parser_tests";
import * as sat_tests from "./sat_tests";
import * as semantics_tests from "./semantics_tests";
import * as smt_tests from "./smt_tests";
import * as uf_tests from "./uf_tests";
import * as verify_tests from "./verify_tests";

import * as util from "util";

export type Run = PassRun | FailRun;

export interface PassRun {
	name: string,
	type: "pass"
}

export interface FailRun {
	name: string,
	type: "fail",
	exception: any,
}

export class TestRunner {
	runs: Run[] = [];

	constructor(private testNameFilter?: string) { }

	runTest(name: string, body: () => void) {
		if (name.indexOf(this.testNameFilter || "") < 0) {
			return;
		}

		try {
			body();
			this.runs.push({ name, type: "pass" });
			return;
		} catch (e) {
			this.runs.push({ name, type: "fail", exception: e });
		}
	}

	runTests(title: string, obj: { [k: string]: () => void }) {
		for (let k in obj) {
			this.runTest(title + "." + k, obj[k]);
		}
	}

	printReport() {
		const passed = this.runs.filter(x => x.type == "pass");
		const failed: FailRun[] = this.runs.filter(x => x.type == "fail") as FailRun[];

		for (let pass of passed) {
			console.log("  pass  " + pass.name);
		}

		for (let failure of failed) {
			console.log("\u{25be}".repeat(80));
			console.log("  FAIL! " + failure.name);
			const indent = "      ";
			let exception: string;
			if (failure.exception instanceof Error) {
				exception = failure.exception.stack + "";
			} else {
				exception = failure.exception + "";
			}
			if (failure.exception.constructor && failure.exception.constructor.name) {
				exception = `(${failure.exception.constructor.name}) ${exception}`;
			}
			console.log(indent + exception.replace(/\t/g, "    ").replace(/\n/g, "\n" + indent));
			console.log("\u{25b4}".repeat(80));
		}

		console.log("");
		console.log("Passed: " + passed.length + ".");
		console.log("Failed: " + failed.length + (failed.length == 0 ? "." : "!"));

		if (passed.length === 0 || failed.length !== 0) {
			return 1;
		}
		return 0;
	}
}

export const spec = Symbol("test-spec");

export type Spec<T> = T
	| (T extends object ? { [K in keyof T]: Spec<T[K]> } : never)
	| { [spec]: (t: T) => ReturnType<typeof deepEqual> };

export function specSupersetOf<T>(subset: Set<T>): Spec<Set<T>> {
	return {
		[spec](test: Set<T>) {
			for (const e of subset) {
				if (!test.has(e)) {
					return { eq: false, path: [e] };
				}
			}
			return { eq: true };
		},
	}
}

function deepEqual(a: any, b: Spec<any>): { eq: true } | { eq: false, path: any[] } {
	if (b !== null && typeof b === "object" && spec in b) {
		return b[spec](a);
	} else if (a === b) {
		return { eq: true };
	} else if (typeof a !== typeof b) {
		return { eq: false, path: [] };
	} else if (a instanceof Set && b instanceof Set) {
		for (let v of a) {
			if (!b.has(v)) {
				return { eq: false, path: [v] };
			}
		}
		for (let v of b) {
			if (!a.has(v)) {
				return { eq: false, path: [v] };
			}
		}
		return { eq: true };
	} else if (a instanceof Set || b instanceof Set) {
		return { eq: false, path: [] };
	} else if (a instanceof Map || b instanceof Map) {
		return { eq: false, path: [] };
	} else if (typeof a === "object") {
		if (a === null || b === null) {
			return { eq: false, path: [] };
		}

		let checked: any = {};
		for (let k in a) {
			const cmp = deepEqual(a[k], b[k]);
			if (!cmp.eq) {
				return { eq: false, path: [k].concat(cmp.path) };
			}
			checked[k] = true;
		}
		for (let k in b) {
			if (!checked[k]) {
				return { eq: false, path: [k] };
			}
		}
		return { eq: true };
	} else {
		return { eq: false, path: [] };
	}
}

export function assert<A, B extends A>(a: A, op: "is equal to", b: Spec<B>): asserts a is B;
export function assert<A>(a: A, op: A extends any[] ? "is array" : never): asserts a is any[] & A;
export function assert(a: () => void, op: "throws", e: unknown): void;

export function assert<A, B extends A>(...args: [A, "is equal to", B] | [any, "is array"] | [() => void, "throws", unknown]) {
	if (args[1] === "is equal to") {
		const [a, op, b] = args;
		const cmp = deepEqual(a, b);
		if (!cmp.eq) {
			const sa = util.inspect(a, { depth: 16, colors: true });
			const sb = util.inspect(b, { depth: 16, colors: true });
			throw new Error(`Expected \n${sa}\nto be equal to\n${sb}\nbut found difference in path \`${JSON.stringify(cmp.path)}\``);
		}
	} else if (args[1] === "is array") {
		const [a, op] = args;
		if (!Array.isArray(a)) {
			throw new Error("Expected `" + JSON.stringify(a, null, "\t") + "` to be an array.");
		}
	} else if (args[1] === "throws") {
		const [f, op, expected] = args;
		let threw = false;
		try {
			f();
		} catch (e) {
			if (e instanceof Error) {
				throw e;
			}
			assert(e, "is equal to", expected);
			threw = true;
		}
		if (!threw) {
			throw new Error(`Expected an error to be thrown.`);
		}
	} else {
		throw new Error("unhandled assertion type `" + JSON.stringify(args[1]) + "`");
	}
}

const testRunner = new TestRunner(process.argv[2]);

testRunner.runTests("data_tests", data_tests.tests);
testRunner.runTests("egraph_tests", egraph_tests.tests);
testRunner.runTests("grammar_tests", grammar_tests.tests);
testRunner.runTests("interpreter_tests", interpreter_tests.tests);
testRunner.runTests("lexer_tests", lexer_tests.tests);
testRunner.runTests("parser_tests", parser_tests.tests);
testRunner.runTests("sat_tests", sat_tests.tests);
testRunner.runTests("semantics_tests", semantics_tests.tests);
testRunner.runTests("smt_tests", smt_tests.tests);
testRunner.runTests("uf_tests", uf_tests.tests);
testRunner.runTests("verify_tests", verify_tests.tests);
testRunner.printReport();
