import * as interpreter_test from "./interpreter_test";
import * as parser_test from "./parser_test";
import * as sat_tests from "./sat_tests";
import * as smt_tests from "./smt_tests";
import * as data_tests from "./data_tests";
import util = require("util");

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
			console.log("  FAIL! " + failure.name);
			const indent = "      ";
			let exception: string;
			if (failure.exception instanceof Error) {
				exception = failure.exception.stack + "";
			} else {
				exception = failure.exception + "";
			}
			console.log(indent + exception.replace(/\t/g, "    ").replace(/\n/g, "\n" + indent));
		}

		console.log("");
		console.log("Passed: " + passed.length + ".");
		console.log("Faied: " + failed.length + (failed.length == 0 ? "." : "!"));

		if (passed.length === 0 || failed.length !== 0) {
			return 1;
		}
		return 0;
	}
}

function deepEqual(a: any, b: any) {
	if (a === b) {
		return true;
	} else if (typeof a !== typeof b) {
		return false;
	} else if (a instanceof Set && b instanceof Set) {
		for (let v of a) {
			if (!b.has(v)) {
				return false;
			}
		}
		for (let v of b) {
			if (!a.has(v)) {
				return false;
			}
		}
		return true;
	} else if (a instanceof Set || b instanceof Set) {
		return false;
	} else if (a instanceof Map || b instanceof Map) {
		return false;
	} else if (typeof a === "object") {
		if (a === null || b === null) {
			return false;
		}

		let checked: any = {};
		for (let k in a) {
			if (!deepEqual(a[k], b[k])) {
				return false;
			}
			checked[k] = true;
		}
		for (let k in b) {
			if (!checked[k]) {
				return false;
			}
		}
		return true;
	} else {
		return false;
	}
}

export function assert<A, B extends A>(a: A, op: "is equal to", b: B): asserts a is B;
export function assert<A>(a: A, op: A extends any[] ? "is array" : never): asserts a is any[] & A;

export function assert<A, B extends A>(...args: [A, "is equal to", B] | [any, "is array"]) {
	if (args[1] === "is equal to") {
		const [a, op, b] = args;
		if (!deepEqual(a, b)) {
			const sa = util.inspect(a, { depth: 16, colors: true });
			const sb = util.inspect(b, { depth: 16, colors: true });
			throw new Error(`Expected \n\t${sa}\nto be equal to\n\t${sb}`);
		}
	} else if (args[1] === "is array") {
		const [a, op] = args;
		if (!Array.isArray(a)) {
			throw new Error("Expected `" + JSON.stringify(a, null, "\t") + "` to be an array.");
		}
	} else {
		throw new Error("unhandled assertion type `" + JSON.stringify(args[1]) + "`");
	}
}

const testRunner = new TestRunner(process.argv[2]);

testRunner.runTests("data_tests", data_tests.tests);
testRunner.runTests("interpreter_test", interpreter_test.tests);
testRunner.runTests("parser_test", parser_test.tests);
testRunner.runTests("sat_tests", sat_tests.tests);
testRunner.runTests("smt_tests", smt_tests.tests);
testRunner.printReport();
