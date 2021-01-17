import * as interpreter_test from "./interpreter_test";
import * as parser_test from "./parser_test";
import * as sat_tests from "./sat_tests";
import * as smt_tests from "./smt_tests";

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
export function assert<A, B extends A>(a: any, op: "is array"): asserts a is any[];

export function assert<A, B extends A>(...args: [A, "is equal to", B] | [any, "is array"]) {
	if (args[1] === "is equal to") {
		const [a, op, b] = args;
		if (!deepEqual(a, b)) {
			let sa = "`" + JSON.stringify(a, null, "\t") + "`";
			let sb = "`" + JSON.stringify(b, null, "\t") + "`";
			throw new Error("Expected " + sa + " to be equal to " + sb);
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

testRunner.runTests("interpreter_test", interpreter_test.tests);
testRunner.runTests("parser_test", parser_test.tests);
testRunner.runTests("sat_tests", sat_tests.tests);
testRunner.runTests("smt_tests", smt_tests.tests);
testRunner.printReport();
