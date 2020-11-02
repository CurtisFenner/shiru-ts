import * as interpreter_test from "./interpreter_test";

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

	runTest(name: string, body: () => void) {
		try {
			body();
			this.runs.push({ name, type: "pass" });
			return;
		} catch (e) {
			this.runs.push({ name, type: "fail", exception: e });
		}
	}

	runTests(obj: { [k: string]: () => void }) {
		for (let k in obj) {
			this.runTest(k, obj[k]);
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

export function assert<T>(a: T, op: "is equal to", b: T) {
	if (a !== b) {
		let sa = "`" + a + "`";
		let sb = "`" + b + "`";
		if (sa == sb) {
			sa += " (" + typeof a + ")";
			sb += " (" + typeof b + ")";
		}

		throw new Error("Expected " + sa + " to be equal to " + sb);
	}
}


const testRunner = new TestRunner();

testRunner.runTests(interpreter_test.tests);
testRunner.printReport();
