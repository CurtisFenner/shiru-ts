import * as components_tests from "./components_tests";
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
import * as ir_tests from "./ir_tests";

import * as util from "util";
import * as fs from "fs";
import * as trace from "./trace";

export type Run = PassRun | FailRun;

export interface PassRun {
	name: string,
	type: "pass",
	elapsedMillis: number,
}

export interface FailRun {
	name: string,
	type: "fail",
	exception: any,
	elapsedMillis: number,
}

export class TestRunner {
	runs: Run[] = [];
	traces: trace.TraceBranch[] = [];

	constructor(private testNameFilters: string[]) { }

	runTest(name: string, body: () => void) {
		let keep = this.testNameFilters.length === 0;
		for (const filter of this.testNameFilters) {
			if (name.indexOf(filter) >= 0) {
				keep = true;
			}
		}
		if (!keep) {
			return;
		}

		trace.clear(name);
		const beforeMillis = performance.now();
		try {
			body();
			const elapsedMillis = performance.now() - beforeMillis;
			this.runs.push({ name, type: "pass", elapsedMillis });
			return;
		} catch (e) {
			const elapsedMillis = performance.now() - beforeMillis;
			this.runs.push({ name, type: "fail", exception: e, elapsedMillis });
			this.traces.push(trace.publish());
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

		if (this.runs.length !== 0) {
			let slowest = this.runs[0];
			for (let i = 1; i < this.runs.length; i++) {
				if (this.runs[i].elapsedMillis > slowest.elapsedMillis) {
					slowest = this.runs[i];
				}
			}
			console.log("Slowest: " + slowest.name + " took " + slowest.elapsedMillis.toFixed(0) + " ms");
		}

		if (passed.length === 0 || failed.length !== 0) {
			return 1;
		}
		return 0;
	}
}

export const spec = Symbol("test-spec");

export type Spec<T> = T
	| (T extends object ? { [K in keyof T]: Spec<T[K]> } : never)
	| { [spec]: (t: T) => ReturnType<typeof deepEqual>, [util.inspect.custom]?: any };

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
		[util.inspect.custom]: (depth: number, options: any) => {
			return "(any superset of) " + util.inspect(subset, options);
		},
	}
}

export function specEq<T>(value: Spec<T>): Spec<T> {
	return {
		[spec](test: T) {
			return deepEqual(test, value);
		},
		[util.inspect.custom]: (depth: number, options: any) => {
			return util.inspect(value, options);
		},
	};
}

export function specSetEq<R extends Iterable<unknown>>(value: R): Spec<R> {
	return {
		[spec](test: R) {
			try {
				const setTest = new Set(test);
				const comparison = deepEqual(new Set(value), setTest);
				return comparison;
			} catch {
				// The `test` is not iterable.
				return { eq: false, path: [] };
			}
		},
		[util.inspect.custom]: (depth: number, options: any) => {
			return "(in any order) " + util.inspect(value, options);
		},
	};
}

export function specPredicate<T>(predicate: (t: T) => true | string[], description: string = "(custom predicate)"): Spec<T> {
	return {
		[spec](test: T) {
			const result = predicate(test);
			if (result === true) {
				return { eq: true };
			} else {
				return { eq: false, path: result };
			}
		},
		[util.inspect.custom]: () => description,
	};
}

export function specDescribe<T>(value: Spec<T>, description: string, path?: string): Spec<T> {
	return {
		[spec](test: T) {
			const cmp = deepEqual(test, value);
			if (cmp.eq === true) {
				return cmp;
			} else {
				cmp.description = description;
				if (path !== undefined) {
					cmp.path = [path].concat(cmp.path);
				}
				return cmp;
			}
		},
		[util.inspect.custom]: (depth: number, options: any) => {
			return util.inspect(value, options);
		},
	};
}

function deepEqual(
	a: any,
	b: Spec<any>,
): { eq: true } | { eq: false, path: any[], expectedValue?: any, description?: string } {
	if (b !== null && typeof b === "object" && spec in b) {
		return b[spec](a);
	} else if (a === b) {
		return { eq: true };
	} else if (typeof a !== typeof b) {
		return { eq: false, path: [], expectedValue: b };
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
	} else if (a instanceof Map && b instanceof Map) {
		for (let [k, v] of a) {
			if (!b.has(k)) {
				return { eq: false, path: [k] };
			}
			const cmp = deepEqual(v, b.get(k));
			if (!cmp.eq) {
				return { eq: false, path: [k].concat(cmp.path) };
			}
		}
		for (let [k, v] of b) {
			if (!a.has(k)) {
				return { eq: false, path: [k] };
			}
			const cmp = deepEqual(v, a.get(k));
			if (!cmp.eq) {
				return { eq: false, path: [k].concat(cmp.path) };
			}
		}
		return { eq: true };
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
				return { eq: cmp.eq, path: [k].concat(cmp.path) };
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
		return { eq: false, path: [], expectedValue: b };
	}
}

export function assert<A, B extends A>(a: A, op: "is equal to", b: Spec<B>): asserts a is B;
export function assert<A>(a: A, op: A extends any[] ? "is array" : never): asserts a is any[] & A;
export function assert(a: () => void, op: "throws", e: unknown): void;
export function assert<A>(a: A | null, op: "is not null"): asserts a is A;

export function assert<A, B extends A>(...args: [A, "is equal to", B] | [any, "is array"] | [() => void, "throws", unknown] | [A, "is not null"]) {
	if (args[1] === "is equal to") {
		const [a, op, b] = args;
		const cmp = deepEqual(a, b);
		if (!cmp.eq) {
			const sa = util.inspect(a, { depth: 16, colors: true });
			const sb = util.inspect("expectedValue" in cmp ? cmp.expectedValue : b, { depth: 16, colors: true });
			const expected = "description" in cmp ? " (" + cmp.description + ")" : "";
			throw new Error(`Expected \n${sa}\nto be equal to\n${sb}${expected}\nbut found difference in path \`${JSON.stringify(cmp.path)}\``);
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
	} else if (args[1] === "is not null") {
		const a = args[0];
		if (a === null) {
			const sa = util.inspect(a, { depth: 16, colors: true });
			throw new Error(`Expected \n${sa}\nto be not null.`);
		}
	} else {
		const _: never = args;
		throw new Error("unhandled assertion type `" + JSON.stringify(args[1]) + "`");
	}
}

const commandArguments: Record<string, string[]> = {};
const bare = "filter";
for (let i = 2; i < process.argv.length; i++) {
	const argument = process.argv[i];
	const m = argument.match(/^([a-z0-9-]+)=(.*)/);
	let key: string;
	let value: string;
	if (m !== null) {
		key = m[1];
		value = m[2];
	} else {
		key = bare;
		value = argument;
	}

	if (!(key in commandArguments)) {
		commandArguments[key] = [];
	}
	commandArguments[key].push(value);
}

if ("trace" in commandArguments) {
	trace.setSlow(true);
}

const testRunner = new TestRunner(commandArguments.filter || []);

testRunner.runTests("components_tests", components_tests.tests);
testRunner.runTests("data_tests", data_tests.tests);
testRunner.runTests("ir_tests", ir_tests.tests);
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


if ("trace" in commandArguments) {
	fs.writeFileSync(commandArguments.trace.at(-1)!, trace.render(testRunner.traces));
}

if ("perf" in commandArguments) {
	const dictionary: any = {};
	for (const run of testRunner.runs) {
		dictionary[run.name] = { elapsedMillis: run.elapsedMillis };
	}
	const body = JSON.stringify({ version: "0.1", tests: dictionary }, null, "    ");
	fs.writeFileSync(commandArguments.perf.at(-1)!, body);
}
