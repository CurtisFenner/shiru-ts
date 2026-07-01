import * as components_tests from "../shiru/components_tests.ts";
import * as data_tests from "../shiru/data_tests.ts";
import * as egraph_tests from "../shiru/egraph_tests.ts";
import * as grammar_tests from "../shiru/grammar_tests.ts";
import * as interpreter_tests from "../shiru/interpreter_tests.ts";
import * as ir_tests from "../shiru/ir_tests.ts";
import * as lexer_tests from "../shiru/lexer_tests.ts";
import * as parser_tests from "../shiru/parser_tests.ts";
import * as sat_tests from "../shiru/sat_tests.ts";
import * as semantics_tests from "../shiru/semantics_tests.ts";
import * as smt_tests from "../shiru/smt_tests.ts";
import * as uf_tests from "../shiru/uf_tests.ts";
import * as verify_tests from "../shiru/verify_tests.ts";

import * as test from "../shiru/test.ts";
import * as trace from "../shiru/trace.ts";

import * as fs from "node:fs/promises";

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

const testRunner = new test.TestRunner(commandArguments.filter || []);

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

const passed = testRunner.runs.filter(x => x.type == "pass");
const failed: test.FailRun[] = testRunner.runs.filter(x => x.type == "fail");

for (let pass of passed) {
	console.log(`  pass  ${pass.name} (${pass.elapsedMillis.toFixed(0)} ms)`);
}

for (let failure of failed) {
	console.log("\u{25be}".repeat(80));
	console.log(`  FAIL! ${failure.name} (${failure.elapsedMillis.toFixed(0)} ms)`);
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

if (testRunner.runs.length !== 0) {
	let slowest = testRunner.runs[0];
	for (let i = 1; i < testRunner.runs.length; i++) {
		if (testRunner.runs[i].elapsedMillis > slowest.elapsedMillis) {
			slowest = testRunner.runs[i];
		}
	}
	console.log(`Slowest: ${slowest.name} took ${slowest.elapsedMillis.toFixed(0)} ms`);
}

if ("trace" in commandArguments) {
	const tracePath = commandArguments.trace.at(-1)!;
	console.error("tracePath:", tracePath);
	try {
		const traceContent = await trace.render(testRunner.traces);
		await fs.writeFile(tracePath, traceContent);
	} catch (err) {
		console.error("error writing", tracePath, err);
	}
}

process.exitCode = (failed.length !== 0 || passed.length === 0)
	? 1
	: 0;
