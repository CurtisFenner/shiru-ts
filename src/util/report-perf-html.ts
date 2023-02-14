import * as fs from "fs";


const commandArguments = process.argv.slice(2);

const inputFile = commandArguments[0];
const outFile = commandArguments[1];
if (!outFile || !inputFile) {
	throw new Error("needs in and out files");
}
const json = JSON.parse(fs.readFileSync(inputFile, "utf-8"));

const columns = Object.keys(json).map(name => ({ name, timestamp: json[name][0].timestamp }));
const measures: Record<string, { rank: number, values: Record<string, number[]> }> = {};
for (const [sha, runs] of Object.entries(json)) {
	for (const run of runs as { tests: object }[]) {
		for (const [testName, testResult] of Object.entries(run.tests)) {
			measures[testName] = measures[testName] || { rank: -1, values: [] };
			measures[testName].values[sha] = measures[testName].values[sha] || [];
			measures[testName].values[sha].push(testResult.elapsedMillis);
		}
	}
}

for (const testResults of Object.values(measures)) {
	let product = 1;
	let count = 0;
	for (const set of Object.values(testResults.values)) {
		for (const value of set) {
			product *= value;
			count += 1;
		}
	}
	testResults.rank = Math.pow(product, 1 / count);
}

const inOrder = Object.keys(measures).sort((a, b) => {
	return measures[b].rank - measures[a].rank;
});
console.log(inOrder);

function htmlEscape(x: string): string {
	return x.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function format2(n: number) {
	const m = Math.abs(n);
	let ms = m.toFixed(2);
	if (m > 11) {
		ms = m.toFixed(0);
	} else if (m > 1.1) {
		ms = m.toFixed(1);
	}
	if (n >= 0) {
		return "+" + ms;
	} else {
		return "-" + ms;
	}
}

const output = [];
output.push("<!doctype html>");
output.push("<html>");
output.push("<head>");
output.push("<meta charset=utf-8>");
output.push(`
<style>
body {
	font-family: sans-serif;
}

table {
	border-left: 1px dotted #AAA;
	border-top: 1px dotted #AAA;
	border-spacing: 0;
}
th, td {
	border-right: 1px dotted #AAA;
	border-bottom: 1px dotted #AAA;
	padding: 2px;
}
</style>
`);
output.push("<table>");
output.push("<thead>");
output.push("<tr>");
output.push("\t<th>Test");
for (const c of columns) {
	output.push("\t<th>" + htmlEscape(c.name) + "<br>" + htmlEscape(c.timestamp) + "</th>");
}

function calculateStats(values: number[]) {
	const sum = values.reduce((a, b) => a + b, 0);
	const average = sum / values.length;
	let m2 = 0;
	for (const value of values) {
		m2 += (value - average) ** 2;
	}
	m2 /= values.length - 1;
	const stddev = Math.sqrt(m2);

	return {
		count: values.length,
		sum,
		average,
		stddev,
	};
}

output.push("<tbody>");
for (const row of inOrder) {
	output.push("<tr>");
	output.push("\t<th>" + htmlEscape(row));
	for (const c of columns) {
		const values = measures[row].values[c.name];
		if (!values) {
			output.push("\t<td>&blank;");
		} else {
			const stats = calculateStats(values);

			const data = stats.average.toFixed(0) + " &plusmn; " + stats.stddev.toFixed(0);
			output.push("\t<td>" + data);
		}
	}
}

fs.writeFileSync(outFile, output.join("\n"));
