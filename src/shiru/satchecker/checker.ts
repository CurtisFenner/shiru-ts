import { Histogram } from "./histogram.js";
import * as sat from "../sat.js";

// @ts-expect-error
import { default as logic } from "logic-solver";

function randomLiteralForTerm(n: number): number {
	return Math.random() < 0.5 ? -n : +n;
}

/**
 * @returns a random 3-SAT instance of the indicated size.
 */
export function random3CNFInstance(numTerms: number, numClauses: number): number[][] {
	if (numTerms !== numTerms || numTerms < 4) {
		throw new Error("invalid numTerms");
	} else if (numClauses !== numClauses || numClauses < 1) {
		throw new Error("invalid numClauses");
	}

	const clauses = [];
	for (let i = 0; i < numClauses; i++) {
		let a = Math.floor(Math.random() * numTerms);
		let b = a;
		while (b == a) b = Math.floor(Math.random() * numTerms);
		let c = b;
		while (c == a || c == b) c = Math.floor(Math.random() * numTerms);

		const clause = [
			randomLiteralForTerm(a + 1),
			randomLiteralForTerm(b + 1),
			randomLiteralForTerm(c + 1),
		];
		clauses.push(clause);
	}

	return clauses;
}

export function minisat(clauses: number[][]): "UNSATISFIABLE" | "SATISFIABLE" {
	const solver = new logic.Solver();
	for (const clause of clauses) {
		solver.require(logic.or(...clause.map(literal => {
			return literal > 0
				? "v" + literal
				: "-v" + (-literal);
		})));
	}
	const solution = solver.solve();
	if (solution === null) {
		return "UNSATISFIABLE";
	}
	return "SATISFIABLE";
}

function shiru(clauses: number[][]): "UNSATISFIABLE" | "SATISFIABLE" {
	const solver = new sat.SATSolver();
	for (const clause of clauses) {
		for (const literal of clause) {
			solver.initTerms(Math.abs(literal));
		}
		solver.addClause(clause);
	}

	return solver.solve() === "unsatisfiable"
		? "UNSATISFIABLE"
		: "SATISFIABLE";
}

const satHisto = new Histogram(25, 10);
const unsatHisto = new Histogram(25, 10);

function compareSolvers(instance: number[][]) {
	const before = performance.now();
	let shiruResult;
	try {
		shiruResult = shiru(instance);
	} catch (e) {
		console.log("Error instance:");
		console.log(instance);
		throw e;
	}
	const after = performance.now();

	if (after - before > 1000) {
		console.error("Slow instance (" + (after - before) + " ms):");
		console.log(instance);
	}

	const miniResult = minisat(instance);

	if (miniResult == "SATISFIABLE") {
		satHisto.record(after - before);
	} else {
		unsatHisto.record(after - before);
	}

	if (shiruResult !== miniResult) {
		console.error("FAILING INSTANCE:", instance);
		console.error("Shiru result:", shiruResult);
		console.error("Minisat result:", miniResult);
		throw new Error("Found violation!");
	}
	return miniResult;
}

function fuzzSolvers() {
	let numVariables = 100 + Math.floor(10 * Math.random());

	// The "satisfiability threshold" for 3-sat
	// (the ratio of clauses to variables where approximately 50% of random instances are satisfiable)
	// is approximately 4.3, with a lower bound of about 3.5.
	let ratio = 3.9 + Math.random() * 0.8;

	let numClauses = Math.floor(numVariables * ratio + 0.5);

	const instance = random3CNFInstance(numVariables, numClauses);
	compareSolvers(instance);
}

let NUM_FUZZES: number | null = null;
const commands = process.argv;
if (commands.length === 3) {
	NUM_FUZZES = parseInt(commands[2]);
} else if (commands.length === 2) {
	NUM_FUZZES = 1_000;
}

if (NUM_FUZZES === null || NUM_FUZZES !== NUM_FUZZES || NUM_FUZZES < 1) {
	console.error("USAGE:");
	console.error("\t<node> <checker.js> <instance count=1000>");
	console.error("\t\tgenerates the given number of 3-sat instances and compares Shiru's result with minisat's.");

	process.exit(1);
}

const before = performance.now();
for (let i = 0; i < NUM_FUZZES; i++) {
	fuzzSolvers();
	if (i % 10 == 9 || i + 1 >= NUM_FUZZES) {
		const satLines = satHisto.print("Satisfiable Instances", (lo, hi, last) => {
			if (last) {
				return lo + "+ ms";
			}
			return lo + "-" + hi + " ms";
		});
		const unsatLines = unsatHisto.print("Unsatisfiable Instances", (lo, hi, last) => {
			if (last) {
				return lo + "+ ms";
			}
			return lo + "-" + hi + " ms";
		});
		console.log("");
		console.log(satLines.join("\n"));
		console.log(unsatLines.join("\n"));
	}
}
const after = performance.now();

console.log("Completed " + NUM_FUZZES + " 3-sat instances in " + (after - before).toFixed(0) + " milliseconds.");
