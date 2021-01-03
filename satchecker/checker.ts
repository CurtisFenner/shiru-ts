import * as child_process from "child_process";
import { solveDimacs } from "../dimacs";
import { Histogram } from "./histogram";
import { generateInstance as generateRandom3CNF } from "./random3cnf";


function runSync(command: string, input?: string): string {
	if (input !== undefined) {
		return child_process.execSync(command, { input }).toString("utf8");
	} else {
		return child_process.execSync(command).toString("utf8");
	}
}

export function minisat(dimacs: string): "UNSATISFIABLE" | "SATISFIABLE" {
	let stdout: string;
	try {
		stdout = runSync("minisat -verb=0", dimacs);
	} catch (e) {
		// minisat returns an exit code for satisfiable or not, but instead we're parsing STDOUT to be more resilient.
		stdout = e.stdout.toString("utf8");
		if (typeof stdout !== "string") {
			throw new Error("unexpected error from runSync");
		}
	}
	const lines = stdout.toString().trim().split("\n");
	return lines[lines.length - 1].trim() as any;
}

function shiru(dimacs: string): "UNSATISFIABLE" | "SATISFIABLE" {
	const result = solveDimacs(dimacs);
	if (result === "unsatisfiable") {
		return "UNSATISFIABLE";
	} else {
		return "SATISFIABLE";
	}
}

function table() {
	const TRIALS = 40;
	console.log("Fraction of satisfiable instances among " + TRIALS + " random 3-sat instances.");
	console.log("Num Terms,Num clauses...");
	let clauseHeading = [""];

	const MIN_CLAUSE = 20;
	const MAX_CLAUSES = 200;
	const CLAUSE_STEP = 5;

	for (let numClauses = MIN_CLAUSE; numClauses <= MAX_CLAUSES; numClauses += CLAUSE_STEP) {
		clauseHeading.push(numClauses + " clauses");
	}

	console.log(clauseHeading.join(","));
	const timingRows: any[][] = [];
	for (let numTerms = 4; numTerms <= 30; numTerms++) {
		let fractionRow = [numTerms];
		const timeRow = [numTerms];
		for (let numClauses = MIN_CLAUSE; numClauses <= MAX_CLAUSES; numClauses += CLAUSE_STEP) {
			let satisfiable = 0;
			let totalElapsed = 0;
			for (let trial = 0; trial < TRIALS; trial++) {
				const instance = generateRandom3CNF(numTerms, numClauses);
				const before = Date.now();
				const result = minisat(instance);
				const elapsed = Date.now() - before;
				totalElapsed += elapsed;
				if (result === "SATISFIABLE") {
					satisfiable += 1;
				} else if (result == "UNSATISFIABLE") {
					// Nothing.
				} else {
					throw new Error("unreachable `" + (result as any) + "`");
				}
			}
			fractionRow.push(satisfiable / TRIALS);
			timeRow.push(totalElapsed / TRIALS);
		}
		console.log(fractionRow.join(","));
		timingRows.push(timeRow);
	}

	console.log("");
	console.log("Average solve time (milliseconds)");
	console.log("Num terms,Num clauses...");
	console.log(clauseHeading.join(","));
	for (let row of timingRows) {
		console.log(row.join(","));
	}
}

const satHisto = new Histogram(25, 10);
const unsatHisto = new Histogram(25, 10);

function compareSolvers(instance: string) {
	const before = Date.now();
	const shiruResult = shiru(instance);
	const after = Date.now();

	if (after - before > 1000) {
		console.error("Slow instance:", instance);
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

	const instance = generateRandom3CNF(numVariables, numClauses);
	const result = compareSolvers(instance);
}

if (require.main === module) {
	const before = Date.now();
	const NUM_FUZZES = 1_000;
	for (let i = 0; i < NUM_FUZZES; i++) {
		fuzzSolvers();
		if (i % 10 == 9) {
			console.log("");
			satHisto.print("Satisfiable Instances", (lo, hi, last) => {
				if (last) {
					return lo + "+ ms";
				}
				return lo + "-" + hi + " ms";
			});
			unsatHisto.print("Unsatisfiable Instances", (lo, hi, last) => {
				if (last) {
					return lo + "+ ms";
				}
				return lo + "-" + hi + " ms";
			});
		}
	}
	const after = Date.now();

	console.log("Completed " + NUM_FUZZES + " 3-sat instances in " + (after - before) + " milliseconds.");
}
