import { readFileSync, readSync } from "fs";
import { SATSolver } from "./sat.js";

export function solveDimacs(instance: string) {
	const cells = instance.split("\n")
		.filter(line => line[0] !== "c")
		.join(" ")
		.trim()
		.split(/\s+/);

	if (cells[0] !== "p") {
		throw new Error("expected first element to be `p`, but it was " + JSON.stringify(cells[0]));
	} else if (cells[1] !== "cnf") {
		throw new Error("expected second element to be `cnf`");
	}

	// Ignore elements [2] and [3].

	let cnf = new SATSolver();
	let clause = [];
	for (let i = 4; i < cells.length; i++) {
		const v = parseInt(cells[i]);
		if (v !== v) {
			console.error("Unexpected cell `" + cells[i] + "`");
			continue;
		}
		if (v === 0) {
			if (clause.length === 0) {
				continue;
			}
			cnf.addClause(clause);
			clause = [];
		} else {
			clause.push(v);

			cnf.initTerms(Math.abs(v));
		}
	}

	const result = cnf.solve();
	return result;
}


if (require.main === module) {
	const commands = process.argv;

	if (commands.length !== 3 && commands.length !== 2) {
		console.error("USAGE:");
		console.error("\t<node> <dimacs.js> <inputfile.cnf>");
		console.error("\t\tsolves the CNF in the indicated file represented in DIMACS CNF format");
		console.error("\t<node> <dimacs.js>");
		console.error("\t\tsolves the CNF in standard-in represented in DIMACS CNF format.");

		process.exit(1);
	}

	// does this work on Windows?
	const dimacsFileName = commands[2];

	let file = "";
	if (!dimacsFileName) {
		// Read the DIMACS file from standard-input.
		let read: number;
		const buffer = Buffer.alloc(1024 * 1024);
		do {
			try {
				read = readSync(process.stdin.fd, buffer, 0, buffer.length, null);
			} catch (e: any) {
				// https://github.com/nodejs/node/issues/35997
				if (e.code === "EOF") {
					read = 0;
				} else {
					throw e;
				}
			}
			file += buffer.slice(0, read).toString();
		} while (read !== 0);
	} else {
		file = readFileSync(dimacsFileName, { encoding: "utf-8" });
	}

	const result = solveDimacs(file);
	if (result === "unsatisfiable") {
		console.log("UNSATISFIABLE");
	} else {
		console.log(JSON.stringify(result, null, "\t"));
		console.log("SATISFIABLE");
	}
}
