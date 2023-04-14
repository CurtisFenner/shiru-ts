import { SATResult, SATSolver } from "./sat.js";

export function parseDimacs(instance: string): number[][] {
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
	const clauses = [];
	let clause = [];
	for (let i = 4; i < cells.length; i++) {
		const v = parseInt(cells[i]);
		if (v !== v) {
			console.error("Unexpected cell `" + cells[i] + "`");
			continue;
		} else if (v === 0) {
			if (clause.length === 0) {
				continue;
			}
			clauses.push(clause);
			clause = [];
		} else {
			clause.push(v);
		}
	}
	if (clause.length !== 0) {
		console.error("unfinished clause (" + clause.join(" | ") + ")");
	}
	return clauses;
}

export function solveDimacs(instance: string): SATResult {
	const clauses = parseDimacs(instance);
	const sat = new SATSolver();
	for (const clause of clauses) {
		for (const literal of clause) {
			sat.initTerms(Math.abs(literal));
		}
		sat.addClause(clause);
	}

	return sat.solve();
}
