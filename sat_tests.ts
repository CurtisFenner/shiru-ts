import { SATSolver } from "./sat";
import { assert } from "./test";

export const tests = {
	simpleSatisfiable() {
		const sat = new SATSolver();
		sat.initTerms(9);

		const instance = [
			[+7, +4, +6],
			[+1, -7, +5],
			[-5, -2, +7],
			[-1, -6, +4],
			[+5, +4, -2],
			[-1, -9, +2],
			[-9, -4, -5],
			[+2, -8, -4],
			[-3, -7, +9],
			[-4, +2, +5],
		];

		for (let clause of instance) {
			sat.addClause(clause);
		}

		const model = sat.solve();
		assert(model, "is array");
		for (let clause of instance) {
			let satisfied = false;
			for (let literal of clause) {
				assert(model.indexOf(literal) < 0 || model.indexOf(-literal) < 0, "is equal to", true);
				satisfied = satisfied || model.indexOf(literal) >= 0;
			}
			assert(satisfied, "is equal to", true);
		}
	},
	simpleUnsatisfiable() {
		const sat = new SATSolver();
		sat.initTerms(3);
		sat.addClause([+1, +2, -3]);
		sat.addClause([+1, -2, -3]);
		sat.addClause([-1, +2, -3]);
		sat.addClause([-1, -2, -3]);
		sat.addClause([+3]);

		const model = sat.solve();
		assert(model, "is equal to", "unsatisfiable");
	}
};

function sorted(t: number[]) {
	return t.slice(0).sort();
}
