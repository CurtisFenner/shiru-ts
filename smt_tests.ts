import { SATSolver } from "./smt";
import { assert } from "./test";

export const tests = {
	simpleSatisfiable() {
		const sat = new SATSolver();
		sat.initTerms(9);

		sat.addClause([+7, +4, +6]);
		sat.addClause([+1, -7, +5]);
		sat.addClause([-5, -2, +7]);
		sat.addClause([-1, -6, +4]);
		sat.addClause([+5, +4, -2]);
		sat.addClause([-1, -9, +2]);
		sat.addClause([-9, -4, -5]);
		sat.addClause([+2, -8, -4]);
		sat.addClause([-3, -7, +9]);
		sat.addClause([-4, +2, +5]);

		const model = sat.solve();
		assert(model, "is array");
		assert(sorted(model), "is equal to", sorted([
			+1,
			+2,
			+3,
			+4,
			-5,
			+6,
			+7,
			+8,
			+9,
		]));
	},
};

function sorted(t: number[]) {
	return t.slice(0).sort();
}
