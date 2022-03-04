import * as ir from "./ir";
import * as uf from "./uf";
import { assert } from "./test";

export const tests = {
	"UFTheory-basic-equality-refuted"() {
		const smt = new uf.UFTheory();
		const x = smt.createVariable(ir.T_INT, "x");
		const y = smt.createVariable(ir.T_INT, "y");
		const z = smt.createVariable(ir.T_INT, "z");
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		const xeqy = smt.createApplication(eq, [x, y]);
		const xeqz = smt.createApplication(eq, [x, z]);
		const yeqz = smt.createApplication(eq, [y, z]);
		const yneqz = smt.createApplication(not, [yeqz]);

		smt.addConstraint([xeqy]);
		smt.addConstraint([xeqz]);
		smt.addConstraint([yneqz]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", "refuted");
	},
	"UFTheory-basic-satisfiable"() {
		const smt = new uf.UFTheory();
		const x1 = smt.createVariable(ir.T_INT, "x1");
		const x2 = smt.createVariable(ir.T_INT, "x2");
		const f = smt.createFunction(ir.T_INT, {}, "f");

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		const x1eqx2 = smt.createApplication(eq, [x1, x2]);
		const fx1 = smt.createApplication(f, [x1]);
		const fx2 = smt.createApplication(f, [x2]);
		const fx1eqfx2 = smt.createApplication(eq, [fx1, fx2]);
		const fx1neqfx2 = smt.createApplication(not, [fx1eqfx2]);

		smt.addConstraint([x1eqx2, fx1neqfx2]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", { model: {} });
	},
	"UFTheory-basic-function-refuted"() {
		const smt = new uf.UFTheory();
		const x1 = smt.createVariable(ir.T_INT, "x1");
		const x2 = smt.createVariable(ir.T_INT, "x2");
		const f = smt.createFunction(ir.T_INT, {}, "f");

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		const x1eqx2 = smt.createApplication(eq, [x1, x2]);
		const fx1 = smt.createApplication(f, [x1]);
		const fx2 = smt.createApplication(f, [x2]);
		const fx1eqfx2 = smt.createApplication(eq, [fx1, fx2]);
		const fx1neqfx2 = smt.createApplication(not, [fx1eqfx2]);

		smt.addConstraint([fx1neqfx2]);
		smt.addConstraint([x1eqx2]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", "refuted");
	},
	"UFTheory-excluded-middle-variables"() {
		const smt = new uf.UFTheory();
		const a = smt.createVariable(ir.T_BOOLEAN, "a");
		const b = smt.createVariable(ir.T_BOOLEAN, "b");
		const c = smt.createVariable(ir.T_BOOLEAN, "c");

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		const aeqb = smt.createApplication(eq, [a, b]);
		const aeqc = smt.createApplication(eq, [a, c]);
		const beqc = smt.createApplication(eq, [b, c]);
		const aneqb = smt.createApplication(not, [aeqb]);
		const aneqc = smt.createApplication(not, [aeqc]);
		const bneqc = smt.createApplication(not, [beqc]);

		// Three booleans cannot all be unequal.
		smt.addConstraint([aneqb]);
		smt.addConstraint([aneqc]);
		smt.addConstraint([bneqc]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-excluded-middle-function-of-bool"() {
		const smt = new uf.UFTheory();
		const a = smt.createVariable(ir.T_BOOLEAN, "a");
		const b = smt.createVariable(ir.T_BOOLEAN, "b");
		const c = smt.createVariable(ir.T_BOOLEAN, "c");
		const f = smt.createFunction(ir.T_INT, {}, "f");

		const fa = smt.createApplication(f, [a]);
		const fb = smt.createApplication(f, [b]);
		const fc = smt.createApplication(f, [c]);

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const faeqfb = smt.createApplication(eq, [fa, fb]);
		const faeqfc = smt.createApplication(eq, [fa, fc]);
		const fbeqfc = smt.createApplication(eq, [fb, fc]);

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");
		const faneqfb = smt.createApplication(not, [faeqfb]);
		const faneqfc = smt.createApplication(not, [faeqfc]);
		const fbneqfc = smt.createApplication(not, [fbeqfc]);

		// The result of mapping three booleans cannot all be unequal.
		smt.addConstraint([faneqfb]);
		smt.addConstraint([faneqfc]);
		smt.addConstraint([fbneqfc]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-bool-equality-ensures-same-sign"() {
		const smt = new uf.UFTheory();
		const x = smt.createVariable(ir.T_BOOLEAN, "x");
		const y = smt.createVariable(ir.T_BOOLEAN, "y");
		const z = smt.createVariable(ir.T_BOOLEAN, "z");

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const xeqy = smt.createApplication(eq, [x, y]);
		const yeqz = smt.createApplication(eq, [y, z]);

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");
		const notx = smt.createApplication(not, [x]);

		smt.addConstraint([xeqy]);
		smt.addConstraint([yeqz]);
		smt.addConstraint([notx]);
		smt.addConstraint([z]);

		// Two booleans that are equal must have the same boolean assignment.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-bool-inequality-ensures-opposite-sign"() {
		const smt = new uf.UFTheory();
		const x = smt.createVariable(ir.T_BOOLEAN, "x");
		const y = smt.createVariable(ir.T_BOOLEAN, "y");
		const z = smt.createVariable(ir.T_BOOLEAN, "z");

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		const xeqy = smt.createApplication(eq, [x, y]);
		const xneqy = smt.createApplication(not, [xeqy]);
		const yeqz = smt.createApplication(eq, [y, z]);

		// Two booleans that are inequal must have opposite boolean assignments.
		smt.addConstraint([xneqy]);
		smt.addConstraint([yeqz]);
		smt.addConstraint([x]);
		smt.addConstraint([z]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-equality-between-same-constants"() {
		const smt = new uf.UFTheory();

		const one = smt.createConstant(ir.T_INT, 1);
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const oneeqone = smt.createApplication(eq, [one, one]);

		// A symbol is equal to itself.
		smt.addConstraint([oneeqone]);
		assert(smt.attemptRefutation(), "is equal to", { model: {} });
	},
	"UFTheory-equality-between-distinct-constants"() {
		const smt = new uf.UFTheory();

		const one = smt.createConstant(ir.T_INT, 1);
		const two = smt.createConstant(ir.T_INT, 2);

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const oneeqtwo = smt.createApplication(eq, [one, two]);

		// Two distinct symbols cannot be equal.
		smt.addConstraint([oneeqtwo]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-assert-contradiction"() {
		const smt = new uf.UFTheory();
		const bool = smt.createVariable(ir.T_BOOLEAN, "bool");
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");
		smt.addConstraint([bool]);
		smt.addConstraint([smt.createApplication(not, [bool])]);

		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-pop-contradiction"() {
		const smt = new uf.UFTheory();

		const one = smt.createConstant(ir.T_INT, 1);
		const two = smt.createConstant(ir.T_INT, 2);

		const alpha = smt.createVariable(ir.T_INT, "alpha");
		const f = smt.createFunction(ir.T_INT, {}, "f");
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");

		const fone = smt.createApplication(f, [one]);
		const falpha = smt.createApplication(f, [alpha]);

		smt.addConstraint([smt.createApplication(eq, [fone, one])]);
		smt.addConstraint([smt.createApplication(eq, [falpha, two])]);

		assert(smt.attemptRefutation(), "is equal to", { model: {} });

		smt.pushScope();
		smt.addConstraint([smt.createApplication(eq, [one, alpha])]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
		smt.popScope();

		assert(smt.attemptRefutation(), "is equal to", { model: {} });

		smt.pushScope();
		smt.addConstraint([smt.createApplication(eq, [two, alpha])]);
		assert(smt.attemptRefutation(), "is equal to", { model: {} });
		smt.popScope();
	},
	"UFTheory-basic-transitivity"() {
		const smt = new uf.UFTheory();

		const alpha = smt.createVariable(ir.T_INT, "alpha");
		const beta = smt.createVariable(ir.T_INT, "beta");
		const gamma = smt.createVariable(ir.T_INT, "gamma");

		const f = smt.createFunction(ir.T_BOOLEAN, { transitive: true }, "f");

		smt.addConstraint([smt.createApplication(f, [alpha, beta])]);
		smt.addConstraint([smt.createApplication(f, [beta, gamma])]);

		// (a <= b && b <= g) is satisfiable.
		assert(smt.attemptRefutation(), "is equal to", { model: {} });

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		// (a <= g) is implied by the previous constraints, so this is not
		// satisfiable.
		smt.addConstraint([smt.createApplication(not, [
			smt.createApplication(f, [alpha, gamma]),
		])]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFSolver-transitivity"() {
		const solver = new uf.UFSolver();
		const alpha = solver.createVariable("alpha");
		const beta = solver.createVariable("beta");
		const gamma = solver.createVariable("gamma");

		const p = solver.createFn({ transitive: true }, "p");

		const query: uf.Assumption<number>[] = [
			{
				constraint: solver.createApplication(p, [alpha, beta]),
				assignment: true,
				reason: 100,
			},
			{
				constraint: solver.createApplication(p, [beta, gamma]),
				assignment: true,
				reason: 200,
			},
			{
				constraint: solver.createApplication(p, [alpha, gamma]),
				assignment: false,
				reason: 300,
			},
		];

		const result = solver.refuteUsingTheory(query);
		assert(result, "is equal to", {
			tag: "inconsistent",
			inconsistencies: [new Set([100, 200, 300])],
		});
	},
	"UFTheory-transitivity-with-choice"() {
		const smt = new uf.UFTheory();

		const alpha = smt.createVariable(ir.T_INT, "alpha");
		const beta = smt.createVariable(ir.T_INT, "beta");
		const gamma = smt.createVariable(ir.T_INT, "gamma");
		const delta = smt.createVariable(ir.T_INT, "delta");

		const f = smt.createFunction(ir.T_BOOLEAN, { transitive: true }, "f");

		smt.addConstraint([smt.createApplication(f, [alpha, beta])]);
		smt.addConstraint([smt.createApplication(f, [alpha, gamma])]);
		smt.addConstraint([
			smt.createApplication(f, [beta, delta]),
			smt.createApplication(f, [gamma, delta]),
		]);

		// This is satisfiable.
		assert(smt.attemptRefutation(), "is equal to", { model: {} });

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		// (a <= d) is implied by either (a <= b & b <= d) or (a <= g & g <= d).
		smt.addConstraint([smt.createApplication(not, [
			smt.createApplication(f, [alpha, delta]),
		])]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-transitivity-with-short-equivalence-class"() {
		const smt = new uf.UFTheory();

		const alpha = smt.createVariable(ir.T_INT, "alpha");
		const beta = smt.createVariable(ir.T_INT, "beta");
		const gamma = smt.createVariable(ir.T_INT, "gamma");
		const delta = smt.createVariable(ir.T_INT, "delta");

		//   b
		//  /|
		// a | d
		//   |/
		//   g

		const f = smt.createFunction(ir.T_BOOLEAN, { transitive: true }, "f");
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");

		smt.addConstraint([smt.createApplication(eq, [beta, gamma])]);
		smt.addConstraint([smt.createApplication(f, [alpha, beta])]);
		smt.addConstraint([smt.createApplication(f, [gamma, delta])]);

		// This is satisfiable.
		assert(smt.attemptRefutation(), "is equal to", { model: {} });

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		// a <= b == g <= d implies a <= d.
		smt.addConstraint([smt.createApplication(not, [
			smt.createApplication(f, [alpha, delta]),
		])]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFSolver-transitivity-with-equivalence"() {
		const solver = new uf.UFSolver();
		const f = solver.createFn({ transitive: true }, "f");
		const eq = solver.createFn({ eq: true }, "==");

		const as = [];
		const bs = [];
		const cs = [];
		for (let i = 0; i < 10; i++) {
			as[i] = solver.createVariable("a[" + i + "]");
			bs[i] = solver.createVariable("b[" + i + "]");
			cs[i] = solver.createVariable("c[" + i + "]");
		}

		const assumptions: uf.Assumption<number>[] = [
			{
				constraint: solver.createApplication(f, [as[0], bs[0]]),
				assignment: true,
				reason: 7777,
			},
			{
				constraint: solver.createApplication(f, [bs[bs.length - 1], cs[0]]),
				assignment: true,
				reason: 8888,
			},
			{
				constraint: solver.createApplication(f, [as[as.length - 1], cs[cs.length - 1]]),
				assignment: false,
				reason: 9999,
			},
		];

		for (const i of [6, 5, 3, 1, 7, 8, 0, 4, 2]) {
			assumptions.push({
				constraint: solver.createApplication(eq, [as[i], as[i + 1]]),
				assignment: true,
				reason: i + 10,
			});
			assumptions.push({
				constraint: solver.createApplication(eq, [bs[i], bs[i + 1]]),
				assignment: true,
				reason: i + 100,
			});
			assumptions.push({
				constraint: solver.createApplication(eq, [cs[i], cs[i + 1]]),
				assignment: true,
				reason: i + 1000,
			});
		}

		const result = solver.refuteUsingTheory(assumptions);
		assert(result, "is equal to", {
			tag: "inconsistent",
			inconsistencies: [
				new Set([
					10, 11, 12, 13, 14, 15, 16, 17, 18,
					100, 101, 102, 103, 104, 105, 106, 107, 108,
					1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008,
					7777, 8888, 9999,
				]),
			],
		});
	},
	"UFTheory-transitivity-with-long-equivalence-class"() {
		const smt = new uf.UFTheory();

		const f = smt.createFunction(ir.T_BOOLEAN, { transitive: true }, "f");
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");

		const alphas = [];
		const betas = [];
		const gammas = [];
		for (let i = 0; i < 10; i++) {
			alphas[i] = smt.createVariable(ir.T_INT, "a[" + i + "]");
			betas[i] = smt.createVariable(ir.T_INT, "b[" + i + "]");
			gammas[i] = smt.createVariable(ir.T_INT, "g[" + i + "]");
		}

		// Join all the elements together.
		for (let i = 0; i + 1 < alphas.length; i++) {
			smt.addConstraint([smt.createApplication(eq, [alphas[i], alphas[i + 1]])]);
			smt.addConstraint([smt.createApplication(eq, [betas[i], betas[i + 1]])]);
			smt.addConstraint([smt.createApplication(eq, [gammas[i], gammas[i + 1]])]);
		}

		// a[0] = ... = a[n] < b[0] = ... = b[n] < g[0] = ... = g[n]
		smt.addConstraint([smt.createApplication(f, [alphas[alphas.length / 2 | 0], betas[betas.length / 2 | 0]])]);
		smt.addConstraint([smt.createApplication(f, [betas[betas.length / 2 | 0], gammas[gammas.length / 2 | 0]])]);

		// This is satisfiable.
		assert(smt.attemptRefutation(), "is equal to", { model: {} });

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true }, "not");

		// a < b and b < g implies a < g.
		smt.addConstraint([smt.createApplication(not, [
			smt.createApplication(f, [alphas[alphas.length / 2 | 0], gammas[gammas.length / 2 | 0]]),
		])]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFSolver-transitive-constants"() {
		const solver = new uf.UFSolver<number>();

		const c1 = solver.createConstant(1);
		const c2 = solver.createConstant(2);
		const b = solver.createVariable("b");

		const eq = solver.createFn({ eq: true }, "==");
		const eq_1_b = solver.createApplication(eq, [c1, b]);
		const eq_2_b = solver.createApplication(eq, [c2, b]);

		const query: uf.Assumption<number>[] = [
			{
				constraint: eq_2_b,
				assignment: true,
				reason: 400,
			},
			{
				constraint: eq_1_b,
				assignment: true,
				reason: 300,
			},
		];
		const result4 = solver.refuteUsingTheory(query);
		assert(result4, "is equal to", {
			tag: "inconsistent",
			inconsistencies: [new Set([300, 400])],
		});
	},
	"UFSolver-eq-violation"() {
		const solver = new uf.UFSolver<number>();

		const c1 = solver.createConstant(1);
		const c2 = solver.createConstant(2);
		const b = solver.createVariable("b");

		const f = solver.createFn({}, "f");
		const f1 = solver.createApplication(f, [c1]);
		const fb = solver.createApplication(f, [b]);

		const eq = solver.createFn({ eq: true }, "==");
		const eq_f1_1 = solver.createApplication(eq, [f1, c1]);
		const eq_fb_2 = solver.createApplication(eq, [fb, c2]);
		const eq_1_b = solver.createApplication(eq, [c1, b]);

		const query: uf.Assumption<number>[] = [
			{
				constraint: eq_f1_1,
				assignment: true,
				reason: 100,
			},
			{
				constraint: eq_fb_2,
				assignment: true,
				reason: 200,
			},
			{
				constraint: eq_1_b,
				assignment: true,
				reason: 300,
			},
		];
		const result4 = solver.refuteUsingTheory(query);
		assert(result4, "is equal to", {
			tag: "inconsistent",
			inconsistencies: [new Set([100, 200, 300])],
		});
	},
	"UFSolver-transitiveAcyclic-is-anti-reflexive"() {
		const solver = new uf.UFSolver<number>();

		const f = solver.createFn({ transitive: true, transitiveAcyclic: true }, "f");
		const eq = solver.createFn({ eq: true }, "==");

		const a = solver.createVariable("a");
		const b = solver.createVariable("b");

		const query1: uf.Assumption<number>[] = [
			{
				constraint: solver.createApplication(eq, [a, b]),
				assignment: true,
				reason: 100,
			},
		];

		const result1 = solver.refuteUsingTheory(query1);
		assert(result1, "is equal to", {
			tag: "model",
			model: { model: {} },
		});

		const query2: uf.Assumption<number>[] = [
			{
				constraint: solver.createApplication(eq, [a, b]),
				assignment: true,
				reason: 100,
			},
			{
				constraint: solver.createApplication(f, [a, b]),
				assignment: true,
				reason: 200,
			},
		];

		const result2 = solver.refuteUsingTheory(query2);
		assert(result2, "is equal to", {
			tag: "inconsistent",
			inconsistencies: [new Set([100, 200])],
		});
	},
	"UFTheory-transitive-with-triangle"() {
		const smt = new uf.UFTheory();

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true }, "==");
		const f = smt.createFunction(ir.T_BOOLEAN, { transitive: true, transitiveAcyclic: true }, "f");

		const a = smt.createVariable(ir.T_INT, "a");
		const b = smt.createVariable(ir.T_INT, "b");
		const c = smt.createVariable(ir.T_INT, "c");
		const d = smt.createVariable(ir.T_INT, "d");

		// a < b
		// =   =
		// c > d
		smt.addConstraint([smt.createApplication(eq, [a, c])]);
		smt.addConstraint([smt.createApplication(eq, [b, d])]);
		smt.addConstraint([smt.createApplication(f, [a, b])]);

		assert(smt.attemptRefutation(), "is equal to", { model: {} });

		smt.addConstraint([smt.createApplication(f, [d, c])]);

		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFSolver-antireflexive-interpreter-yes"() {
		const solver = new uf.UFSolver<string>();

		const ltF = solver.createFn({
			interpreter: {
				f(...args: (unknown | null)[]): unknown | null {
					if (args.length !== 2) {
						throw new Error("unexpected");
					}
					const a = args[0];
					const b = args[1];
					if (a === null || b === null) {
						return null;
					}
					if (typeof a !== "number" || typeof b !== "number") {
						throw new Error("unexpected");
					}
					return a < b;
				},
			},
		}, "<");

		const n1 = solver.createConstant(1);

		const refutation = solver.refuteUsingTheory([
			{
				constraint: solver.createApplication(ltF, [n1, n1]),
				assignment: true,
				reason: "alpha",
			},
		]);

		assert(refutation, "is equal to", {
			tag: "inconsistent",
			inconsistencies: [new Set(["alpha"])],
		});
	},
	"UFTheory-antireflexive-interpreter"() {
		const smt = new uf.UFTheory();
		smt.addConstraint([
			smt.createConstant(ir.T_BOOLEAN, true),
		]);
		const ltF = smt.createFunction(ir.T_BOOLEAN, {
			interpreter: {
				f(...args: (unknown | null)[]): unknown | null {
					if (args.length !== 2) {
						throw new Error("unexpected");
					}
					const a = args[0];
					const b = args[1];
					if (a === null || b === null) {
						return null;
					}
					if (typeof a !== "number" || typeof b !== "number") {
						throw new Error("unexpected");
					}
					return a < b;
				},
			},
		}, "<");

		const isSatisfiable = (clauses: uf.ValueID[][]): boolean => {
			smt.pushScope();
			for (let i = 0; i < clauses.length; i++) {
				smt.addConstraint(clauses[i]);
			}
			const result = smt.attemptRefutation();
			smt.popScope();
			return result !== "refuted";
		}

		const n1 = smt.createConstant(ir.T_INT, 1);
		const n2 = smt.createConstant(ir.T_INT, 2);
		const n3 = smt.createConstant(ir.T_INT, 3);

		assert(isSatisfiable([[smt.createApplication(ltF, [n1, n1])]]), "is equal to", false);
		assert(isSatisfiable([[smt.createApplication(ltF, [n2, n1])]]), "is equal to", false);
		assert(isSatisfiable([[smt.createApplication(ltF, [n1, n2])]]), "is equal to", true);
		assert(isSatisfiable([[smt.createApplication(ltF, [n1, n3])]]), "is equal to", true);
	},
	"UFSolver-always-false-interpreter"() {

		const solver = new uf.UFSolver<string>();

		const ltF = solver.createFn({
			interpreter: {
				f(...args: (unknown | null)[]): unknown | null {
					return false;
				},
			},
		}, "<");

		const refutation = solver.refuteUsingTheory([
			{
				constraint: solver.createApplication(ltF, []),
				assignment: true,
				reason: "alpha",
			},
		]);

		assert(refutation, "is equal to", {
			tag: "inconsistent",
			inconsistencies: [new Set(["alpha"])],
		});
	},
};
