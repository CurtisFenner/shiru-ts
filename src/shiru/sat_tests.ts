import { SATSolver } from "./sat";
import { assert } from "./test";

class Arithmetic {
	private sat = new SATSolver();
	private count = 0;

	bitZero: number;
	bitOne: number;

	solution: Map<number, 0 | 1> | null = null;

	constructor() {
		const bits = this.vector(2);
		this.bitZero = bits[0];
		this.bitOne = bits[1];
		this.eqConst([this.bitZero], 0);
		this.eqConst([this.bitOne], 1);
	}

	solve() {
		const solution = this.sat.solve();
		if (solution === "unsatisfiable") {
			throw "unsatisfiable";
		}
		this.solution = new Map();
		for (const literal of solution) {
			this.solution.set(Math.abs(literal), literal > 0 ? 1 : 0);
		}
		return solution;
	}

	readInt(v: number[]) {
		const solution = this.solution;
		if (!solution) {
			throw new Error("readInt: call solve() first");
		}

		const bits = [];
		for (let i = v.length - 1; i >= 0; i--) {
			bits.push(solution.get(v[i]));
		}
		return parseInt(bits.join(""), 2);
	}

	vector(n: number) {
		this.count += n;
		this.sat.initTerms(this.count);
		let out = [];
		for (let i = 0; i < n; i++) {
			out.push(this.count - i);
		}
		return out;
	}

	/// Least significant bit first.
	eqConst(a: number[], v: number) {
		const binary = v.toString(2);
		for (let i = 0; i < a.length; i++) {
			const sign = binary[binary.length - 1 - i] === "1" ? 1 : -1;
			const clause = [sign * a[i]];
			this.sat.addClause(clause);
		}
	}

	implies(supposeLiterals: number[], concludeLiteral: number) {
		// (& supposeLiterals) => concludeLiteral
		// ~(& supposeLiterals) or concludeLiteral
		const clause = [concludeLiteral, ...supposeLiterals.map(x => -x)];
		this.sat.addClause(clause);
	}

	table(inputs: number[], outputs: number[], table: number[][]) {
		for (const row of table) {
			const ant = [];
			for (let i = 0; i < inputs.length; i++) {
				const sign = row[i] ? 1 : -1;
				ant.push(inputs[i] * sign);
			}
			for (let o = 0; o < outputs.length; o++) {
				const sign = row[inputs.length + o] ? 1 : -1;
				this.implies(ant, outputs[o] * sign);
			}
		}
	}

	bitAdderEquation(a: number, b: number, cin: number, s: number, cout: number) {
		this.table([a, b, cin], [cout, s], [
			[0, 0, 0, 0, 0],
			[0, 0, 1, 0, 1],
			[0, 1, 0, 0, 1],
			[0, 1, 1, 1, 0],
			[1, 0, 0, 0, 1],
			[1, 0, 1, 1, 0],
			[1, 1, 0, 1, 0],
			[1, 1, 1, 1, 1],
		]);
	}

	/// Add an equation that a + b = sum.
	/// Least significant bit first.
	sum(a: number[], b: number[], sum: number[]) {
		if (a.length !== b.length || a.length !== sum.length) {
			throw new Error("sum: bad call");
		}

		let carry = this.bitZero;
		for (let i = 0; i < a.length; i++) {
			const nextCarry = this.vector(1)[0];
			this.bitAdderEquation(a[i], b[i], carry, sum[i], nextCarry);
			carry = nextCarry;
		}
	}

	select(control: number, zero: number[], one: number[]): number[] {
		if (zero.length !== one.length) {
			throw new Error("select: bad");
		}

		const alloc = this.vector(zero.length);
		for (let i = 0; i < zero.length; i++) {
			this.sat.addClause([-control, -one[i], alloc[i]]);
			this.sat.addClause([-control, one[i], -alloc[i]]);

			this.sat.addClause([control, -zero[i], alloc[i]]);
			this.sat.addClause([control, zero[i], -alloc[i]]);
		}

		return alloc;
	}

	product(a: number[], b: number[]): number[] {
		// Perform "cross multiplication": repeatedly shift `b >> i` and add
		// whenever `a[i]` is `1`.
		b = b.slice(0);
		const zeros = [];
		for (let i = 0; i < b.length; i++) {
			zeros.push(this.bitZero);
		}
		let partial: number[] = this.select(a[0], zeros, b);
		for (let i = 1; i < a.length; i++) {
			b = [this.bitZero, ...b.slice(0, b.length - 1)];
			const shift = this.select(a[i], zeros, b);
			const nextPartial = this.vector(b.length);
			this.sum(partial, shift, nextPartial);
			partial = nextPartial;
		}
		return partial;
	}
}

export const tests = {
	"simple-satisfiable"() {
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
	"simple-unsatisfiable"() {
		const sat = new SATSolver();
		sat.initTerms(3);
		sat.addClause([+1, +2, -3]);
		sat.addClause([+1, -2, -3]);
		sat.addClause([-1, +2, -3]);
		sat.addClause([-1, -2, -3]);
		sat.addClause([+3]);

		const model = sat.solve();
		assert(model, "is equal to", "unsatisfiable");
	},
	"conflicting-unit-clauses"() {
		const sat = new SATSolver();
		sat.initTerms(1);
		sat.addClause([+1]);
		sat.addClause([-1]);
		const model = sat.solve();
		assert(model, "is equal to", "unsatisfiable");
	},
	"conflict-in-initial-unit-propagation"() {
		const sat = new SATSolver();
		sat.initTerms(5);

		// Initial unit propagation leads to a conflict.
		const instance = [
			[1, 2],
			[3],
			[4],
			[-2, -1, -4, -3],
			[5],
			[2, -1, -5, -4, -3],
			[-1, -5, -4, -3],
			[-2, 1, -5, -4, -3],
		];

		for (let clause of instance) {
			sat.addClause(clause);
		}

		const result = sat.solve();
		assert(result, "is equal to", "unsatisfiable");
	},
	"semiprime-factoring"() {
		const arithmetic = new Arithmetic();

		const width = 20;
		const alpha = arithmetic.vector(width);
		const beta = arithmetic.vector(width);

		const product = arithmetic.product(alpha, beta);

		const factor1 = 811;
		const factor2 = 839;
		arithmetic.eqConst(product, factor1 * factor2);

		// Only "half words".
		arithmetic.eqConst(alpha.slice(width / 2), 0);
		arithmetic.eqConst(beta.slice(width / 2), 0);

		arithmetic.solve();

		const factored = [
			arithmetic.readInt(alpha),
			arithmetic.readInt(beta)
		].sort((a, b) => a - b);

		assert(arithmetic.readInt(product), "is equal to", factor1 * factor2);
		assert(factored, "is equal to", [factor1, factor2]);

	},
	"prime-testing"() {
		const arithmetic = new Arithmetic();

		const width = 16;
		const alpha = arithmetic.vector(width);
		const beta = arithmetic.vector(width);

		const product = arithmetic.product(alpha, beta);

		arithmetic.eqConst(product, 7333);

		// Only "half words".
		arithmetic.eqConst(alpha.slice(width / 2), 0);
		arithmetic.eqConst(beta.slice(width / 2), 0);

		assert(() => arithmetic.solve(), "throws", "unsatisfiable");
	},
	"clauses-with-repeated-literals"() {
		// The solver must be able to tolerate clauses with repeated literals
		// and tautological clauses.
		const clauses = [
			[2, 3], [-4, 5], [16, 15, -14],
			[16, -18, -17], [-19, 16, -20], [4, 21],
			[23, 24], [-20, 25], [26, 27],
			[-20, 28], [-33, 14, 34], [34, -36, -35],
			[-37, 34, -38], [20, 39], [41, 42],
			[-38, 43], [38, 44], [20, 46],
			[48, 49], [-4, 50], [16, 15, -14],
			[16, -18, -17], [-19, 16, -20], [4, 51],
			[53, 54], [-20, 55], [56, 57],
			[-20, 58], [-33, 14, 34], [34, -36, -35],
			[-37, 34, -38], [20, 59], [61, 62],
			[-38, 63], [38, 64], [20, 66],
			[1], [-4, 6], [-4, 7],
			[-4, 8], [-4, 9], [-4, 10],
			[-4, 11], [-4, 12], [-4, 13],
			[6, 20, -4], [7, 20, -4], [8, 20, -4],
			[9, 20, -4], [10, 20, -4], [11, 20, -4],
			[12, 20, -4], [13, 20, -4], [6, 20, 20, -4],
			[7, 20, 20, -4], [8, 20, 20, -4], [9, 20, 20, -4],
			[29, 20, 20, -4], [30, 20, 20, -4], [31, 20, 20, -4],
			[32, 20, 20, -4], [60, 20, -4], [6, 20, -4],
			[7, 20, -4], [8, 20, -4], [9, 20, -4],
			[29, 20, -4], [30, 20, -4], [31, 20, -4],
			[32, 20, -4], [6, 20, 38, -4], [7, 20, 38, -4],
			[8, 20, 38, -4], [9, 20, 38, -4], [29, 20, 38, -4],
			[30, 20, 38, -4], [31, 20, 38, -4], [32, 20, 38, -4],
			[65, 20, -4], [4], [-67],
			[-50, 50, 1, -2, 3],
			[67, -53], [-22, -3, 53, 67], [-2, 22, 53, 67],
			[-47, -24, 53, 67], [-23, 47, 53, 67], [-40, -27, 53, 67],
			[-26, 40, 53, 67], [-45, -42, 53, 67], [-41, 45, 53, 67],
			[-52, -49, 53, 67], [-48, 52, 53, 67], [-60, -57, 53, 67],
			[-56, 60, 53, 67], [-65, -62, 53, 67], [-61, 65, 53, 67],
			[-55, -20, 53],
		];

		const sat = new SATSolver();
		for (const clause of clauses) {
			sat.initTerms(Math.max(...clause.map(x => Math.abs(x))));
			sat.addClause(clause);
		}

		const solution = sat.solve();
		assert(Array.isArray(solution), "is equal to", true);
	},
};
