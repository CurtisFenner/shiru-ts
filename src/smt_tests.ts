import { SMTSolver, UFPredicate, UFTheory } from "./smt";
import { assert } from "./test";


type BoundedExpr = number | string | [BoundedExpr, "+" | "*", BoundedExpr];
type BoundedRelation = [BoundedExpr, "=" | "!=", BoundedExpr];

// Defines the finite domain of a variable referenced in a BoundedExpr.
type BoundedConfig = [string, number[]];

/// Defines a simple SMTTheory where string variables can take on values from a
/// finite set of numbers, and can have simple arithmetic expressions evaluated.
class BoundedTheory extends SMTSolver<BoundedRelation[], Record<string, number>> {
	private variables: Record<string, number[]> = {};
	private constraints: Record<number, BoundedRelation> = {};
	private constraintKey: Record<string, number> = {};
	private nextTerm = 1;

	private evaluate(environment: Record<string, number>, expr: BoundedExpr): number {
		if (typeof expr === "number") {
			return expr;
		} else if (typeof expr === "string") {
			return environment[expr];
		} else {
			const left = this.evaluate(environment, expr[0]);
			const right = this.evaluate(environment, expr[2]);
			if (expr[1] === "*") {
				return left * right;
			} else {
				return left + right;
			}
		}
	}

	private check(environment: Record<string, number>, relation: BoundedRelation): boolean {
		const left = this.evaluate(environment, relation[0]);
		const right = this.evaluate(environment, relation[2]);
		if (relation[1] === "!=") {
			return left != right;
		} else {
			return left == right;
		}
	}

	defineVariable(configuration: BoundedConfig): void {
		this.variables[configuration[0]] = configuration[1];
	}

	rejectModel(concrete: number[]): number[] | Record<string, number> {
		let environments: Record<string, number>[] = [{}];
		for (let v in this.variables) {
			const domain = this.variables[v];
			const empty: Record<string, number>[] = [];
			const withValue = domain.map(value => environments.map(r => ({ ...r, [v]: value })));
			environments = empty.concat(...withValue);
		}

		for (let environment of environments) {
			let all = true;
			for (let signedConstraint of concrete) {
				const term = Math.abs(signedConstraint);
				const constraint = this.constraints[term];
				const actual = this.check(environment, constraint);
				if (actual && signedConstraint < 0) {
					all = false;
				} else if (!actual && signedConstraint > 0) {
					all = false;
				}
			}
			if (all) {
				// Found a model which is consistent with this theory.
				return environment;
			}
		}

		// At least one must change.
		return concrete.map(x => -x);
	}

	clausify(constraint: BoundedRelation[]): number[][] {
		let clause: number[] = [];
		for (let alternative of constraint) {
			const key = JSON.stringify(alternative);
			if (this.constraintKey[key]) {
				clause.push(this.constraintKey[key]);
			} else {
				const term = this.nextTerm;
				this.nextTerm += 1;
				this.constraints[term] = alternative;
				clause.push(term);
			}
		}
		return [clause];
	}
}

export const tests = {
	"simple-smt-bounded-refutable"() {
		const smt = new BoundedTheory();
		smt.defineVariable(["a", [-2, -1, 0, 1, 2]]);
		smt.defineVariable(["b", [-2, -1, 0, 1, 2]]);
		smt.defineVariable(["c", [-2, -1, 0, 1, 2]]);
		smt.addConstraint([
			[["a", "+", "b"], "=", 4],
			[["a", "+", "b"], "=", -4],
		]);
		smt.addConstraint([["c", "=", 0]]);
		smt.addConstraint([[["a", "*", "a"], "=", ["a", "+", "a"]]]);

		const refute = smt.attemptRefutation();
		assert(refute, "is equal to", {
			a: 2,
			b: 2,
			c: 0,
		});
		const refute2 = smt.attemptRefutation();
		assert(refute2, "is equal to", refute);

		// Add a constraint that isn't true for a: 2, b: 2, c: 0.
		smt.addConstraint([
			[["a", "+", ["c", "*", "b"]], "!=", "a"],
		]);

		const refute3 = smt.attemptRefutation();
		assert(refute3, "is equal to", "refuted");
	},
	"UFTheory-basic-equality-refuted"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 1);
		smt.defineVariable("y1", 1);
		smt.defineVariable("z1", 1);

		smt.addConstraint([
			{ tag: "=", left: "x1", right: "y1" },
		]);
		smt.addConstraint([
			{ tag: "=", left: "x1", right: "z1" },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: "y1", right: "z1" } },
		]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", "refuted");
	},
	"UFTheory-basic-satisfiable"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 1);
		smt.defineVariable("x2", 1);
		smt.defineFunction("f", [1, 1], 2);

		smt.addConstraint([
			{ tag: "=", left: "x1", right: "x2" },
			{ tag: "not", constraint: { tag: "=", left: ["app", "f", ["x1"]], right: ["app", "f", ["x2"]] } },
		]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", {});
	},
	"UFTheory-basic-function-refuted"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 1);
		smt.defineVariable("x2", 1);
		smt.defineFunction("f", [1, 1], 2);

		smt.addConstraint([
			{ tag: "=", left: "x1", right: "x2" },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: ["app", "f", ["x1"]], right: ["app", "f", ["x2"]] } },
		]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", "refuted");
	},
	"UFTheory-excluded-middle-variables"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", "bool");
		smt.defineVariable("x2", "bool");
		smt.defineVariable("x3", "bool");

		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: "x1", right: "x2" } },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: "x1", right: "x3" } },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: "x2", right: "x3" } },
		]);

		// Three booleans cannot all be unequal.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-excluded-middle-predicates"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 0);
		smt.defineVariable("x2", 0);
		smt.defineVariable("x3", 0);
		smt.defineFunction("p", [0], "bool");

		const p1: UFPredicate = ["app", "p", ["x1"]];
		const p2: UFPredicate = ["app", "p", ["x2"]];
		const p3: UFPredicate = ["app", "p", ["x3"]];
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: p1, right: p2 } },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: p1, right: p3 } },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: p2, right: p3 } },
		]);

		// Three booleans cannot all be unequal.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
};
