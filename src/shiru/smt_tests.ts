import { SMTSolver } from "./smt.js";
import { assert } from "./test.js";


type BoundedExpr = number | string | [BoundedExpr, "+" | "*", BoundedExpr];
type BoundedRelation = [BoundedExpr, "=" | "!=", BoundedExpr];

// Defines the finite domain of a variable referenced in a BoundedExpr.
type BoundedConfig = [string, number[]];

/// Defines a simple SMTTheory where string variables can take on values from a
/// finite set of numbers, and can have simple arithmetic expressions evaluated.
type BoundedModel = Record<string, number>;

class BoundedTheory extends SMTSolver<BoundedRelation[], BoundedModel> {
	private variables: Record<string, number[]> = {};
	private constraints: Record<number, BoundedRelation> = {};
	private constraintKey: BoundedModel = {};
	private nextTerm = 1;

	private evaluate(
		environment: BoundedModel,
		expr: BoundedExpr,
	): number {
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

	override showLiteral(literal: number): string {
		return literal.toFixed(0);
	}

	private check(
		environment: BoundedModel,
		relation: BoundedRelation,
	): boolean {
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

	override learnTheoryClauses(
		partialAssignment: number[],
		unassigned: number[],
	): { tag: "implied", impliedClauses: number[][], model: BoundedModel }
		| { tag: "unsatisfiable", conflictClauses: number[][] } {
		let environments: BoundedModel[] = [{}];
		for (let v in this.variables) {
			const domain = this.variables[v];
			const empty: BoundedModel[] = [];
			const withValue = domain.map(value => {
				return environments.map(r => ({ ...r, [v]: value }));
			});
			environments = empty.concat(...withValue);
		}

		for (let environment of environments) {
			let all = true;
			for (let signedConstraint of partialAssignment) {
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
				return {
					tag: "implied",
					impliedClauses: [],
					model: environment,
				};
			}
		}

		// At least one assignment must change.
		return {
			tag: "unsatisfiable",
			conflictClauses: [partialAssignment.map(x => -x)],
		};
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
	"BoundedTheory-basic"() {
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
};
