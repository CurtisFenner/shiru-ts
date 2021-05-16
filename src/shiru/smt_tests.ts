import { SMTSolver, UFConstraint, UFFunction, UFPredicate, UFTheory, UFValue, UFVariable } from "./smt";
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

function app(f: string, ...args: (UFValue | string)[]): UFValue {
	return { tag: "app", f: f as UFFunction, args: args as UFValue[] };
}

function eq(left: UFValue | string, right: UFValue | string): UFConstraint {
	return {
		tag: "=",
		left: left as UFValue,
		right: right as UFValue,
	};
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
	"UFTheory-basic-equality-refuted"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 1);
		smt.defineVariable("y1", 1);
		smt.defineVariable("z1", 1);

		smt.addConstraint([
			{ tag: "=", left: "x1" as UFVariable, right: "y1" as UFVariable },
		]);
		smt.addConstraint([
			{ tag: "=", left: "x1" as UFVariable, right: "z1" as UFVariable },
		]);
		smt.addConstraint([
			{
				tag: "not",
				constraint: { tag: "=", left: "y1" as UFVariable, right: "z1" as UFVariable }
			},
		]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", "refuted");
	},
	"UFTheory-basic-satisfiable"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 1);
		smt.defineVariable("x2", 1);
		smt.defineFunction("f", 2);

		smt.addConstraint([
			{ tag: "=", left: "x1" as UFVariable, right: "x2" as UFVariable },
			{
				tag: "not",
				constraint: {
					tag: "=", left: app("f", "x1"), right: app("f", "x2"),
				}
			},
		]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", {});
	},
	"UFTheory-basic-function-refuted"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 1);
		smt.defineVariable("x2", 1);
		smt.defineFunction("f", 2);

		smt.addConstraint([
			{ tag: "=", left: "x1" as UFVariable, right: "x2" as UFVariable },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "=", left: app("f", "x1"), right: app("f", "x2") } },
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
			{ tag: "not", constraint: eq("x1", "x2") },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: eq("x1", "x3") },
		]);
		smt.addConstraint([
			{ tag: "not", constraint: eq("x2", "x3") },
		]);

		// Three booleans cannot all be unequal.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-excluded-middle-predicates"() {
		const smt = new UFTheory();
		smt.defineVariable("x1", 0);
		smt.defineVariable("x2", 0);
		smt.defineVariable("x3", 0);
		smt.defineFunction("p", "bool");

		const p1: UFPredicate = app("p", "x1");
		const p2: UFPredicate = app("p", "x2");
		const p3: UFPredicate = app("p", "x3");
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
	"UFTheory-bool-equality-ensures-same-sign"() {
		const smt = new UFTheory();
		smt.defineVariable("x", "bool");
		smt.defineVariable("y", "bool");
		smt.defineVariable("z", "bool");
		smt.addConstraint([eq("x", "y")]);
		smt.addConstraint([eq("y", "z")]);
		smt.addConstraint([
			{ tag: "not", constraint: { tag: "predicate", predicate: "x" as UFVariable } },
		]);
		smt.addConstraint([
			{ tag: "predicate", predicate: "z" as UFVariable },
		]);

		// Two booleans that are equal must have the same boolean assignment.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-bool-inequality-ensures-opposite-sign"() {
		const smt = new UFTheory();
		smt.defineVariable("x", "bool");
		smt.defineVariable("y", "bool");
		smt.defineVariable("z", "bool");
		smt.addConstraint([
			{ tag: "not", constraint: eq("x", "y") },
		]);
		smt.addConstraint([eq("y", "z")]);
		smt.addConstraint([
			{ tag: "predicate", predicate: "x" as UFVariable },
		]);
		smt.addConstraint([
			{ tag: "predicate", predicate: "z" as UFVariable },
		]);

		// Two booleans that are inequal must have opposite boolean assignments.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-equality-between-same-constants"() {
		const smt = new UFTheory();

		// Create distinct symbols.
		const alpha: UFValue = { tag: "literal", literal: "a", sort: 1 };
		smt.addConstraint([
			{ tag: "=", left: alpha, right: alpha },
		]);

		// A symbol may be equal to itself.
		assert(smt.attemptRefutation(), "is equal to", {});
	},
	"UFTheory-equality-between-distinct-constants"() {
		const smt = new UFTheory();

		// Create distinct symbols.
		const alpha: UFValue = { tag: "literal", literal: "a", sort: 1 };
		const beta: UFValue = { tag: "literal", literal: "b", sort: 1 };
		smt.addConstraint([
			{ tag: "=", left: alpha, right: beta },
		]);

		// Two distinct symbols cannot be equal.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
};
