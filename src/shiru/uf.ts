import * as ir from "./ir.js";
import * as sat from "./sat.js";
import * as smt from "./smt.js";

export interface UFCounterexample {
	model: {},
}

export type FnID = symbol & { __brand: "uf.FnID" };

export type ValueID = symbol & { __brand: "uf.FnID" };

export interface Semantics {
	/** An `eq` function respects congruence: a == b implies f(a) == f(b). */
	eq?: true,

	/** A `not` function is only applied to booleans.
	 * f(true) == false, and f(false) == true.
	 */
	not?: true,

	/** A `transitive` function respects transitivity:
	 * f(a, b) and f(b, a) implies f(a, c).
	 * (This need not be specified for `eq` functions)
	 */
	transitive?: true,

	/** A `transitiveAcyclic` function is a `transitive` function which does not
	 * admit cycles (a < b < c < d < ... < a). This implies that the relation
	 * is anti-reflexive.
	 */
	transitiveAcyclic?: true,

	interpreter?: (...args: (unknown | null)[]) => unknown | null,
}

export class UFTheory extends smt.SMTSolver<ValueID[], UFCounterexample> {
	/** For debugging purposes.
	 *
	 * Inverts the constraint -> literal mapping implemented by `clausify`.
	 */
	override showLiteral(literal: number): string {
		throw new Error("Method not implemented.");
	}

	override learnTheoryClauses(
		partialAssignment: sat.Literal[],
		unassigned: sat.Literal[],
	): { tag: "implied", impliedClauses: sat.Literal[][], model: UFCounterexample }
		| { tag: "unsatisfiable", conflictClauses: sat.Literal[][] } {
		throw new Error("TODO: learnTheoryClauses");
	}

	protected override clausify(constraint: ValueID[]): sat.Literal[][] {
		throw new Error("TODO: clausify");
	}

	createFunction(
		returnType: ir.Type,
		semantics: Semantics,
		debugName: string,
	): FnID {
		throw new Error("TODO: createFunction");
	}

	createConstant(t: ir.Type, c: unknown): ValueID {
		throw new Error("TODO: createConstant");
	}

	createVariable(type: ir.Type, debugName: string): ValueID {
		throw new Error("TODO: createVariable");
	}

	createApplication(fnID: FnID, args: ValueID[]): ValueID {
		throw new Error("TODO: createApplication");
	}
}
