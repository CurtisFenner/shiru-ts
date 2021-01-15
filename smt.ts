import { Literal, SATSolver } from "./sat";

export class UnionFind {
	parents: number[] = [];
	ranks: number[] = [];

	expandTo(n: number) {
		for (let i = this.parents.length; i <= n; i++) {
			this.parents.push(i);
			this.ranks.push(0);
		}
	}

	/// representative returns a "representative" element of the given object's
	/// equivalence class, such that two elements are members of the same 
	/// equivalence class if and only if their representatives are the same.
	representative(n: number): number {
		while (this.parents[n] !== n) {
			// "Path halving"
			this.parents[n] = this.parents[this.parents[n]];
			n = this.parents[n];
		}
		return n;
	}

	/// compareEqual returns whether or not the two objects are members of the
	/// same equivalence class.
	compareEqual(a: number, b: number): boolean {
		return this.representative(a) === this.representative(b);
	}

	/// union updates this datastructure to join the equivalence classes of 
	/// objects a and b.
	/// RETURNS false when the objects were already members of the same 
	///         equivalence class.
	union(a: number, b: number): boolean {
		const ra = this.representative(a);
		const rb = this.representative(b);
		if (ra == rb) {
			return false;
		}

		let child: number;
		let parent: number;

		if (this.ranks[ra] < this.ranks[rb]) {
			child = ra;
			parent = rb;
		} else {
			child = rb;
			parent = ra;
		}

		this.parents[child] = parent;
		if (this.ranks[child] === this.ranks[parent]) {
			this.ranks[parent] += 1;
		}
		return true;
	}

	/// RETURNS the set of equivalence classes managed by this data structure.
	components(): number[][] {
		let components: number[][] = [];
		for (let i = 0; i < this.parents.length; i++) {
			components.push([]);
		}
		for (let i = 0; i < this.parents.length; i++) {
			components[this.parents[i]].push(i);
		}
		let out: number[][] = [];
		for (let i = 0; i < components.length; i++) {
			if (components[i].length !== 0) {
				out.push(components[i]);
			}
		}
		return out;
	}
}

/// SMTSolver represents an "satisfiability modulo theories" instance, with 
/// support for quantifier instantiation.
/// With respect to refutation, SMTSolver is sound but not complete -- some
/// returned "satisfactions" do not actually satisfy the instance, but all
/// refutation results definitely refute the instance.
export class SMTSolver<E, Config, Counterexample> {
	sat: SATSolver;
	constructor(private theory: SMTTheory<E, Config, Counterexample>) {
		this.sat = new SATSolver();
	}

	configure(configuration: Config) {
		this.theory.configure(configuration);
	}

	addConstraint(constraint: E) {
		for (let clause of this.theory.clausify(constraint)) {
			let maxTerm = 0;
			for (let literal of clause) {
				const term = literal > 0 ? literal : -literal;
				maxTerm = Math.max(maxTerm, term);
			}
			this.sat.initTerms(maxTerm);
			this.sat.addClause(clause);
		}
	}

	/// RETURNS "refuted" when the given constraints can provably not be
	/// satisfied.
	/// RETURNS a counter example (satisfaction) when refutation fails; this may
	/// not be a truly realizable counter-examples, as instantiation and the 
	/// theory solver may be incomplete.
	attemptRefutation(): "refuted" | Counterexample {
		while (true) {
			const booleanModel = this.sat.solve();
			if (booleanModel === "unsatisfiable") {
				return "refuted";
			} else {
				// Clausal proof adds additional constraints to the formula, which
				// preserve satisfiablity (but not necessarily logical equivalence).
				// These are useful in subsequent runs of the solver; HOWEVER, 
				// clauses which merely preserve satisfiability and not logical 
				// equivalence must be pruned.
				// TODO: Remove (and attempt to re-add) any non-implied clauses.
				const theoryClause = this.theory.rejectModel(booleanModel);
				if (Array.isArray(theoryClause)) {
					// Completely undo the assignment.
					// TODO: theoryClause should be an asserting clause, so the
					// logic in backtracking should be able to replace this.
					this.sat.rollbackToDecisionLevel(-1);
					console.log("prior to add theory clause:", this.sat);
					console.log("!!", "add theory clause", theoryClause);
					this.sat.addClause(theoryClause);
				} else {
					// TODO: Instantiation may need to take place here.
					// The SAT+SMT solver has failed to refute the formula.
					this.sat.rollbackToDecisionLevel(-1);
					return theoryClause;
				}
			}
		}
	}
}

export abstract class SMTTheory<E, Config, Counterexample> {

	abstract configure(configuration: Config): void;

	/// rejectModel returns a new clause to add to the SAT solver which 
	/// rejects this concrete assignment.
	/// The returned clause should be an asserting clause in reference to the
	/// concrete assignment.
	abstract rejectModel(concrete: Literal[]): Counterexample | Literal[];

	/// clausify returns a set of clauses to add to the underlying SAT solver.
	/// This modifies state, associating literals (and other internal variables)
	/// with the pieces of this constraint, possibly for instantiation.
	abstract clausify(constraint: E): Literal[][];

	/// TODO: Instantiation of quantifiers, which is sometimes done in the place
	/// of making decisions in the SATSolver.
}
