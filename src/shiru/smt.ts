import * as sat from "./sat";

/// SMTSolver represents an "satisfiability modulo theories" instance, with
/// support for quantifier instantiation.
/// With respect to refutation, SMTSolver is sound but not complete -- some
/// returned "satisfactions" do not actually satisfy the instance, but all
/// refutation results definitely refute the instance.
export abstract class SMTSolver<E, Counterexample> {
	protected clauses: sat.Literal[][] = [];
	protected unscopedClauses: sat.Literal[][] = [];
	private scopes: { clauseCount: number }[] = [];

	addConstraint(constraint: E) {
		for (let clause of this.clausify(constraint)) {
			this.addClausified(clause, this.clauses);
		}
	}

	addUnscopedConstraint(constraint: E) {
		for (const clause of this.clausify(constraint)) {
			this.addClausified(clause, this.unscopedClauses);
		}
	}

	protected addClausified(clause: sat.Literal[], target: sat.Literal[][]) {
		let maxTerm = 0;
		for (let literal of clause) {
			const term = literal > 0 ? literal : -literal;
			maxTerm = Math.max(maxTerm, term);
		}
		target.push(clause);
	}

	pushScope() {
		this.scopes.push({
			clauseCount: this.clauses.length,
		});
	}

	popScope() {
		const scope = this.scopes.pop();
		if (scope === undefined) {
			throw new Error("SMTSolver.popScope");
		}

		this.clauses.splice(scope.clauseCount);
	}

	/// RETURNS "refuted" when the given constraints can provably not be
	/// satisfied.
	/// RETURNS a counter example (satisfaction) when refutation fails; this may
	/// not be a truly realizable counter-examples, as instantiation and the
	/// theory solver may be incomplete.
	attemptRefutation(): "refuted" | Counterexample {
		const solver = new sat.SATSolver();

		for (const clause of this.unscopedClauses) {
			if (clause.length === 0) {
				return "refuted";
			}
			const maxTerm = Math.max(...clause.map(x => x > 0 ? x : -x));
			solver.initTerms(maxTerm);
			solver.addClause(clause);
		}

		let progress = 0;

		while (true) {
			while (progress < this.clauses.length) {
				const clause = this.clauses[progress];
				if (clause.length === 0) {
					return "refuted";
				}
				const maxTerm = Math.max(...clause.map(x => x > 0 ? x : -x));
				solver.initTerms(maxTerm);
				solver.addClause(clause);
				progress += 1;
			}

			const booleanModel = solver.solve();
			if (booleanModel === "unsatisfiable") {
				return "refuted";
			} else {
				// Clausal proof adds additional constraints to the formula, which
				// preserve satisfiablity (but not necessarily logical equivalence).
				// These are useful in subsequent runs of the solver; HOWEVER,
				// clauses which merely preserve satisfiability and not logical
				// equivalence must be pruned.
				// TODO: Remove (and attempt to re-add) any non-implied clauses.
				const theoryClauses = this.rejectModel(booleanModel);
				if (Array.isArray(theoryClauses)) {
					// Completely undo the assignment.
					// TODO: theoryClauses should contain an asserting clause,
					// so the logic in backtracking should be able to replace
					// this.
					solver.rollbackToDecisionLevel(-1);
					if (theoryClauses.length === 0) {
						throw new Error("SMTSolver.attemptRefutation: expected at least one clause from theory refutation");
					}
					for (const theoryClause of theoryClauses) {
						if (theoryClause.length === 0) {
							throw new Error("SMTSolver.attemptRefutation: expected theoryClause to not be empty");
						}

						solver.addClause(theoryClause);
					}
				} else {
					// TODO: Instantiation may need to take place here.
					// The SAT+SMT solver has failed to refute the formula.
					solver.rollbackToDecisionLevel(-1);
					return theoryClauses;
				}
			}
		}
	}

	/// rejectModel returns new clause(s) to add to the SAT solver which
	/// rejects this concrete assignment.
	/// The returned clause(s) should be an asserting clause in reference to the
	/// concrete assignment.
	protected abstract rejectModel(concrete: sat.Literal[]): Counterexample | sat.Literal[][];

	/// clausify returns a set of clauses to add to the underlying SAT solver.
	/// This modifies state, associating literals (and other internal variables)
	/// with the pieces of this constraint, possibly for instantiation.
	protected abstract clausify(constraint: E): sat.Literal[][];

	/// TODO: Instantiation of quantifiers, which is sometimes done in the place
	/// of making decisions in the SATSolver.
}
