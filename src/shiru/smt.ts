import * as data from "./data.js";
import * as sat from "./sat.js";
import * as trace from "./trace.js";

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

	attemptRefutation() {
		trace.start("attemptRefutation");
		const out = this._attemptRefutation();
		trace.stop("attemptRefutation");
		return out;
	}

	showLiteral(literal: number): string {
		return literal.toString();
	}

	showClause(clause: number[], assignment: Set<number>, lines: string[] = []) {
		let first = true;
		const satisfiedLiteral = clause.find(x => assignment.has(x));
		if (satisfiedLiteral !== undefined) {
			// This clause is satisfied by the satisfied literal.
			lines.push("// satisfied by " + this.showLiteral(satisfiedLiteral));
			return false;
		}

		let hasUnrefuted = false;
		for (const literal of clause) {
			const literalIsRefuted = assignment.has(-literal);
			if (literalIsRefuted) {
				continue;
			}
			hasUnrefuted = true;

			lines.push((first ? "&&" : "") + "\t||\t" + this.showLiteral(literal));
			first = false;
		}
		if (!hasUnrefuted) {
			lines.push("// contradiction!");
		}
		return true;
	}

	showFormula(clauses: number[][], partialAssignment: number[] = [], indent = ""): string[] {
		const literals = new Set(partialAssignment);

		const lines: string[] = [];
		for (const clause of clauses) {
			this.showClause(clause, literals, lines);
		}
		return [
			indent + "formula - " + "v".repeat(120),
			...lines.map(x => indent + "\t" + x),
			indent + "formula - " + "^".repeat(120),
		];
	}

	/// RETURNS "refuted" when the given constraints can provably not be
	/// satisfied.
	/// RETURNS a counter example (satisfaction) when refutation fails; this may
	/// not be a truly realizable counter-examples, as instantiation and the
	/// theory solver may be incomplete.
	_attemptRefutation(): "refuted" | Counterexample {
		trace.mark("initial SMT instance", () => {
			return this.showFormula(this.clauses).join("\n");
		});
		trace.mark("initial SMT unscoped instance", () => {
			return this.showFormula(this.unscopedClauses).join("\n");
		});
		const solver = new sat.SATSolver();

		for (const clause of this.unscopedClauses) {
			if (clause.length === 0) {
				return "refuted";
			}
			const maxTerm = Math.max(...clause.map(x => x > 0 ? x : -x));
			solver.initTerms(maxTerm);
			solver.addClause(clause);
		}

		// Add all the clauses to the SATSolver.
		for (const clause of this.clauses) {
			if (clause.length === 0) {
				return "refuted";
			}
			const maxTerm = Math.max(...clause.map(x => x > 0 ? x : -x));
			solver.initTerms(maxTerm);
			solver.addClause(clause);
		}

		trace.start("partial-theory-simplification");
		while (true) {
			// Before attempting a full CDCL(T) search loop, perform BCP to get a
			// partial assignment and ask the theory solver if it is satisfiable.
			const initial = solver.fastPartialSolve();
			if (initial === "unsatisfiable") {
				trace.stop("partial-theory-simplification");
				return "refuted";
			}
			const partialAssignment = solver.getAssignment();
			const unassigned = [];
			const partialAssignmentMap = solver.getAssignmentMap();
			for (let term = 1; term < partialAssignmentMap.length; term += 1) {
				if (partialAssignmentMap[term] === 0) {
					unassigned.push(term);
				}
			}
			const additional = this.learnAdditional(partialAssignment, unassigned);
			if (additional === "unsatisfiable") {
				trace.stop("partial-theory-simplification");
				return "refuted";
			} else if (additional.length === 0) {
				// No unit clauses were added.
				break;
			}
			for (const literal of additional) {
				// Add additional unit clauses that are implied by the theory.
				solver.addClause([literal]);
			}
		}
		trace.stop("partial-theory-simplification");

		trace.mark("Partial solving boolean assignment", () => {
			const assignment = solver.getAssignment();
			return assignment.sort((a, b) => Math.abs(a) - Math.abs(b)).join(", ");
		});

		// Use the SMT solver's clauses, rather than the SAT solver's clauses,
		// to exclude any learned CDCL clauses.
		const simplified = solver.simplifyClauses([...this.clauses, ...this.unscopedClauses]);
		const simplifyingAssignment = new Set(solver.getAssignment());

		trace.mark("Result of partial solving", () => {
			const lines = this.showFormula(simplified);
			return lines.join("\n");
		});

		// Find the subset of terms which must be passed to the theory solver
		// to satisfy the boolean formula.
		const termsRequiringAssignment = new Set<number>();

		for (const clause of simplified) {
			for (const literal of clause) {
				termsRequiringAssignment.add(Math.abs(literal));
			}
		}

		trace.mark("termsRequiringAssignment", () => {
			const lines = [...termsRequiringAssignment].map(x => this.showLiteral(x));
			return lines.join("\n");
		});

		// In addition, add all forced unit clauses. These may be useful to the
		// theory solver.
		const instantiationTerms = new Set<number>();
		for (const literal of solver.getAssignment()) {
			instantiationTerms.add(Math.abs(literal));
		}

		trace.mark("instantiationTerms", () => {
			const lines = [...instantiationTerms].map(x => this.showLiteral(x));
			return lines.join("\n");
		});

		trace.start("solving");
		let lastUndeterminedBooleanModel: sat.Literal[] = [];
		while (true) {
			const booleanModel = solver.solve();
			if (booleanModel === "unsatisfiable") {
				trace.stop("solving");
				return "refuted";
			}

			const instantiationBooleanModel = booleanModel.filter(literal => {
				const term = literal > 0 ? +literal : -literal;
				return instantiationTerms.has(term);
			});
			const undeterminedBooleanModel = booleanModel.filter(literal => {
				const term = literal > 0 ? +literal : -literal;
				return termsRequiringAssignment.has(term);
			});
			trace.start("rejectBooleanModel");
			trace.mark([
				"booleanModel (not passed to theory) size:",
				booleanModel.length,
				"=",
				instantiationBooleanModel.length,
				"instantiation",
				"+",
				undeterminedBooleanModel.length,
				"undetermined",
			], () => {
				return booleanModel.map(x => this.showLiteral(x)).join("\n");
			});

			const commonWithLast = data.measureCommonPrefix(lastUndeterminedBooleanModel, undeterminedBooleanModel);
			lastUndeterminedBooleanModel = undeterminedBooleanModel.slice(0);
			const notCommon = lastUndeterminedBooleanModel.length - commonWithLast;
			const partialModel = commonWithLast + notCommon / 1.5;

			// Attempt to reject using a smaller boolean model
			const smallerTheoryClauses = this.rejectBooleanModel((undeterminedBooleanModel.slice(0, partialModel)));

			const theoryClauses = Array.isArray(smallerTheoryClauses)
				? smallerTheoryClauses
				: this.rejectBooleanModel(instantiationBooleanModel.concat(undeterminedBooleanModel));

			if (Array.isArray(theoryClauses)) {
				// Completely undo the assignment.
				// TODO: theoryClauses should contain an asserting clause,
				// so the logic in backtracking should be able to replace
				// this.
				solver.rollbackToDecisionLevel(-1);
				if (theoryClauses.length === 0) {
					throw new Error(
						"SMTSolver.attemptRefutation: expected at least one clause from theory refutation"
					);
				}

				trace.start(["learned ", theoryClauses.length, " theory clauses"]);
				for (const theoryClause of theoryClauses) {
					if (theoryClause.length === 0) {
						throw new Error("SMTSolver.attemptRefutation: expected theoryClause to not be empty");
					}

					trace.mark(["learned clause of", theoryClause.length, "terms"], () => {
						const lines: string[] = [];
						this.showClause(theoryClause, new Set(), lines);
						return lines.join("\n");
					});
					trace.mark("simplified version", () => {
						const lines: string[] = [];
						this.showClause(theoryClause, simplifyingAssignment, lines);
						return lines.join("\n");
					});

					solver.addClause(theoryClause);
				}
				trace.stop();
				trace.stop();
			} else {
				trace.stop();
				// TODO: Instantiation may need to take place here.
				// The SAT+SMT solver has failed to refute the formula.
				solver.rollbackToDecisionLevel(-1);
				trace.stop("solving");
				return theoryClauses;
			}

		}
	}

	/**
	 * `rejectBooleanModel` use a theory-solver to produce new clauses to add
	 * to the SAT solver which reject this concrete assignment.
	 *
	 * The returned clauses should include an asserting clause in reference to
	 * the concrete assignment.
	 */
	protected abstract rejectBooleanModel(
		concrete: sat.Literal[],
	): Counterexample | sat.Literal[][];

	/**
	 * `learnAdditional(partialAssignment, unassigned)` uses a theory-solver to
	 * produce additional facts about the given `unassigned` terms.
	 */
	protected abstract learnAdditional(
		partialAssignment: sat.Literal[],
		unassigned: sat.Literal[],
	): sat.Literal[] | "unsatisfiable";

	/// clausify returns a set of clauses to add to the underlying SAT solver.
	/// This modifies state, associating literals (and other internal variables)
	/// with the pieces of this constraint, possibly for instantiation.
	protected abstract clausify(constraint: E): sat.Literal[][];

	/// TODO: Instantiation of quantifiers, which is sometimes done in the place
	/// of making decisions in the SATSolver.
}
