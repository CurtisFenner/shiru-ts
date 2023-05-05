import * as data from "./data.js";
import * as sat from "./sat.js";
import * as trace from "./trace.js";

/**
 * `SMTSolver` represents a "satisfiability modulo theories" instance.
 * With respect to refutation, SMTSolver is sound, but not complete: some
 * "models" are not actually feasible in the represented theory. However, all
 * refutations definitely refute the instance in the given theory.
 */
export abstract class SMTSolver<E, Model> {
	protected clauses: sat.Literal[][] = [];
	protected unscopedClauses: sat.Literal[][] = [];
	private scopes: { clauseCount: number }[] = [];

	/**
	 * Update this SMT instance so that all subsequent solves within the
	 * containing scope must also ensure that `constraint` is satisfied by a
	 * model.
	 * 
	 * @see pushScope
	 * @see popScope
	 */
	addConstraint(constraint: E) {
		for (let clause of this.clausify(constraint)) {
			this.addClausified(clause, this.clauses);
		}
	}

	/**
	 * Update this SMT instance so that all subsequent solves must also
	 * ensure that `constraint` is satisfied by a model.
	 */
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

	abstract showLiteral(literal: number): string;

	showClause(
		clause: number[],
		assignment: Set<number>,
		lines: string[],
	): boolean {
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

	showFormula(
		clauses: number[][],
		partialAssignment: number[] = [],
		indent = "",
	): string[] {
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

	/**
	 * @returns `"refuted"` when th given constraints can provably not be
	 * satisfied in the theory.
	 * @returns a `Model` that may satisfy the constraints when refutation
	 * fails. this model may not actually be feasible in the theory: solving is
	 * sound but not complete with respect to refutation.
	 */
	attemptRefutation(): "refuted" | Model {
		trace.start("attemptRefutation");
		const out = this._attemptRefutation();
		trace.stop("attemptRefutation");
		return out;
	}

	_attemptRefutation(): "refuted" | Model {
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
			const additionalClauses = this.learnTheoryClauses(partialAssignment, unassigned);
			if (additionalClauses.tag === "unsatisfiable") {
				trace.stop("partial-theory-simplification");
				return "refuted";
			} else if (additionalClauses.impliedClauses.length === 0) {
				// No clauses were learned.
				break;
			}
			for (const clause of additionalClauses.impliedClauses) {
				// Add additional clauses that are implied by the theory.
				solver.addClause(clause);
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
			trace.start([
				"booleanModel (not passed to theory) size:",
				booleanModel.length,
				"=",
				instantiationBooleanModel.length,
				"instantiation",
				"+",
				undeterminedBooleanModel.length,
				"undetermined",
			]);
			trace.mark("full booleanModel", () => {
				return booleanModel.map(x => this.showLiteral(x)).join("\n");
			});

			const commonWithLast = data.measureCommonPrefix(
				lastUndeterminedBooleanModel,
				undeterminedBooleanModel,
			);
			lastUndeterminedBooleanModel = undeterminedBooleanModel.slice(0);
			const notCommon = lastUndeterminedBooleanModel.length - commonWithLast;
			const partialModelSize = commonWithLast + notCommon / 1.5;

			// Attempt to reject using a smaller boolean model
			const partialModel = undeterminedBooleanModel.slice(0, partialModelSize);
			const smallerTheoryClauses = this.learnTheoryClauses(partialModel, []);

			const theoryClauses = smallerTheoryClauses.tag === "unsatisfiable"
				? smallerTheoryClauses
				: this.learnTheoryClauses(
					instantiationBooleanModel.concat(undeterminedBooleanModel),
					[],
				);

			if (theoryClauses.tag === "unsatisfiable") {
				// Completely undo the assignment.
				// TODO: theoryClauses should contain an asserting clause,
				// so the logic in backtracking should be able to replace
				// this.
				solver.rollbackToDecisionLevel(-1);
				if (theoryClauses.conflictClauses.length === 0) {
					throw new Error(
						"SMTSolver.attemptRefutation: " +
						"expected at least one clause from theory refutation",
					);
				}

				trace.start(["learned ", theoryClauses.conflictClauses.length, " theory clauses"]);
				for (const theoryClause of theoryClauses.conflictClauses) {
					if (theoryClause.length === 0) {
						throw new Error(
							"SMTSolver.attemptRefutation: " +
							"expected theoryClause to not be empty",
						);
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
				return theoryClauses.model;
			}

		}
	}

	/**
	 * `learnTheoryClauses(partialAssignment, unassigned)` uses a theory-solver
	 * to produce additional facts about the given `unassigned` terms, and to
	 * reject partial assignments which are not feasible in the theory.
	 */
	protected abstract learnTheoryClauses(
		partialAssignment: sat.Literal[],
		unassigned: sat.Literal[],
	): { tag: "implied", impliedClauses: sat.Literal[][], model: Model }
		| { tag: "unsatisfiable", conflictClauses: sat.Literal[][] };

	/// clausify returns a set of clauses to add to the underlying SAT solver.
	/// This modifies state, associating literals (and other internal variables)
	/// with the pieces of this constraint, possibly for instantiation.
	protected abstract clausify(constraint: E): sat.Literal[][];

	/// TODO: Instantiation of quantifiers, which is sometimes done in the place
	/// of making decisions in the SATSolver.
}
