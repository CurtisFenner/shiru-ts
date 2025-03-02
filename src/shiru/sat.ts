/**
 * `Literal` represents a Boolean literal. A `Literal` is a non-zero integer.
 *
 * The positive integer `a` is satisfied by an assignment of `true` to variable
 * `a`; a negative integer `-b` is satisfied by an assignment of `false` to
 * variable `b`.
 */
export type Literal = number;

/** `ClauseID` represents an index into the `clauses` field of a `SATSolver`. */
type ClauseID = number;

function swap<T>(array: T[], a: number, b: number) {
	const t = array[a];
	array[a] = array[b];
	array[b] = t;
}

/// `SATResult` represents the result of sat-solving.
/// `"unsatisfiable"`: This instance has no satisfying assignment.
/// `Literal[]`: A partial assignment that satisfies this instance.
export type SATResult = "unsatisfiable" | Literal[];

/// `UnitLiteralQueue` is a helper data structure to maintain a queue of unit
/// literals.
class UnitLiteralQueue {
	private unitLiterals: Map<number, [Literal, ClauseID]> = new Map();

	/// Adds a literal, with a given antecedent, to this queue.
	/// RETURNS a `ClauseID` when this proposed unit literal is in conflict with
	/// another unit literal in this mapping.
	pushOrFindConflict(literal: Literal, antecedent: ClauseID): ClauseID | null {
		const term = literal > 0 ? literal : -literal;
		const existing = this.unitLiterals.get(term);
		if (existing !== undefined && existing[0] !== literal) {
			// This contradicts a unit-literal.
			return existing[1];
		} else if (!existing) {
			this.unitLiterals.set(term, [literal, antecedent]);
		}
		return null;
	}

	/// N.B.: Iterating over this map clears entries from it!
	*[Symbol.iterator]() {
		for (let key of this.unitLiterals.keys()) {
			const value = this.unitLiterals.get(key) as [Literal, ClauseID];
			this.unitLiterals.delete(key);
			yield value;
		}
	}

	clear(): void {
		this.unitLiterals.clear();
	}

	size(): number {
		return this.unitLiterals.size;
	}
}

type PropagationConflict = {
	literal: Literal,
	literalAntecedent: ClauseID,
	negativeLiteralAntecedent: ClauseID,
};

/// `SATSolver` solves the satisfiability problem on Boolean formulas in
/// conjunctive-normal-form (an "and of ors").
export class SATSolver {
	private clauses: number[][] = [];

	/// `watchedPositive[n]` is the `ClauseID`s that are "watching" the literal
	/// `+n`.
	/// A satisfied clauses watches two arbitrary literals within the clause.
	/// An unsatisfied clauses watches two unfalsified literals within the
	/// clause.
	/// Each clause array is continually re-ordered so that a watched literal is
	/// always one of the first two literals in the clause.
	private watchedPositive: ClauseID[][] = [];

	/// `watchedNegative[n]`: see `watchedPositive`.
	private watchedNegative: ClauseID[][] = [];

	/**
	 * `positiveLiteralCount[n]` is the number of times term `n` appears
	 * positively in a clause.
	 */
	private positiveLiteralCount: number[] = [];

	/**
	 * `negativeLiteralCount[n]` is the number of times term `n` appears
	 * negatively in a clause.
	 */
	private negativeLiteralCount: number[] = [];

	/**
	 * `assignments[n]` is the assignment of term `n`.
	 *
	 * * `0`: the term is unassigned.
	 * * `1`: the term is assigned "true".
	 * * `-1`: the term is assigned "false".
	 */
	private assignments: (-1 | 0 | 1)[] = [];

	/// `assignmentStack` is a stack of literals that have been assigned.
	private assignmentStack: Literal[] = [];

	/// `assignmentStackPosition[t]` is the index of where to find an assignment
	/// to term `t` in `assignmentStack`, or `-1` for unassigned variables.
	private assignmentStackPosition: number[] = [];

	/// `decisionLevel` is one more than the number of "free" assignments that
	/// have been made.
	private decisionLevel: number = 0;

	/// `termDecisionLevel[t]` is the decision level at the time term `t` was
	/// given an assignment.
	/// (It is not-defined for unassigned terms)
	private termDecisionLevel: number[] = [];

	/// `antecedentClause[n]` is a `ClauseID` which became a unit-clause
	/// "forcing" the assignment of this term (the "antecedent" clause).
	/// For an unassigned term `n`, `antecedentClause[n]` is not-defined.
	/// For a term assigned "freely" (rather than as a result of BCP), the value
	/// is `-1`.
	private antecedentClause: (ClauseID | -1)[] = [];

	/// Initializes the internal data-structures for terms 1, 2, ..., `term`
	/// (if not already initialized).
	/// Terms must be initialized before being used in clauses passed to
	/// `addClause`.
	initTerms(term: number) {
		for (let i = this.assignments.length; i <= term; i++) {
			this.assignments[i] = 0;
			this.assignmentStackPosition[i] = -1;
			this.antecedentClause[i] = 0;
			this.watchedPositive[i] = [];
			this.watchedNegative[i] = [];
			this.positiveLiteralCount[i] = 0;
			this.negativeLiteralCount[i] = 0;
		}
	}

	/// RETURNS the current assignment stack.
	getAssignment() {
		return this.assignmentStack.slice(0);
	}

	/**
	 * `getAssignmentMap()` returns a mapping from terms to their assignments
	 * (`-1` is negative, `0` is unassigned, and `1` is positive).
	 *
	 * Note that because there is no term `0`, entry `[0]` is not-defined (and
	 * may not be a number).
	 */
	getAssignmentMap(): (-1 | 0 | 1)[] {
		return this.assignments.slice(0);
	}

	/**
	 * `simplifyClauses(clauses)` returns the given set of clauses "simplified"
	 * by the current assignment.
	 *
	 * Only unsatisfied clauses are returned, and only unrefuted literals in
	 * those clauses are included.
	 */
	simplifyClauses(clauses: Literal[][]): Literal[][] {
		const simplifiedClauses = [];
		for (const clause of clauses) {
			const simplifiedClause: Literal[] = [];
			let hasSatisfied = false;
			for (const literal of clause) {
				const term = literal > 0 ? +literal : -literal;
				const assignment = this.assignments[term];
				if (assignment === 0) {
					simplifiedClause.push(literal);
				} else if (assignment * literal > 0) {
					hasSatisfied = true;
					break;
				}
			}
			if (!hasSatisfied) {
				simplifiedClauses.push(simplifiedClause);
			}
		}
		return simplifiedClauses;
	}

	/**
	 * `fastPartialSolve()` partially solves this instance.
	 *
	 * `fastPartialSolve()` returns `"unsatisfiable"` if this instance has been
	 * refuted.
	 *
	 * Otherwise, it returns a partial assignment. If this instance is
	 * satisfiable, this partial assignment is necessarily a subset of any
	 * satisfying assignment.
	 *
	 * This method mutates this SATSolver instance to include new assignments,
	 * but does not increase the decision level.
	 *
	 * **Requires** that the current decision level is zero.
	 */
	fastPartialSolve(): SATResult {
		if (this.decisionLevel !== 0) {
			throw new Error("SATSolver.fastPartialSolve: requires that the current decision level is 0");
		}

		const unitLiterals = this.extractUnitClauses();
		if (unitLiterals === "unsatisfiable") {
			return "unsatisfiable";
		}

		const initialConflict = this.propagate(unitLiterals);
		if (initialConflict !== null) {
			return "unsatisfiable";
		}

		return this.getAssignment();
	}

	/**
	 * `solve()` searches for a satisfying assignment (given the current
	 * partial assignment).
	 *
	 * `solve()` returns `"unsatisfiable"` when the solver has proven that this
	 * instance has no satisfying assignment which contains the partial
	 * assignment the solver had at the time `solve()` was invoked.
	 *
	 * **Requires** that the current decision level is 0.
	 */
	solve(): SATResult {
		if (this.decisionLevel > 0) {
			throw new Error("SATSolver.solve() requires decision level must be at 0");
		} else if (this.assignments.length === 0) {
			throw new Error("SATSolver.solve() requires at least one term");
		}

		// Find initial unit clauses (and later, pure literals).
		this.decisionLevel = 0;
		const unitLiterals = this.extractUnitClauses();
		if (unitLiterals === "unsatisfiable") {
			return "unsatisfiable";
		}

		const initialConflict = this.propagate(unitLiterals);
		if (initialConflict !== null) {
			return "unsatisfiable";
		}

		// Define an initial ordering for the terms. A consistent ordering of
		// terms means larger benefits from learned clauses.
		let ordering = [];
		for (let i = 1; i < this.assignments.length; i++) {
			ordering[i - 1] = i;
		}

		// Set up state for cVSIDS variable ordering heuristic.
		// (See "Understanding VSIDS Branching Heuristics in Conﬂict-Driven
		// Clause-Learning SAT Solvers")
		let termWeights: number[] = [];
		for (let i = 0; i < this.assignmentStackPosition.length; i++) {
			termWeights.push(0);
		}
		for (let clause of this.clauses) {
			if (clause.length < 2) {
				continue;
			}

			// The initial number of occurrences of a variable is a very rough
			// indication of the "centrality" of the variable.
			for (let literal of clause) {
				let term = literal > 0 ? literal : -literal;
				termWeights[term] += 1;
			}
		}

		const termWeightComparator = (termA: number, termB: number) => {
			return termWeights[termB] - termWeights[termA];
		};
		ordering.sort(termWeightComparator);

		// Start the main CDCL loop.
		// Repeat assignments until an assigment has been made to every term.
		let cursor = 0;
		const termCount = this.assignments.length - 1;
		while (this.assignmentStack.length < termCount) {
			const decisionTerm = ordering[cursor];
			cursor += 1;
			cursor %= ordering.length;

			if (this.assignments[decisionTerm] !== 0) {
				// This variable has already been assigned.
				continue;
			}

			if (unitLiterals.size() !== 0) {
				throw new Error("invariant violation");
			}


			// Use a heuristic to determine which assignment to use.
			const decisionLiteral = this.positiveLiteralCount[decisionTerm] < this.negativeLiteralCount[decisionTerm]
				? +decisionTerm
				: -decisionTerm;

			// Enqueue a free decision.
			this.decisionLevel += 1;
			const expectNull = unitLiterals.pushOrFindConflict(decisionLiteral, -1);
			if (expectNull !== null) {
				throw new Error("invariant violation: expected no conflict when no unit literals were found");
			}

			// Propagate unit consequences of that free decision.
			while (true) {
				const conflict = this.propagate(unitLiterals);
				if (conflict === null) {
					break;
				}
				const conflictClause = this.diagnoseConflict(conflict);

				// Rewind at least one decision in the conflict clause.
				const assertingLiteral = this.rollbackForConflictClause(conflictClause);
				if (assertingLiteral === "unsatisfiable") {
					return "unsatisfiable";
				}

				// Then, add the clause, bearing in mind it SHOULD be a unit
				// clause (asserting clause), which should expand
				// propagation within a PREVIOUS decision level.
				const conflictClauseID = this.addClause(conflictClause);

				unitLiterals.clear();
				unitLiterals.pushOrFindConflict(assertingLiteral, conflictClauseID);

				// Use "cVSIDS" strategy for clause ordering.
				for (const literal of conflictClause) {
					const term = literal > 0 ? +literal : -literal;
					termWeights[term] += 1;
				}
				for (let i = 0; i < termWeights.length; i++) {
					termWeights[i] *= 0.99;
				}
				ordering.sort(termWeightComparator);

				// Ensure that variables are assigned in the same order.
				// This means that subsequent conflicts are in the same
				// "area" of the search space, and compound on each other.
				cursor = 0;

				// Continue in the unit-propagation loop.
			}
		}

		return this.getAssignment();
	}

	/**
	 * `rollbackForConflictClause(conflictClause)` examines the given conflict
	 * clause and rolls back to a point at which the clause is not falsified by
	 * the current assignment.
	 *
	 * `findRollbackLevel(conflictClause)` returns `"unsatisfiable"` when even
	 * assignments made before the first decision must be rolled back for this
	 * clause to be satisfiable.
	 *
	 * **Requires** that
	 *   + every literal in conflictClause must be falsified by the
	 *     current assignment.
	 *   + only a single variable may have the latest decision level, unless the
	 *     latest decision level is 0.
	 *   + the literal with the latest decision level must be a decision
	 *     variable, unless the latest decision level is 0.
	 */
	rollbackForConflictClause(
		conflictClause: Literal[],
	): Literal | "unsatisfiable" {
		let maxDecisionLevel = 0;
		let assertingLiteral = -1;

		// Find the term set after the most recent decision.
		let multiple = false;
		for (let i = 0; i < conflictClause.length; i++) {
			const conflictLiteral = conflictClause[i];
			const conflictTerm = conflictLiteral > 0 ? conflictLiteral : -conflictLiteral;

			const termDecisionLevel = this.termDecisionLevel[conflictTerm];
			if (termDecisionLevel > maxDecisionLevel) {
				// Identify any term that will be unassigned if this latest
				// decision is undone.
				maxDecisionLevel = termDecisionLevel;
				multiple = false;
				assertingLiteral = conflictLiteral;
			} else if (termDecisionLevel === maxDecisionLevel) {
				// Used to verify the precondition that there is only a single
				// literal at the latest (non-zero) decision level.
				multiple = true;
			}
		}

		// Find the second highest decision level; after that decision, this
		// clause is a unit clause.
		let secondHighestDecisionLevel = 0;
		for (let i = 0; i < conflictClause.length; i++) {
			const conflictLiteral = conflictClause[i];
			const conflictTerm = conflictLiteral > 0 ? conflictLiteral : -conflictLiteral;

			const termDecisionLevel = this.termDecisionLevel[conflictTerm];
			if (termDecisionLevel < maxDecisionLevel && termDecisionLevel > secondHighestDecisionLevel) {
				secondHighestDecisionLevel = termDecisionLevel;
			}
		}

		if (maxDecisionLevel == 0) {
			// If the conflict-clause is all of terms prior to the
			// first decision (including an empty conflict clause),
			// this instance has been refuted.
			return "unsatisfiable";
		} else if (multiple) {
			throw new Error("SATSolver.rollbackForConflictClause: Expected exactly 1 literal in the latest decision level.");
		} else {
			this.rollbackToDecisionLevel(secondHighestDecisionLevel);
			return assertingLiteral;
		}
	}

	/**
	 * `extractUnitClauses()` finds all clauses that are unit clauses given the
	 * current partial assignment.
	 *
	 * `extractUnitClauses()` returns `"unsatisfiable"` when two conflicting
	 * unit clauses were found.
	 */
	extractUnitClauses(): UnitLiteralQueue | "unsatisfiable" {
		let unitLiterals = new UnitLiteralQueue();
		for (let i = 0; i < this.clauses.length; i++) {
			const clause = this.clauses[i];

			let satisfied = false;
			let lastUnfalsifiedLiteral = 0;
			let unfalsifiedCount = 0;
			for (let k = 0; k < clause.length; k++) {
				const literal = clause[k];
				const term = literal > 0 ? +literal : -literal;
				const assignment = this.assignments[term];
				if (assignment === 0) {
					lastUnfalsifiedLiteral = literal;
					unfalsifiedCount += 1;
				} else if (literal * assignment > 0) {
					satisfied = true;
					break;
				}
			}

			if (!satisfied && unfalsifiedCount === 1) {
				const literal = lastUnfalsifiedLiteral;
				const conflict = unitLiterals.pushOrFindConflict(literal, i);
				if (conflict !== null) {
					// There are two contradicting unit-clauses.
					return "unsatisfiable";
				}
			}
		}
		return unitLiterals;
	}

	/// Adds a clause to this CNF-SAT instance.
	/// The array `clause` is interpreted as a disjunction ("or") of its
	/// contained literals.
	/// A clause is satisfied when at least one of its literals is satisfied.
	addClause(unprocessedClause: Literal[]): ClauseID {
		// Check for tautological clauses and for redundant literals.
		let hasUnassigned = false;
		const clause: Literal[] = [];
		let termFirstLiteral: Record<number, number> = {};
		for (let i = 0; i < unprocessedClause.length; i++) {
			const literal = unprocessedClause[i];
			const term = literal > 0 ? +literal : -literal;
			if (this.assignments[term] === 0) {
				hasUnassigned = true;
			}

			if (term in termFirstLiteral) {
				if (termFirstLiteral[term] !== literal) {
					// This clause is a tautology.
					return -1;
				}
			} else {
				termFirstLiteral[term] = literal;
				clause.push(literal);
			}
		}

		for (let i = 0; i < clause.length; i++) {
			const literal = clause[i];
			if (literal > 0) {
				this.positiveLiteralCount[+literal] += 1;
			} else {
				this.negativeLiteralCount[-literal] += 1;
			}
		}

		if (!hasUnassigned) {
			throw new Error("SATSolver.addClause() requires at least one unassigned literal");
		}

		const clauseID = this.clauses.length;
		this.clauses.push(clause);

		// Push unassigned literals to the front of the clause, with more
		// recently assigned literals after that, to reduce unnecessary watches.
		clause.sort((literalA: Literal, literalB: Literal) => {
			const termA = literalA > 0 ? literalA : -literalA;
			const termB = literalB > 0 ? literalB : -literalB;

			let rankA = this.assignmentStackPosition[termA];
			let rankB = this.assignmentStackPosition[termB];

			if (rankA < 0) {
				rankA = this.assignmentStackPosition.length + 1;
			}
			if (rankB < 0) {
				rankB = this.assignmentStackPosition.length + 1;
			}
			return rankB - rankA;
		});

		// Watch (up to) the first two literals.
		for (let i = 0; i < 2 && i < clause.length; i++) {
			const literal = clause[i];
			if (literal > 0) {
				this.watchedPositive[literal].push(clauseID);
			} else {
				this.watchedNegative[-literal].push(clauseID);
			}
		}

		return clauseID;
	}

	/// Validates that certain internal invariants hold. Useful for debugging.
	_validateWatches() {
		const happyLiterals = this.assignments.map((v, i) => v * i);
		const watches: number[][] = this.clauses.map(x => []);
		for (let i = 1; i < this.watchedNegative.length; i++) {
			for (let clauseID of this.watchedNegative[i]) {
				watches[clauseID].push(-i);
			}
			for (let clauseID of this.watchedPositive[i]) {
				watches[clauseID].push(+i);
			}
		}

		for (let i = 0; i < this.clauses.length; i++) {
			const clause = this.clauses[i];

			let satisfied = false;
			const unfalsifiedLiterals = [];
			for (let literal of clause) {
				if (happyLiterals.includes(literal)) {
					satisfied = true;
				} else if (this.assignments[Math.abs(literal)] === 0) {
					unfalsifiedLiterals.push(literal);
				}
			}

			const w = watches[i];
			if (!satisfied) {
				const unwatchedUnfalsified = unfalsifiedLiterals.filter(x => w.indexOf(x) < 0);
				for (let watcher of w) {
					const term = Math.abs(watcher);
					if (this.assignments[term] * watcher < 0 && unwatchedUnfalsified.length >= 1) {
						throw new Error(`Watched term ${term} in unsatisfied clause #${i} [${clause}] has been assigned ${this.assignments[term]}, and ${unwatchedUnfalsified} are available.`);
					}
				}
			}
			if (w.length > 2) {
				throw new Error("Too many watched literals in this clause!");
			} else if (w.length < 2 && w.length < clause.length) {
				throw new Error(`Too few watched literals in clause #${i} ${clause} watched only by ${w}`);
			} else if (w[0] !== clause[0] && w[0] !== clause[1]) {
				throw new Error("First watched literal " + w[0] + " is not one of first two literals!");
			} else if (w[1] !== clause[0] && w[1] !== clause[1]) {
				throw new Error("Second watched literal " + w[1] + " is not one of first two literals!");
			}

			if (!satisfied) {
				if (unfalsifiedLiterals.length >= 2) {
					for (let k of w) {
						if (!unfalsifiedLiterals.includes(k)) {
							throw new Error("Watched literal `" + k + "` has been falsified!");
						}
					}
				}
				if (w.length === 0) {
					throw new Error("Clause " + clause + " is not being watched by any literals, but isn't satisfied!");
				}
			}
		}
	}

	/**
	 * `propagate(unitLiterals)` assigns the literals in the `unitLiterals`
	 * queue, and then performs boolean-constraint-propagation, resulting in
	 * additional assignments to newly created unit clauses.
	 *
	 * `propgate` returns a conflict when boolean-constraint-propagation results
	 * in a conflict: see `UnitLiteralQueue.pushOrFindConflict`.
	 *
	 * `propagate` returns `null` when the queue was completely drained without
	 * encountering a conflict.
	 */
	propagate(
		unitLiterals: UnitLiteralQueue,
	): PropagationConflict | null {
		for (let [unitLiteral, antecedent] of unitLiterals) {
			// Invariant: the literal "not unitLiteral" is not in
			// `unitLiterals`.
			const [newUnitLiterals, newAntecedents] = this.assign(unitLiteral, antecedent);
			for (let i = 0; i < newUnitLiterals.length; i++) {
				const conflict = unitLiterals.pushOrFindConflict(newUnitLiterals[i], newAntecedents[i]);
				if (conflict !== null) {
					// There are two contradicting unit-clauses; we are still
					// prior to any decisions, so the formula overall must be
					// unsatisfiable.
					return {
						literal: newUnitLiterals[i],
						literalAntecedent: newAntecedents[i],
						negativeLiteralAntecedent: conflict,
					};
				}
			}
		}
		return null;
	}

	/// REQUIRES the given term is currently unassigned.
	/// REQUIRES that this assignment doesn't result in any falsified clauses.
	/// MODIFIES the data for this term to reflect the new assignment.
	/// RETURNS newly created unit-clauses following this assignment.
	private assign(assignedLiteral: Literal, causingClause: ClauseID | -1): [Literal[], ClauseID[]] {
		const discoveredUnitLiterals: Literal[] = [];
		const discoveredAntecedents: ClauseID[] = [];

		const assignedTerm = assignedLiteral > 0 ? assignedLiteral : -assignedLiteral;
		if (this.assignments[assignedTerm] !== 0) {
			throw new Error("SATSolver.assign() requires literal is not already assigned");
		}

		const watchers = assignedLiteral > 0 ? this.watchedNegative[assignedTerm] : this.watchedPositive[assignedTerm];
		let watchersKeepIndex = 0;
		for (let wi = 0; wi < watchers.length; wi++) {
			const watchingClauseID = watchers[wi];
			const watchingClause = this.clauses[watchingClauseID];

			let satisfiedIndex = -1;
			let unfalsfiedCount = 0;
			let latestUnfalsfiedLiteralIndex = -1;
			for (let i = 0; i < watchingClause.length; i++) {
				const l = watchingClause[i];
				const t = l > 0 ? l : -l;
				const a = this.assignments[t];
				const satisfyiedBy = l > 0 ? +1 : -1;
				if (a === satisfyiedBy) {
					satisfiedIndex = i;
					break;
				} else if (a === 0) {
					unfalsfiedCount += 1;
					// N.B.: since watched literals are pushed to the front of
					// the watchingClause array, if there are any unwatched
					// unfalsified literals, they will be the result of this
					// loop.
					latestUnfalsfiedLiteralIndex = i;
				}
			}

			// Either find a new literal to watch,
			// or recognize that this `watchingClause` is now a unit clause.
			const destination = watchingClause[0] === -assignedLiteral ? 0 : 1;

			// As an optimization, try to prevent more useless wake-ups by
			// swapping this watch with an earlier assigned that satisfied the
			// clause.
			if (satisfiedIndex >= 0) {
				if (satisfiedIndex <= 1) {
					// There are no unwatched satisfied literals in this clause,
					// so this literal will remain the watcher.
					// N.B.: without this, this watcher would be cleared at the
					// end of this loop.
					watchers[watchersKeepIndex] = watchingClauseID;
					watchersKeepIndex += 1;
				} else {
					// This clause is already satisfied, and does not require
					// any further updates or inspection.
					const satisfiedLiteral = watchingClause[satisfiedIndex];
					swap(watchingClause, destination, satisfiedIndex);
					if (satisfiedLiteral > 0) {
						// Positive
						this.watchedPositive[satisfiedLiteral].push(watchingClauseID);
					} else {
						// Negative
						this.watchedNegative[-satisfiedLiteral].push(watchingClauseID);
					}
				}

				continue;
			}

			if (unfalsfiedCount == 1) {
				// `this.assignments` is not yet updated; thus the only
				// falsified literal is the one being deleted; so this is a
				// conflicting unit-clause.
				throw new Error(`SATSolver.assign: This assignment falsifies the clause #${watchingClauseID}.`
					+ `\n(adding assignment ${assignedLiteral} to stack [${this.assignmentStack}];`
					+ `\nwatchingClause =#${watchingClauseID} ${watchingClause})`);
			} else if (unfalsfiedCount == 2) {
				// `watchingClause` is not yet satisfied, and has no unfalsified
				// literals other than its two watched literals.
				// Thus, this is becoming a unit clause of only the other
				// watched literal.
				discoveredUnitLiterals.push(watchingClause[1 - destination]);
				discoveredAntecedents.push(watchingClauseID);

				// Keep the literal watched, since there isn't another literal
				// to watch it.
				watchers[watchersKeepIndex] = watchingClauseID;
				watchersKeepIndex += 1;
			} else {
				// There remains an unfalsified literal, other than the two
				// watched literals, in this unsatisfied watchingClause.
				const newWatchedLiteral = watchingClause[latestUnfalsfiedLiteralIndex];
				if (newWatchedLiteral > 0) {
					this.watchedPositive[newWatchedLiteral].push(watchingClauseID);
				} else {
					this.watchedNegative[-newWatchedLiteral].push(watchingClauseID);
				}

				swap(watchingClause, destination, latestUnfalsfiedLiteralIndex);
			}
		}
		watchers.length = watchersKeepIndex;

		this.assignments[assignedTerm] = assignedLiteral > 0 ? +1 : -1;
		this.assignmentStackPosition[assignedTerm] = this.assignmentStack.length;
		this.assignmentStack.push(assignedLiteral);
		this.antecedentClause[assignedTerm] = causingClause;
		this.termDecisionLevel[assignedTerm] = this.decisionLevel;

		return [
			discoveredUnitLiterals,
			discoveredAntecedents,
		];
	}

	private diagnoseConflict(conflict: PropagationConflict): Literal[] {
		// This method is called when a "conflict" is detected:
		// boolean-constraint-propagation results in a unit clause "literal"
		// and "not literal".
		// `literalAntecedent` indicates the clause within which "literal" is a
		// unit clause; `negativeLiteralAntecedent` indicates the same for
		// "not literal".

		// This method must "diagnose" the conflict, producing a new clause
		// which rejects previous "decisions".

		// The simplest diagnosis is to reject the entire set of decision
		// currently in the assignment stack. However, some of those decisions
		// may not be relevant to this particular conflict; generating a more
		// general conflict clause will prune more of the remaining search
		// space.

		// The `antecedentClause` mapping can be used to generate an
		// "implication graph". The vertices of the graph are literals.
		// For non-decision variables, an edge exists for the negation of each
		// other literal in the vertex's selected antecedent clause.

		// This implication graph structure indicates that a vertex is _implied_
		// by the conjunction of all predecessor vertices. A vertex with no
		// precedessors is a "decision variable", and had a truth value selected
		// arbitrarily.

		// The problem of "diagnosing" a conflict is determing a set of vertices
		// which transitively imply the conflicting the two conflicting
		// literals.

		// To drive backtracking solely by conflict clauses, the conflict clause
		// should be an "asserting clause" -- one which will be a unit clause
		// after unassigning all decisions mentioned in the conflict. This means
		// it must have only one literal from the latest decision level.

		// The simplest method is "rel_sat": resolve all literals in the current
		// decision level except the decision variable:
		let conflictClause = [];
		let seen = new Set();

		let q = [conflict.literal, -conflict.literal];
		for (let i = 0; i < q.length; i++) {
			const literal = q[i];
			const term = literal > 0 ? literal : -literal;

			let antecedent: ClauseID;
			if (literal == conflict.literal) {
				antecedent = conflict.literalAntecedent;
			} else if (literal == -conflict.literal) {
				antecedent = conflict.negativeLiteralAntecedent;
			} else {
				antecedent = this.antecedentClause[term];
			}

			if (antecedent < 0 || (this.termDecisionLevel[term] < this.decisionLevel && literal !== conflict.literal && literal !== -conflict.literal)) {
				conflictClause.push(literal);
			} else {
				const clause = this.clauses[antecedent];
				for (let other of clause) {
					if (other !== literal && !seen.has(other)) {
						seen.add(other);
						q.push(other);
					}
				}
			}
		}

		return conflictClause;
	}

	rollbackToDecisionLevel(level: number) {
		while (this.decisionLevel > level && this.assignmentStack.length > 0) {
			this.popAssignment();
		}
		if (this.assignmentStack.length === 0) {
			if (level > 0) {
				throw new Error(`bad level argument ${level}`);
			}
		}
	}

	popAssignment() {
		// N.B.: The two-watched-literal scheme requires no bookkeeping updates
		// upon unassignment.
		const literal = this.assignmentStack.pop();
		if (!literal) throw new Error("cannot pop when empty");
		const term = literal > 0 ? literal : -literal;
		this.assignments[term] = 0;
		this.assignmentStackPosition[term] = -1;
		if (this.antecedentClause[term] < 0) {
			this.decisionLevel -= 1;
		}
	}
};
