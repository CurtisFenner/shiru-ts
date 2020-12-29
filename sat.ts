
/// `Literal` represents a Boolean literal. A `Literal` is a non-zero integer.
/// The positive integer `a` is satisfied by an assignment of `true` to variable
/// `a`; a negative integer `-b` is satisfied by an assignment of `false` to
/// variable `b`.
export type Literal = number;

/// `ClauseID` represents an index into the `clauses` field of a `SATSolver`.
type ClauseID = number;

function swap<T>(array: T[], a: number, b: number) {
	const t = array[a];
	array[a] = array[b];
	array[b] = t;
}

/// SATResult represents the result of sat-solving.
/// `null`: An answer has not yet been determined.
/// `"unsatisfiable"`: This instance has no satisfying assignment.
/// `Literal[]`: A partial assignment that satisfies this instance.
export type SATResult = DefiniteSATResult | null;
export type DefiniteSATResult = "unsatisfiable" | Literal[];


/// UnitLiteralQueue is a helper data structure to maintain a queue of unit
/// literals.
class UnitLiteralQueue {
	private unitLiterals: Map<number, [Literal, ClauseID]> = new Map();

	/// RETURNS a ClauseID when this proposed unit literal is in conflict with
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

	pushAllOrFindConflict([newUnitLiterals, newAntecedents]: [Literal[], ClauseID[]]): [Literal, ClauseID, ClauseID] | null {
		if (newUnitLiterals.length !== newAntecedents.length) {
			throw new Error("UnitLiteralQueue.pushAllOrFindConflict requires newUnitLiterals.length == newAntecedents.length");
		}
		for (let i = 0; i < newUnitLiterals.length; i++) {
			const conflict = this.pushOrFindConflict(newUnitLiterals[i], newAntecedents[i]);
			if (conflict !== null) {
				return [newUnitLiterals[i], newAntecedents[i], conflict];
			}
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

/// SATSolver solves the satisfiability problem on Boolean formulas in
/// conjunctive-normal-form (an "and of ors").
export class SATSolver {
	private clauses: number[][] = [];

	/// `watchedPositive[n]` is the `ClauseID`s that are "watching" the literal
	/// `+n`. Satisfied clauses watch two arbitrary literals within them.
	/// Unsatisfied clauses watch two unfalsified literals within them.
	/// A watched literal is always one of the first two literals in the clause
	/// array.
	private watchedPositive: Set<ClauseID>[] = [];

	/// `watchedPositive[n]`: see `watchedPositive`.
	private watchedNegative: Set<ClauseID>[] = [];

	private assignments: (-1 | 0 | 1)[] = [];
	private assignmentStack: number[] = [];

	/// assignmentOrder[t] is the index of `t` or `-t` in `assignmentStack`, or
	/// `-1` for unassigned variables.
	private assignmentStackPosition: number[] = [];

	/// `decisionLevel` is one more than the number of "free" assignments that
	/// have been made.
	private decisionLevel: number = 0;
	private termDecisionLevel: number[] = [];

	/// `antecedentClause[n]` is a `ClauseID` which became a unit-clause
	/// "forcing" the assignment of this term (the "antecedent" clause).
	/// For an unassigned term `n`, `antecedentClause[n]` is undefined.
	/// For a term assigned "freely" (rather than as a result of BCP), the value
	/// is `-1`.
	private antecedentClause: (ClauseID | -1)[] = [];
	initTerms(term: number) {
		for (let i = this.assignments.length; i <= term; i++) {
			this.assignments[i] = 0;
			this.assignmentStackPosition[i] = -1;
			this.antecedentClause[i] = 0;
			this.watchedPositive[i] = new Set();
			this.watchedNegative[i] = new Set();
		}
	}

	getAssignment() {
		return this.assignmentStack.slice(0);
	}

	/// solve solves this instance.
	solve(): DefiniteSATResult {
		if (this.decisionLevel !== 0) {
			throw new Error("SATSolver.solve() requires decision level must be at 0");
		} else if (this.assignments.length === 0) {
			throw new Error("SATSolver.solve() requires at least one term");
		} else if (this.assignmentStack.length !== 0) {
			throw new Error("SATSolver.solve() requires no assignments have been made.");
		}

		// Find initial unit clauses (and later, pure literals).
		let unitLiterals = new UnitLiteralQueue();
		for (let i = 0; i < this.clauses.length; i++) {
			const clause = this.clauses[i];
			if (clause.length === 1) {
				const literal = clause[0];
				const conflict = unitLiterals.pushOrFindConflict(literal, i);
				if (conflict) {
					// There are two contradicting unit-clauses.
					return "unsatisfiable";
				}
			}
		}

		for (let [unitLiteral, antecedent] of unitLiterals) {
			// Invariant: the literal "not unitLiteral" is not in
			// `unitLiterals`.
			const [newUnitLiterals, newAntecedents] = this.assign(unitLiteral, antecedent);
			for (let i = 0; i < newUnitLiterals.length; i++) {
				const conflict = unitLiterals.pushOrFindConflict(newUnitLiterals[i], newAntecedents[i]);
				if (conflict) {
					// There are two contradicting unit-clauses; we are still 
					// prior to any decisions, so the formula overall must be
					// unsatisfiable.
					return "unsatisfiable";
				}
			}
		}

		let ordering = [];
		for (let i = 1; i < this.assignments.length; i++) {
			ordering[i - 1] = i;
		}

		// Start the main CDCL loop.
		// Repeat assignments until an assigment has been made to every term.
		let cursor = 0;
		while (this.assignmentStack.length < this.assignments.length - 1) {
			let decisionTerm = ordering[cursor];
			cursor += 1;
			cursor %= ordering.length;

			if (this.assignments[decisionTerm] !== 0) {
				// This variable has already been assigned.
				continue;

			}

			if (unitLiterals.size() !== 0) {
				throw new Error("invariant violation");
			}

			// Enqueue a free decision.
			this.decisionLevel += 1;
			const expectNull = unitLiterals.pushOrFindConflict(+decisionTerm, -1);
			if (expectNull !== null) {
				throw new Error("bad state");
			}

			// Propagate unit consequences of that free decision.
			for (let [unitLiteral, antecedent] of unitLiterals) {
				const newUnitClauses = this.assign(unitLiteral, antecedent);
				const conflict = unitLiterals.pushAllOrFindConflict(newUnitClauses);
				if (conflict !== null) {
					const conflictClause = this.diagnoseConflict(conflict[0], conflict[1], conflict[2]);
					let maxDecisionLevel = 0;
					for (let i = 0; i < conflictClause.length; i++) {
						const conflictLiteral = conflictClause[i];
						const conflictTerm = conflictLiteral > 0 ? conflictLiteral : -conflictLiteral;
						maxDecisionLevel = Math.max(maxDecisionLevel, this.termDecisionLevel[conflictTerm]);
					}
					if (maxDecisionLevel == 0) {
						// If the conflict-clause is all of terms prior to the 
						// first decision (including an empty conflict clause),
						// this instance has been refuted.
						return "unsatisfiable";
					}

					// Find the decision level at which the conflict clause 
					// becomes a unit clause.
					let conflictUnsatisfied = new Set(conflictClause);
					let stopDecisionLevel = 0;
					for (let i = 0; i <= this.assignmentStack.length; i++) {
						if (conflictUnsatisfied.size === 1) {
							// N.B.: This loop should never finish normally!
							break;
						}

						conflictUnsatisfied.delete(-this.assignmentStack[i]);
						stopDecisionLevel = this.termDecisionLevel[Math.abs(this.assignmentStack[i])];
					}


					// Rewind at least one decision in the conflict clause.
					this.rollbackToDecisionLevel(stopDecisionLevel);

					// Then, add the clause, bearing in mind it SHOULD be a unit
					// clause (asserting clause), which should expand 
					// propagation within a PREVIOUS decision level.
					const conflictClauseID = this.addClause(conflictClause);

					// Find the unit literal in the conflict clause.
					let assertingLiteral = null;
					for (let conflictLiteral of conflictClause) {
						const conflictTerm = conflictLiteral > 0 ? conflictLiteral : -conflictLiteral;
						const sign = this.assignments[conflictTerm];
						if (sign * conflictLiteral > 0) {
							throw new Error("invariant violation: conflictClause is satisfied by the current assignment");
						} else if (sign === 0) {
							// Unassigned literal.
							if (assertingLiteral === null) {
								assertingLiteral = conflictLiteral;
							} else {
								throw new Error("invariant violation: conflictClause is not an asserting clause (too many unassigned literals)");
							}
						}
					}

					if (assertingLiteral === null) {
						throw new Error("invariant violation: conflictClause is not an asserting clause (contradiction)");
					}

					unitLiterals.clear();
					unitLiterals.pushOrFindConflict(assertingLiteral, conflictClauseID);

					// Continue in the unit-propagation loop.
				}
			}
		}

		return this.getAssignment();
	}

	addClause(clause: Literal[]): ClauseID {
		let hasUnassigned = false;
		for (let literal of clause) {
			const term = literal > 0 ? literal : -literal;
			if (this.assignments[term] === 0) {
				hasUnassigned = true;
				break;
			}
		}
		if (!hasUnassigned) {
			throw new Error("SATSolver.addClause() requires at least one unassigned literal");
		}

		const clauseID = this.clauses.length;
		this.clauses.push(clause);

		// Push unassigned literals to the front of the clause, with more 
		// recently assigned literals after that.
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
				this.watchedPositive[literal].add(clauseID);
			} else {
				this.watchedNegative[-literal].add(clauseID);
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
			if (w.length > 2) {
				throw new Error("Too many watched literals in this clause!");
			} else if (w.length < 2) {
				throw new Error("Too few watched literals in this clause!");
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
		for (let watchingClauseID of watchers) {
			const watchingClause = this.clauses[watchingClauseID];

			let satisfied = false;
			let unfalsfiedCount = 0;
			let latestUnfalsfiedLiteralIndex = -1;
			for (let i = 0; i < watchingClause.length; i++) {
				const l = watchingClause[i];
				const t = l > 0 ? l : -l;
				const a = this.assignments[t];
				const satisfyiedBy = l > 0 ? +1 : -1;
				if (a === satisfyiedBy) {
					satisfied = true;
					break;
				} else if (a === 0) {
					unfalsfiedCount += 1;
					// N.B.: since watched literals are pushed to the front of
					// the watchingClause array, if there are any unwatched unfalsified
					// literals, they will be the result of this loop.
					latestUnfalsfiedLiteralIndex = i;
				}
			}

			if (satisfied) {
				// If already satisfied, can remain.
				continue;
			}

			// Either find a new literal to watch,
			// or recognize that this watchingClause is now a unit clause.
			const destination = watchingClause[0] === -assignedLiteral ? 0 : 1;

			if (unfalsfiedCount == 1) {
				// `this.assignments` is not yet updated; thus the only 
				// falsified literal is the one being deleted; so this is a
				// conflicting unit-clause.
				throw new Error("This assignment falsifies an entire clause.\n(adding assignment "
					+ assignedLiteral + " to assignment stack " + this.assignmentStack
					+ ";\nwatchingClause = " + watchingClause + " with id " + watchingClauseID + ")");
			} else if (unfalsfiedCount == 2) {
				// `watchingClause` is not yet satisfied, and has no unfalsified 
				// literals other than its two watched literals.
				// Thus, this is becoming a unit clause of only the other
				// watched literal.
				discoveredUnitLiterals.push(watchingClause[1 - destination]);
				discoveredAntecedents.push(watchingClauseID);
			} else {
				// There remains an unfalsified literal, other than the two 
				// watched literals, in this unsatisfied watchingClause.
				watchers.delete(watchingClauseID);
				const newWatchedLiteral = watchingClause[latestUnfalsfiedLiteralIndex];
				const newWatchedTerm = newWatchedLiteral > 0 ? newWatchedLiteral : -newWatchedLiteral;
				if (newWatchedLiteral > 0) {
					this.watchedPositive[newWatchedTerm].add(watchingClauseID);
				} else {
					this.watchedNegative[newWatchedTerm].add(watchingClauseID);
				}

				swap(watchingClause, destination, latestUnfalsfiedLiteralIndex);
			}
		}

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

	private diagnoseConflict(conflictLiteral: Literal,
		conflictLiteralAntecedent: ClauseID,
		negativeConflictLiteralAntecedent: ClauseID): Literal[] {
		// This method is called when a "conflict" is detected: an assignment
		// has already been made of "not literal", but the clause `cause` is a
		// unit-clause of just `literal`.

		// This method has to "diagnose" the conflict, producing a new clause
		// which rejects previous "decisions".

		// The simplest diagnosis is to reject the entire set of decision 
		// currently in the assignment stack. However, some of those decisions
		// may not be relevant to this particular conflict; generating a more 
		// general conflict clause will prune more of the remaining search 
		// space.

		// The `antecedentClause` mapping can be used to generate an 
		// "implication graph". The vertices of the graph are literals.
		// For non-decision variables, an edge exists for the negation of each
		// other literal in the vertex's antecedent clause.

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

		let q = [conflictLiteral, -conflictLiteral];
		for (let i = 0; i < q.length; i++) {
			const literal = q[i];
			const term = literal > 0 ? literal : -literal;

			let antecedent: ClauseID;
			if (literal == conflictLiteral) {
				antecedent = conflictLiteralAntecedent;
			} else if (literal == -conflictLiteral) {
				antecedent = negativeConflictLiteralAntecedent;
			} else {
				antecedent = this.antecedentClause[term];
			}

			if (antecedent < 0 || (this.termDecisionLevel[term] < this.decisionLevel && literal !== conflictLiteral && literal !== -conflictLiteral)) {
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

	private rollbackToDecisionLevel(level: number) {
		while (this.decisionLevel > level) {
			this.popAssignment();
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
