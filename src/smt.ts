import { TrieMap, DisjointSet } from "./data";
import { Literal, SATSolver } from "./sat";

/// SMTSolver represents an "satisfiability modulo theories" instance, with 
/// support for quantifier instantiation.
/// With respect to refutation, SMTSolver is sound but not complete -- some
/// returned "satisfactions" do not actually satisfy the instance, but all
/// refutation results definitely refute the instance.
export abstract class SMTSolver<E, Counterexample> {
	private sat: SATSolver;
	constructor() {
		this.sat = new SATSolver();
	}

	addConstraint(constraint: E) {
		for (let clause of this.clausify(constraint)) {
			this.addClausified(clause);
		}
	}
	
	protected addClausified(clause: Literal[]) {
		let maxTerm = 0;
		for (let literal of clause) {
			const term = literal > 0 ? literal : -literal;
			maxTerm = Math.max(maxTerm, term);
		}
		this.sat.initTerms(maxTerm);
		this.sat.addClause(clause);
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
				const theoryClause = this.rejectModel(booleanModel);
				if (Array.isArray(theoryClause)) {
					// Completely undo the assignment.
					// TODO: theoryClause should be an asserting clause, so the
					// logic in backtracking should be able to replace this.
					this.sat.rollbackToDecisionLevel(-1);
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


	/// rejectModel returns a new clause to add to the SAT solver which 
	/// rejects this concrete assignment.
	/// The returned clause should be an asserting clause in reference to the
	/// concrete assignment.
	protected abstract rejectModel(concrete: Literal[]): Counterexample | Literal[];

	/// clausify returns a set of clauses to add to the underlying SAT solver.
	/// This modifies state, associating literals (and other internal variables)
	/// with the pieces of this constraint, possibly for instantiation.
	protected abstract clausify(constraint: E): Literal[][];

	/// TODO: Instantiation of quantifiers, which is sometimes done in the place
	/// of making decisions in the SATSolver.
}

export interface UFCounter { }
export type UFVariable = string
export type UFFunction = string
export type UFValue = UFVariable | ["app", UFFunction, UFValue[]];

// A UFPredicate is a UFValue with sort `"bool"`.
export type UFPredicate = UFValue;

export type UFConstraint = { tag: "=", left: UFValue, right: UFValue }
	| { tag: "predicate", predicate: UFPredicate }
	| { tag: "not", constraint: UFConstraint };

/// Types are identified by opaque numbers (or the special type "bool").
export type UFType = number | "bool";

type UFSATTermData = { tag: "app", f: UFFunction, argsDS: number[] }
	| { tag: "=", leftDS: number, rightDS: number }
	| { tag: "var", v: string }

/// UFTheory implements the "theory of uninterpreted functions".
/// This theory understands the properties of equality
/// (symmetric, reflective, and transitive)
/// as well as the "extensionality"/"congruence" of function application:
/// a == b implies f(a) == f(b)
export class UFTheory extends SMTSolver<UFConstraint[], UFCounter> {

	// The next index to use for a new value to be tracked in the DisjointSet
	// instance.
	private byDSIndex: Map<number, { sort: UFType, value: UFValue }> = new Map();
	private _nextDisjointSetIndex = 0;
	private vendDSIndex(obj: { sort: UFType, value: UFValue }): number {
		const out = this._nextDisjointSetIndex;
		this.byDSIndex.set(out, obj);
		this._nextDisjointSetIndex += 1;
		return out;
	}

	// The next term to be used in the underlying sat solver.
	private bySatTerm: Record<number, UFSATTermData> = {};
	private _nextSatTerm = 1;
	private vendSatTerm(termData: UFSATTermData): number {
		const out = this._nextSatTerm;
		this.bySatTerm[out] = termData;
		this._nextSatTerm += 1;
		return out;
	}

	private variables: Record<UFVariable, { t: UFType, index: number, satTerm: number | null }> = {};
	private functions: Record<UFFunction, {
		parameters: UFType[], returns: UFType,
		/// mapping from arguments => identity of application within DisjointSet & SAT (when returns bool)
		apps: TrieMap<number[], { dsIndex: number, satTerm: number | null }>,
		/// mapping from identify within DisjointSet => arguments
		argsByDSIndex: Record<number, number[]>,
	}> = {};

	/// mapping from lhs/rhs uf-index to map.
	private equalitySatTerms: TrieMap<[number, number], number> = new TrieMap();

	defineVariable(variable: UFVariable, t: UFType) {
		if (variable in this.variables) {
			throw new Error(`variable \`${variable}\` is already defined`);
		}
		const dsIndex = this.vendDSIndex({ sort: t, value: variable });
		let satTerm = null;
		if (t === "bool") {
			satTerm = this.vendSatTerm({ tag: "var", v: variable });
		}
		this.variables[variable] = { t: t, index: dsIndex, satTerm };
	}

	defineFunction(f: UFFunction, parameters: UFType[], returns: UFType) {
		if (f in this.functions) {
			throw new Error(`function \`${f}\` is already defined`);
		}
		let terms = null;
		if (returns === "bool") {
			terms = new TrieMap<number[], number>();
		}

		this.functions[f] = {
			parameters: parameters,
			returns,
			apps: new TrieMap(),
			argsByDSIndex: {},
		};
	}

	rejectModel(concrete: readonly Literal[]): Literal[] | UFCounter {
		const ds: DisjointSet<number[]> = new DisjointSet();

		// Union all positive equalities.
		for (let literal of concrete) {
			const term = literal > 0 ? literal : -literal;
			const info = this.bySatTerm[term];

			if (literal > 0) {
				if (info.tag === "=") {
					ds.union(info.leftDS, info.rightDS, [literal]);
				}
			}
		}

		while (true) {
			// Find all function applications and "canonicalize" them, producing new
			// union operations.
			let congruenceEqualities = [];
			for (let f in this.functions) {
				let repByCanonArgs: TrieMap<number[], { fDSID: number, args: number[] }> = new TrieMap();
				const fInfo = this.functions[f];
				for (let _id in fInfo.argsByDSIndex) {
					const id = parseInt(_id);
					const args = fInfo.argsByDSIndex[id];
					const canonicalizedArgs = args.map(x => ds.representative(x));
					const existing = repByCanonArgs.get(canonicalizedArgs);
					if (existing !== undefined) {
						if (!ds.compareEqual(id, existing.fDSID)) {
							// Enqueue a congruence equality.
							// Updating ds here would invalidate repByCanonArgs.
							let reason = [];
							for (let i = 0; i < args.length; i++) {
								for (let e of ds.explainEquality(args[i], existing.args[i])) {
									reason.push(...e);
								}
							}

							// The reason for this equivalence is the 
							// conjunction of the reasons for each argument 
							// being equivalent.
							congruenceEqualities.push({ left: id, right: existing, reason });
						}
					} else {
						repByCanonArgs.put(canonicalizedArgs, { fDSID: id, args });
					}
				}
			}

			for (let { left, right, reason } of congruenceEqualities) {
				ds.union(left, right.fDSID, reason);
			}

			if (congruenceEqualities.length === 0) {
				break;
			}
		}

		let disequal: TrieMap<number[], Literal> = new TrieMap();
		for (let literal of concrete) {
			const term = literal > 0 ? literal : -literal;
			const info = this.bySatTerm[term];

			if (literal < 0) {
				if (info.tag === "=") {
					const leftRep = ds.representative(info.leftDS);
					const rightRep = ds.representative(info.rightDS);
					if (leftRep === rightRep) {
						// Some equality literals imply they are in the same 
						// component, but this disequality implies they must be
						// in different components.
						const explanation = ds.explainEquality(info.leftDS, info.rightDS);
						const conflictClause = [-literal];
						for (let e of explanation) {
							conflictClause.push(...e.map(x => -x));
						}
						return conflictClause;
					}
					disequal.put([Math.min(leftRep, rightRep), Math.max(leftRep, rightRep)], literal);
				}
			}
		}

		// Search for a "triangle" of inequalities in the boolean-sorted 
		// components.
		const components = ds.components();
		for (let component of components) {
			const rep = ds.representative(component[0]);
			const repInfo = this.byDSIndex.get(rep);
			if (repInfo?.sort !== "bool") {
				continue;
			}

			for (let [edge, edgeLiteral] of disequal) {
				const a = edge[0];
				const b = edge[1];
				const edgeARep = disequal.get([Math.min(a, rep), Math.max(a, rep)]);
				const edgeBRep = disequal.get([Math.min(b, rep), Math.max(b, rep)]);
				if (edgeARep !== undefined && edgeBRep !== undefined) {
					// (a, b), (a, rep), (b, rep) form a triangle of
					// inequalities between booleans.
					return [-edgeLiteral, -edgeARep, -edgeBRep];
				}
			}
		}

		// No contradiction was found.
		return {};
	}

	clausify(clause: UFConstraint[]): number[][] {
		// Each clause is a disjunction of UFConstraints.
		const satClause = [];
		for (let alternative of clause) {
			satClause.push(this.literalFor(alternative));
		}
		return [satClause];
	}

	private equalitySatTerm(leftDS: number, rightDS: number): Literal {
		let eqTerm = this.equalitySatTerms.get([leftDS, rightDS]);
		if (eqTerm === undefined) {
			eqTerm = this.vendSatTerm({ tag: "=", leftDS, rightDS });
			this.equalitySatTerms.put([leftDS, rightDS], eqTerm);
		}
		return eqTerm;
	}

	private literalFor(constraint: UFConstraint): Literal {
		if (typeof constraint === "string") {
			const vInfo = this.variables[constraint];
			const satTerm = vInfo.satTerm;
			if (satTerm === null) {
				throw new Error(`varaible ${constraint} with non-bool type ${vInfo.t} cannot be used in a clause`);
			}

			return satTerm;
		} else if (constraint.tag === "not") {
			return -this.literalFor(constraint.constraint);
		} else if (constraint.tag === "=") {
			const left = this.valueIndex(constraint.left);
			const right = this.valueIndex(constraint.right);
			return this.equalitySatTerm(left.dsIndex, right.dsIndex);
		} else if (constraint.tag === "predicate") {
			const app = this.valueIndex(constraint.predicate);
			if (app.satTerm === null) {
				throw new Error(`value ${constraint} with non-bool sort cannot be used in a clause`);
			}
			return app.satTerm;
		}
		throw new Error(`unhandled ${constraint}`);
	}

	/// RETURNS an index into a DisjointSet object.
	private valueIndex(v: UFValue): { dsIndex: number, satTerm: number | null } {
		if (typeof v === "string") {
			const vInfo = this.variables[v];
			if (vInfo === undefined) {
				throw new Error(`variable ${v} has not been defined`);
			}
			return { dsIndex: vInfo.index, satTerm: vInfo.satTerm };
		}
		if (v[0] === "app") {
			const args = v[2].map(a => this.valueIndex(a).dsIndex);
			const f = v[1];
			const fInfo = this.functions[f];
			let app = fInfo.apps.get(args);
			if (app === undefined) {
				app = { dsIndex: this.vendDSIndex({ sort: fInfo.returns, value: v }), satTerm: null };
				if (fInfo.returns === "bool") {
					app.satTerm = this.vendSatTerm({
						tag: "app",
						f: f,
						argsDS: args,
					});
				}
				fInfo.apps.put(args, app);
				fInfo.argsByDSIndex[app.dsIndex] = args;
			}
			return app;
		}

		throw new Error(`unhandled ${v}`);
	}
}
