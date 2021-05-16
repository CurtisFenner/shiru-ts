import { TrieMap, DisjointSet } from "./data";
import { Literal, SATSolver } from "./sat";

/// SMTSolver represents an "satisfiability modulo theories" instance, with
/// support for quantifier instantiation.
/// With respect to refutation, SMTSolver is sound but not complete -- some
/// returned "satisfactions" do not actually satisfy the instance, but all
/// refutation results definitely refute the instance.
export abstract class SMTSolver<E, Counterexample> {
	private sat: SATSolver;
	private addedAdditional = false;

	constructor() {
		this.sat = new SATSolver();
	}

	addConstraint(constraint: E) {
		for (let clause of this.clausify(constraint)) {
			this.addClausified(clause);
		}
	}

	/// RETURNS any additional clauses, immediately before the first call to
	/// solve.
	protected additionalClauses(): Literal[][] {
		return [];
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
		if (!this.addedAdditional) {
			for (let clause of this.additionalClauses()) {
				const maxTerm = Math.max(...clause.map(x => x > 0 ? x : -x));
				this.sat.initTerms(maxTerm);
				this.sat.addClause(clause);
			}
		}

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
export type UFVariable = string & { __brand: "smt-uf-variable" };

export function isUFVariable(value: UFValue): value is UFVariable {
	return typeof value === "string";
}

export type UFFunction = string & { __brand: "smt-uf-function" };
export type UFValue = UFVariable
	| { tag: "app", f: UFFunction, args: UFValue[] }
	| UFLiteralValue;

// UFLiteralValue considers only the equality of the `literal` field.
export type UFLiteralValue = { tag: "literal", literal: unknown, sort: UFSort };

// A UFPredicate is a UFValue with sort `"bool"`.
export type UFPredicate = UFValue;

export type UFConstraint = { tag: "=", left: UFValue, right: UFValue }
	| { tag: "predicate", predicate: UFPredicate }
	| { tag: "not", constraint: UFConstraint };

/// Sorts are identified by opaque numbers (or the special type "bool").
export type UFSort = number | "bool";

type UFSATTermData = { tag: "app", f: UFFunction, argsDS: number[] }
	| { tag: "=", leftDS: number, rightDS: number }
	| { tag: "var", v: string };

type DSObjectData = string
	| { tag: "app", f: string, args: number[] }
	| { tag: "const", value: unknown, sort: UFSort };

/// Data structure to track object identities to be used in a SATSolver and
/// DisjointSet data structure.
class UFValueTracker {
	// Map from a function name to its return sort.
	private functions: Record<string, {
		applications: TrieMap<number[], { dsIndex: number, satTerm: number | null }>,
		returnSort: UFSort
	}> = {};

	/// Map from a variable name to its sort.
	private variables: Record<string, { dsIndex: number, satTerm: null | number, sort: UFSort }> = {};

	/// Map from UFConstValue to its identifier in the disjoint-set data
	/// structure.
	private constants: Map<unknown, { dsIndex: number }> = new Map();

	/// Map from a DisjointSet object to data.
	/// A `string` represents a variable.
	/// A tuple represents a function application.
	private dsObjects: DSObjectData[] = [];

	/// Map from a SATSolver term to data.
	/// A `string` represents a variable.
	/// A tuple represents a function application.
	private satTerms: UFSATTermData[] = [null] as any;

	private equalityVariables: TrieMap<[number, number], number> = new TrieMap();

	defineVariable(name: string, sort: UFSort): { dsIndex: number, satTerm: number | null } {
		const existing = this.variables[name];
		if (existing) {
			throw new Error(`variable \`${name}\` has already been defined`);
		}
		const dsIndex = this.dsObjects.length;
		this.dsObjects[dsIndex] = name;
		this.variables[name] = {
			dsIndex: dsIndex,
			satTerm: null,
			sort,
		};
		if (sort === "bool") {
			const satTerm = this.satTerms.length;
			this.variables[name].satTerm = satTerm;
			this.satTerms[satTerm] = { tag: "var", v: name };
		}
		return this.variables[name];
	}

	getVariable(name: string) {
		const existing = this.variables[name];
		if (!existing) {
			throw new Error(`no such variable \`${name}\``);
		}
		return existing;
	}

	defineFunction(name: string, returnSort: UFSort) {
		if (this.functions[name] !== undefined) {
			throw new Error(`function \`${name}\` is already defined`);
		}
		this.functions[name] = {
			applications: new TrieMap(),
			returnSort,
		};
	}

	iterateApplications() {
		const db = this;
		return {
			*[Symbol.iterator]() {
				for (let f in db.functions) {
					yield [f, db.functions[f].applications] as const;
				}
				db.functions;
			}
		}
	}

	getDSDefinition(ds: number): DSObjectData {
		return this.dsObjects[ds];
	}

	getDSSort(ds: number): UFSort {
		const definition = this.dsObjects[ds];
		if (typeof definition === "string") {
			return this.variables[definition].sort;
		} else if (definition.tag === "app") {
			return this.functions[definition.f].returnSort;
		} else {
			return definition.sort;
		}
	}

	addLiteral(value: unknown, sort: UFSort) {
		if (sort === "bool") {
			throw new Error("addConst: do not use this method for bool sort");
		}

		if (!this.constants.has(value)) {
			const dsIndex = this.dsObjects.length;
			this.dsObjects[dsIndex] = { tag: "const", value, sort };
			this.constants.set(value, { dsIndex });
		}

		return {
			dsIndex: this.constants.get(value)!.dsIndex,
			satTerm: null,
		}
	}

	addApplication(f: UFFunction, argsDS: number[]) {
		const fInfo = this.functions[f];
		if (fInfo === undefined) {
			throw new Error(`function \`${f}\` has not been defined`);
		}
		const existing = fInfo.applications.get(argsDS);
		if (existing) {
			return existing;
		}

		const dsIndex = this.dsObjects.length;
		this.dsObjects[dsIndex] = { tag: "app", f, args: argsDS };
		let satTerm = null;
		if (fInfo.returnSort === "bool") {
			satTerm = this.satTerms.length;
			this.satTerms[satTerm] = { tag: "app", f, argsDS };
		} else {
		}
		const application = { dsIndex, satTerm };
		fInfo.applications.put(argsDS, application);
		return application;
	}

	getEqualityVariable(leftDS: number, rightDS: number) {
		const existing = this.equalityVariables.get([leftDS, rightDS]);
		if (existing !== undefined) {
			return existing;
		}

		const satTerm = this.satTerms.length;
		this.satTerms[satTerm] = { tag: "=", leftDS, rightDS };
		return satTerm;
	}

	describeSatTerm(term: number) {
		return this.satTerms[term];
	}
}

/// UFTheory implements the "theory of uninterpreted functions".
/// This theory understands the properties of equality
/// (symmetric, reflective, and transitive)
/// as well as the "extensionality"/"congruence" of function application:
/// a == b implies f(a) == f(b)
export class UFTheory extends SMTSolver<UFConstraint[], UFCounter> {
	valueTracker = new UFValueTracker();

	falseObject: { dsIndex: number, satTerm: number };
	trueObject: { dsIndex: number, satTerm: number };

	constructor() {
		super();

		this.falseObject = this.valueTracker.defineVariable("$FALSE", "bool") as any;
		this.trueObject = this.valueTracker.defineVariable("$TRUE", "bool") as any;
	}

	defineVariable(name: string, sort: UFSort) {
		if (name[0] === "$") {
			throw new Error("variables starting with $ are reserved by the implementation");
		}
		this.valueTracker.defineVariable(name, sort);
	}

	defineFunction(name: string, returnSort: UFSort) {
		if (name[0] === "$") {
			throw new Error("functions starting with $ are reserved by the implementation");
		}
		this.valueTracker.defineFunction(name, returnSort);
	}

	additionalClauses() {
		// valueTracker registers a sat variable for each of these.
		// Generate a unit clause for each to be the correct sign.
		return [
			[this.trueObject.satTerm],
			[-this.falseObject.satTerm],
		];
	}

	rejectModel(concrete: readonly Literal[]): Literal[] | UFCounter {
		const ds: DisjointSet<number[]> = new DisjointSet();

		// Union all positive equalities.
		for (let literal of concrete) {
			const term = literal > 0 ? literal : -literal;
			const info = this.valueTracker.describeSatTerm(term);
			if (info.tag === "=") {
				if (literal > 0) {
					ds.union(info.leftDS, info.rightDS, [literal]);
				}
			} else {
				// For bool sorted objects, join them to the literals true and
				// false.
				let obj: number;
				if (info.tag === "app") {
					obj = this.valueTracker.addApplication(info.f, info.argsDS).dsIndex;
				} else {
					obj = this.valueTracker.getVariable(info.v).dsIndex;
				}
				if (literal > 0) {
					ds.union(this.trueObject.dsIndex, obj, [literal]);
				} else {
					ds.union(this.falseObject.dsIndex, obj, [literal]);
				}
			}
		}

		while (true) {
			// Find all function applications and "canonicalize" them, producing new
			// union operations.
			let congruenceEqualities = [];
			for (const [f, applications] of this.valueTracker.iterateApplications()) {
				let canonicalByRepresentatives: TrieMap<number[], { dsIndex: number, argsDS: number[] }> = new TrieMap();
				for (let [applicationArgs, applicationIdentity] of applications) {
					const argRepresentatives = applicationArgs.map(x => ds.representative(x));
					const equalTo = canonicalByRepresentatives.get(argRepresentatives);
					if (equalTo !== undefined) {
						if (!ds.compareEqual(applicationIdentity.dsIndex, equalTo.dsIndex)) {
							// Enqueue a congruence equality:
							// Eagerly updating ds here would invalidate canonicalByRepresentatives.
							let reason = [];
							for (let i = 0; i < applicationArgs.length; i++) {
								for (let e of ds.explainEquality(applicationArgs[i], equalTo.argsDS[i])) {
									reason.push(...e);
								}
							}

							// The reason for this equivalence is the
							// conjunction of the reasons for each argument
							// being equal.
							congruenceEqualities.push({
								left: applicationIdentity.dsIndex,
								right: equalTo.dsIndex,
								reason,
							});
						}
					} else {
						canonicalByRepresentatives.put(argRepresentatives, {
							dsIndex: applicationIdentity.dsIndex,
							argsDS: applicationArgs,
						});
					}
				}
			}

			for (let { left, right, reason } of congruenceEqualities) {
				ds.union(left, right, reason);
			}

			if (congruenceEqualities.length === 0) {
				break;
			}
		}

		let disequal: TrieMap<number[], Literal> = new TrieMap();
		for (let literal of concrete) {
			const term = literal > 0 ? literal : -literal;
			const info = this.valueTracker.describeSatTerm(term);

			if (info.tag === "=") {
				if (literal < 0) {
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

		// Ensure that "true != false".
		if (ds.compareEqual(this.falseObject.dsIndex, this.trueObject.dsIndex)) {
			return ds.explainEquality(this.falseObject.dsIndex, this.trueObject.dsIndex).map(x => -x);
		}

		const components = ds.components();
		for (let component of components) {
			const rep = ds.representative(component[0]);
			const sort = this.valueTracker.getDSSort(rep);

			// Check for distinct symbols within the same component.
			let symbol = null;
			for (let x of component) {
				const definition = this.valueTracker.getDSDefinition(x);
				if (typeof definition === "object") {
					if (definition.tag === "const") {
						if (symbol === null) {
							symbol = x;
						} else {
							// Two distinct symbols are equal.
							const conflictClause = [];
							for (let e of ds.explainEquality(x, symbol)) {
								conflictClause.push(...e.map(s => -s));
							}
							return conflictClause;
						}
					}
				}
			}

			// Search for a "triangle" of inequalities in the boolean-sorted
			// components.
			if (sort === "bool") {
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

	private literalFor(constraint: UFConstraint): Literal {
		if (constraint.tag === "not") {
			return -this.literalFor(constraint.constraint);
		} else if (constraint.tag === "=") {
			const left = this.valueIndex(constraint.left);
			const right = this.valueIndex(constraint.right);
			return this.valueTracker.getEqualityVariable(left.dsIndex, right.dsIndex);
		} else if (constraint.tag === "predicate") {
			const app = this.valueIndex(constraint.predicate);
			if (app.satTerm === null) {
				throw new Error(`value ${JSON.stringify(constraint)} with non-bool sort cannot be used in a clause`);
			}
			return app.satTerm;
		}
		throw new Error(`unhandled ${constraint}`);
	}

	/// RETURNS an index into a DisjointSet object.
	private valueIndex(v: UFValue): { dsIndex: number, satTerm: number | null } {
		if (isUFVariable(v)) {
			const vInfo = this.valueTracker.getVariable(v);
			return { dsIndex: vInfo.dsIndex, satTerm: vInfo.satTerm };
		} else if (v.tag === "app") {
			const args = v.args.map(a => this.valueIndex(a).dsIndex);
			return this.valueTracker.addApplication(v.f, args);
		} else if (v.tag === "literal") {
			if (typeof v.literal === "boolean") {
				return v.literal ? this.trueObject : this.falseObject;
			}
			return this.valueTracker.addLiteral(v.literal, v.sort);
		}
		throw new Error(`unhandled ${v}`);
	}
}
