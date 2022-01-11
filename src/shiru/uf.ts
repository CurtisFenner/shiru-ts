import { DefaultMap } from "./data";
import * as egraph from "./egraph";
import * as ir from "./ir";
import * as smt from "./smt";

export interface UFCounterexample { }

type VarID = symbol & { __brand: "uf-var" };
export type FnID = symbol & { __brand: "uf-fn" };

type Value = VarValue | AppValue | ConstantValue;

interface VarValue {
	tag: "var",
	var: VarID,
}

interface AppValue {
	tag: "app",
	fn: FnID,
	args: ValueID[],
}

interface ConstantValue {
	tag: "constant",
	constant: unknown,
}

// A (boolean) variable ID.
type ReasonSatLiteral = number;

export type ValueID = egraph.EObject & { __uf: "uf.ValueID" };

export interface Semantics {
	/// An `eq` function respects congruence: a == b implies f(a) == f(b).
	eq?: true,

	not?: true,

	/// A `transitive` function respects transitivity:
	/// f(a, b) and f(b, a) implies f(a, c).
	/// (This need not be specified for `eq` functions)
	transitive?: true,

	/// A `transitiveAcyclic` function is a `transitive` function which does not
	/// admit cycles (a < b < c < d < ... < a). This implies that the relation
	/// is anti-reflexive.
	transitiveAcyclic?: true,

	interpreter?: {
		f(...args: (unknown | null)[]): unknown | null,
	},
}

function transitivitySearch<Reason>(
	digraphOutEdges: DefaultMap<symbol, { reason: Set<Reason>, target: symbol }[]>,
	source: symbol,
	target: symbol,
): Set<Reason> | null {
	const reached = new Set<symbol>();
	const frontier = [{ source, reason: new Set<Reason>() }];

	while (frontier.length !== 0) {
		const top = frontier.pop()!;
		const outEdges = digraphOutEdges.get(top.source);
		for (const outEdge of outEdges) {
			if (!reached.has(outEdge.target)) {
				const reason = new Set([...top.reason, ...outEdge.reason]);
				if (outEdge.target === target) {
					return reason;
				}
				reached.add(outEdge.target);
				frontier.push({
					source: outEdge.target,
					reason,
				});
			}
		}
	}
	return null;
}

export interface Assumption<Reason> {
	constraint: ValueID,
	assignment: boolean,
	reason: Reason,
};

interface UFInconsistency<Reason> {
	tag: "inconsistent",
	inconsistent: Set<Reason>,
}

export class UFSolver<Reason> {
	private values = new Map<ValueID, Value>();
	private fns = new Map<FnID, Semantics>();
	private egraph = new egraph.EGraph<VarID | FnID, "constant", Reason>();

	private constants = new DefaultMap<unknown, ValueID>(constant => {
		const varID = Symbol("uf-constant") as VarID;
		const object = this.egraph.add(varID, [], "constant", String(constant)) as ValueID;
		this.values.set(object, { tag: "constant", constant });
		return object;
	});

	createVariable(hint?: string): ValueID {
		const varID = Symbol("uf-var") as VarID;
		const object = this.egraph.add(varID, [], undefined, hint) as ValueID;
		this.values.set(object, { tag: "var", var: Symbol("uf-var") as VarID });
		return object;
	}

	createFn(semantics: Semantics): FnID {
		const fnID = Symbol("uf-fn") as FnID;
		if (semantics.transitiveAcyclic && !semantics.transitive) {
			throw new Error("UFSolver.createFn: semantics.transitiveAcyclic requires semantics.transitive");
		}
		this.fns.set(fnID, semantics);
		return fnID;
	}

	createApplication(fn: FnID, args: ValueID[]): ValueID {
		const object = this.egraph.add(fn, args) as ValueID;
		this.values.set(object, { tag: "app", fn, args });
		return object;
	}

	createConstant(literal: unknown): ValueID {
		return this.constants.get(literal);
	}

	getDefinition(valueID: ValueID): Value {
		const value = this.values.get(valueID);
		if (value === undefined) {
			throw new Error("UFSolver.getDefinition: no such value");
		}
		return value;
	}

	getFnSemantics(fnID: FnID): Semantics {
		const semantics = this.fns.get(fnID);
		if (semantics === undefined) {
			throw new Error("UFSolver.getFnSemantics: no such fn");
		}
		return semantics;
	}

	// Create symbolic constants for the two boolean values.
	trueObject = this.createConstant(true);
	falseObject = this.createConstant(false);

	/// refuteAssumptions(assumptions) returns a set of facts which the solver
	/// has determined are inconsistent, or a model ("counterexample") when the
	/// facts appear to be consistent.
	/// refuteAssumptions() is _sound_ with respect to refutation; when
	/// "inconsistent" is returned, the assumptions are definitely inconsistent.
	refuteAssumptions(
		assumptions: Assumption<Reason>[],
	): UFInconsistency<Reason> | { tag: "model", model: UFCounterexample } {
		this.egraph.reset();

		for (const assumption of assumptions) {
			const truthObject = assumption.assignment
				? this.trueObject
				: this.falseObject;
			this.egraph.merge(truthObject, assumption.constraint, new Set([assumption.reason]));
		}

		let progress = true;
		while (progress) {
			progress = false;

			const classes = this.egraph.getClasses(true);

			// Iterate over all true constraints (those equal to the true
			// object).
			const trueClass = classes.get(this.trueObject)!;
			for (const trueMember of trueClass.members) {
				const reasonTrue = this.egraph.query(this.trueObject, trueMember.id)!;
				const handled = this.handleTrueMember(trueMember.term, trueMember.operands as ValueID[], reasonTrue);
				if (handled === "change") {
					progress = true;
				} else if (handled !== "no-change") {
					return handled;
				}
			}

			// Iterate over all false constraints (those equal to the false
			// object).
			const falseClass = classes.get(this.falseObject)!;
			for (const falseMember of falseClass.members) {
				const reasonFalse = this.egraph.query(this.falseObject, falseMember.id)!;
				const handled = this.handleFalseMember(falseMember.term, falseMember.operands as ValueID[], reasonFalse);
				if (handled === "change") {
					progress = true;
				} else if (handled !== "no-change") {
					return handled;
				}
			}

			if (this.egraph.updateCongruence()) {
				progress = true;
			}

			if (this.propagateFnInterpreters() === "change") {
				progress = true;
			}

			const inconsistency = this.findInconsistentConstants()
				|| this.findTransitivityContradictions();
			if (inconsistency !== null) {
				return {
					tag: "inconsistent",
					inconsistent: inconsistency,
				};
			}
		}

		// The UFSolver has failed to show that the given assumptions are
		// inconsistent.
		return {
			tag: "model",
			model: {},
		};
	}

	private handleTrueMember(
		term: FnID | VarID,
		operands: ValueID[],
		reasonTrue: Set<Reason>,
	): "change" | "no-change" | UFInconsistency<Reason> {
		const semantics = this.fns.get(term as FnID);
		if (semantics !== undefined) {
			if (semantics.eq) {
				const newKnowledge = this.egraph.merge(operands[0], operands[1], reasonTrue);
				if (newKnowledge) {
					return "change";
				}
			}
		}
		return "no-change";
	}

	private handleFalseMember(
		term: FnID | VarID,
		operands: ValueID[],
		reasonFalse: Set<Reason>,
	): "change" | "no-change" | UFInconsistency<Reason> {
		const semantics = this.fns.get(term as FnID)
		if (semantics !== undefined) {
			if (semantics.eq) {
				const query = this.egraph.query(operands[0], operands[1]);
				if (query !== null) {
					return {
						tag: "inconsistent",
						inconsistent: new Set([...query, ...reasonFalse]),
					};
				}
			}
		}
		return "no-change";
	}

	/// `evaluateConstant` returns a constant (as it was passed to
	/// `createConstant`) that is equal to the given value under the current
	/// constraints.
	private evaluateConstant(value: ValueID): { constant: unknown, reason: Set<Reason> } | null {
		const constants = this.egraph.getTagged("constant", value);
		if (constants.length === 0) {
			return null;
		}
		const id = constants[0].id;
		const valueDefinition = this.values.get(id as ValueID);
		if (valueDefinition?.tag !== "constant") {
			throw new Error("UFSolver.evaluateConstant: non-literal tagged");
		}
		return {
			constant: valueDefinition.constant,
			reason: this.egraph.query(value, id)!,
		};
	}

	/// `propagateFnInterpreters()` adds additional constants and equalities by
	/// using the `interpreter` semantics of functions.
	private propagateFnInterpreters(): "change" | "no-change" {
		let madeChanges = false;
		while (true) {
			let iterationMadeChanges = false;
			for (const [eclass, { members }] of this.egraph.getClasses()) {
				for (const member of members) {
					const semantics = this.fns.get(member.term as FnID);
					if (semantics !== undefined) {
						const interpreter = semantics.interpreter;
						if (interpreter !== undefined) {
							const reason = new Set<Reason>();
							const args = [];
							for (const operand of member.operands) {
								const ec = this.evaluateConstant(operand as ValueID);
								if (ec !== null) {
									args.push(ec.constant);
									for (const s of ec.reason) {
										reason.add(s);
									}
								} else {
									args.push(null);
								}
							}
							const r = interpreter.f(...args);
							if (r !== null) {
								const constant = this.createConstant(r);
								const changed = this.egraph.merge(constant, eclass, reason);
								if (changed) {
									iterationMadeChanges = true;
								}
							}
						}
					}
				}
			}
			if (!iterationMadeChanges) {
				break;
			}
			madeChanges = true;
		}
		return madeChanges ? "change" : "no-change";
	}

	private findTransitivityContradictions(): null | Set<Reason> {
		// A directed graph for each transitive function.
		const digraphs = new DefaultMap<FnID, DefaultMap<symbol, { reason: Set<Reason>, target: symbol }[]>>(f => {
			return new DefaultMap(k => []);
		});

		// Retrieve the true/false constraints.
		const classes = this.egraph.getClasses(true);
		const trueClass = classes.get(this.trueObject);
		const falseClass = classes.get(this.falseObject);
		if (trueClass === undefined) {
			throw new Error("findTransitivityContradictions: ICE");
		} else if (falseClass === undefined) {
			throw new Error("findTransitivityContradictions: ICE");
		}

		// For each transitive function, build a directed graph for each
		// application in the "true" equality class.
		for (const app of trueClass.members) {
			const semantics = this.fns.get(app.term as FnID);
			if (semantics !== undefined && semantics.transitive === true) {
				if (app.operands.length !== 2) {
					throw new Error("findTransitivityContradictions: ICE");
				}

				const source = app.operands[0];
				const target = app.operands[1];
				const sourceRep = this.egraph.getRepresentative(source);
				const targetRep = this.egraph.getRepresentative(target);

				const reason = new Set([
					...this.egraph.query(this.trueObject, app.id)!,
					...this.egraph.query(source, sourceRep)!,
					...this.egraph.query(target, targetRep)!,
				]);
				digraphs.get(app.term as FnID).get(sourceRep).push({
					reason: reason,
					target: targetRep,
				});
			}
		}

		// Find each negative transitive constraint.
		for (const app of falseClass.members) {
			const semantics = this.fns.get(app.term as FnID);
			if (semantics !== undefined && semantics.transitive === true) {
				if (app.operands.length !== 2) {
					throw new Error("findTransitivityContradictions: ICE");
				}
				const source = app.operands[0];
				const target = app.operands[1];
				const sourceRep = this.egraph.getRepresentative(source);
				const targetRep = this.egraph.getRepresentative(target);

				// Naively performs a DFS on the set of `<` edges, searching for
				// a contradiction.
				const transitiveChain = transitivitySearch(digraphs.get(app.term as FnID), sourceRep, targetRep);
				if (transitiveChain !== null) {
					return new Set([
						...this.egraph.query(source, sourceRep)!,
						...this.egraph.query(target, targetRep)!,
						...transitiveChain,
						...this.egraph.query(app.id, this.falseObject)!,
					]);
				}
			}
		}

		// Find violations of transitive-acyclic semantics.
		for (const [id] of classes) {
			if (this.egraph.getRepresentative(id) !== id) {
				// Only consider e-class representatives.
				continue;
			}

			// Search for a path from the group to itself.
			for (const [fnID, digraph] of digraphs) {
				const semantics = this.fns.get(fnID)!;
				if (semantics.transitiveAcyclic === true) {
					const transitiveChain = transitivitySearch(digraph, id, id);
					if (transitiveChain !== null) {
						return transitiveChain;
					}
				}
			}
		}

		return null;
	}

	/// findInconsistentConstants() returns a set of reasons which are
	/// inconsistent because they imply that two distinct constants are equal.
	private findInconsistentConstants(): null | Set<Reason> {
		for (const [id, _group] of this.egraph.getClasses()) {
			const constants = this.egraph.getTagged("constant", id);
			if (constants.length > 1) {
				// Two distinct constants are in the same equality class.
				return new Set([...this.egraph.query(constants[0].id, constants[1].id)!]);
			}
		}
		return null;
	}
}

/// UFTheory implements the "theory of uninterpreted functions".
/// This theory understands the properties of equality
/// (symmetric, reflexive, and transitive)
/// as well as the "congruence" of function application:
/// a == b implies f(a) == f(b)
export class UFTheory extends smt.SMTSolver<ValueID[], UFCounterexample> {
	// The UF-theory solver that solves Boolean assignments to theory
	// constraints.
	private solver: UFSolver<ReasonSatLiteral> = new UFSolver();

	// The next SAT term to vend in clausification.
	private nextSatTerm = 1;

	// The SAT term associated with a given Boolean-typed object tracked by the
	// solver.
	private termByObject = new DefaultMap<ValueID, number>(object => {
		const term = this.nextSatTerm;
		this.nextSatTerm += 1;
		this.objectByTerm.set(term, object);
		return term;
	});

	// The Boolean-typed object associated with the given SAT term.
	private objectByTerm = new Map<number, ValueID>();

	createVariable(type: ir.Type): ValueID {
		const v = this.solver.createVariable();
		if (ir.equalTypes(ir.T_BOOLEAN, type)) {
			// Boolean-typed variables must be equal to either true or false.
			// This constraint ensures that the sat solver will commit the
			// variable to a particular assignment.
			this.addUnscopedConstraint([
				this.createApplication(this.eqFn, [this.solver.trueObject, v]),
				this.createApplication(this.eqFn, [this.solver.falseObject, v]),
			]);
		}
		return v;
	}

	createConstant(t: ir.Type, c: unknown): ValueID {
		if (c === null || c === undefined) {
			throw new Error("createConstant: cannot use `" + c + "` as constant");
		}
		return this.solver.createConstant(c);
	}

	createFunction(returnType: ir.Type, semantics: Semantics): FnID {
		return this.solver.createFn(semantics);
	}

	private eqFn = this.createFunction(ir.T_BOOLEAN, { eq: true });

	createApplication(fnID: FnID, args: ValueID[]): ValueID {
		return this.solver.createApplication(fnID, args);
	}

	private toSatLiteral(valueID: ValueID): number {
		const value = this.solver.getDefinition(valueID);
		if (value.tag === "app") {
			const semantics = this.solver.getFnSemantics(value.fn);
			if (semantics.not === true) {
				return -this.toSatLiteral(value.args[0]);
			}
		}
		return this.termByObject.get(valueID);
	}

	clausify(disjunction: ValueID[]): number[][] {
		const clause = [];
		for (const value of disjunction) {
			clause.push(this.toSatLiteral(value));
		}

		return [clause];
	}

	rejectModel(literals: number[]): UFCounterexample | number[] {
		const assumptions: Assumption<ReasonSatLiteral>[] = [];
		for (const literal of literals) {
			const term = literal > 0 ? +literal : -literal;
			const object = this.objectByTerm.get(term)!;
			assumptions.push({
				constraint: object,
				assignment: literal > 0,
				reason: literal,
			});
		}
		const result = this.solver.refuteAssumptions(assumptions);
		if (result.tag === "inconsistent") {
			const learnedClause = [];
			for (const element of result.inconsistent) {
				learnedClause.push(-element);
			}
			return learnedClause;
		}
		return result.model;
	}
}
