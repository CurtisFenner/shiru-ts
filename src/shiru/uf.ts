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

export interface Semantics<Reason> {
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

	generalInterpreter?: {
		g(
			matcher: EMatcher<Reason>,
			solver: UFSolver<Reason>,
			id: egraph.EObject,
			operands: egraph.EObject[],
		): "change" | "no-change",
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

export class EMatcher<Reason> {
	private membersByClassAndTerm = new Map<egraph.EObject, Map<FnID | VarID, egraph.EClassDescription<FnID | VarID>>>();

	constructor(
		public egraph: egraph.EGraph<FnID | VarID, "constant", Reason>,
		eclasses: Map<egraph.EObject, egraph.EClassDescription<FnID | VarID>>,
	) {
		for (const { members, representative } of eclasses.values()) {
			const map = new Map<FnID | VarID, egraph.EClassDescription<FnID | VarID>>();
			for (const member of members) {
				let byTerm = map.get(member.term);
				if (byTerm === undefined) {
					byTerm = { members: [], representative };
					map.set(member.term, byTerm);
				}
				byTerm.members.push(member);
			}
			this.membersByClassAndTerm.set(representative, map);
		}
	}

	asApplication(
		obj: egraph.EObject,
		term: FnID,
	): Array<{
		id: egraph.EObject,
		term: FnID,
		operands: egraph.EObject[],
		reason: Set<Reason>,
	}> {
		const eclass = this.membersByClassAndTerm.get(this.egraph.getRepresentative(obj));
		if (eclass === undefined) {
			throw new Error("asApplication: obj is not contained in this membersByClassAndTerm index");
		}

		const byTerm = eclass.get(term);
		if (byTerm === undefined) {
			return [];
		}

		const out = [];
		for (let i = 0; i < byTerm.members.length; i++) {
			const member = byTerm.members[i];
			const reason = this.egraph.query(obj, member.id);
			if (reason === null) {
				throw new Error("asApplication: membersByClassAndItem index does not match egraph.query result");
			}
			out.push({
				id: member.id,
				term,
				operands: member.operands,
				reason,
			});
		}
		return out;
	}
}

export class UFSolver<Reason> {
	private values = new Map<ValueID, Value>();
	private fns = new Map<FnID, Semantics<Reason>>();
	private egraph = new egraph.EGraph<VarID | FnID, "constant", Reason>();

	private constants = new DefaultMap<unknown, ValueID>(constant => {
		const varID = Symbol("uf-constant") as VarID;
		const object = this.egraph.add(varID, [], "constant", String(constant)) as ValueID;
		this.values.set(object, { tag: "constant", constant });
		return object;
	});

	createVariable(hint?: string): ValueID {
		const varID = Symbol(hint || "uf-var") as VarID;
		const object = this.egraph.add(varID, [], undefined, hint) as ValueID;
		this.values.set(object, { tag: "var", var: varID });
		return object;
	}

	createFn(semantics: Semantics<Reason>, hint?: string): FnID {
		const fnID = Symbol(hint || "uf-fn") as FnID;
		if (semantics.transitiveAcyclic && !semantics.transitive) {
			throw new Error("UFSolver.createFn: semantics.transitiveAcyclic requires semantics.transitive");
		}
		this.fns.set(fnID, semantics);
		return fnID;
	}

	hasApplication(fn: FnID, args: ValueID[]): ValueID | null {
		return this.egraph.hasStructure(fn, args) as ValueID | null;
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

	getFnSemantics(fnID: FnID): Semantics<Reason> {
		const semantics = this.fns.get(fnID);
		if (semantics === undefined) {
			throw new Error("UFSolver.getFnSemantics: no such fn");
		}
		return semantics;
	}

	// Create symbolic constants for the two boolean values.
	trueObject = this.createConstant(true);
	falseObject = this.createConstant(false);

	printSatisfyingModels = true;

	/// refuteInTheory(assumptions) returns a set of facts which the solver
	/// has determined are inconsistent, or a model ("counterexample") when the
	/// facts appear to be consistent.
	/// refuteInTheory() is _sound_ with respect to refutation; when
	/// "inconsistent" is returned, the assumptions are definitely inconsistent.
	refuteInTheory(
		assumptions: Assumption<Reason>[],
	): UFInconsistency<Reason> | { tag: "model", model: UFCounterexample } {
		this.egraph.reset();

		for (const assumption of assumptions) {
			const truthObject = assumption.assignment
				? this.trueObject
				: this.falseObject;
			this.egraph.merge(truthObject, assumption.constraint, new Set([assumption.reason]));
		}

		// Continuously learn more facts and check for contradictions.
		let progress = true;
		while (progress) {
			progress = false;

			const classes = this.egraph.getClasses(true);

			const trueMembersResult = this.handleTrueMembers(classes);
			if (trueMembersResult === "change") {
				progress = true;
			} else if (trueMembersResult !== "no-change") {
				return trueMembersResult;
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

			const falseMembersResult = this.handleFalseMembers(classes);
			if (falseMembersResult === "change") {
				progress = true;
			} else if (falseMembersResult !== "no-change") {
				return falseMembersResult;
			}
		}

		// The UFSolver has failed to show that the given assumptions are
		// inconsistent.

		// Print the model.
		if (this.printSatisfyingModels) {
			console.log("</refuteInTheory: model>");
			console.log("\tassumptions:");
			for (const assumption of assumptions) {
				console.log("\t\t", assumption.assignment, "for", assumption.constraint);
			}
			console.log("\tmodel:");
			for (const [rep, members] of this.egraph.getClasses()) {
				console.log("\t\t", rep);
				for (const member of members.members) {
					console.log("\t\t\t=", member.id);
				}
			}
		}

		return {
			tag: "model",
			model: {},
		};
	}

	private handleTrueMembers(
		classes: Map<egraph.EObject, egraph.EClassDescription<FnID | VarID>>,
	): "change" | "no-change" | UFInconsistency<Reason> {
		// Iterate over all true constraints (those equal to the true
		// object).
		let change: "change" | "no-change" = "no-change";
		const trueClass = classes.get(this.trueObject)!;
		for (const trueMember of trueClass.members) {
			const reasonTrue = () => this.egraph.query(this.trueObject, trueMember.id)!;
			const handled = this.handleTrueMember(trueMember.term, trueMember.operands as ValueID[], reasonTrue);
			if (handled === "change") {
				change = "change";
			} else if (handled !== "no-change") {
				return handled;
			}
		}
		return change;
	}

	private handleTrueMember(
		term: FnID | VarID,
		operands: ValueID[],
		reasonTrue: () => Set<Reason>,
	): "change" | "no-change" | UFInconsistency<Reason> {
		const semantics = this.fns.get(term as FnID);
		if (semantics !== undefined) {
			if (semantics.eq) {
				const left = operands[0];
				const right = operands[1];
				if (this.egraph.getRepresentative(left) !== this.egraph.getRepresentative(right)) {
					const newKnowledge = this.egraph.merge(left, right, reasonTrue());
					if (newKnowledge) {
						return "change";
					}
				}
			}
		}
		return "no-change";
	}

	private handleFalseMembers(
		classes: Map<egraph.EObject, egraph.EClassDescription<FnID | VarID>>,
	): "change" | "no-change" | UFInconsistency<Reason> {
		// Iterate over all false constraints (those equal to the false
		// object).
		let change: "change" | "no-change" = "no-change";
		const falseClass = classes.get(this.falseObject)!;
		for (const falseMember of falseClass.members) {
			const reasonFalse = () => this.egraph.query(this.falseObject, falseMember.id)!;
			const handled = this.handleFalseMember(falseMember.term, falseMember.operands as ValueID[], reasonFalse);
			if (handled === "change") {
				change = "change";
			} else if (handled !== "no-change") {
				return handled;
			}
		}
		return change;
	}

	private handleFalseMember(
		term: FnID | VarID,
		operands: ValueID[],
		reasonFalse: () => Set<Reason>,
	): "change" | "no-change" | UFInconsistency<Reason> {
		const semantics = this.fns.get(term as FnID)
		if (semantics !== undefined) {
			if (semantics.eq) {
				const query = this.egraph.query(operands[0], operands[1]);
				if (query !== null) {
					return {
						tag: "inconsistent",
						inconsistent: new Set([...query, ...reasonFalse()]),
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
			const eclasses = this.egraph.getClasses();
			const matcher = new EMatcher(this.egraph, eclasses);
			for (const { members } of eclasses.values()) {
				for (const member of members) {
					const semantics = this.fns.get(member.term as FnID);
					if (semantics !== undefined) {
						const interpreter = semantics.interpreter;
						if (interpreter !== undefined) {
							const subresult = this.propagateFnInterpreter(matcher, member, interpreter);
							if (subresult === "change") {
								iterationMadeChanges = true;
							}
						}

						const generalInterpreter = semantics.generalInterpreter;
						if (generalInterpreter !== undefined) {
							const subresult = this.propagateGeneralInterpreter(matcher, member, generalInterpreter);
							if (subresult === "change") {
								iterationMadeChanges = true;
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

	private propagateGeneralInterpreter(
		matcher: EMatcher<Reason>,
		member: { id: egraph.EObject, operands: egraph.EObject[] },
		interpreter: {
			g(
				matcher: EMatcher<Reason>,
				solver: UFSolver<Reason>,
				id: egraph.EObject,
				operands: egraph.EObject[],
			): "change" | "no-change",
		},
	): "change" | "no-change" {
		return interpreter.g(matcher, this, member.id, member.operands);
	}

	private propagateFnInterpreter(
		matcher: EMatcher<Reason>,
		member: { id: egraph.EObject, operands: egraph.EObject[] },
		interpreter: { f(...args: unknown[]): unknown },
	): "change" | "no-change" {
		return this.propagateGeneralInterpreter(matcher, member, {
			g(
				matcher: EMatcher<Reason>,
				solver: UFSolver<Reason>,
				id: egraph.EObject,
				operands: egraph.EObject[],
			): "change" | "no-change" {
				const reason = new Set<Reason>();
				const args = [];
				for (const operand of operands) {
					const operandConstant = solver.evaluateConstant(operand as ValueID);
					if (operandConstant !== null) {
						args.push(operandConstant.constant);
						for (const r of operandConstant.reason) {
							reason.add(r);
						}
					} else {
						args.push(null);
					}
				}

				const result = interpreter.f(...args);
				if (result !== null) {
					const resultConstant = solver.createConstant(result);
					const changed = solver.egraph.merge(resultConstant, id, reason);
					if (changed) {
						return "change";
					}
				}
				return "no-change";
			},
		});
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

	private booleanFunctions = new Set<FnID>();

	// The Boolean-typed object associated with the given SAT term.
	private objectByTerm = new Map<number, ValueID>();

	createVariable(type: ir.Type, nameHint?: string): ValueID {
		const v = this.solver.createVariable(nameHint);
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

	createFunction(returnType: ir.Type, semantics: Semantics<ReasonSatLiteral>, hint?: string): FnID {
		const fnID = this.solver.createFn(semantics, hint);
		if (ir.equalTypes(ir.T_BOOLEAN, returnType)) {
			this.booleanFunctions.add(fnID);
		}
		return fnID;
	}

	private eqFn = this.createFunction(ir.T_BOOLEAN, { eq: true }, "==");

	createApplication(fnID: FnID, args: ValueID[]): ValueID {
		const application = this.solver.createApplication(fnID, args);
		if (this.booleanFunctions.has(fnID)) {
			// This application must be assigned true or false by the SAT
			// solver.
			this.toSatLiteral(application);
		}
		return application;
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
		const result = this.solver.refuteInTheory(assumptions);
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
