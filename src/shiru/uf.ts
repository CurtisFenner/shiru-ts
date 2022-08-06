import { DefaultMap } from "./data";
import * as egraph from "./egraph";
import * as ir from "./ir";
import * as smt from "./smt";
import * as trace from "./trace";

export interface UFCounterexample { model: {} }

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

	interpreter?: (...args: (unknown | null)[]) => unknown | null,

	generalInterpreter?: (
		matcher: EMatcher<Reason>,
		id: ValueID,
		operands: ValueID[],
	) => "change" | "no-change",
}

function transitivitySearch<Reason>(
	digraphOutEdges: DefaultMap<symbol, { reason: egraph.ReasonTree<Reason>, target: symbol }[]>,
	source: symbol,
	target: symbol,
): egraph.ReasonTree<Reason> | null {
	const reached = new Set<symbol>();
	const frontier = [{ source, reason: new egraph.ReasonTree<Reason>() }];

	while (frontier.length !== 0) {
		const top = frontier.pop()!;
		const outEdges = digraphOutEdges.get(top.source);
		for (const outEdge of outEdges) {
			if (!reached.has(outEdge.target)) {
				const reason = egraph.ReasonTree.withChildren([top.reason, outEdge.reason]);
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
	inconsistencies: Set<Reason>[],
}

export class EMatcher<Reason> {
	private membersByClassAndTerm = new Map<egraph.EObject, Map<FnID | VarID, egraph.EClassDescription<FnID | VarID>>>();

	constructor(
		private solver: UFSolver<Reason>,
		private egraph: egraph.EGraph<FnID | VarID, "constant", Reason>,
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

	hasApplication(f: FnID | VarID, operands: ValueID[]): ValueID | null {
		return this.egraph.hasStructure(f, operands) as ValueID;
	}

	query(a: ValueID, b: ValueID): egraph.ReasonTree<Reason> | null {
		return this.egraph.query(a, b);
	}

	merge(a: ValueID, b: ValueID, reason: egraph.ReasonTree<Reason>): boolean {
		// TODO: Currently, this EMatcher's state is not updated when a merge is
		//  performed, meaning that `matchAsApplication` does not return some
		//  matches that it could.
		return this.egraph.merge(a, b, reason);
	}

	evaluateConstant(value: ValueID): { constant: unknown, reason: egraph.ReasonTree<Reason> } | null {
		return this.solver.evaluateConstant(value);
	}

	createConstant(constant: unknown): ValueID {
		const id = this.solver.createConstant(constant);
		const representative = this.egraph.getRepresentative(id);
		if (!this.membersByClassAndTerm.has(representative)) {
			// If this is a new object, it must be tracked by this EMatcher so
			// that subsequent calls to `matchAsApplication` behave correctly.
			const map = new Map<FnID | VarID, egraph.EClassDescription<FnID | VarID>>();
			const definition = this.egraph.getDefinition(id);
			map.set(definition.term, {
				representative,
				members: [
					{
						id,
						term: definition.term,
						operands: definition.operands,
					},
				],
			});
			this.membersByClassAndTerm.set(representative, map);
		}
		return id;
	}

	/**
	 * `matchAsApplication(obj, term)` searches for objects within the matched
	 * `EGraph` which are equal to `obj` and with the given `term` in its
	 * definition.
	 *
	 * Note: For now, this does not reflect equalities generated with `merge`
	 * since the creation of this `EMatcher`.
	 */	matchAsApplication(
		obj: ValueID,
		term: FnID,
	): Array<{
		id: ValueID,
		term: FnID,
		operands: ValueID[],
		reason: egraph.ReasonTree<Reason>,
	}> {
		const eclass = this.membersByClassAndTerm.get(this.egraph.getRepresentative(obj));
		if (eclass === undefined) {
			throw new Error("matchAsApplication: obj (" + String(obj) + ") is not contained in this membersByClassAndTerm index");
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
				throw new Error("matchAsApplication: membersByClassAndItem index does not match egraph.query result");
			}
			out.push({
				id: member.id as ValueID,
				term,
				operands: member.operands as ValueID[],
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
		const object = this.egraph.add(varID, [], String(constant)) as ValueID;
		this.egraph.addTag(object, "constant");
		this.values.set(object, { tag: "constant", constant });
		return object;
	});

	createVariable(debugName: string): ValueID {
		const varID = Symbol(debugName || "unknown-var") as VarID;
		const object = this.egraph.add(varID, [], debugName) as ValueID;
		this.values.set(object, { tag: "var", var: varID });
		return object;
	}

	createFn(semantics: Semantics<Reason>, debugName: string): FnID {
		const fnID = Symbol(debugName || "unknown-fn") as FnID;
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

	/**
	 * `refuteUsingTheory(assumptions, queries)` returns a set of facts which
	 * the solver has determined are inconsistent, or a model ("counterexample")
	 * when the facts appear to be consistent.
	 * 
	 * The model will include boolean assignments for any `queries` that are
	 * known.
	 *
	 * `refuteUsingTheory` is _sound with respect to refutation_; when
	 * `"inconsistent"` is returned, the theory-solver has proven that the
	 * assumptions are definitely inconsistent.
	 */
	refuteUsingTheory(
		assumptions: Assumption<Reason>[],
		queries: ValueID[] = [],
	): UFInconsistency<Reason> | { tag: "model", model: UFCounterexample, answers: Map<ValueID, boolean> } {
		trace.start("initialize");
		this.egraph.reset();

		trace.start("truths");
		for (const assumption of assumptions) {
			const truthObject = assumption.assignment
				? this.trueObject
				: this.falseObject;
			this.egraph.merge(truthObject, assumption.constraint,
				new egraph.ReasonTree([assumption.reason]));
		}
		trace.stop();
		trace.stop("initialize");

		const inconsistencies: Set<Reason>[] = [];

		let progress = true;
		while (progress) {
			progress = false;

			trace.start("getClasses");
			const classes = this.egraph.getClasses(true);
			trace.stop("getClasses");

			// Iterate over all true constraints (those equal to the true
			// object).
			trace.start("true class");
			const trueClass = classes.get(this.trueObject)!;
			for (const trueMember of trueClass.members) {
				const reasonTrue = this.egraph.query(this.trueObject, trueMember.id)!;
				const handled = this.handleTrueMember(trueMember.term, trueMember.operands as ValueID[], reasonTrue);
				if (handled === "change") {
					progress = true;
				} else if (handled !== "no-change") {
					inconsistencies.push(...handled.inconsistencies);
				}
			}
			trace.stop();

			// Iterate over all false constraints (those equal to the false
			// object).
			trace.start("false class");
			const falseClass = classes.get(this.falseObject)!;
			for (const falseMember of falseClass.members) {
				const handled = this.handleFalseMember(falseMember.term, falseMember.operands as ValueID[], falseMember.id as ValueID);
				if (handled === "change") {
					progress = true;
				} else if (handled !== "no-change") {
					inconsistencies.push(...handled.inconsistencies);
				}
			}
			trace.stop();

			trace.start("updateCongruence");
			if (this.egraph.updateCongruence()) {
				progress = true;
			}
			trace.stop();

			trace.start("propagateFnInterpreters");
			if (this.propagateFnInterpreters() === "change") {
				progress = true;
			}
			trace.stop();

			const constantInconsistency = this.findInconsistentConstants()
				|| this.findTransitivityContradictions();
			if (constantInconsistency !== null) {
				inconsistencies.push(constantInconsistency.toSet());
			}

			if (inconsistencies.length !== 0) {
				return { tag: "inconsistent", inconsistencies };
			}
		}

		const answers = new Map<ValueID, boolean>();
		for (const query of queries) {
			if (this.egraph.query(query, this.falseObject) !== null) {
				answers.set(query, false);
			} else if (this.egraph.query(query, this.trueObject) !== null) {
				answers.set(query, true);
			}
		}

		// The UFSolver has failed to show that the given assumptions are
		// inconsistent.
		return {
			tag: "model",
			model: { model: {} },
			answers,
		};
	}

	private handleTrueMember(
		term: FnID | VarID,
		operands: ValueID[],
		reasonTrue: egraph.ReasonTree<Reason>,
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
		member: ValueID,
	): "change" | "no-change" | UFInconsistency<Reason> {
		const semantics = this.fns.get(term as FnID)
		if (semantics !== undefined) {
			if (semantics.eq) {
				const query = this.egraph.query(operands[0], operands[1]);
				if (query !== null) {
					return {
						tag: "inconsistent",
						inconsistencies: [egraph.ReasonTree.withChildren([query, this.egraph.query(this.falseObject, member)!]).toSet()],
					};
				}
			}
		}
		return "no-change";
	}

	/**
	 * `evaluateConstant` returns a constant (as it was passed to
	 * `createConstant`) that is equal to the given value under the current
	 * constraints.
	 */
	evaluateConstant(value: ValueID): { constant: unknown, reason: egraph.ReasonTree<Reason> } | null {
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

	/**
	 * `propagateFnInterpreters()` adds additional constants and equalities by
	 * using the `interpreter` and `generalInterpreter` semantics of functions.
	 */
	private propagateFnInterpreters(): "change" | "no-change" {
		let madeChanges = false;
		while (true) {
			let iterationMadeChanges = false;
			const eclasses = this.egraph.getClasses();
			const matcher = new EMatcher(this, this.egraph, eclasses);
			for (const { members } of eclasses.values()) {
				for (const member of members) {
					const semantics = this.fns.get(member.term as FnID);
					if (semantics !== undefined) {
						const simpleInterpreter = semantics.interpreter;
						if (simpleInterpreter !== undefined) {
							const changeMade = this.propagateSimpleInterpreter(matcher, member, simpleInterpreter);
							if (changeMade === "change") {
								iterationMadeChanges = true;
							}
						}
						const generalInterpreter = semantics.generalInterpreter;
						if (generalInterpreter !== undefined) {
							const changeMade = generalInterpreter(matcher, member.id as ValueID, member.operands as ValueID[]);
							if (changeMade === "change") {
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
		interpreter: (
			matcher: EMatcher<Reason>,
			id: ValueID,
			operands: ValueID[],
		) => "change" | "no-change",
	): "change" | "no-change" {
		return interpreter(matcher, member.id as ValueID, member.operands as ValueID[]);
	}

	private propagateSimpleInterpreter(
		matcher: EMatcher<Reason>,
		member: { id: egraph.EObject, operands: egraph.EObject[] },
		interpreter: (...args: unknown[]) => unknown,
	): "change" | "no-change" {
		return this.propagateGeneralInterpreter(matcher, member, (
			matcher: EMatcher<Reason>,
			id: ValueID,
			operands: ValueID[],
		): "change" | "no-change" => {
			const operandReasons = [];
			const args = [];
			for (const operand of operands) {
				// Search for a constant value among the objects equal to the
				// operand.
				const operandConstant = matcher.evaluateConstant(operand as ValueID);
				if (operandConstant !== null) {
					args.push(operandConstant.constant);
					operandReasons.push(operandConstant.reason);
				} else {
					args.push(null);
				}
			}

			// Call the interpreter with the known constant values.
			const result = interpreter(...args);
			if (result !== null) {
				const resultConstant = matcher.createConstant(result);
				const changed = matcher.merge(resultConstant, id, egraph.ReasonTree.withChildren(operandReasons));
				if (changed) {
					return "change";
				}
			}
			return "no-change";
		});
	}

	private findTransitivityContradictions(): null | egraph.ReasonTree<Reason> {
		// A directed graph for each transitive function.
		const digraphs = new DefaultMap<FnID, DefaultMap<symbol, { reason: egraph.ReasonTree<Reason>, target: symbol }[]>>(f => {
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

				const reason = egraph.ReasonTree.withChildren([
					this.egraph.query(this.trueObject, app.id)!,
					this.egraph.query(source, sourceRep)!,
					this.egraph.query(target, targetRep)!]);
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
					return egraph.ReasonTree.withChildren([
						this.egraph.query(source, sourceRep)!,
						this.egraph.query(target, targetRep)!,
						transitiveChain,
						this.egraph.query(app.id, this.falseObject)!]);
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
	private findInconsistentConstants(): null | egraph.ReasonTree<Reason> {
		for (const [id, _group] of this.egraph.getClasses()) {
			const constants = this.egraph.getTagged("constant", id);
			if (constants.length > 1) {
				// Two distinct constants are in the same equality class.
				return this.egraph.query(constants[0].id, constants[1].id)!;
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

	createVariable(type: ir.Type, debugName: string): ValueID {
		const v = this.solver.createVariable(debugName);
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

	createFunction(
		returnType: ir.Type,
		semantics: Semantics<ReasonSatLiteral>,
		debugName: string,
	): FnID {
		return this.solver.createFn(semantics, debugName);
	}

	private eqFn = this.createFunction(ir.T_BOOLEAN, { eq: true }, "proof==");

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

	override showLiteral(literal: number): string {
		if (literal < 0) {
			return "NOT " + this.showLiteral(-literal);
		}
		const object = this.objectByTerm.get(literal)!;
		const pattern = /^Symbol\(egraph-term    (.+)    \)$/;
		const match = String(object).match(pattern);
		return (match && match[1]) || String(object);
	}

	private printClause(clause: number[], lines: string[]): void {
		for (let i = 0; i < clause.length; i++) {
			lines.push((i === 0 ? "and" : "") + "\tor\t" + this.showLiteral(clause[i]));
		}
	}

	printInstance(lines: string[] = []): string[] {
		for (const clause of this.unscopedClauses) {
			this.printClause(clause, lines);
		}
		for (const clause of this.clauses) {
			this.printClause(clause, lines);
		}
		return lines;
	}

	protected learnAdditional(
		partialAssignment: number[],
		unassigned: number[],
	): number[] | "unsatisfiable" {
		trace.start("learnAdditional");
		const assumptions: Assumption<ReasonSatLiteral>[] = [];
		for (const literal of partialAssignment) {
			const term = literal > 0 ? +literal : -literal;
			const constraint = this.objectByTerm.get(term)!;
			assumptions.push({
				constraint,
				assignment: literal > 0,
				reason: literal,
			});
		}

		const queries: ValueID[] = [];
		for (const literal of unassigned) {
			const term = literal > 0 ? +literal : -literal;
			const constraint = this.objectByTerm.get(term)!;
			queries.push(constraint);
		}
		const result = this.solver.refuteUsingTheory(assumptions, queries);

		if (result.tag === "inconsistent") {
			trace.stop();
			return "unsatisfiable";
		}

		const learnedLiterals: number[] = [];
		for (const [object, assignment] of result.answers) {
			const term = this.termByObject.get(object);
			learnedLiterals.push(assignment ? +term : -term);
		}
		trace.stop();
		return learnedLiterals;
	}

	rejectBooleanModel(literals: number[]): UFCounterexample | number[][] {
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

		trace.start("refuteUsingTheory(" + assumptions.length + " assumptions)");
		const result = this.solver.refuteUsingTheory(assumptions, []);
		trace.stop();
		if (result.tag === "inconsistent") {
			const learnedClauses = [];
			for (const inconsistent of result.inconsistencies) {
				const learnedClause = [];
				for (const element of inconsistent) {
					learnedClause.push(-element);
				}
				learnedClauses.push(learnedClause);
			}
			return learnedClauses;
		}
		return result.model;
	}

	override attemptRefutation(): "refuted" | UFCounterexample {
		// Run the solver.
		const output = super.attemptRefutation();
		return output;
	}
}
