import { DefaultMap, TreeBag, zipMaps } from "./data.js";
import * as egraph from "./egraph.js";
import * as ir from "./ir.js";
import * as smt from "./smt.js";
import * as trace from "./trace.js";

export interface UFCounterexample { model: {} }

type VarID = symbol & { __brand: "uf-var" };
export type FnID = symbol & { __brand: "uf-fn" };

type Value = VarValue | AppValue | ConstantValue;

interface VarValue {
	tag: "var",
	var: VarID,
	type: ir.Type,
}

interface AppValue {
	tag: "app",
	fn: FnID,
	args: ValueID[],
	type: ir.Type,
}

interface ConstantValue {
	tag: "constant",
	constant: unknown,
	type: ir.Type | "unknown",
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
		matcher: UFSolver<Reason>,
		id: ValueID,
		operands: ValueID[],
	) => "change" | "no-change",
}

function transitivitySearch<Node>(
	digraphOutEdges: DefaultMap<Node, { arrowTruth: Equality[], target: Node }[]>,
	source: Node,
	target: Node,
): Equality[] | null {
	const reached = new Map<Node, { parent: Node, arrowTruth: Equality[] }>();
	const frontier = [source];

	while (frontier.length !== 0) {
		const top = frontier.pop()!;
		const outEdges = digraphOutEdges.get(top);
		for (const outEdge of outEdges) {
			if (!reached.has(outEdge.target)) {
				reached.set(outEdge.target, { parent: top, arrowTruth: outEdge.arrowTruth });
				if (outEdge.target === target) {
					// Follow the path backwards to construct the full set of
					// inequalities that were followed.
					const out: Equality[] = [...outEdge.arrowTruth];
					let cursor: Node = top;
					while (cursor !== source) {
						const parent = reached.get(cursor);
						if (parent === undefined) {
							break;
						}
						out.push(...parent.arrowTruth);
						cursor = parent.parent;
					}
					return out;
				}
				frontier.push(outEdge.target);
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

interface Equality {
	left: ValueID,
	right: ValueID,
}

interface InconsistentConstraints<Reason> {
	/**
	 * The conjunction (and) of these constraints is inconsistent.
	 */
	equalityConstraints: Equality[],

	simpleReasons?: Reason[],
}

type UFTags = {
	constant: { valueID: ValueID, constantValue: unknown },
	/**
	 * All the applications of the given fn in this component.
	 */
	indexByFn: Map<FnID, TreeBag<{ id: ValueID, operands: ValueID[] }>>,
};

export class UFSolver<Reason> {
	private values = new Map<ValueID, Value>();
	private fns = new Map<FnID, { returnType: ir.Type, semantics: Semantics<Reason> }>();
	private egraph: egraph.EGraph<VarID | FnID, UFTags, Reason>;

	// Create symbolic constants for the two boolean values.
	trueObject: ValueID;
	falseObject: ValueID;

	constructor() {
		this.egraph = new egraph.EGraph((a, b, s, l, r) => {
			return this.preMerge(a as ValueID, b as ValueID, s, l as ValueID[], r as ValueID[]);
		}, {
			constant(child, parent) {
				return parent;
			},
			indexByFn(child, parent) {
				const out = new Map<FnID, TreeBag<{ id: ValueID, operands: ValueID[] }>>();
				for (const [key, value] of child.entries()) {
					const other = parent.get(key);
					if (other === undefined) {
						out.set(key, value);
					} else {
						out.set(key, value.union(other));
					}
				}
				for (const [key, value] of parent.entries()) {
					if (!child.has(key)) {
						out.set(key, value);
					}
				}
				return out;
			},
		});
		this.trueObject = this.createConstant(true);
		this.falseObject = this.createConstant(false);
	}

	private constants = new DefaultMap<unknown, ValueID>(constant => {
		const varID = Symbol("uf-constant") as VarID;
		const object = this.egraph.add(varID, [], String(constant)) as ValueID;
		this.egraph.addTag(object, "constant", { valueID: object, constantValue: constant });
		const type = typeof constant === "boolean"
			? ir.T_BOOLEAN
			: "unknown";
		this.values.set(object, { tag: "constant", constant, type });
		return object;
	});

	createVariable(type: ir.Type, debugName: string): ValueID {
		const varID = Symbol(debugName || "unknown-var") as VarID;
		const object = this.egraph.add(varID, [], debugName) as ValueID;
		this.values.set(object, { tag: "var", var: varID, type });
		return object;
	}

	createFn(returnType: ir.Type, semantics: Semantics<Reason>, debugName: string): FnID {
		const fnID = Symbol(debugName || "unknown-fn") as FnID;
		if (semantics.transitiveAcyclic && !semantics.transitive) {
			throw new Error("UFSolver.createFn: semantics.transitiveAcyclic requires semantics.transitive");
		}
		this.fns.set(fnID, { returnType, semantics });
		return fnID;
	}

	hasApplication(fn: FnID, args: ValueID[]): ValueID | null {
		return this.egraph.hasStructure(fn, args) as ValueID | null;
	}

	createApplication(fn: FnID, args: ValueID[]): ValueID {
		const definition = this.fns.get(fn);
		if (definition === undefined) {
			throw new Error("UFSolver.createApplication: fn is not defined");
		}
		const object = this.egraph.add(fn, args) as ValueID;
		this.values.set(object, { type: definition.returnType, tag: "app", fn, args });
		this.egraph.addTag(object, "indexByFn", new Map([
			[fn, TreeBag.of({ id: object, operands: args })],
		]));
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

	getFnReturnType(fnID: FnID): ir.Type {
		const definition = this.fns.get(fnID);
		if (definition === undefined) {
			throw new Error("UFSolver.getFnReturnType: no such fn");
		}
		return definition.returnType;
	}

	getFnSemantics(fnID: FnID): Semantics<Reason> {
		const definition = this.fns.get(fnID);
		if (definition === undefined) {
			throw new Error("UFSolver.getFnSemantics: no such fn");
		}
		return definition.semantics;
	}

	getType(value: ValueID): ir.Type | "unknown" {
		const definition = this.getDefinition(value);
		return definition.type;
	}

	areCongruent(a: ValueID, b: ValueID): boolean {
		return this.egraph.areCongruent(a, b);
	}

	mergeBecauseCongruent(
		a: ValueID,
		b: ValueID,
		lefts: ValueID[],
		rights: ValueID[],
	): boolean {
		return this.egraph.mergeApplications(a, b, null, lefts, rights);
	}

	matchAsApplication(value: ValueID, fn: FnID): TreeBag<{
		id: ValueID,
		operands: ValueID[],
	}> {
		const tag = this.egraph.getTagged("indexByFn", value)?.get(fn);
		if (tag === undefined) {
			return TreeBag.of();
		}
		return tag;
	}

	private pendingInconsistencies: InconsistentConstraints<Reason>[] = [];

	private preMerge(
		a: ValueID,
		b: ValueID,
		simpleReason: Reason | null,
		lefts: ValueID[],
		rights: ValueID[]
	): null | "cancel" {
		const constantsA = this.egraph.getTagged("constant", a);
		if (constantsA === null) {
			return null;
		}
		const constantsB = this.egraph.getTagged("constant", b);
		if (constantsB === null) {
			return null;
		}

		// Two distinct constants would be congruent after this merge.
		// However, because we are canceling the merge, we have to record
		// the reasons for this merge rather than the pair (left == right).
		this.pendingInconsistencies.push({
			equalityConstraints: [
				...lefts.map((left, i) => {
					return { left, right: rights[i] };
				}),
				{ left: constantsA.valueID, right: a },
				{ left: constantsB.valueID, right: b },
			],
			simpleReasons: simpleReason === null ? [] : [simpleReason],
		});

		// Avoid merging these to reduce explosion of false facts.
		return "cancel";
	}

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
		this.pendingInconsistencies.length = 0;

		trace.start("truths");
		for (const assumption of assumptions) {
			const truthObject = assumption.assignment
				? this.trueObject
				: this.falseObject;
			this.egraph.mergeApplications(truthObject, assumption.constraint, assumption.reason, [], []);
		}
		trace.stop();
		trace.stop("initialize");

		let progress = true;
		while (progress) {
			trace.start("iteration");
			progress = false;

			// Iterate over all true constraints (those equal to the true
			// object).
			trace.start("handleTrueMembers");
			progress = this.handleTrueMembers() || progress;
			trace.stop();

			// Iterate over all false constraints (those equal to the false
			// object).
			trace.start("handleFalseMembers");
			progress = this.handleFalseMembers() || progress;
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

			trace.start("findTransitivityContradictions");
			this.findTransitivityContradictions();
			trace.stop();

			trace.stop();

			if (this.pendingInconsistencies.length !== 0) {
				trace.start("diagnoseInconsistencies");
				const inconsistencies = this.pendingInconsistencies
					.map(x => this.diagnoseInconsistency(x));
				trace.stop("diagnoseInconsistencies");
				return {
					tag: "inconsistent",
					inconsistencies
				};
			}
		}

		trace.start("queries");
		const answers = new Map<ValueID, boolean>();
		for (const query of queries) {
			if (this.egraph.areCongruent(query, this.falseObject)) {
				answers.set(query, false);
			} else if (this.egraph.areCongruent(query, this.trueObject)) {
				answers.set(query, true);
			}
		}
		trace.stop("queries");

		// The UFSolver has failed to show that the given assumptions are
		// inconsistent.
		return {
			tag: "model",
			model: { model: {} },
			answers,
		};
	}

	/**
	 * Convert the set of theory constraints to a conjunction of `Reason`s which
	 * are inconsistent in this theory.
	 */
	private diagnoseInconsistency(inconsistency: InconsistentConstraints<Reason>): Set<Reason> {
		trace.mark([
			"diagnoseInconsistency",
			inconsistency.equalityConstraints.length,
			"eqs",
			inconsistency.simpleReasons,
		], () => {
			const lines: string[] = [];
			const stringified = JSON.stringify(inconsistency, (_, value) => {
				if (typeof value === "symbol") {
					return String(value);
				} else if (typeof value === "bigint") {
					return String(value);
				}
				return value;
			}, "\t");
			lines.push(stringified);
			return lines.join("\n");
		});
		const conjunction = new Set<Reason>();
		const subConjunctions: Set<Reason>[] = [];
		for (const equality of inconsistency.equalityConstraints) {
			const subConjunction = this.egraph.explainCongruence(equality.left, equality.right);
			subConjunctions.push(subConjunction);
			for (const r of subConjunction) {
				conjunction.add(r);
			}
		}
		if (inconsistency.simpleReasons && inconsistency.simpleReasons.length !== 0) {
			for (const simpleReason of inconsistency.simpleReasons) {
				conjunction.add(simpleReason);
			}
		}
		return conjunction;
	}

	private handleTrueMembers(): boolean {
		let progress = false;
		const trueApplications = this.egraph.getTagged("indexByFn", this.trueObject);
		if (trueApplications !== null) {
			for (const [fn, applications] of trueApplications) {
				trace.start([String(fn), "has", applications.size, "applications"]);
				const fnDefinition = this.fns.get(fn)!;
				if (fnDefinition.semantics.eq === true) {
					for (const application of applications) {
						const changeMade = this.egraph.mergeApplications(
							application.operands[0],
							application.operands[1],
							null,
							[application.id],
							[this.trueObject],
						);
						progress = progress || changeMade;
					}
				}
				trace.stop();
			}
		}
		return progress;
	}

	private handleFalseMembers(): boolean {
		const falseClass = this.egraph.getTagged("indexByFn", this.falseObject);
		if (falseClass === null) {
			return false;
		}

		let progress = false;
		const disequalities = [];
		for (const [fn, applications] of falseClass) {
			const fnDefinition = this.fns.get(fn)!;
			if (fnDefinition.semantics.eq === true) {
				for (const application of applications) {
					const left = application.operands[0] as ValueID;
					const right = application.operands[1] as ValueID;
					const disequality = { equality: application.id as ValueID, left, right };
					disequalities.push(disequality);
					progress = this.checkDisequality(disequality) || progress;
				}
			}
		}

		// Categorize boolean expressions as disequal to `true` and `false`.
		const notTrueReasons = new Map<ValueID, { equality: ValueID, pair: ValueID, pairConstant: ValueID }>();
		const notFalseReasons = new Map<ValueID, { equality: ValueID, pair: ValueID, pairConstant: ValueID }>();
		for (const disequality of disequalities) {
			const leftType = this.getType(disequality.left);
			const rightType = this.getType(disequality.right);
			if (leftType === "unknown" || !ir.equalTypes(leftType, ir.T_BOOLEAN)) {
				continue;
			} else if (rightType === "unknown" || !ir.equalTypes(rightType, ir.T_BOOLEAN)) {
				continue;
			}
			const leftConstant = this.evaluateConstant(disequality.left);
			if (leftConstant !== null && typeof leftConstant.constant === "boolean") {
				const target = leftConstant.constant
					? notTrueReasons
					: notFalseReasons;
				target.set(disequality.right, {
					equality: disequality.equality,
					pair: disequality.left,
					pairConstant: leftConstant.constantID,
				});
			}

			const rightConstant = this.evaluateConstant(disequality.right);
			if (rightConstant !== null && typeof rightConstant.constant === "boolean") {
				const target = rightConstant.constant
					? notTrueReasons
					: notFalseReasons;
				target.set(disequality.left, {
					equality: disequality.equality,
					pair: disequality.right,
					pairConstant: rightConstant.constantID,
				});
			}
		}

		// Complain if any boolean-typed expressions are disequal to both `true`
		// and `false`.
		for (const key of notTrueReasons.keys()) {
			const notFalseReason = notFalseReasons.get(key);
			if (notFalseReason === undefined) {
				continue;
			}
			const notTrueReason = notTrueReasons.get(key)!;

			this.pendingInconsistencies.push({
				equalityConstraints: [
					{ left: notFalseReason.equality, right: this.falseObject },
					{ left: notFalseReason.pair, right: notFalseReason.pairConstant },
					{ left: notTrueReason.equality, right: this.falseObject },
					{ left: notTrueReason.pair, right: notTrueReason.pairConstant },
				],
			});
			progress = true;
		}

		return progress;
	}

	private checkDisequality({ equality, left, right }: { equality: ValueID, left: ValueID, right: ValueID }): boolean {
		if (this.egraph.areCongruent(left, right)) {
			this.pendingInconsistencies.push({
				equalityConstraints: [
					{ left, right },
					{ left: this.falseObject, right: equality },
				],
			});
			return true;
		}
		return false;
	}

	/**
	 * `evaluateConstant` returns a constant (as it was passed to
	 * `createConstant`) that is equal to the given value under the current
	 * constraints.
	 */
	evaluateConstant(value: ValueID): { constant: unknown, constantID: ValueID } | null {
		const constants = this.egraph.getTagged("constant", value);
		if (constants === null) {
			return null;
		}
		const id = constants.valueID;
		const valueDefinition = this.values.get(id);
		if (valueDefinition?.tag !== "constant") {
			throw new Error("UFSolver.evaluateConstant: non-literal tagged");
		}
		return {
			constant: valueDefinition.constant,
			constantID: id,
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
			for (const [fn, { semantics }] of this.fns) {
				const simpleInterpreter = semantics.interpreter;
				const generalInterpreter = semantics.generalInterpreter;
				if (simpleInterpreter !== undefined || generalInterpreter !== undefined) {
					const applications = this.egraph.getAllApplications(fn) as
						{ id: ValueID, operands: ValueID[] }[];
					for (const application of applications) {
						if (simpleInterpreter !== undefined) {
							const changeMade = this.propagateSimpleInterpreter(application, simpleInterpreter);
							if (changeMade === "change") {
								iterationMadeChanges = true;
							}
						}
						if (generalInterpreter !== undefined) {
							const changeMade = generalInterpreter(this, application.id, application.operands);
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
		member: { id: egraph.EObject, operands: egraph.EObject[] },
		interpreter: (
			matcher: UFSolver<Reason>,
			id: ValueID,
			operands: ValueID[],
		) => "change" | "no-change",
	): "change" | "no-change" {
		return interpreter(this, member.id as ValueID, member.operands as ValueID[]);
	}

	private propagateSimpleInterpreter(
		member: { id: egraph.EObject, operands: egraph.EObject[] },
		interpreter: (...args: unknown[]) => unknown,
	): "change" | "no-change" {
		return this.propagateGeneralInterpreter(member, (
			matcher: UFSolver<Reason>,
			id: ValueID,
			operands: ValueID[],
		): "change" | "no-change" => {
			const operandsWithConstant = [];
			const constants = [];
			const args = [];
			for (const operand of operands) {
				// Search for a constant value among the objects equal to the
				// operand.
				const operandConstant = matcher.evaluateConstant(operand as ValueID);
				if (operandConstant !== null) {
					args.push(operandConstant.constant);
					operandsWithConstant.push(operand);
					constants.push(operandConstant.constantID);
				} else {
					args.push(null);
				}
			}

			// Call the interpreter with the known constant values.
			const result = interpreter(...args);
			if (result !== null) {
				const resultConstant = matcher.createConstant(result);
				const changed = matcher.mergeBecauseCongruent(resultConstant, id, operandsWithConstant, constants);
				if (changed) {
					return "change";
				}
			}
			return "no-change";
		});
	}

	private handleTransitiveApplications(
		fnDefinition: Semantics<Reason>,
		trueApplications: { id: ValueID, operands: [ValueID, ValueID] }[],
		falseApplications: { id: ValueID, operands: [ValueID, ValueID] }[],
	): void {
		// For each transitive function, build a directed graph for each
		// application in the "true" equality class.
		trace.start("build digraph");
		const digraph = new DefaultMap<ValueID, { arrowTruth: Equality[], target: ValueID }[]>(k => []);
		for (const trueApplication of trueApplications) {
			const source = trueApplication.operands[0];
			const target = trueApplication.operands[1];
			const sourceRep = this.egraph.getRepresentative(source) as ValueID;
			const targetRep = this.egraph.getRepresentative(target) as ValueID;
			digraph.get(sourceRep).push({
				arrowTruth: [
					{ left: this.trueObject, right: trueApplication.id },
					{ left: source, right: sourceRep },
					{ left: target, right: targetRep },
				],
				target: targetRep,
			});
		}
		trace.stop("build digraph");

		trace.start("search for negative paths in digraph");
		for (const falseApplication of falseApplications) {
			const source = falseApplication.operands[0];
			const target = falseApplication.operands[1];
			const sourceRep = this.egraph.getRepresentative(source) as ValueID;
			const targetRep = this.egraph.getRepresentative(target) as ValueID;

			// Naively performs a DFS on the set of `<` edges, searching for
			// a contradiction.
			const transitiveChain = transitivitySearch(digraph, sourceRep, targetRep);
			if (transitiveChain !== null) {
				this.pendingInconsistencies.push({
					equalityConstraints: [
						{ left: source, right: sourceRep },
						{ left: target, right: targetRep },
						{ left: falseApplication.id as ValueID, right: this.falseObject },
						...transitiveChain,
					],
				});
			}
		}
		trace.stop();

		if (fnDefinition.transitiveAcyclic === true) {
			trace.start("transitiveAcyclic");
			for (const [source, _] of digraph) {
				const transitiveChain = transitivitySearch(digraph, source, source);
				if (transitiveChain !== null) {
					this.pendingInconsistencies.push({
						equalityConstraints: transitiveChain,
					});
				}
			}
			trace.stop();
		}
	}

	private findTransitivityContradictions(): void {
		// Retrieve the true/false constraints for each transtive function.
		const trueClass = this.egraph.getTagged("indexByFn", this.trueObject);
		const falseClass = this.egraph.getTagged("indexByFn", this.falseObject);
		const empty = new Map<FnID, TreeBag<{ id: ValueID, operands: ValueID[] }>>();
		const zipped = zipMaps(trueClass || empty, falseClass || empty);
		for (const [fn, trueApplicationsBag, falseApplicationsBag] of zipped) {
			const fnDefinition = this.fns.get(fn)!.semantics;
			if (fnDefinition.transitive === true) {
				const trueApplications = trueApplicationsBag ? [...trueApplicationsBag] : [];
				const falseApplications = falseApplicationsBag ? [...falseApplicationsBag] : [];
				this.handleTransitiveApplications(fnDefinition,
					trueApplications as { id: ValueID, operands: [ValueID, ValueID] }[],
					falseApplications as { id: ValueID, operands: [ValueID, ValueID] }[]);
			}
		}
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


	createVariable(type: ir.Type, debugName: string): ValueID {
		const v = this.solver.createVariable(type, debugName);
		if (ir.equalTypes(ir.T_BOOLEAN, type)) {
			// Boolean-typed variables must be equal to either true or false.
			// This constraint ensures that the sat solver will commit the
			// variable to a particular assignment.
			this.addUnscopedConstraint([
				v,
				this.createApplication(this.notFn, [v]),
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
		if (semantics.not) {
			return this.notFn;
		}
		return this.solver.createFn(returnType, semantics, debugName);
	}

	notFn = this.solver.createFn(ir.T_BOOLEAN, {
		not: true,
		interpreter(a: unknown) {
			if (typeof a === "boolean") {
				return !a;
			}
			return null;
		},
	}, "not");

	createApplication(fnID: FnID, args: ValueID[]): ValueID {
		// Apply simplifications
		const semantics = this.solver.getFnSemantics(fnID);
		if (semantics.eq === true) {
			const left = args[0];
			const right = args[1];
			if (left === this.solver.trueObject) {
				return right;
			} else if (left === this.solver.falseObject) {
				return this.createApplication(this.notFn, [right]);
			} else if (right === this.solver.trueObject) {
				return left;
			} else if (right === this.solver.falseObject) {
				return this.createApplication(this.notFn, [left]);
			}
		}
		return this.solver.createApplication(fnID, args);
	}

	private toSatLiteralMap = new Map<ValueID, number>();

	// The Boolean-typed object associated with the given SAT term.
	private objectByTerm = new Map<number, ValueID>();

	private toSatLiteral(valueID: ValueID, additionalClauses: number[][]): number {
		const existing = this.toSatLiteralMap.get(valueID);
		if (existing !== undefined) {
			return existing;
		}

		const vend = (positiveValue: ValueID): number => {
			const term = this.toSatLiteralMap.size + 1;
			this.toSatLiteralMap.set(positiveValue, term);
			this.objectByTerm.set(term, positiveValue);
			return term;
		};

		const out = this.toSatLiteralInternal(valueID, vend, additionalClauses);
		if (!this.objectByTerm.has(Math.abs(out))) {
			throw new Error("UFTheory.toSatLiteral: toSatLiteralInternal returned a literal for an undefined term");
		}
		this.toSatLiteralMap.set(valueID, out);
		return out;
	}

	/**
	 * @returns a SAT term assocaited with a Boolean-typed object tracked by the
	 * solver.
	 */
	private toSatLiteralInternal(
		valueID: ValueID,
		vendTerm: (positiveValue: ValueID) => number,
		additionalClauses: number[][],
	): number {
		const definition = this.solver.getDefinition(valueID);
		if (definition.tag === "app") {
			const semantics = this.solver.getFnSemantics(definition.fn);
			if (semantics.not === true) {
				return -this.toSatLiteral(definition.args[0], additionalClauses);
			} else if (semantics.eq === true) {
				const [leftID, rightID] = definition.args;
				const left = this.solver.getDefinition(leftID);
				const right = this.solver.getDefinition(rightID);
				if (left.type !== "unknown" && right.type !== "unknown") {
					if (ir.equalTypes(ir.T_BOOLEAN, left.type) && ir.equalTypes(ir.T_BOOLEAN, right.type)) {
						// E == (A == B)
						// (~A | ~B | E) & (~A | B | ~E) & (A | ~B | ~C) & (A | B | C)
						const leftLiteral = this.toSatLiteral(leftID, additionalClauses);
						const rightLiteral = this.toSatLiteral(rightID, additionalClauses);

						// Create a new variable
						const equalityLiteral = vendTerm(valueID);

						// Add clauses to explain the truth table to the SAT solver.
						additionalClauses.push(
							[leftLiteral, rightLiteral, equalityLiteral],
							[-leftLiteral, -rightLiteral, equalityLiteral],
							[-leftLiteral, rightLiteral, -equalityLiteral],
							[leftLiteral, -rightLiteral, -equalityLiteral],
						);
						return equalityLiteral;
					}
				}
			}
		}

		// Define a new term
		return vendTerm(valueID);
	}

	clausify(disjunction: ValueID[]): number[][] {
		const clauses: number[][] = [];
		const clause = [];
		for (const value of disjunction) {
			clause.push(this.toSatLiteral(value, clauses));
		}
		clauses.push(clause);

		return clauses;
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
	): number[][] | "unsatisfiable" {
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

		const learnedClauses: number[][] = [];
		for (const [object, assignment] of result.answers) {
			const term = this.toSatLiteral(object, learnedClauses);
			learnedClauses.push([assignment ? +term : -term]);
		}
		trace.stop();
		return learnedClauses;
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

		trace.start("refuteUsingTheory");
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

	generateTestCode(): string {
		const defs: string[] = [
			"const smt = new uf.UFTheory();",
		];
		const showType = (t: ir.Type) => {
			if (ir.equalTypes(ir.T_BOOLEAN, t)) {
				return "ir.T_BOOLEAN";
			} else if (ir.equalTypes(ir.T_BYTES, t)) {
				return "ir.T_BYTES";
			} else if (ir.equalTypes(ir.T_INT, t)) {
				return "ir.T_INT";
			} else if (ir.equalTypes(ir.T_UNIT, t)) {
				return "ir.T_UNIT";
			}
			return JSON.stringify(t);
		};
		const fs = new DefaultMap<FnID, string>(value => {
			const def = this.solver.getFnSemantics(value);
			const name = "f" + String(value).replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length;
			const returnType = showType(this.solver.getFnReturnType(value));
			const semantics = JSON.stringify(def, (_, value) => {
				if (typeof value !== "function") {
					return value;
				}
				return value.toString().replace(/\s+/g, " ");
			}, "\t");
			const hint = JSON.stringify(String(value));
			defs.push(`const ${name} = smt.createFunction(${returnType}, ${semantics}, ${hint});`);
			return name;
		});
		const exprs = new DefaultMap<ValueID, string>(value => {
			const def = this.solver.getDefinition(value);
			if (def.tag === "var") {
				const name = "v" + String(value).replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length;
				const type = showType(def.type);
				const hint = JSON.stringify(String(value));
				defs.push(`const ${name} = smt.createVariable(${type}, ${hint});`);
				return name;
			} else if (def.tag === "app") {
				const f = fs.get(def.fn);
				const name = "f" + String(def.fn).replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length;
				const args = def.args.map(x => exprs.get(x));
				defs.push(`const ${name} = smt.createApplication(${f}, [${args.join(", ")}]);`);
				return name;
			} else if (def.tag === "constant") {
				const name = "c" + String(def.constant).replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length;
				const value = (typeof def.constant === "bigint")
					? "BigInt(" + JSON.stringify(def.constant.toString()) + ")"
					: JSON.stringify(def.constant);
				defs.push(`const ${name} = smt.createConstant(ir.T_INT, ${value});`);
				return name;
			}
			const _: never = def;
			throw new Error("unreachable");
		});

		const showLiteral = (literal: number) => {
			const term = Math.abs(literal);
			const value = this.objectByTerm.get(term)!;
			const showValue = exprs.get(value);
			return literal < 0
				? "smt.createApplication(smt.notFn, [" + showValue + "])"
				: showValue;
		};

		const out = [];

		// Scoped constraints
		out.push("// Scoped constraints");
		out.push("");
		for (const clause of this.clauses) {
			out.push(`smt.addConstraint([`);
			for (const literal of clause) {
				out.push("\t" + showLiteral(literal) + ",");
			}
			out.push(`]);`);
		}

		// Unscoped constraints
		out.push("// Unscoped constraints");
		out.push("");
		for (const clause of this.unscopedClauses) {
			out.push(`smt.addUnscopedConstraint([`);
			for (const literal of clause) {
				out.push("\t" + showLiteral(literal) + ",");
			}
			out.push(`]);`);
		}

		return [
			...defs,
			"",
			...out,
			"",
			"const response = smt.attemptRefutation();",
		].join("\n");
	}

	override attemptRefutation(): "refuted" | UFCounterexample {
		// Run the solver.
		trace.mark("test case source", () => {
			return this.generateTestCode();
		});
		const output = super.attemptRefutation();
		return output;
	}
}
