import { Components } from "./components.js";
import {
	BitSet,
	bitsetEmpty,
	bitsetIntersect,
	bitsetLeastSignificantBit,
	bitsetMinus,
	bitsetSingleton,
	bitsetUnion,
	DefaultMap,
	nonEmptyPath,
	sortedBy,
	TreeBag,
	TrieMap,
	zipMaps,
} from "./data.js";
import * as egraph from "./egraph.js";
import * as ir from "./ir.js";
import * as smt from "./smt.js";
import * as trace from "./trace.js";

export interface UFCounterexample { model: {} }

type VarID = symbol & { __brand: "uf-var" };
export type FnID = symbol & { __brand: "uf-fn" };

interface VarValue {
	tag: "var",
	var: VarID,
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


type ValueToken = {
	tag: "var",
	var: VarID,
} | {
	tag: "constant",
	constant: unknown,
} | {
	tag: "application",
	fn: FnID,
	operands: ValueToken[],
};

type MiniComponentData = {
	simplestComplexity: number,
	simplestDefinition: ValueToken,

	/**
	 * A bitset indexing into the `disequalityList` array, indicating
	 * that this component is targeted by one of the operands of the
	 * disequality.
	 */
	disequalityBitSet: BitSet,

	constant: { token: ValueToken, constant: unknown } | null,
};

type SimplifiedValue = {
	result: ValueToken,
	assumptions: { left: ValueToken, right: ValueToken }[],
};

class FastSolver<Reason> {
	constructor(private originalSolver: UFSolver<Reason>) { }

	private getDefinition(valueID: ValueID): {
		tag: "application",
		fn: FnID,
		operands: ValueID[],
	} | {
		tag: "atom",
		extra: ConstantValue | VarValue,
	} {
		return this.originalSolver.getDefinition(valueID);
	}

	private getFnSemantics(fnID: FnID): Semantics<Reason> {
		return this.originalSolver.getFnSemantics(fnID);
	}

	private constantCache = new DefaultMap<unknown, ValueToken>(constant => {
		return {
			tag: "constant",
			constant,
		};
	});

	private findConstantToken(constantValue: unknown): ValueToken {
		return this.constantCache.get(constantValue)
	}

	private varCache = new DefaultMap<VarID, ValueToken>(v => ({ tag: "var", var: v, id: Math.random() }));

	private findVarToken(varName: VarID): ValueToken {
		return this.varCache.get(varName);
	}

	private applicationCache = new TrieMap<[FnID, ...ValueToken[]], ValueToken>();

	private findApplicationToken(fn: FnID, ...operands: ValueToken[]): ValueToken {
		const key: [FnID, ...ValueToken[]] = [fn, ...operands];
		let existing = this.applicationCache.get(key);
		if (existing === undefined) {
			existing = {
				tag: "application",
				fn,
				operands,
			};
			this.applicationCache.put(key, existing);
		}

		return existing;
	}

	private cs = new Components<ValueToken, Reason, MiniComponentData>(
		(a: ValueToken) => {
			let simplestComplexity = 2;
			if (a.tag === "constant") {
				return {
					simplestComplexity: 0,
					simplestDefinition: a,
					disequalityBitSet: bitsetEmpty,
					constant: { token: a, constant: a.constant },
				};
			} else if (a.tag === "var") {
				return {
					simplestComplexity: 1,
					simplestDefinition: a,
					disequalityBitSet: bitsetEmpty,
					constant: null,
				};
			}
			return {
				simplestComplexity,
				simplestDefinition: a,
				disequalityBitSet: bitsetEmpty,
				constant: null,
			};
		},
		(a: MiniComponentData, b: MiniComponentData) => {
			return {
				simplestComplexity: Math.min(a.simplestComplexity, b.simplestComplexity),
				simplestDefinition: a.simplestComplexity < b.simplestComplexity
					? a.simplestDefinition
					: b.simplestDefinition,
				disequalityBitSet: bitsetUnion(a.disequalityBitSet, b.disequalityBitSet),
				constant: a.constant || b.constant,
			};
		}
	);

	findPaths(
		pairs: { left: ValueToken, right: ValueToken }[],
		...additional: Reason[]
	): Reason[] {
		const out = [...additional];
		for (const pair of pairs) {
			const path = this.cs.findPath(pair.left, pair.right)!;
			out.push(...path);
		}
		return out;
	};

	simplifyValueInternal(value: ValueID): SimplifiedValue {
		const definition = this.getDefinition(value);
		if (definition.tag === "atom") {
			if (definition.extra.tag === "constant") {
				const valueToken = this.findConstantToken(definition.extra.constant);
				return {
					result: valueToken,
					assumptions: [],
				};
			} else {
				return {
					result: this.findVarToken(definition.extra.var),
					assumptions: [],
				};
			}
		}

		const assumptions = [];
		const simplifiedOperands: ValueToken[] = [];
		for (const operand of definition.operands) {
			const simplifiedOperand = this.simplifyValue(operand);
			assumptions.push(...simplifiedOperand.assumptions);
			simplifiedOperands.push(simplifiedOperand.result);
		}

		const applicationToken = this.findApplicationToken(definition.fn, ...simplifiedOperands);
		const applicationResult = {
			result: applicationToken,
			assumptions,
		};

		const semantics = this.getFnSemantics(definition.fn);
		if (semantics.interpreter) {
			const constantOperands = [];
			const constantReasons = [];
			for (let i = 0; i < simplifiedOperands.length; i++) {
				const data = this.cs.getData(simplifiedOperands[i]);
				if (data.constant === null) {
					constantOperands.push(null);
				} else {
					constantOperands.push(data.constant.constant);
					constantReasons.push({ left: data?.constant.token, right: simplifiedOperands[i] });
				}
			}

			const interpreterResult = semantics.interpreter(...constantOperands);
			if (interpreterResult !== null) {
				const constantToken = this.findConstantToken(interpreterResult);
				this.addCongruence(
					applicationResult,
					{ result: constantToken, assumptions: constantReasons },
					null
				);
			}
		}

		return applicationResult;
	}


	private originalSimplifications = new Map<ValueID, ValueToken>();

	simplifyValue(value: ValueID) {
		const before = this.originalSimplifications.get(value);
		const simplified = this.simplifyValueInternal(value);
		if (before !== undefined) {
			// This ensures that congruence deductions that were made during
			// simplification are reflected in the Components data
			// structure.
			this.cs.addCongruence(before, simplified.result, null, simplified.assumptions);
		} else {
			// TODO: Justify why we don't need to save the assumptions here.
			this.originalSimplifications.set(value, simplified.result);
		}

		const related = this.cs.getData(simplified.result);
		const simplestDefinition = related.simplestDefinition;
		return {
			result: simplestDefinition,
			assumptions: simplified.result === simplestDefinition
				? simplified.assumptions
				: [...simplified.assumptions, { left: simplified.result, right: simplestDefinition }],
		};
	};

	private inconsistencies: Set<Reason>[] = [];

	private recordInconsistency(set: Set<Reason>): void {
		if (set.size === 0) {
			throw new Error("unexpected empty inconsistency set");
		}
		this.inconsistencies.push(set);
	}

	private disequalityList: {
		left: SimplifiedValue,
		right: SimplifiedValue,
		reason: Reason,
	}[] = [];

	private disequalityListAlreadyHandled: BitSet = bitsetEmpty;

	private addCongruence(
		leftValue: SimplifiedValue,
		rightValue: SimplifiedValue,
		reasonForCongruence: Reason | null,
	): void {
		const emitProblemInconsistentWithEquality = (
			reasons: Reason[],
		): void => {
			const inconsistency = this.findPaths([
				...leftValue.assumptions,
				...rightValue.assumptions,
			], ...(reasonForCongruence === null ? [] : [reasonForCongruence]), ...reasons);
			this.recordInconsistency(new Set(inconsistency));
		};

		const leftData = this.cs.getData(leftValue.result);
		const rightData = this.cs.getData(rightValue.result);
		if (leftData === rightData) {
			// The components are already congruent.
			return;
		}

		let hasConflictingConstants = false;
		if (leftData.constant !== null && rightData.constant !== null) {
			// The components are not congruent, but are both congruent to
			// constants, which are necessarily distinct.
			trace.start("cannot merge components because both have constants");
			emitProblemInconsistentWithEquality(
				this.findPaths([
					{ left: leftData.constant?.token, right: leftValue.result },
					{ left: rightData.constant?.token, right: rightValue.result },
				]),
			);
			trace.stop();
			hasConflictingConstants = true;
		}

		const disequalities = bitsetMinus(
			bitsetIntersect(leftData.disequalityBitSet, rightData.disequalityBitSet),
			this.disequalityListAlreadyHandled
		);
		if (!hasConflictingConstants && disequalities !== bitsetEmpty) {
			const disequalityIndex = bitsetLeastSignificantBit(disequalities);
			const disequality = this.disequalityList[disequalityIndex];
			this.disequalityListAlreadyHandled = bitsetUnion(this.disequalityListAlreadyHandled, bitsetSingleton(disequalityIndex));

			const distinctA = disequality.left;
			const distinctB = disequality.right;

			let distinctLeft: SimplifiedValue;
			let distinctRight: SimplifiedValue;
			if (this.cs.areCongruent(distinctA.result, leftValue.result)) {
				distinctLeft = distinctA;
				distinctRight = distinctB;
			} else if (this.cs.areCongruent(distinctA.result, rightValue.result)) {
				distinctLeft = distinctB;
				distinctRight = distinctA;
			} else {
				throw new Error(
					"findProblemsWithEquality: expected at least one of leftValue/rightValue to be congruent to distinctA"
				);
			}

			trace.start(["cannot merge components because of a disequality between", disequality.left, "and", disequality.right]);
			emitProblemInconsistentWithEquality(
				this.findPaths([
					...distinctLeft.assumptions,
					...distinctRight.assumptions,
					{ left: distinctLeft.result, right: leftValue.result },
					{ left: distinctRight.result, right: rightValue.result },
				], disequality.reason)
			);
			trace.stop();
		}

		this.cs.addCongruence(leftValue.result, rightValue.result, reasonForCongruence, [
			...leftValue.assumptions,
			...rightValue.assumptions,
		]);
	}

	private addDisequality(
		leftValue: SimplifiedValue,
		rightValue: SimplifiedValue,
		disequality: {
			left: ValueID,
			right: ValueID,
			assumption: Assumption<Reason>,
			definition: {
				tag: "application";
				fn: FnID;
				operands: ValueID[];
			},
		},
	): void {
		if (this.cs.areCongruent(leftValue.result, rightValue.result)) {
			trace.start(["explain disequality inconsistency", leftValue.result, rightValue.result]);
			const inconsistency = this.findPaths([
				...leftValue.assumptions,
				...rightValue.assumptions,
				{ left: leftValue.result, right: rightValue.result },
			], disequality.assumption.reason);
			trace.mark(["found", inconsistency.length, "reason clause"]);
			trace.stop();
			this.recordInconsistency(new Set(inconsistency));
		}

		const disequalityBit = bitsetSingleton(this.disequalityList.length);
		this.disequalityList.push({
			left: this.simplifyValue(disequality.left),
			right: this.simplifyValue(disequality.right),
			reason: disequality.assumption.reason,
		});
		const bitData: MiniComponentData = {
			simplestComplexity: Infinity,
			simplestDefinition: this.cs.getData(leftValue.result).simplestDefinition,
			disequalityBitSet: disequalityBit,
			constant: null,
		};

		this.cs.mergeData(leftValue.result, bitData);
		this.cs.mergeData(rightValue.result, bitData);
	}

	fastRefuteUsingTheory(
		assumptions: Assumption<Reason>[],
		queries: ValueID[] = [],
		queriesNeedReasons: boolean = true,
	): UFInconsistency<Reason> | {
		tag: "model",
		model: UFCounterexample,
		answers: Map<ValueID, { assignment: boolean, reason: Set<Reason> }>
	} {
		const atoms = [];
		let equalities: {
			left: ValueID,
			right: ValueID,
			assumption: Assumption<Reason>,
			definition: {
				tag: "application";
				fn: FnID;
				operands: ValueID[];
			},
		}[] = [];
		const uninterpretedRelations = [];

		trace.start("classify predicates");
		for (const assumption of assumptions) {
			const definition = this.getDefinition(assumption.constraint);
			if (definition.tag === "application") {
				const semantics = this.getFnSemantics(definition.fn);
				if (semantics.eq) {
					equalities.push({
						assumption,
						definition,
						left: definition.operands[0],
						right: definition.operands[1],
					});
				} else {
					uninterpretedRelations.push({
						assumption,
						definition,
					});
				}
			} else if (definition.tag === "atom") {
				atoms.push({
					assumption,
					definition,
				});
			}
		}
		trace.stop();

		trace.start("sort equalities");
		equalities = sortedBy(equalities, e => {
			const ofLeft = this.cs.getData(this.simplifyValue(e.left).result).simplestComplexity;
			const ofRight = this.cs.getData(this.simplifyValue(e.right).result).simplestComplexity;
			return [Math.min(ofLeft, ofRight), Math.max(ofLeft, ofRight)];
		});
		trace.stop();

		// Attempt to simplify each expression as much as possible, so that a
		// single pass learns as much information as possible.
		trace.start(["iterate", equalities.length, "equalities"]);
		for (const equality of equalities) {
			trace.start(["equality", equality.left, equality.assumption.assignment ? "==" : "!=", equality.right]);
			const leftValue = this.simplifyValue(equality.left);
			const rightValue = this.simplifyValue(equality.right);

			if (equality.assumption.assignment) {
				this.addCongruence(leftValue, rightValue, equality.assumption.reason);
			} else {
				this.addDisequality(leftValue, rightValue, equality);
			}
			trace.stopThreshold(0.005);
		}
		trace.stop();

		if (this.inconsistencies.length !== 0) {
			return {
				tag: "inconsistent",
				inconsistencies: this.inconsistencies,
			};
		}

		return {
			tag: "model",
			model: { model: {} },
			answers: new Map(),
		};
	}
}

export class UFSolver<Reason> {
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
		const type = typeof constant === "boolean"
			? ir.T_BOOLEAN
			: "unknown";
		const object = this.egraph.add(varID, [], String(constant), { tag: "constant", constant, type }) as ValueID;
		this.egraph.addTag(object, "constant", { valueID: object, constantValue: constant });
		return object;
	});

	variableIndex = 1;
	createVariable(type: ir.Type, debugName: string): ValueID {
		const varID = Symbol((debugName || "unknown-var") + "_" + this.variableIndex) as VarID;
		const object = this.egraph.add(varID, [], debugName + "_" + this.variableIndex, { tag: "var", var: varID, type }) as ValueID;
		this.variableIndex += 1;
		return object;
	}

	createFn(returnType: ir.Type, semantics: Semantics<Reason>, debugName: string): FnID {
		const fnID = Symbol(debugName || "unknown-fn") as FnID;
		if (semantics.transitiveAcyclic && !semantics.transitive) {
			throw new Error("UFSolver.createFn: semantics.transitiveAcyclic requires semantics.transitive");
		}
		this.fns.set(fnID, { returnType, semantics });
		if (semantics.eq || semantics.not) {
			this.egraph.excludeCongruenceIndexing.add(fnID);
		}

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
		this.egraph.addTag(object, "indexByFn", new Map([
			[fn, TreeBag.of({ id: object, operands: args })],
		]));
		return object;
	}

	createConstant(literal: unknown): ValueID {
		return this.constants.get(literal);
	}

	getDefinition(valueID: ValueID): {
		tag: "application",
		fn: FnID,
		operands: ValueID[]
	} | {
		tag: "atom",
		extra: ConstantValue | VarValue
	} {
		const definition = this.egraph.getDefinition(valueID);
		if (definition.extra !== undefined) {
			const extra = definition.extra as ConstantValue | VarValue;
			return {
				tag: "atom",
				extra,
			};
		} else {
			return {
				tag: "application",
				fn: definition.term as FnID,
				operands: definition.operands as ValueID[],
			};
		}
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
		if (definition.tag === "application") {
			return this.getFnReturnType(definition.fn);
		} else {
			return definition.extra.type;
		}
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
	 * A much simpler implementation of the theory decision procedure, which is
	 * much faster but cannot refute all instances.
	 */
	fastRefuteUsingTheoryReducing(
		assumptions: Assumption<Reason>[],
		queries: ValueID[] = [],
		queriesNeedReasons: boolean = true,
	): UFInconsistency<Reason> | {
		tag: "model",
		model: UFCounterexample,
		answers: Map<ValueID, { assignment: boolean, reason: Set<Reason> }>
	} {
		const result = this.fastRefuteUsingTheory(assumptions, queries, queriesNeedReasons);
		if (result.tag === "inconsistent") {
			const out: Set<Reason>[] = [];
			for (const problem of result.inconsistencies) {
				if (problem.size <= 40) {
					out.push(problem);
					continue;
				}
				const prefix = [...problem].slice(0, problem.size / 4);
				const suffix = [...problem].slice(problem.size * 3 / 4);
				const reduced = new Set(prefix.concat(suffix));

				const reducedAssumptions = assumptions.filter(x => reduced.has(x.reason));
				const reducedResult = this.fastRefuteUsingTheoryReducing(reducedAssumptions, [], false);
				if (reducedResult.tag === "inconsistent") {
					out.push(...reducedResult.inconsistencies)
				} else {
					out.push(problem);
				}
			}
			return {
				...result,
				inconsistencies: out,
			};
		}
		return result;
	}

	fastRefuteUsingTheory(
		assumptions: Assumption<Reason>[],
		queries: ValueID[] = [],
		queriesNeedReasons: boolean = true,
	) {

		trace.start(["fastRefuteUsingTheory", assumptions.length]);
		const fastSolver = new FastSolver<Reason>(this);
		const fastOut = fastSolver.fastRefuteUsingTheory(assumptions, queries, queriesNeedReasons);
		trace.mark(fastOut.tag);
		trace.stop();
		return fastOut;
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
	 *
	 * @param queriesNeedReasons indicates that `answers` should indicate the
	 * reason for the truth, and not just the truth value.
	 */
	refuteUsingTheory(
		assumptions: Assumption<Reason>[],
		queries: ValueID[] = [],
		queriesNeedReasons: boolean = true,
	): UFInconsistency<Reason> | {
		tag: "model",
		model: UFCounterexample,
		answers: Map<ValueID, { assignment: boolean, reason: Set<Reason> }>
	} {
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
				const seen = new TrieMap<unknown[], true>();
				let diagnoses = [];
				for (const inconsistent of this.pendingInconsistencies) {
					const key = this.inconsistencyKeyForDeduplication(inconsistent);
					if (seen.get(key) === undefined) {
						diagnoses.push(this.diagnoseInconsistency(inconsistent));
						seen.put(key, true);
					}
				}
				trace.stop("diagnoseInconsistencies");
				return {
					tag: "inconsistent",
					inconsistencies: diagnoses,
				};
			}
		}

		trace.start("queries");
		const answers = new Map<ValueID, { assignment: boolean, reason: Set<Reason> }>();
		for (const query of queries) {
			if (this.egraph.areCongruent(query, this.falseObject)) {
				let reason = queriesNeedReasons
					? this.egraph.explainCongruence(query, this.falseObject)
					: new Set<Reason>();
				answers.set(query, { assignment: false, reason });
			} else if (this.egraph.areCongruent(query, this.trueObject)) {
				let reason = queriesNeedReasons
					? this.egraph.explainCongruence(query, this.trueObject)
					: new Set<Reason>();
				answers.set(query, { assignment: true, reason });
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

	private objectNumberer: Map<unknown, number> = new Map();
	private objectNumber(object: unknown): number {
		let existing = this.objectNumberer.get(object);
		if (existing !== undefined) {
			return existing;
		}
		existing = this.objectNumberer.size + 1;
		this.objectNumberer.set(object, existing);
		return existing;
	}

	private inconsistencyKeyForDeduplication(inconsistency: InconsistentConstraints<Reason>): unknown[] {
		const simpleReasons = (inconsistency.simpleReasons || []).map(x => this.objectNumber(x));
		const equalities = inconsistency.equalityConstraints.flatMap(x => {
			const left = this.objectNumber(x.left);
			const right = this.objectNumber(x.right);
			return [Math.min(left), Math.max(right)];
		}).sort();
		return ["equalities", ...equalities, "simpleReasons", ...simpleReasons];
	}

	/**
	 * Convert the set of theory constraints to a conjunction of `Reason`s which
	 * are inconsistent in this theory.
	 */
	private diagnoseInconsistency(inconsistency: InconsistentConstraints<Reason>): Set<Reason> {
		trace.start([
			"diagnoseInconsistency",
			inconsistency.equalityConstraints.length,
			"eqs",
			inconsistency.simpleReasons,
		]);
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
		trace.stop();
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

	private checkDisequality(
		{ equality, left, right }: { equality: ValueID, left: ValueID, right: ValueID },
	): boolean {
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
		const valueDefinition = this.getDefinition(constants.valueID);
		if (valueDefinition.tag !== "atom" || valueDefinition.extra.tag !== "constant") {
			throw new Error("UFSolver.evaluateConstant: non-literal tagged");
		}
		return {
			constant: valueDefinition.extra.constant,
			constantID: constants.valueID,
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
			const transitiveChain = nonEmptyPath(digraph, sourceRep, targetRep);
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
				const transitiveChain = nonEmptyPath(digraph, source, source);
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
			this.addBooleanBranchConstraint(v);
		}
		return v;
	}

	private addBooleanBranchConstraint(value: ValueID): void {
		// Boolean-typed variables must be equal to either true or false.
		// This constraint ensures that the sat solver will commit the
		// variable to a particular assignment.
		this.addConstraint([
			value,
			this.createApplication(this.notFn, [value]),
		]);
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

			const symmetric = this.solver.hasApplication(fnID, [right, left]);
			if (symmetric !== null) {
				return symmetric;
			}
		} else if (semantics.not) {
			const operand = args[0];
			const operandDefinition = this.solver.getDefinition(operand);
			if (operandDefinition.tag === "application") {
				const semantics = this.solver.getFnSemantics(operandDefinition.fn);
				if (semantics.not === true) {
					return operandDefinition.operands[0];
				}
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
			const term = this.objectByTerm.size + 1;
			this.toSatLiteralMap.set(positiveValue, term);
			this.objectByTerm.set(term, positiveValue);
			return term;
		};

		const out = this.toSatLiteralInternal(valueID, vend, additionalClauses);
		if (!this.objectByTerm.has(Math.abs(out))) {
			throw new Error(
				"UFTheory.toSatLiteral: " +
				"toSatLiteralInternal returned a literal for an undefined term",
			);
		}
		this.toSatLiteralMap.set(valueID, out);
		return out;
	}

	/**
	 * @returns a SAT term associated with a Boolean-typed object tracked by the
	 * solver.
	 */
	private toSatLiteralInternal(
		valueID: ValueID,
		vendTerm: (positiveValue: ValueID) => number,
		additionalClauses: number[][],
	): number {
		const definition = this.solver.getDefinition(valueID);
		if (definition.tag === "application") {
			const semantics = this.solver.getFnSemantics(definition.fn);
			if (semantics.not === true) {
				return -this.toSatLiteral(definition.operands[0], additionalClauses);
			} else if (semantics.eq === true) {
				const [leftID, rightID] = definition.operands;
				const leftType = this.solver.getType(leftID);
				const rightType = this.solver.getType(rightID);
				if (leftType !== "unknown" && rightType !== "unknown") {
					if (ir.equalTypes(ir.T_BOOLEAN, leftType) && ir.equalTypes(ir.T_BOOLEAN, rightType)) {
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

	override clausify(disjunction: ValueID[]): number[][] {
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
		for (const clause of this.clauses) {
			this.printClause(clause, lines);
		}
		return lines;
	}

	override learnTheoryClauses(
		partialAssignment: number[],
		unassigned: number[],
	): { tag: "implied", impliedClauses: number[][], model: UFCounterexample }
		| { tag: "unsatisfiable", conflictClauses: number[][] } {
		trace.start("learnTheoryClauses");
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

		let result: UFInconsistency<ReasonSatLiteral> | {
			tag: "model",
			model: UFCounterexample,
			answers: Map<ValueID, { assignment: boolean, reason: Set<ReasonSatLiteral> }>
		};

		const fastResult = this.solver.fastRefuteUsingTheory(assumptions, queries);

		result = fastResult;

		if (result.tag !== "inconsistent") {
			trace.start("slow refuteUsingTheory");
			const slowResult = this.solver.refuteUsingTheory(assumptions, queries);
			trace.stop("slow refuteUsingTheory");
			result = slowResult;
		}

		if (result.tag === "inconsistent") {
			const conflictClauses = [];
			for (const inconsistent of result.inconsistencies) {
				const learnedClause = [];
				for (const literal of inconsistent) {
					learnedClause.push(-literal);
				}
				conflictClauses.push(learnedClause);
			}
			trace.stop();
			return {
				tag: "unsatisfiable",
				conflictClauses,
			};
		}

		const impliedClauses: number[][] = [];
		for (const [object, { assignment, reason }] of result.answers) {
			const term = this.toSatLiteral(object, impliedClauses);
			impliedClauses.push([...[...reason].map(literal => -literal), assignment ? +term : -term]);
		}
		trace.stop();
		return { tag: "implied", impliedClauses, model: result.model };
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

		let uniqued: Record<string, true> = {};
		const makeUnique = (name: string): string => {
			if (name in uniqued) {
				for (let i = 1; true; i++) {
					const d = name + "_" + i.toFixed(0);
					if (d in uniqued) continue;
					return d;
				}
			}
			uniqued[name] = true;
			return name;
		}

		const fs = new DefaultMap<FnID, string>(value => {
			const name = makeUnique("f" + String(value)
				.replace(/=/g, "eq")
				.replace(/</g, "lt")
				.replace(/>/g, "gt")
				.replace(/\+/g, "pl")
				.replace(/-/g, "mn")
				.replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length);
			const returnType = showType(this.solver.getFnReturnType(value));

			const semantics = this.solver.getFnSemantics(value);
			let semanticsCode = Object.entries(semantics).map(([key, value]) => {
				if (value === undefined) {
					return "";
				}
				let shown: string = value.toString();
				if (typeof value === "function" && !shown.startsWith("function ")) {
					shown = "function " + shown;
				}
				return "\t" + JSON.stringify(key) + ": " + shown + "," + "\n";
			}).join("");
			if (semanticsCode === "") {
				semanticsCode = "{}";
			} else {
				semanticsCode = "{\n" + semanticsCode + "}";
			}


			const hint = JSON.stringify(value.description);
			defs.push(`const ${name} = smt.createFunction(${returnType}, ${semanticsCode}, ${hint});`);
			return name;
		});
		const exprs = new DefaultMap<ValueID, string>(value => {
			const def = this.solver.getDefinition(value);
			if (def.tag === "atom") {
				if (def.extra.tag === "var") {
					const name = makeUnique("v" + String(value).replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length);
					const type = showType(this.solver.getType(value) as ir.Type);
					const hint = JSON.stringify(String(value));
					defs.push(`const ${name} = smt.createVariable(${type}, ${hint});`);
					return name;
				} else {
					const constant = def.extra.constant;
					const name = makeUnique("c" + String(constant).replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length);
					const value = (typeof constant === "bigint")
						? "BigInt(" + JSON.stringify(constant.toString()) + ")"
						: JSON.stringify(constant);
					defs.push(`const ${name} = smt.createConstant(ir.T_INT, ${value});`);
					return name;
				}
			} else {
				const f = fs.get(def.fn);
				const name = makeUnique("a" + String(def.fn).replace(/[^a-zA-Z0-9]+/g, "") + "_" + defs.length);
				const args = def.operands.map(x => exprs.get(x));
				defs.push(`const ${name} = smt.createApplication(${f}, [${args.join(", ")}]);`);
				return name;
			}
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
