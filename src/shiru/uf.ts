import { BitSet, bitsetEmpty, bitsetIntersect, bitsetSingleton, bitsetToIndexes, bitsetUnion, DisjointSet, TrieMap } from "./data.js";
import * as ir from "./ir.js";
import * as sat from "./sat.js";
import * as smt from "./smt.js";

export interface UFCounterexample {
	model: {},
}

export type FnID = symbol & { __brand: "uf.FnID" };

export type ValueID = symbol & { __brand: "uf.ValueID" };

export interface Semantics {
	/** An `eq` function respects congruence: a == b implies f(a) == f(b). */
	eq?: true,

	/** A `not` function is only applied to booleans.
	 * f(true) == false, and f(false) == true.
	 */
	not?: true,

	/** A `transitive` function respects transitivity:
	 * f(a, b) and f(b, a) implies f(a, c).
	 * (This need not be specified for `eq` functions)
	 */
	transitive?: true,

	/** An `irreflexive` function is one which `f(a, a)` is always false.
	 *
	 * For a `transitive` function `≺`, this means there are no "cycles":
	 * `a ≺ b ≺ c ≺ d ≺ ... ⊀ a`.
	 */
	irreflexive?: true,

	interpreter?: (...args: (unknown | null)[]) => unknown | null,
}

type ValueDefinition = { tag: "application", fn: FnID, operands: ValueID[] }
	| { tag: "constant", constant: unknown, t: ir.Type }
	| { tag: "variable", t: ir.Type };

type ECData = {
	constant?: unknown,
	distinct: BitSet,
	value: ValueID,

	/** A set of reasons which together explain why all elements in this
	 * equivalence class are equal to each other.
	 */
	reason: Reason,
};

/** A set of indexes in to a `partialAssignment` */
type Reason = BitSet & { __brandReason: "Reason" };

class TheoryState {
	private nextDistinctBit = 1;
	private ds = new DisjointSet<ValueID, ECData>(
		value => {
			const definition = this.theory.valueMap.get(value)!;
			if (definition.tag === "constant") {
				return {
					constant: definition.constant,
					distinct: bitsetSingleton(0),
					value,
					reason: bitsetEmpty as Reason,
				};
			}
			return {
				distinct: bitsetEmpty,
				value,
				reason: bitsetEmpty as Reason,
			};
		},
		(child, parent) => {
			return {
				constant: parent.constant ?? child.constant,
				distinct: bitsetUnion(child.distinct, parent.distinct),
				value: (parent.constant !== undefined)
					? parent.value
					: child.value,
				reason: bitsetUnion(parent.reason, child.reason) as Reason,
			};
		},
	);

	constructor(private theory: UFTheory) { }

	private attemptUnion(
		a: ValueID,
		b: ValueID,
		reason: Reason,
	): null | { conflictReason: Reason } {
		if (this.ds.compareEqual(a, b)) {
			return null;
		}

		const dataA = this.ds.getData(a);
		const dataB = this.ds.getData(b);
		if (bitsetIntersect(dataA.distinct, dataB.distinct)) {
			return {
				conflictReason: bitsetUnion(
					bitsetUnion(dataA.reason, dataB.reason),
					reason,
				) as Reason
			};
		}

		this.ds.union(a, b);
		return null;
	}

	evaluateBoolean(value: ValueID): { value: boolean, antecedent: Reason } | "unknown" {
		const { simplified, reason } = this.simplifyValue(value);
		if (!this.ds.hasInitialized(simplified)) {
			return "unknown";
		}
		const data = this.ds.getData(simplified);
		if (typeof data.constant !== "boolean") {
			return "unknown";
		}
		return {
			value: data.constant,
			antecedent: reason,
		};
	}

	private reasonEqual(a: ValueID, b: ValueID): null | Reason {
		const aData = this.ds.getData(a);
		const bData = this.ds.getData(b);
		if (aData === bData) {
			return aData.reason;
		}
		return null;
	}

	assumeValue(
		unsimplifiedValue: ValueID,
		truth: boolean,
		reason: Reason,
	): null | { conflictReason: Reason } {
		const boolean = truth
			? this.theory.trueConstant
			: this.theory.falseConstant;

		const simplification = this.simplifyValue(unsimplifiedValue);
		reason = bitsetUnion(reason, simplification.reason) as Reason;
		const booleanUnion = this.attemptUnion(simplification.simplified, boolean, reason);
		if (booleanUnion !== null) {
			return booleanUnion;
		}

		const definition = this.theory.valueMap.get(simplification.simplified)!;

		if (definition.tag === "application") {
			const semantics = this.theory.fnMap.get(definition.fn)!.semantics;
			const operands = definition.operands;
			if (semantics.eq) {
				if (truth) {
					return this.assumeEquality(
						operands[0],
						operands[1],
						bitsetUnion(reason, simplification.reason) as Reason,
					);
				} else {
					return this.assumeDisequality(
						operands[0],
						operands[1],
						bitsetUnion(reason, simplification.reason) as Reason,
					);
				}
			}
		}

		return null;
	}

	assumeEquality(
		left: ValueID,
		right: ValueID,
		reason: Reason,
	): null | { conflictReason: Reason } {
		const unionResult = this.attemptUnion(left, right, reason);
		if (unionResult !== null) {
			return unionResult;
		}
		return null;
	}

	assumeDisequality(
		left: ValueID,
		right: ValueID,
		reason: Reason,
	): null | { conflictReason: Reason } {
		const equalReason = this.reasonEqual(left, right);
		if (equalReason !== null) {
			return {
				conflictReason: bitsetUnion(
					equalReason,
					reason,
				) as Reason,
			};
		}

		const distinctBit = this.nextDistinctBit;
		this.nextDistinctBit += 1;
		const distinctSet = bitsetSingleton(distinctBit);
		this.ds.unionData(left, {
			value: left,
			distinct: distinctSet,
			reason: bitsetEmpty as Reason,
		});
		this.ds.unionData(right, {
			value: right,
			distinct: distinctSet,
			reason: bitsetEmpty as Reason,
		});
		return null;
	}

	simplifyValue(value: ValueID): { simplified: ValueID, reason: Reason } {
		const definition = this.theory.valueMap.get(value)!;
		if (definition.tag === "constant") {
			return { simplified: value, reason: 0n as Reason };
		}
		let simplified = value;
		let reason = 0n as Reason;
		if (definition.tag === "application") {
			const operands = [];
			for (const operandSimplification of definition.operands.map(x => this.simplifyValue(x))) {
				operands.push(operandSimplification.simplified);
				reason = bitsetUnion(reason, operandSimplification.reason) as Reason;
			}
			simplified = this.theory.createApplication(definition.fn, operands);
			const fnData = this.theory.fnMap.get(definition.fn)!;
			const semantics = fnData.semantics;
			if (semantics.eq) {
				const data0 = this.ds.getData(operands[0]);
				const data1 = this.ds.getData(operands[1]);
				if (data0 === data1) {
					return {
						simplified: this.theory.trueConstant,
						reason: bitsetUnion(reason, data0.reason) as Reason,
					};
				}

				if (operands[0] === this.theory.trueConstant) {
					simplified = operands[1];
				} else if (operands[1] === this.theory.trueConstant) {
					simplified = operands[0];
				}
			} else if (semantics.interpreter) {
				const constants = operands.map(operand => {
					return this.ds.getData(operand).constant ?? null;
				});
				const result = semantics.interpreter(...constants);
				if (result !== null) {
					simplified = this.theory.createConstant(fnData.returnType, result);
				}
			}
		}

		if (this.ds.hasInitialized(simplified)) {
			const dataOfSimplified = this.ds.getData(simplified);
			return {
				simplified: dataOfSimplified.value,
				reason: bitsetUnion(reason, dataOfSimplified.reason) as Reason,
			};
		}
		return { simplified, reason };
	}
}

export class UFTheory extends smt.SMTSolver<ValueID[], UFCounterexample> {
	private applicationTrie = new TrieMap<[FnID, ...ValueID[]], ValueID>();

	fnMap = new Map<FnID, {
		returnType: ir.Type,
		semantics: Semantics,
	}>();

	private constantMap = new Map<unknown, ValueID>();

	valueMap = new Map<ValueID, ValueDefinition>();

	private literalMap = new Map<ValueID, sat.Literal>();
	private termMap = new Map<sat.Literal, ValueID>();

	public readonly trueConstant: ValueID;
	public readonly falseConstant: ValueID;
	public readonly notFn: FnID;

	constructor() {
		super();

		this.trueConstant = this.createConstant(ir.T_BOOLEAN, true);
		this.falseConstant = this.createConstant(ir.T_BOOLEAN, false);
		this.notFn = this.createFunction(ir.T_BOOLEAN, {
			not: true,
		}, "not");

		this.addConstraint([this.trueConstant]);
		this.addConstraint([this.createApplication(this.notFn, [this.falseConstant])]);
	}

	/** For debugging purposes.
	 *
	 * Inverts the constraint -> literal mapping implemented by `clausify`.
	 */
	override showLiteral(literal: sat.Literal): string {
		if (literal < 0) {
			return "NOT " + this.showLiteral(-literal);
		}
		const term = literal;
		const valueID = this.termMap.get(term);
		if (!valueID) {
			throw new Error("invalid literal");
		}
		return valueID.description ?? String(valueID);
	}

	override learnTheoryClauses(
		partialAssignment: sat.Literal[],
		unassigned: sat.Literal[],
	): { tag: "implied", impliedClauses: sat.Literal[][], model: UFCounterexample }
		| { tag: "unsatisfiable", conflictClauses: sat.Literal[][] } {
		const once = this.learnTheoryClausesOnce(partialAssignment, unassigned);
		if (once.tag !== "unsatisfiable") {
			return once;
		}

		if (once.conflictClauses.every(clause => clause.length > 3)) {
			// Attempt to reduce.
			const conflictClauses = [];
			for (const clause of once.conflictClauses) {
				if (clause.length <= 3) {
					conflictClauses.push(clause);
					continue;
				}

				const terms = new Set(clause.map(x => Math.abs(x)));
				const reducedAssignmentSource = partialAssignment.filter(literal => terms.has(Math.abs(literal)))
					.reverse();
				const twice = this.learnTheoryClausesOnce(reducedAssignmentSource, []);
				if (twice.tag !== "unsatisfiable") {
					// Behavior is inconsistent!
					// This is, for now, sound and expected, but not desirable.
					return once;
				}

				conflictClauses.push(...twice.conflictClauses);
			}
			return {
				tag: "unsatisfiable",
				conflictClauses,
			};
		}

		return once;
	}

	private learnTheoryClausesOnce(
		partialAssignment: sat.Literal[],
		unassignedLiterals: sat.Literal[],
	): { tag: "implied", impliedClauses: sat.Literal[][], model: UFCounterexample }
		| { tag: "unsatisfiable", conflictClauses: sat.Literal[][] } {
		// TODO: Sort assignment literals in a logical way.
		const truths = [];
		for (const literal of partialAssignment) {
			const truthAssignment = literal > 0;
			const term = truthAssignment ? literal : -literal;
			const value = this.termMap.get(term)!;
			truths.push({
				literal,
				value,
				truthAssignment,
				reason: bitsetSingleton(truths.length) as Reason,
			});
		}

		const state = new TheoryState(this);
		for (let pass = 0; pass < 2; pass++) {
			for (let i = 0; i < truths.length; i++) {
				const result = state.assumeValue(truths[i].value, truths[i].truthAssignment, truths[i].reason);
				if (result !== null) {
					const resultSet = new Set(bitsetToIndexes(result.conflictReason));
					const contradictoryAssignment = partialAssignment.filter((_, index) => resultSet.has(index));
					const conflictClause = contradictoryAssignment.map(x => -x);

					return {
						tag: "unsatisfiable",
						conflictClauses: [conflictClause],
					};
				}
			}
		}

		const impliedClauses: sat.Literal[][] = [];
		for (const literal of unassignedLiterals) {
			const truthAssignment = literal > 0;
			const term = truthAssignment ? literal : -literal;
			const termValue = this.termMap.get(term)!;
			const termSimplified = state.simplifyValue(termValue);
			let learnedReason = new Set(bitsetToIndexes(termSimplified.reason));
			let learnedTermAssignment = null;
			if (termSimplified.simplified === this.trueConstant) {
				learnedTermAssignment = true;
			} else if (termSimplified.simplified === this.falseConstant) {
				learnedTermAssignment = false;
			}

			if (learnedTermAssignment !== null) {
				const antecedent = partialAssignment.filter((_, index) => learnedReason.has(index));
				impliedClauses.push([
					...antecedent.map(x => -x),
					learnedTermAssignment ? term : -term,
				]);
			}
		}

		return {
			tag: "implied",
			impliedClauses,
			model: {
				model: {},
			},
		};
	}

	protected override clausify(constraint: ValueID[]): sat.Literal[][] {
		return [
			constraint.map(value => this.toSatLiteral(value))
		];
	}

	private toSatLiteral(value: ValueID): sat.Literal {
		const existing = this.literalMap.get(value);
		if (existing !== undefined) {
			return existing;
		}

		const toCache = this.toSatLiteralUncached(value);
		this.literalMap.set(value, toCache);
		return toCache;
	}

	private toSatLiteralUncached(value: ValueID): sat.Literal {
		const definition = this.valueMap.get(value)!;
		if (definition.tag === "application") {
			const fn = this.fnMap.get(definition.fn);
			if (fn?.semantics.not) {
				return -this.toSatLiteral(definition.operands[0]);
			}
		}

		const nextTerm = this.termMap.size + 1;
		this.termMap.set(nextTerm, value);
		return nextTerm;
	}

	createFunction(
		returnType: ir.Type,
		semantics: Semantics,
		debugName: string,
	): FnID {
		const fn = Symbol(debugName) as FnID;
		this.fnMap.set(fn, { returnType, semantics });
		return fn;
	}

	createConstant(t: ir.Type, constant: unknown): ValueID {
		if (constant === undefined) {
			throw new Error("UFTheory.createConstant: constant must not be undefined");
		}

		const existing = this.constantMap.get(constant);
		if (existing !== undefined) {
			return existing;
		}

		const value = Symbol(String(constant)) as ValueID;
		this.constantMap.set(constant, value);
		this.valueMap.set(value, {
			tag: "constant",
			t,
			constant,
		});
		return value;
	}

	createVariable(t: ir.Type, debugName: string): ValueID {
		const value = Symbol(debugName + "#" + this.valueMap.size) as ValueID;
		this.valueMap.set(value, {
			tag: "variable",
			t,
		});

		this.createSATTermForBoolean(value, t);
		return value;
	}

	createApplication(fn: FnID, operands: ValueID[]): ValueID {
		const key: [FnID, ...ValueID[]] = [fn, ...operands];
		const existing = this.applicationTrie.get(key);
		if (existing) {
			return existing;
		}
		const fnDefinition = this.fnMap.get(fn);
		if (!fnDefinition) {
			throw new Error("invalid fn");
		}

		const description =
			(fn.description || "?") + "(" + operands.map(x => x.description || "?").join(", ") + ")";
		const application = Symbol(description) as ValueID;
		this.applicationTrie.put(key, application);
		this.valueMap.set(application, {
			tag: "application",
			fn,
			operands,
		});

		this.createSATTermForBoolean(application, fnDefinition.returnType);
		return application;
	}

	private createSATTermForBoolean(value: ValueID, t: ir.Type): void {
		if (ir.equalTypes(ir.T_BOOLEAN, t)) {
			// Create a term, forcing an assignment to true or false within the
			// theory solver.
			this.toSatLiteral(value);
		}
	}
}
