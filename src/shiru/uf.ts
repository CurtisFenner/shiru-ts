import { BitSet, bitsetEmpty, bitsetIntersect, bitsetSingleton, bitsetUnion, DisjointSet, TrieMap } from "./data.js";
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

	/** A `transitiveAcyclic` function is a `transitive` function which does not
	 * admit cycles (a < b < c < d < ... < a). This implies that the relation
	 * is anti-reflexive.
	 */
	transitiveAcyclic?: true,

	interpreter?: (...args: (unknown | null)[]) => unknown | null,
}

type ValueDefinition = { tag: "application", fn: FnID, operands: ValueID[] }
	| { tag: "constant", constant: unknown, t: ir.Type }
	| { tag: "variable", t: ir.Type };

type ECData = {
	constant?: unknown,
	distinct: BitSet,
	value: ValueID,
};

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
				};
			}
			return { distinct: bitsetEmpty, value };
		},
		(child, parent) => {
			return {
				constant: parent.constant ?? child.constant,
				distinct: bitsetUnion(child.distinct, parent.distinct),
				value: (parent.constant ?? false)
					? parent.value
					: child.value,
			};
		},
	);

	constructor(private theory: UFTheory) { }

	private union(a: ValueID, b: ValueID): null | "contradiction" {
		if (this.ds.compareEqual(a, b)) {
			return null;
		}

		const dataA = this.ds.getData(a);
		const dataB = this.ds.getData(b);
		if (bitsetIntersect(dataA.distinct, dataB.distinct)) {
			return "contradiction";
		}

		this.ds.union(a, b);
		return null;
	}

	evaluateBoolean(value: ValueID): boolean | "unknown" {
		const simplified = this.simplifyValue(value);
		if (!this.ds.hasInitialized(simplified)) {
			return "unknown";
		}
		const data = this.ds.getData(simplified);
		if (typeof data.constant !== "boolean") {
			return "unknown";
		}
		return data.constant;
	}

	assumeValue(unsimplifiedValue: ValueID, truth: boolean): null | "contradiction" {
		const boolean = truth
			? this.theory.trueConstant
			: this.theory.falseConstant;

		const simplified = this.simplifyValue(unsimplifiedValue);
		const booleanUnion = this.union(simplified, boolean);

		const definition = this.theory.valueMap.get(simplified)!;

		let unionResult: null | "contradiction" = null;
		if (definition.tag === "application") {
			const semantics = this.theory.fnMap.get(definition.fn)!.semantics;
			const operands = definition.operands;
			if (semantics.eq) {
				if (truth) {
					unionResult = this.union(operands[0], operands[1]);
				} else {
					if (this.ds.compareEqual(operands[0], operands[1])) {
						unionResult = "contradiction";
					} else {
						const distinctBit = this.nextDistinctBit;
						this.nextDistinctBit += 1;
						const distinctSet = bitsetSingleton(distinctBit);
						this.ds.unionData(operands[0], {
							value: operands[0],
							distinct: distinctSet,
						});
						this.ds.unionData(operands[1], {
							value: operands[1],
							distinct: distinctSet,
						});
					}
				}
			}
		}

		return booleanUnion || unionResult;
	}

	simplifyValue(value: ValueID): ValueID {
		const definition = this.theory.valueMap.get(value)!;
		if (definition.tag === "constant") {
			return value;
		}
		let simplified = value;
		if (definition.tag === "application") {
			const operands = definition.operands.map(x => this.simplifyValue(x));
			simplified = this.theory.createApplication(definition.fn, operands);
			const fnData = this.theory.fnMap.get(definition.fn)!;
			const semantics = fnData.semantics;
			if (semantics.eq) {
				if (this.ds.compareEqual(operands[0], operands[1])) {
					return this.theory.trueConstant;
				}
				const data0 = this.ds.getData(operands[0]);
				const data1 = this.ds.getData(operands[1]);
				if (bitsetIntersect(data0.distinct, data1.distinct)) {
					return this.theory.falseConstant;
				} else if (operands[0] === this.theory.trueConstant) {
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
			return this.ds.representative(simplified)
		}
		return simplified;
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
		throw new Error("Method not implemented.");
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
		const before = performance.now();
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
			});
		}

		const state = new TheoryState(this);
		for (let i = 0; i < truths.length; i++) {
			const result = state.assumeValue(truths[i].value, truths[i].truthAssignment);
			if (result === "contradiction") {
				const contradictoryAssigment = truths.slice(0, i + 1).map(x => x.literal);
				const conflictClause = contradictoryAssigment.map(x => -x);
				const after = performance.now();
				return {
					tag: "unsatisfiable",
					conflictClauses: [conflictClause],
				};
			}
		}

		const impliedClauses: sat.Literal[][] = [];
		for (const literal of unassignedLiterals) {
			const truthAssignment = literal > 0;
			const term = truthAssignment ? literal : -literal;
			const value = this.termMap.get(term)!;
			const simplified = state.simplifyValue(value);
			let termValue = null;
			if (simplified === this.trueConstant) {
				termValue = true;
			} else if (simplified === this.falseConstant) {
				termValue = false;
			}

			if (termValue !== null) {
				impliedClauses.push([
					...partialAssignment.map(x => -x),
					termValue === truthAssignment
						? literal
						: -literal,
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
		return value;
	}

	createApplication(fn: FnID, operands: ValueID[]): ValueID {
		const key: [FnID, ...ValueID[]] = [fn, ...operands];
		const existing = this.applicationTrie.get(key);
		if (existing) {
			return existing;
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
		return application;
	}
}
