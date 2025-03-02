import { TrieMap } from "./data.js";
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

export class UFTheory extends smt.SMTSolver<ValueID[], UFCounterexample> {
	private applicationTrie = new TrieMap<[FnID, ...ValueID[]], ValueID>();

	private fnMap = new Map<FnID, {
		returnType: ir.Type,
		semantics: Semantics,
	}>();

	private constantMap = new Map<unknown, ValueID>();

	private valueMap = new Map<ValueID, ValueDefinition>();

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
		return {
			tag: "implied",
			impliedClauses: [],
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
		const value = Symbol(debugName) as ValueID;
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
