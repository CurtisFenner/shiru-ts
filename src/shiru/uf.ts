import { DefaultMap } from "./data";
import * as egraph from "./egraph";
import * as ir from "./ir";
import * as smt from "./smt";

export interface UFCounterexample { }

export type VarID = symbol & { __brand: "uf-var" };
export type FnID = symbol & { __brand: "uf-fn" };

type Value = VarValue | AppValue | LiteralValue;

interface VarValue {
	tag: "var",
	variable: VarID,
}

interface AppValue {
	tag: "app",
	fn: FnID,
	args: ValueID[],
}

interface LiteralValue {
	tag: "literal",
	literal: unknown,
};

// A (boolean) variable ID.
type Reason = number;

export type ValueID = symbol & { __brand: "uf.ValueID" };

interface Semantics {
	eq?: true,
	not?: true,
}

interface FnInfo {
	returnType: ir.Type,
	semantics: Semantics,
}

/// UFTheory implements the "theory of uninterpreted functions".
/// This theory understands the properties of equality
/// (symmetric, reflective, and transitive)
/// as well as the "congruence" of function application:
/// a == b implies f(a) == f(b)
export class UFTheory extends smt.SMTSolver<ValueID[], UFCounterexample> {
	private nextTerm = 1;
	/// `booleans` and `toBooleans` contain Boolean-typed values.
	private valueByTerm = new Map<number, ValueID>();
	private literalByValue = new Map<ValueID, number>();

	private eg = new egraph.EGraph<VarID | FnID | LiteralValue, "constant", Reason>();

	private constantValue = new Map<ValueID, unknown>();
	private constants = new DefaultMap<unknown, ValueID>(c => {
		const term: LiteralValue = { tag: "literal", literal: c };
		const id = this.eg.add(term, [], "constant") as ValueID;
		this.constantValue.set(id, c);
		return id;
	});

	private values = new Map<ValueID, Value>();
	private functions = new Map<FnID, FnInfo>();

	createVariable(type: ir.Type): ValueID {
		const varID = Symbol("uf-symbol") as VarID;
		const variable = this.eg.add(varID, []) as ValueID;
		this.values.set(variable, { tag: "var", variable: varID });
		if (ir.equalTypes(type, ir.T_BOOLEAN)) {
			const term = this.nextTerm;
			this.nextTerm += 1;
			this.literalByValue.set(variable, +term);
			this.valueByTerm.set(term, variable);
		}
		return variable;
	}

	createConstant(t: ir.Type, c: unknown): ValueID {
		return this.constants.get(c);
	}

	createFunction(returnType: ir.Type, semantics: Semantics): FnID {
		const id = Symbol("uf-function") as FnID;
		this.functions.set(id, { returnType, semantics });
		return id;
	}

	createApplication(fnID: FnID, args: ValueID[]): ValueID {
		const fn = this.functions.get(fnID);
		if (fn === undefined) {
			throw new Error("UFTheory.createApplication: undefined function");
		}
		const value = this.eg.add(fnID, args) as ValueID;
		if (!this.values.has(value)) {
			this.values.set(value, {
				tag: "app",
				fn: fnID,
				args,
			});

			if (ir.equalTypes(fn.returnType, ir.T_BOOLEAN)) {
				if (fn.semantics.not) {
					// Negate the existing literal.
					const sub = this.literalByValue.get(args[0]);
					if (sub === undefined) {
						throw new Error("UFTheory.createApplication: cannot negate non-boolean");
					}
					this.literalByValue.set(value, -sub);
				} else {
					const term = this.nextTerm;
					this.nextTerm += 1;
					this.valueByTerm.set(term, value);
					this.literalByValue.set(value, +term);
				}
			}
		}

		return value;
	}

	clausify(constraint: ValueID[]): number[][] {
		const clause = [];
		for (const option of constraint) {
			const literal = this.literalByValue.get(option);
			if (literal === undefined) {
				throw new Error("UFTheory.clausify: non-boolean");
			}
			clause.push(literal);
		}
		return [clause];
	}

	rejectModel(literals: number[]): UFCounterexample | number[] {
		this.eg.reset();
		const trueObject = this.createConstant(ir.T_BOOLEAN, true);
		const falseObject = this.createConstant(ir.T_BOOLEAN, false);

		for (const literal of literals) {
			const term = literal > 0 ? literal : -literal;
			const positiveValue = this.valueByTerm.get(term)!;
			const definition = this.values.get(positiveValue)!;

			if (literal > 0) {
				this.eg.merge(positiveValue, trueObject, new Set([literal]));
			} else {
				this.eg.merge(positiveValue, falseObject, new Set([literal]));
			}

			if (definition.tag === "app") {
				const fn = this.functions.get(definition.fn)!;
				if (fn.semantics.eq === true) {
					if (literal > 0) {
						this.eg.merge(definition.args[0], definition.args[1], new Set([literal]));
					}
				}
			}
		}

		while (true) {
			// Check for contradictions.
			for (const [id] of this.eg.getClasses()) {
				const constants = this.eg.getTagged("constant", id);
				if (constants.length > 1) {
					// Two distinct constants are in the same equality class.
					return [...this.eg.query(constants[0].id, constants[1].id)!].map(x => -x);
				}
			}

			for (const literal of literals) {
				const term = literal > 0 ? literal : -literal;
				const positiveValue = this.valueByTerm.get(term)!;
				if (literal < 0) {
					const definition = this.values.get(positiveValue)!;
					if (definition.tag === "app") {
						const fn = this.functions.get(definition.fn)!;
						if (fn.semantics.eq === true) {
							// A model must have these two objects disequal.
							const bridge = this.eg.query(definition.args[0], definition.args[1]);
							if (bridge !== null) {
								return [literal, ...bridge].map(x => -x);
							}
						}
					}
				}
			}

			let madeChanges = this.eg.updateCongruence();

			if (!madeChanges) {
				return {};
			}
		}
	}
}
