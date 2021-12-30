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

export type ValueID = egraph.EObject & { __brand: "uf.ValueID" };

export interface Semantics {
	eq?: true,
	not?: true,

	interpreter?: {
		f(...args: (unknown | null)[]): unknown | null,
	},
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
	private values = new Map<ValueID, Value>();
	private functions = new Map<FnID, FnInfo>();

	private constantValue = new Map<ValueID, unknown>();
	private constants = new DefaultMap<unknown, ValueID>(c => {
		const term: LiteralValue = { tag: "literal", literal: c };
		const id = this.eg.add(term, [], "constant", "constant") as ValueID;
		this.constantValue.set(id, c);
		this.values.set(id, term);
		return id;
	});


	createVariable(type: ir.Type): ValueID {
		const varID = Symbol("uf-symbol") as VarID;
		const variable = this.eg.add(varID, [], undefined, "variable") as ValueID;
		this.values.set(variable, { tag: "var", variable: varID });
		return this.vendTermForBoolean(type, variable);
	}

	private vendTermForBoolean(t: ir.Type, id: ValueID): ValueID {
		if (ir.equalTypes(t, ir.T_BOOLEAN)) {
			if (!this.literalByValue.has(id)) {
				const term = this.nextTerm;
				this.nextTerm += 1;
				this.literalByValue.set(id, +term);
				this.valueByTerm.set(term, id);
			}
		}
		return id;
	}

	createConstant(t: ir.Type, c: unknown): ValueID {
		if (c === null) {
			throw new Error("createConstant: cannot use `null` as constant");
		}
		const id = this.constants.get(c);
		return this.vendTermForBoolean(t, id);
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
		const value = this.eg.add(fnID, args, undefined, "app(" + fnID.toString() + ")") as ValueID;
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
					this.vendTermForBoolean(ir.T_BOOLEAN, value);
				}
			}
		}

		return value;
	}

	/// `evaluateConstant` returns a constant (as it was passed to
	/// `createConstant`) that is equal to the given value under the current
	/// constraints.
	evaluateConstant(value: ValueID): { constant: unknown, reason: Set<number> } | null {
		const constants = this.eg.getTagged("constant", value);
		if (constants.length === 0) {
			return null;
		}
		const id = constants[0].id;
		const constant = this.constantValue.get(id as ValueID);
		return {
			constant,
			reason: this.eg.query(value, id)!,
		};
	}

	/// `interpretFunctions` adds additional constants and equalities by using
	/// the `interpreter` semantics of functions.
	interpretFunctions() {
		let madeChanges = false;
		while (true) {
			let iterationMadeChanges = false;
			for (const [eclass, { members }] of this.eg.getClasses()) {
				for (const member of members) {
					const fn = this.functions.get(member.term as FnID);
					if (fn !== undefined) {
						const interpreter = fn.semantics.interpreter;
						if (interpreter !== undefined) {
							const reason = new Set<number>();
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
								const constant = this.createConstant(fn.returnType, r);
								const changed = this.eg.merge(constant, eclass, reason);
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
		return madeChanges;
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
			const definition = this.values.get(positiveValue);
			if (definition === undefined) {
				throw new Error("rejectModel: undefined literal");
			}

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

			let madeChanges = false;
			madeChanges = this.eg.updateCongruence() || madeChanges;
			madeChanges = this.interpretFunctions() || madeChanges;

			if (!madeChanges) {
				return {};
			}
		}
	}
}
