import { DefaultMap, DisjointSet, TrieMap } from "./data";

export type EObject = symbol & { __brand: "EObject" };

export type EClassDescription<Term> = {
	members: { id: EObject, term: Term, operands: EObject[] }[],
	representative: EObject,
};

/**
 * `ReasonTree` represents a tree of sets to be merged lazily.
 */
export class ReasonTree<T> {
	private elementList?: T[];
	private children: ReasonTree<T>[] = [];

	constructor(elements?: T[]) {
		this.elementList = elements;
	}

	static withChildren<T>(children: ReasonTree<T>[]): ReasonTree<T> {
		const tree = new ReasonTree<T>();
		tree.children = children;
		return tree;
	}

	addChild(child: ReasonTree<T>): void {
		this.children.push(child);
	}

	toSet(accumulate: Set<T> = new Set()): Set<T> {
		if (this.elementList !== undefined) {
			for (const leaf of this.elementList) {
				accumulate.add(leaf);
			}
		}
		for (const child of this.children) {
			child.toSet(accumulate);
		}
		return accumulate;
	}
}

type PendingCongruence = {
	left: EObject,
	right: EObject,
	leftOperands: EObject[],
	rightOperands: EObject[],
};

/// An "equivalence-graph", loosely inspired by "egg (e-graphs good)".
export class EGraph<Term, Tag, Reason> {
	/**
	 * `tagged.get(tag).get(rep)` is the set of objects tagged with `tag` that
	 * are equal to representative `rep`.
	 */
	private tagged = new DefaultMap<Tag, DefaultMap<EObject, Set<EObject>>>(t => new DefaultMap(r => new Set()));

	private tuples: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();
	private objectDefinition: Map<EObject, { term: Term, operands: EObject[], uniqueObjectCount: number }> = new Map();
	private ds: DisjointSet<EObject, ReasonTree<Reason>> = new DisjointSet();

	private lazyCongruence: PendingCongruence[] = [];

	/**
	 * A canonicalized version of the function is added.
	 */
	private functionByRep: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();

	private references: DefaultMap<EObject, Set<EObject>> = new DefaultMap(() => new Set());

	private updateFunctionRep(obj: EObject): [Term, ...EObject[]] {
		const def = this.objectDefinition.get(obj)!!;
		const representativeKey: [Term, ...EObject[]] = [def.term];
		for (const operand of def.operands) {
			representativeKey.push(this.getRepresentative(operand));
		}

		const existing = this.functionByRep.get(representativeKey);
		if (existing !== undefined && existing !== obj) {
			const existingDef = this.getDefinition(existing);
			this.lazyCongruence.push({
				left: existing,
				right: obj,
				leftOperands: existingDef.operands,
				rightOperands: def.operands,
			});
		} else {
			this.functionByRep.put(representativeKey, obj);
		}
		return representativeKey;
	}

	reset(): void {
		this.ds.reset();
		this.queryCache.clear();
		for (const [_, map] of this.tagged) {
			for (const [id, set] of map) {
				const has = set.has(id);
				set.clear();
				if (has) {
					set.add(id);
				}
			}
		}

		this.references.clear();
		this.functionByRep.clear();
		this.lazyCongruence = [];
		for (const [object, { term, operands }] of this.objectDefinition) {
			this.functionByRep.put([term, ...operands], object);
			for (const operand of operands) {
				this.references.get(operand).add(object);
			}
		}
	}

	/**
	 * `getDefinition(id)` returns the `term` and `operands` passed to
	 * `add(term, operands)` to create the given object.
	 */
	getDefinition(id: EObject): { term: Term, operands: EObject[] } {
		const definition = this.objectDefinition.get(id);
		if (definition === undefined) {
			throw new Error("EGraph.getDefinition: object `" + String(id) + "` not defined");
		}
		return { term: definition.term, operands: definition.operands };
	}

	getTagged(tag: Tag, id: EObject): Array<{ id: EObject, term: Term, operands: EObject[] }> {
		const out = [];
		const representative = this.ds.representative(id);
		for (const tagged of this.tagged.get(tag).get(representative)) {
			const def = this.objectDefinition.get(tagged)!;
			out.push({ id: tagged, term: def.term, operands: def.operands });
		}
		return out;
	}

	debugSymbolNames = true;
	private uniqueObjectCount = 1;

	/**
	 * `hasStructure(term, operands)` searches for an object with the given
	 * definition, returning it if it was already created using
	 * `add(term, operands)`. The search is based on object identity, and not by
	 * equalities tracked by this `EGraph`.
	 * 
	 * `hasStructure` returns `null` when `add(term, operands)` has not already
	 * been invoked with the given term and operand objects.
	 */
	hasStructure(term: Term, operands: EObject[]): EObject | null {
		const tuple: [Term, ...EObject[]] = [term, ...operands];
		return this.tuples.get(tuple) || null;
	}

	addTag(object: EObject, tag: Tag): void {
		const representative = this.getRepresentative(object);
		this.tagged.get(tag).get(representative).add(object);
		if (representative !== object) {
			this.tagged.get(tag).get(object).add(object);
		}
	}

	add(term: Term, operands: EObject[], hint?: string): EObject {
		const tuple: [Term, ...EObject[]] = [term, ...operands];
		const existing = this.tuples.get(tuple);
		if (existing) {
			return existing;
		}

		if (!hint && this.debugSymbolNames) {
			const fnName = String(term).match(/^Symbol\((.+)\)$/);
			hint = (fnName ? fnName[1] : "unknown");
			if (operands.length !== 0) {
				hint += "(";
				hint += operands.map(x => {
					if (x === undefined) {
						throw new Error("EGraph.add: unexpected undefined");
					}
					const raw = String(x);
					const match = String(x).match(/^Symbol\(egraph-term    (.+)    \)$/);
					if (match) {
						return match[1];
					} else {
						return raw;
					}
				}).join(", ");
				hint += ")";
			}
		}

		const id: EObject = Symbol("egraph-term    " + hint + " #" + this.uniqueObjectCount + "    ") as EObject;
		this.uniqueObjectCount += 1;
		this.tuples.put(tuple, id);
		this.objectDefinition.set(id, {
			term,
			operands,
			uniqueObjectCount: this.uniqueObjectCount,
		});
		this.functionByRep.put(tuple, id);
		for (const operand of operands) {
			this.references.get(this.getRepresentative(operand)).add(id);
		}
		this.updateFunctionRep(id);
		return id;
	}

	mergeBecauseCongruence(a: EObject, b: EObject, lefts: EObject[], rights: EObject[]): boolean {
		if (lefts.length !== rights.length) {
			throw new Error("EGraph.mergeBecauseCongruence: lefts.length !== rights.length");
		}
		const elementReasons = [];
		for (let i = 0; i < lefts.length; i++) {
			const reason = this.explainCongruence(lefts[i], rights[i]);
			elementReasons.push(reason);
		}

		return this.merge(a, b, ReasonTree.withChildren(elementReasons));
	}

	/// `reason` is a conjunction of `Reason`s.
	/// merge(a, b, reason) returns false when this fact was already present in
	/// this egraph.
	merge(a: EObject, b: EObject, reason: ReasonTree<Reason>): boolean {
		const arep = this.ds.representative(a);
		const brep = this.ds.representative(b);
		if (arep === brep) {
			return false;
		}

		// Merge a and b specifically (and not their representatives) so that
		// the reason is precisely tracked.
		this.ds.union(a, b, reason);

		const parent = this.ds.representative(arep);
		if (parent !== arep && parent !== brep) {
			throw new Error("EGraph.merge: unexpected new representative");
		}
		const child = arep === parent ? brep : arep;
		for (const [tag, map] of this.tagged) {
			const parentSet = this.tagged.get(tag).get(parent);
			for (const e of map.get(child)) {
				parentSet.add(e);
			}
		}

		// Find all references of the child and process them with
		// updateFunctionRep
		const childReferences = this.references.get(child);
		for (const childReference of childReferences) {
			this.references.get(parent).add(childReference);
			this.updateFunctionRep(childReference);
		}

		return true;
	}

	updateCongruence(): boolean {
		let madeChanges = false;
		while (this.lazyCongruence.length !== 0) {
			const q = this.lazyCongruence;
			this.lazyCongruence = [];
			for (const e of q) {
				madeChanges = this.mergeBecauseCongruence(e.left, e.right, e.leftOperands, e.rightOperands) || madeChanges;
			}
		}
		return madeChanges;
	}

	private queryCache: Map<EObject, Map<EObject, ReasonTree<Reason>>> = new Map();

	areCongruent(a: EObject, b: EObject): boolean {
		return this.ds.compareEqual(a, b);
	}

	explainCongruence(a: EObject, b: EObject): ReasonTree<Reason> {
		if (!this.ds.compareEqual(a, b)) {
			throw new Error("EGraph.explainCongruence: objects are not congruent");
		}

		let cacheA = this.queryCache.get(a);
		if (cacheA !== undefined) {
			const cacheB = cacheA.get(b);
			if (cacheB !== undefined) {
				return cacheB;
			}
		}

		const seq = this.ds.explainEquality(a, b);
		const all = ReasonTree.withChildren(seq);

		if (cacheA === undefined) {
			cacheA = new Map();
			this.queryCache.set(a, cacheA);
		}
		cacheA.set(b, all);
		return all;
	}

	/// getRepresentative(obj) returns a "representative" element of obj's
	/// equivalence class, such that any two objects that are equal have the
	/// same representative, and any objects that are not equal have different
	/// representatives.
	getRepresentative(obj: EObject): EObject {
		return this.ds.representative(obj);
	}

	getClasses(duplicate?: boolean): Map<EObject, EClassDescription<Term>> {
		const mapping: Map<EObject, EClassDescription<Term>> = new Map();
		for (const [k, id] of this.tuples) {
			const representative = this.ds.representative(id);
			let eclass = mapping.get(representative);
			if (eclass === undefined) {
				eclass = { members: [], representative };
				mapping.set(representative, eclass);
			}
			if (duplicate) {
				mapping.set(id, eclass);
			}
			const term = k[0];
			const operands = k.slice(1) as EObject[];
			eclass.members.push({ id, term, operands });
		}
		return mapping;
	}
}
