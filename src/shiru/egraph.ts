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
		} else {
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
			return id;
		}
	}

	/// `reason` is a conjunction of `Reason`s.
	/// merge(a, b, reason) returns false when this fact was already present in
	/// this egrahp.
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
		return true;
	}

	private updateCongruenceStep(): boolean {
		// The keys of `canonical` are representatives.
		// The `id` is the symbol of the original (non-canonicalized) object;
		// the `reason` is the union of reasons for why the canonicalized
		// version is equal to the original version.
		const canonical = new TrieMap<[Term, ...EObject[]], { id: EObject, representative: EObject }[]>();
		for (const [[term, ...operands], id] of this.tuples) {
			const key: [Term, ...EObject[]] = [term];
			for (let i = 0; i < operands.length; i++) {
				key.push(this.getRepresentative(operands[i]));
			}
			let group = canonical.get(key);
			if (group === undefined) {
				group = [];
				canonical.put(key, group);
			}

			group.push({ id, representative: this.getRepresentative(id) });
		}

		let madeChanges = false;
		for (const [_, members] of canonical) {
			const first = members[0];
			for (let i = 1; i < members.length; i++) {
				const second = members[i];
				if (first.representative === second.representative) {
					// They're already equal.
					continue;
				}

				const conjunctionOfOperandReasons: ReasonTree<Reason> = new ReasonTree();
				const firstDefinition = this.objectDefinition.get(first.id)!;
				const secondDefinition = this.objectDefinition.get(second.id)!;
				for (let i = 0; i < firstDefinition.operands.length; i++) {
					const a = firstDefinition.operands[i];
					const b = secondDefinition.operands[i];
					const reasonOperandEqual = this.query(a, b)!;
					conjunctionOfOperandReasons.addChild(reasonOperandEqual);
				}

				this.merge(first.id, second.id, conjunctionOfOperandReasons);
				madeChanges = true;
			}
		}
		return madeChanges;
	}

	updateCongruence(): boolean {
		let madeChanges = false;
		while (this.updateCongruenceStep()) { madeChanges = true; }
		return madeChanges;
	}

	private queryCache: Map<EObject, Map<EObject, ReasonTree<Reason>>> = new Map();

	query(a: EObject, b: EObject): null | ReasonTree<Reason> {
		if (!this.ds.compareEqual(a, b)) {
			return null;
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
