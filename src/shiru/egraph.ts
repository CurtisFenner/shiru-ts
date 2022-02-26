import { DefaultMap, DisjointSet, TrieMap } from "./data";

export type EObject = symbol & { __brand: "EObject" };

export type EClassDescription<Term> = {
	members: { id: EObject, term: Term, operands: EObject[] }[],
	representative: EObject,
};

/// An "equivalence-graph", loosely inspired by "egg (e-graphs good)".
export class EGraph<Term, Tag, Reason> {
	/// `tagged.get(tag).get(rep)` is the set of IDs tagged with `tag` that are
	/// equal to representative `rep`.
	private tagged = new DefaultMap<Tag, DefaultMap<EObject, Set<EObject>>>(t => new DefaultMap(r => new Set()));
	private taggedDef = new Map<EObject, { term: Term, operands: EObject[], tag: Tag }>();

	private tuples: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();
	private objectDefinition: Map<EObject, { term: Term, operands: EObject[], uniqueObjectCount: number }> = new Map();
	private ds: DisjointSet<EObject, Set<Reason>> = new DisjointSet();

	reset(): void {
		this.ds.reset();
		this.queryCache = new Map();
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

	getTagged(tag: Tag, id: EObject): Array<{ id: EObject, term: Term, operands: EObject[] }> {
		const out = [];
		const representative = this.ds.representative(id);
		for (const tagged of this.tagged.get(tag).get(representative)) {
			const def = this.taggedDef.get(tagged)!;
			out.push({ id: tagged, term: def.term, operands: def.operands });
		}
		return out;
	}

	private uniqueObjectCount = 1;

	hasStructure(term: Term, operands: EObject[]): EObject | null {
		const tuple: [Term, ...EObject[]] = [term, ...operands];
		return this.tuples.get(tuple) || null;
	}

	debugSymbolNames = true;

	add(term: Term, operands: EObject[], tag?: Tag, hint?: string): EObject {
		for (let i = 0; i < operands.length; i++) {
			if (operands[i] === undefined) {
				throw new Error("EGraph.add: unexpected undefined at index `" + i + "` for term `" + String(term) + "`");
			}
		}

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
			if (tag !== undefined) {
				this.tagged.get(tag).get(id).add(id);
				this.taggedDef.set(id, { term, operands, tag });
			}
			return id;
		}
	}

	/// `reason` is a conjunction of `Reason`s.
	/// merge(a, b, reason) returns false when this fact was already present in
	/// this egrahp.
	merge(a: EObject, b: EObject, reason: Set<Reason>): boolean {
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

				const conjunctionOfOperandReasons: Set<Reason> = new Set();
				const firstDefinition = this.objectDefinition.get(first.id)!;
				const secondDefinition = this.objectDefinition.get(second.id)!;
				for (let i = 0; i < firstDefinition.operands.length; i++) {
					const a = firstDefinition.operands[i];
					const b = secondDefinition.operands[i];
					const reasonOperandEqual = this.query(a, b)!
					for (const r of reasonOperandEqual) {
						conjunctionOfOperandReasons.add(r);
					}
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

	private queryCache: Map<EObject, Map<EObject, Set<Reason>>> = new Map();

	query(a: EObject, b: EObject): null | Set<Reason> {
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
		const all = new Set<Reason>();
		for (const list of seq) {
			for (const el of list) {
				all.add(el);
			}
		}

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
