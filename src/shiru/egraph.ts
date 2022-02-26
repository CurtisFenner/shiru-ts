import { DefaultMap, DisjointSet, TrieMap } from "./data";

export type EObject = symbol & { __brand: "EObject" };

export type EClassDescription<Term> = {
	members: { id: EObject, term: Term, operands: EObject[] }[]
};

/// An "equivalence-graph", loosely inspired by "egg (e-graphs good)".
export class EGraph<Term, Tag, Reason> {
	/// `tagged.get(tag).get(rep)` is the set of IDs tagged with `tag` that are
	/// equal to representative `rep`.
	private tagged = new DefaultMap<Tag, DefaultMap<EObject, Set<EObject>>>(t => new DefaultMap(r => new Set()));
	private taggedDef = new Map<EObject, { term: Term, operands: EObject[], tag: Tag }>();

	private tuples: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();
	private ds: DisjointSet<EObject, Set<Reason>> = new DisjointSet();

	reset(): void {
		this.ds.reset();
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

	add(term: Term, operands: EObject[], tag?: Tag, hint?: string): EObject {
		const tuple: [Term, ...EObject[]] = [term, ...operands];
		const existing = this.tuples.get(tuple);
		if (existing) {
			return existing;
		} else {
			const id: EObject = Symbol("egraph-term(" + hint + ")") as EObject;
			this.tuples.put(tuple, id);
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
		const canonical = new TrieMap<[Term, ...EObject[]], { id: EObject, reason: Set<Reason> }[]>();
		for (const [[term, ...operands], id] of this.tuples) {
			const representatives = operands.map(x => this.ds.representative(x));
			const reason = new Set<Reason>();
			for (let i = 0; i < representatives.length; i++) {
				const representative = representatives[i];
				const original = operands[i];
				const explanation = this.query(representative, original)!;
				for (const r of explanation) {
					reason.add(r);
				}
			}
			const key: [Term, ...EObject[]] = [term, ...representatives];
			let group = canonical.get(key);
			if (group === undefined) {
				group = [];
				canonical.put(key, group);
			}
			group.push({ id, reason });
		}

		let madeChanges = false;
		for (const [_, members] of canonical) {
			if (members.length < 2) {
				continue;
			}
			const first = members[0];
			for (let i = 1; i < members.length; i++) {
				const second = members[i];
				if (this.ds.representative(first.id) === this.ds.representative(second.id)) {
					// They're already equal.
					continue;
				}
				const reason = new Set([...first.reason, ...second.reason]);
				this.merge(first.id, second.id, reason);
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

	query(a: EObject, b: EObject): null | Set<Reason> {
		if (!this.ds.compareEqual(a, b)) {
			return null;
		}
		const seq = this.ds.explainEquality(a, b);
		const all = new Set<Reason>();
		for (const list of seq) {
			for (const el of list) {
				all.add(el);
			}
		}
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
				eclass = { members: [] };
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
