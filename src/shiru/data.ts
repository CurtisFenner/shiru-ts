/// TrieMap implements a map where keys are arrays.
/// This is implemented using a "trie" of ES6 Map objects.
export class TrieMap<KS extends readonly unknown[], V> {
	// Unfortunately, more accurate typing of this very elaborate.
	private map: Map<KS[number], TrieMap<KS, V>> = new Map();
	private value: V | undefined = undefined;

	get(key: KS, from?: number): V | undefined {
		from = from || 0;

		if (key.length === from) {
			return this.value;
		} else {
			const head = key[from];
			const child = this.map.get(head);
			if (child) {
				return child.get(key, from + 1);
			} else {
				return undefined;
			}
		}
	}

	put(key: KS, v: V, from?: number) {
		from = from || 0;
		if (key.length === from) {
			this.value = v;
		} else {
			const head = key[from];
			let child = this.map.get(head);
			if (!child) {
				child = new TrieMap;
				this.map.set(key[from], child);
			}
			child.put(key, v, from + 1);
		}
	}

	/// Iterate over [K[], V] pairs in this map.
	/// N.B.: The key array is retained and mutated by this generator, so it
	// should not be retained or modified by the caller.
	*[Symbol.iterator](progress: KS[number][] = []): Generator<[KS, V]> {
		if (this.value !== undefined) {
			yield [progress as unknown as KS, this.value];
		}
		for (let [key, tree] of this.map) {
			progress.push(key);
			yield* tree[Symbol.iterator](progress);
			progress.pop();
		}
	}
}

export class DefaultMap<K, V> {
	private map = new Map<K, V>();
	constructor(private defaulter: (k: K) => V) { }

	get(key: K): V {
		if (this.map.has(key)) {
			return this.map.get(key)!;
		} else {
			const v = this.defaulter(key);
			this.map.set(key, v);
			return v;
		}
	}

	*[Symbol.iterator]() {
		yield* this.map[Symbol.iterator]();
	}
}

interface Edge<E, K> {
	next: E,
	key: K,
};

type BFS<E, K> = { n: E, parent: null } | { n: E, parent: BFS<E, K>, key: K };

/// DisjointSet implements the "disjoint set" (a.k.a. "union find") data-
/// structure, which tracks the set of components in an undirected graph between
/// a set of integers {0, 1, 2, ... n} as edges are added.
/// This implementation is augmented with information about "keys" so that
/// queries can find a path between two nodes in the same component.
export class DisjointSet<E, K> {
	parents: Map<E, E> = new Map();
	ranks: Map<E, number> = new Map();
	outgoingEdges: Map<E, Edge<E, K>[]> = new Map();

	reset() {
		for (const [k, _] of this.parents) {
			this.parents.set(k, k);
			this.ranks.set(k, 0);
			this.outgoingEdges.set(k, []);
		}
	}

	init(e: E) {
		if (!this.parents.has(e)) {
			this.parents.set(e, e);
			this.ranks.set(e, 0);
			this.outgoingEdges.set(e, []);
		}
	}

	/// representative returns a "representative" element of the given object's
	/// equivalence class, such that two elements are members of the same
	/// equivalence class if and only if their representatives are the same.
	representative(e: E): E {
		this.init(e);
		while (true) {
			const parent = this.parents.get(e)!;
			if (parent === e) {
				break;
			}
			const grandparent = this.parents.get(parent)!;
			this.parents.set(e, grandparent);
			e = grandparent;
		}
		return e;
	}

	/// compareEqual returns whether or not the two objects are members of the
	/// same equivalence class.
	compareEqual(a: E, b: E): boolean {
		return this.representative(a) === this.representative(b);
	}

	/// explainEquality returns a sequences of keys linking the two values in
	/// the same component.
	explainEquality(a: E, b: E): K[] {
		// Perform BFS on the outgoing edges graph.
		const q: BFS<E, K>[] = [{ n: a, parent: null }];
		for (let i = 0; i < q.length; i++) {
			const top = q[i];
			if (top.n === b) {
				let keys = [];
				let c = top;
				while (c.parent) {
					keys.push(c.key);
					c = c.parent;
				}
				return keys;
			}
			for (const e of this.outgoingEdges.get(top.n)!) {
				q.push({
					n: e.next,
					parent: top,
					key: e.key,
				});
			}
		}

		throw new Error(`objects ${a} and ${b} are in different components`);
	}

	/// union updates this datastructure to join the equivalence classes of
	/// objects a and b.
	/// RETURNS false when the objects were already members of the same
	///         equivalence class.
	union(a: E, b: E, key: K): boolean {
		this.init(a);
		this.init(b);
		const ra = this.representative(a);
		const rb = this.representative(b);
		if (ra == rb) {
			return false;
		}
		this.outgoingEdges.get(a)!.push({ next: b, key: key });
		this.outgoingEdges.get(b)!.push({ next: a, key: key });

		let child: E;
		let parent: E;
		if (this.ranks.get(ra)! < this.ranks.get(rb)!) {
			child = ra;
			parent = rb;
		} else {
			child = rb;
			parent = ra;
		}

		this.parents.set(child, parent);
		if (this.ranks.get(child) === this.ranks.get(parent)) {
			this.ranks.set(parent, this.ranks.get(parent)! + 1);
		}
		return true;
	}

	/// RETURNS the set of equivalence classes managed by this data structure.
	components(): E[][] {
		let components: Map<E, E[]> = new Map();
		for (const [e, parent] of this.parents) {
			if (e === parent) {
				components.set(e, []);
			}
		}
		for (const [e, _] of this.parents) {
			components.get(this.representative(e))!.push(e);
		}
		return [...components.values()];
	}
}
