/// TrieMap implements a map where keys are arrays.
/// This is implemented using a "trie" of ES6 Map objects.
export class TrieMap<KS extends readonly unknown[], V> {
	// Unfortunately, more accurate typing of this very elaborate.
	private map: Map<KS[number], TrieMap<KS, V>> = new Map();
	private value: V | undefined = undefined;
	size: number = 0;

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

	put(key: KS, v: V, from?: number): number {
		from = from || 0;
		if (key.length === from) {
			const count = this.value === undefined ? 1 : 0;
			this.value = v;
			return count;
		}

		const head = key[from];
		let child = this.map.get(head);
		if (!child) {
			child = new TrieMap();
			this.map.set(key[from], child);
		}

		const change = child.put(key, v, from + 1);
		this.size += change;
		return change;
	}

	clear(): void {
		this.map.clear();
		this.size = 0;
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

	clear(): void {
		this.map.clear();
	}

	*[Symbol.iterator]() {
		yield* this.map[Symbol.iterator]();
	}
}

type BFS<E> = { n: E, parent: null } | { n: E, parent: BFS<E> };

/// DisjointSet implements the "disjoint set" (a.k.a. "union find") data-
/// structure, which tracks the set of components in an undirected graph between
/// a set of integers {0, 1, 2, ... n} as edges are added.
/// This implementation is augmented with information about "keys" so that
/// queries can find a path between two nodes in the same component.
export class DisjointSet<E, K> {
	parents: Map<E, E> = new Map();
	ranks: Map<E, number> = new Map();

	/// outgoingEdges is a tree, including only edges that bridge previously
	/// separated components.
	outgoingEdges: Map<E, Map<E, K>> = new Map();

	/// neighbors is a full graph, including all edges added by union().
	neighbors: Map<E, Map<E, K>> = new Map();

	reset() {
		this.neighbors.clear();
		this.parents.clear();
		this.ranks.clear();
		this.outgoingEdges.clear();
	}

	init(e: E) {
		if (!this.parents.has(e)) {
			this.parents.set(e, e);
			this.ranks.set(e, 0);
			this.outgoingEdges.set(e, new Map());
			this.neighbors.set(e, new Map());
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
		if (a === b) {
			return [];
		}

		const fastReason = this.neighbors.get(a)?.get(b);
		if (fastReason !== undefined) {
			return [fastReason];
		}

		// Perform BFS on the outgoing edges graph.
		const q: BFS<E>[] = [{ n: a, parent: null }];
		for (let i = 0; i < q.length; i++) {
			const top = q[i];
			for (const next of this.outgoingEdges.get(top.n)!.keys()) {
				// The outgoingEdges graph is strictly a tree, so we can avoid
				// using a set for visited edges by simply skipping edges that
				// go directly backward.
				const isBackEdge = next === top.parent?.n;
				if (!isBackEdge) {
					const edge = {
						n: next,
						parent: top,
					};

					if (next === b) {
						let keys = [];
						let c: BFS<E> = edge;
						while (c.parent) {
							const key = this.outgoingEdges.get(c.parent.n)!.get(c.n)!;
							keys.push(key);
							c = c.parent;
						}
						return keys;
					}

					q.push(edge);
				}
			}
		}

		throw new Error(`objects ${String(a)} and ${String(b)} are in different components`);
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

		if (!this.neighbors.get(a)!.has(b)) {
			this.neighbors.get(a)!.set(b, key);
			this.neighbors.get(b)!.set(a, key);
		}

		if (ra == rb) {
			return false;
		}
		this.outgoingEdges.get(a)!.set(b, key);
		this.outgoingEdges.get(b)!.set(a, key);

		let child: E;
		let parent: E;
		const rankA = this.ranks.get(ra)!;
		const rankB = this.ranks.get(rb)!;
		if (rankA < rankB) {
			child = ra;
			parent = rb;
		} else {
			child = rb;
			parent = ra;
		}

		this.parents.set(child, parent);
		if (rankA === rankB) {
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
