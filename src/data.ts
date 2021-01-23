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

interface Edge<K> {
	next: number,
	key: K,
};

type BFS<K> = { n: number, parent: null } | { n: number, parent: BFS<K>, key: K };

/// DisjointSet implements the "disjoint set" (a.k.a. "union find") data-
/// structure, which tracks the set of components in an undirected graph between
/// a set of integers {0, 1, 2, ... n} as edges are added.
/// This implementation is augmented with information about "keys" so that 
/// queries can find a path between two nodes in the same component.
export class DisjointSet<K> {
	parents: number[] = [];
	ranks: number[] = [];
	outgoingEdges: Edge<K>[][] = [];

	expandTo(n: number) {
		for (let i = this.parents.length; i <= n; i++) {
			this.parents.push(i);
			this.ranks.push(0);
			this.outgoingEdges.push([]);
		}
	}

	/// representative returns a "representative" element of the given object's
	/// equivalence class, such that two elements are members of the same 
	/// equivalence class if and only if their representatives are the same.
	representative(n: number): number {
		this.expandTo(n);
		while (this.parents[n] !== n) {
			// "Path halving"
			this.parents[n] = this.parents[this.parents[n]];
			n = this.parents[n];
		}
		return n;
	}

	/// compareEqual returns whether or not the two objects are members of the
	/// same equivalence class.
	compareEqual(a: number, b: number): boolean {
		return this.representative(a) === this.representative(b);
	}

	/// explainEquality returns a sequences of keys linking the two values in
	/// the same component.
	explainEquality(a: number, b: number): K[] {
		// Perform BFS on the outgoing edges graph.
		const q: BFS<K>[] = [{ n: a, parent: null }];
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
			for (let e of this.outgoingEdges[top.n]) {
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
	union(a: number, b: number, key: K): boolean {
		this.expandTo(a < b ? b : a);
		const ra = this.representative(a);
		const rb = this.representative(b);
		if (ra == rb) {
			return false;
		}
		this.outgoingEdges[a].push({ next: b, key: key });
		this.outgoingEdges[b].push({ next: a, key: key });

		let child: number;
		let parent: number;

		if (this.ranks[ra] < this.ranks[rb]) {
			child = ra;
			parent = rb;
		} else {
			child = rb;
			parent = ra;
		}

		this.parents[child] = parent;
		if (this.ranks[child] === this.ranks[parent]) {
			this.ranks[parent] += 1;
		}
		return true;
	}

	/// RETURNS the set of equivalence classes managed by this data structure.
	components(): number[][] {
		let components: number[][] = [];
		for (let i = 0; i < this.parents.length; i++) {
			components.push([]);
		}
		for (let i = 0; i < this.parents.length; i++) {
			components[this.parents[i]].push(i);
		}
		let out: number[][] = [];
		for (let i = 0; i < components.length; i++) {
			if (components[i].length !== 0) {
				out.push(components[i]);
			}
		}
		return out;
	}
}
