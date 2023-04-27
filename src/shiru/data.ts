type Tail<T extends readonly unknown[]> = T extends [unknown, ... infer Tail]
	? Tail
	: never;

/**
 * TrieMap implements a map where keys are arrays (or tuples).
 * This is implemented using a "trie" of ES6 Map objects.
 */
export class TrieMap<KS extends readonly unknown[], V> {
	private map: Map<KS[number], TrieMap<KS, V>> = new Map();
	private value: V | undefined = undefined;
	size: number = 0;

	/**
	 * Note that the returned map should NOT be mutated.
	 */
	getSuffixes(key: KS[0]): TrieMap<Tail<KS>, V> | undefined {
		const at = this.map.get(key);
		if (at === undefined) {
			return undefined;
		}
		return at as unknown as TrieMap<Tail<KS>, V>;
	}

	get(key: KS, from: number = 0): V | undefined {
		let cursor: TrieMap<KS, V> | undefined = this;
		while (from < key.length) {
			const head = key[from];
			cursor = cursor.map.get(head);
			if (cursor === undefined) {
				return undefined;
			}

			from += 1;
		}
		return cursor.value;
	}

	put(key: KS, v: V, from: number = 0): number {
		if (key.length === from) {
			const count = this.value === undefined ? 1 : 0;
			this.value = v;
			return count;
		}

		const head = key[from];
		let child = this.map.get(head);
		if (child === undefined) {
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

	/**
	 * Iterate over [K[], V] pairs in this map.
	 * 
	 * Warning: The key array is retained and mutate by this generator, so it
	 * should not be retained or modified by the caller.
	 */
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

/**
 * DisjointSet implements the "disjoint set" (a.k.a "union find")
 * data-structure, which tracks the set of components in an undirected graph as
 * edges are added.
 */
export class DisjointSet<E> {
	parents: Map<E, E> = new Map();
	ranks: Map<E, number> = new Map();

	reset() {
		this.parents.clear();
		this.ranks.clear();
	}

	init(e: E) {
		if (!this.parents.has(e)) {
			this.parents.set(e, e);
			this.ranks.set(e, 0);
		}
	}

	/**
	 * representative returns a "representative" element of the given object's
	 * equivalence class, such that two elements are members of the same
	 * equivalence class if and only if their representatives are the same.
	 * 
	 * After a union is performed, the new representative will be the
	 * former representative of the unioned elements.
	 */
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

	/**
	 * compareEqual returns whether the two objects are members of the same
	 * equivalence class.
	 */
	compareEqual(a: E, b: E): boolean {
		return this.representative(a) === this.representative(b);
	}

	/**
	 * union updates this data-structure to merge the equivalence classes of a
	 * and b.
	 * 
	 * returns false when the objects were already members of the same
	 * equivalence class.
	 */
	union(a: E, b: E): boolean {
		this.init(a);
		this.init(b);
		const ra = this.representative(a);
		const rb = this.representative(b);

		if (ra == rb) {
			return false;
		}

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

	/**
	 * components returns the set of equivalence classes managed by this
	 * data-structure.
	 */
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

export class TreeBag<T> {
	readonly size: number;
	private constructor(private list: T[], private children: TreeBag<T>[] | null) {
		let childrenSizes = 0;
		if (children !== null) {
			for (const child of children) {
				childrenSizes += child.size;
			}
		}
		this.size = list.length + childrenSizes;
	}

	static of<T>(...ts: T[]) {
		return new TreeBag([...ts], null);
	}

	union(other: TreeBag<T>): TreeBag<T> {
		if (other.size === 0) {
			return this;
		} else if (this.size === 0) {
			return other;
		} else if (this.size + other.size < 9) {
			return new TreeBag([...this, ...other], null);
		}
		return new TreeBag([], [this, other]);
	}

	*[Symbol.iterator](): Iterator<T> {
		if (this.children !== null) {
			while (this.children.length > 0) {
				this.list.push(...this.children.pop()!);
			}
			this.children = null;
		}
		yield* this.list;
	}
}

export function* zipMaps<K, A, B>(
	left: Map<K, A>,
	right: Map<K, B>,
): Generator<[K, A | undefined, B | undefined]> {
	for (const key of left.keys()) {
		yield [key, left.get(key), right.get(key)];
	}
	for (const key of right.keys()) {
		if (!left.has(key)) {
			yield [key, undefined, right.get(key)!];
		}
	}
}
