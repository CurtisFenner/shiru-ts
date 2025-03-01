type Tail<T extends readonly unknown[]> = T extends [unknown, ... infer Tail]
	? Tail
	: never;

export function sortedBy<T, K extends unknown[]>(
	array: T[],
	ranking: (element: T) => K,
): T[] {
	const ranks = array.map((e, i) => ({ rank: ranking(e), i }));
	ranks.sort((a, b) => {
		for (let i = 0; i < a.rank.length && i < b.rank.length; i++) {
			const left = a.rank[i] as any;
			const right = b.rank[i] as any;
			if (left < right) {
				return -1;
			} else if (right < left) {
				return 1;
			}
		}
		return a.rank.length - b.rank.length;
	});
	return ranks.map(x => array[x.i]);
}

export type BitSet = bigint & { __brand: "solver.BitSet" };
export type BitSet16 = BitSet & { __brand2: "solver.BitSet16" };

export function bitsetLeast16(n: bigint): BitSet16 {
	return BigInt.asUintN(16, n) as BitSet16;
}

export function bitset16LeastSignificantBit(n: BitSet16): number {
	if (n & 0b0000_0000_0000_0001n) return 0;
	if (n & 0b0000_0000_0000_0010n) return 1;
	if (n & 0b0000_0000_0000_0100n) return 2;
	if (n & 0b0000_0000_0000_1000n) return 3;
	if (n & 0b0000_0000_0001_0000n) return 4;
	if (n & 0b0000_0000_0010_0000n) return 5;
	if (n & 0b0000_0000_0100_0000n) return 6;
	if (n & 0b0000_0000_1000_0000n) return 7;
	if (n & 0b0000_0001_0000_0000n) return 8;
	if (n & 0b0000_0010_0000_0000n) return 9;
	if (n & 0b0000_0100_0000_0000n) return 10;
	if (n & 0b0000_1000_0000_0000n) return 11;
	if (n & 0b0001_0000_0000_0000n) return 12;
	if (n & 0b0010_0000_0000_0000n) return 13;
	if (n & 0b0100_0000_0000_0000n) return 14;
	return 15;
}

export function bitsetIntersect(a: BitSet, b: BitSet): BitSet {
	return (a & b) as BitSet;
}

export function bitsetUnion(a: BitSet, b: BitSet): BitSet {
	return (a | b) as BitSet;
}

export function bitsetSingleton(index: number): BitSet {
	return 1n << BigInt(index) as BitSet;
}

export function bitsetMinus(a: BitSet, b: BitSet): BitSet {
	return (a & ~b) as BitSet;
}

export const bitsetEmpty = 0n as BitSet;

export function bitsetLeastSignificantBit(n: BitSet): number {
	if (n <= bitsetEmpty) {
		return -1;
	}

	let shifting: bigint = n;
	for (let limbStart = 0; true; limbStart += 16) {
		const masked = bitsetLeast16(shifting);
		if (masked !== 0n) {
			return limbStart + bitset16LeastSignificantBit(masked);
		}
		shifting = shifting >> 16n;
	}
}

/**
 * TrieMap implements a map where keys are arrays (or tuples).
 * This is implemented using a "trie" of ES6 Map objects.
 */
export class TrieMap<KS extends readonly unknown[], V> {
	private map: Map<KS[number], TrieMap<KS, V>> = new Map();
	private value: V | undefined = undefined;
	size: number = 0;

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
export class DisjointSet<E, Data> {
	private parents: Map<E, E> = new Map();
	private ranks: Map<E, number> = new Map();
	private data: Map<E, Data> = new Map();

	constructor(
		private initialDataFor: (e: E) => Data,
		private mergeDataFor: (childData: Data, parentData: Data) => Data,
	) { }

	reset() {
		this.parents.clear();
		this.ranks.clear();
		this.data.clear();
	}

	init(e: E) {
		if (!this.parents.has(e)) {
			this.parents.set(e, e);
			this.ranks.set(e, 0);
			this.data.set(e, this.initialDataFor(e));
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
	 * @return which object would be the new representative and old
	 * representative if union(a, b) was invoked in the current state.
	 */
	chooseParent(a: E, b: E): { child: E, parent: E, childRank: number, parentRank: number } {
		const ra = this.representative(a);
		const rb = this.representative(b);
		const rankA = this.ranks.get(ra)!;
		const rankB = this.ranks.get(rb)!;
		if (rankA < rankB) {
			return {
				child: ra,
				parent: rb,
				childRank: rankA,
				parentRank: rankB,
			};
		} else {
			return {
				child: rb,
				parent: ra,
				childRank: rankB,
				parentRank: rankA,
			};
		}
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

		const { child, parent, childRank, parentRank } = this.chooseParent(a, b);

		this.parents.set(child, parent);
		if (childRank === parentRank) {
			this.ranks.set(parent, this.ranks.get(parent)! + 1);
		}

		const dataChild = this.data.get(child)!;
		this.unionData(parent, dataChild);
		return true;
	}

	getData(e: E): Data {
		const representative = this.representative(e);
		return this.data.get(representative)!;
	}

	unionData(e: E, data: Data): Data {
		const merged = this.mergeDataFor(this.getData(e), data);
		this.data.set(this.representative(e), merged);
		return merged;
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

export function measureCommonPrefix<T>(a: T[], b: T[]): number {
	const length = Math.min(a.length, b.length);
	for (let i = 0; i < length; i++) {
		if (a[i] !== b[i]) {
			return i;
		}
	}
	return length;
}

export function nonEmptyPath<Node, E>(
	digraphOutEdges: DefaultMap<Node, { arrowTruth: E[], target: Node }[]>,
	source: Node,
	target: Node,
): E[] | null {
	const reached = new Map<Node, { parent: Node, arrowTruth: E[] }>();
	const frontier = [source];

	while (frontier.length !== 0) {
		const top = frontier.pop()!;
		const outEdges = digraphOutEdges.get(top);
		for (const outEdge of outEdges) {
			if (reached.has(outEdge.target)) {
				continue;
			}
			reached.set(outEdge.target, { parent: top, arrowTruth: outEdge.arrowTruth });
			if (outEdge.target === target) {
				// Follow the path backwards to construct the full set of
				// inequalities that were followed.
				const out: E[] = [...outEdge.arrowTruth];
				let cursor: Node = top;
				while (cursor !== source) {
					const parent = reached.get(cursor);
					if (parent === undefined) {
						break;
					}
					out.push(...parent.arrowTruth);
					cursor = parent.parent;
				}
				return out;
			}
			frontier.push(outEdge.target);
		}
	}
	return null;
}
