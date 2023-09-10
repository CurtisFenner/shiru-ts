import { DefaultMap, DisjointSet } from "./data.js";

type Dependency<T> = {
	left: T,
	right: T,
};

type Neighbor<T, R> = {
	from: T,
	to: T,
	r: R | null,
	dependencies: Dependency<T>[],
	time: number,
}

/**
 * Components is a disjoint-set data-structure augmented with path information.
 * 
 * These paths can be used to "explain" how two elements came to be in the same
 * equivalence class.
 */
export class Components<T, R, Data> {
	private disjointSet: DisjointSet<T, Data>;
	private time = 1;
	private outEdge = new DefaultMap<T, Neighbor<T, R>[]>(key => []);

	constructor(
		initialDataFor: (e: T) => Data,
		mergeDataFor: (childData: Data, parentData: Data) => Data,
	) {
		this.disjointSet = new DisjointSet<T, Data>(initialDataFor, mergeDataFor);
	}

	getData(e: T): Data {
		return this.disjointSet.getData(e);
	}

	reset() {
		this.disjointSet.reset();
		this.time = 1;
		this.outEdge.clear();
	}

	representative(t: T): T {
		return this.disjointSet.representative(t);
	}

	areCongruent(a: T, b: T): boolean {
		return this.disjointSet.compareEqual(a, b);
	}

	/**
	 * @return which object would be the new representative of a and b if
	 * addCongruence(a, b, ...) was invoked in the current state.
	 */
	predictRepresentativeOfMerge(a: T, b: T): { child: T, parent: T } {
		const { child, parent } = this.disjointSet.chooseParent(a, b);
		return { child, parent };
	}

	mergeData(e: T, data: Data): Data {
		return this.disjointSet.unionData(e, data);
	}

	addCongruence(a: T, b: T, r: R | null, dependencies: { left: T, right: T }[]): number {
		const queryTime = this.time;
		const newTime = queryTime + 1;

		if (this.areCongruent(a, b)) {
			return queryTime;
		}

		this.outEdge.get(a).push({
			from: a,
			to: b,
			r,
			dependencies,
			time: newTime,
		});
		this.outEdge.get(b).push({
			from: b,
			to: a,
			r,
			dependencies,
			time: newTime,
		});
		this.disjointSet.union(a, b);

		this.time = newTime;
		return newTime;
	}

	findPathAtTime(
		dependency: Dependency<T>,
		time: number,
	): { rs: R[], dependencies: { time: number, dependencies: Dependency<T>[] }[] } | null {
		if (dependency.left === dependency.right) {
			return { rs: [], dependencies: [] };
		}

		const frontiers: { sources: ("left" | "right")[], values: T[] }[] = [];
		let frontierTotal = 0;
		for (let i = 0; i < 10; i++) {
			frontiers.push({ sources: [], values: [] });
		}

		const push = (node: T, source: "left" | "right"): void => {
			frontierTotal += 1;
			const neighbors = this.outEdge.get(node);
			let size = neighbors.length >> 2;
			for (let i = 0; true; i++) {
				size = size >> 2;
				if (size === 0) {
					const frontier = frontiers[i];
					frontier.sources.push(source);
					frontier.values.push(node);
					return;
				}
			}
		};

		push(dependency.left, "left");
		push(dependency.right, "right");

		const leftParent = new Map<T, Neighbor<T, R> | null>();
		const rightParent = new Map<T, Neighbor<T, R> | null>();
		leftParent.set(dependency.left, null);
		rightParent.set(dependency.right, null);

		let cursor = 0;
		let collision: T | null = null;
		while (frontierTotal !== 0) {
			let frontier;
			for (let k = 0; true; k++) {
				if (frontiers[k].values.length !== 0) {
					frontier = frontiers[k];
					break;
				}
			}
			const front = frontier.values.pop()!;
			const source = frontier.sources.pop()!;
			frontierTotal -= 1;

			const parent = source === "left" ? leftParent : rightParent;
			cursor += 1;

			const neighbors = this.outEdge.get(front);
			for (let i = 0; i < neighbors.length; i++) {
				const neighbor = neighbors[i];
				if (time < neighbor.time) {
					// This edge (and later edges) were added AFTER the query time.
					break;
				}

				if (parent.has(neighbor.to)) {
					// A shorter path to this node from this source has already
					// been found.
					continue;
				}
				parent.set(neighbor.to, neighbor);
				push(neighbor.to, source);

				const otherParent = source === "left" ? rightParent : leftParent;
				if (otherParent.has(neighbor.to)) {
					// A path has been found!
					collision = neighbor.to;
					frontierTotal = 0;
					break;
				}
			}
		}

		if (collision === null) {
			return null;
		}
		const rs: R[] = [];
		const ds: { time: number, dependencies: Dependency<T>[] }[] = [];
		for (const parent of [leftParent, rightParent]) {
			let node: T = collision;
			while (true) {
				const edge = parent.get(node);
				if (edge === null) {
					break;
				} else if (edge === undefined) {
					throw new Error("findPathAtTime: ICE, no path");
				}

				if (edge.r !== null) {
					rs.push(edge.r);
				}

				if (edge.dependencies.length !== 0) {
					// The time to search for the dependencies must be strictly BEFORE
					// this edge was added.
					ds.push({ time: edge.time - 1, dependencies: edge.dependencies });
				}

				node = edge.from;
			}
		}

		return { rs, dependencies: ds };
	}

	findPath(initialLeft: T, initialRight: T, initialTime = this.time): Set<R> | null {
		if (initialLeft === initialRight) {
			return new Set();
		}

		const q: { time: number, dependencies: Dependency<T>[] }[] = [
			{
				time: initialTime,
				dependencies: [{ left: initialLeft, right: initialRight }],
			},
		];

		const enqueued = new DefaultMap<T, Map<T, number>>(() => new Map());

		let steps = 0;
		const path = new Set<R>();
		while (q.length !== 0) {
			const top = q.pop()!;
			for (const dependency of top.dependencies) {
				steps += 1;
				const answer = this.findPathAtTime(dependency, top.time);
				if (answer === null) {
					return null;
				}

				for (const r of answer.rs) {
					path.add(r);
				}
				for (const children of answer.dependencies) {
					for (const child of children.dependencies) {
						if (child.left === child.right) {
							continue;
						}

						const prior = enqueued.get(child.left).get(child.right);
						if (prior === undefined || prior > children.time) {
							enqueued.get(child.left).set(child.right, children.time);
							enqueued.get(child.right).set(child.left, children.time);
							q.push({ time: children.time, dependencies: [child] });
						}
					}
				}
			}
		}

		return path;
	}
}
