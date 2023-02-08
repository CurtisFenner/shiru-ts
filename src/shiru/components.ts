import { DefaultMap, DisjointSet } from "./data";

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

export class Components<T, R> {
	private disjointSet = new DisjointSet<T, null>();
	private time = 1;
	private outEdge = new DefaultMap<T, Neighbor<T, R>[]>(key => [])

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
		this.disjointSet.union(a, b, null);

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

		const frontier = [dependency.left, dependency.right];
		const frontierSource = ["left", "right"];

		const leftParent = new Map<T, Neighbor<T, R> | null>();
		const rightParent = new Map<T, Neighbor<T, R> | null>();
		leftParent.set(dependency.left, null);
		rightParent.set(dependency.right, null);

		let cursor = 0;
		while (cursor < frontier.length) {
			const front = frontier[cursor];
			const source = frontierSource[cursor];
			cursor += 1;

			const neighbors = this.outEdge.get(front);
			for (let i = 0; i < neighbors.length; i++) {
				const neighbor = neighbors[i];
				if (time < neighbor.time) {
					// This edge (and later edges) were added AFTER the query time.
					break;
				}

				const parent = source === "left" ? leftParent : rightParent;
				if (parent.has(neighbor.to)) {
					// A shorter path to this node from this source has already
					// been found.
					continue;
				}
				parent.set(neighbor.to, neighbor);
				frontier.push(neighbor.to);
				frontierSource.push(source);

				const otherParent = source === "left" ? rightParent : leftParent;
				if (otherParent.has(neighbor.to)) {
					// A path has been found!
					const rs: R[] = [];
					const ds: { time: number, dependencies: Dependency<T>[] }[] = [];
					for (const parent of [leftParent, rightParent]) {
						let node = neighbor.to;
						while (true) {
							const edge = parent.get(node);
							if (edge === null) {
								break;
							} else if (edge === undefined) {
								throw new Error("findPathAtTime: ICE, no path");
							}

							if (edge.r !== null) {
								// For efficiency, don't include null reasons.
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
			}
		}
		return null;
	}

	findPath(initialLeft: T, initialRight: T, initialTime = this.time): Set<R> | null {
		const q: { time: number, dependencies: Dependency<T>[] }[] = [
			{
				time: initialTime,
				dependencies: [{ left: initialLeft, right: initialRight }],
			},
		];

		const path = new Set<R>();
		while (q.length !== 0) {
			const top = q.pop()!;
			for (const dependency of top.dependencies) {
				const answer = this.findPathAtTime(dependency, top.time);
				if (answer === null) {
					return null;
				}

				for (const r of answer.rs) {
					path.add(r);
				}
				q.push(...answer.dependencies);
			}
		}

		return path;
	}
}
