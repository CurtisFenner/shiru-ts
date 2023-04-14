import { TrieMap, DisjointSet } from "./data.js";
import { assert } from "./test.js";

export const tests = {
	"TrieMap-basic"() {
		const map: TrieMap<number[], string> = new TrieMap();

		assert(map.get([]), "is equal to", undefined);
		assert(map.get([0]), "is equal to", undefined);
		assert(map.get([1, 2, 3]), "is equal to", undefined);

		map.put([1, 2, 3], "three");
		map.put([1, 2, 3, 4], "four");
		map.put([1, 2, 5], "five");
		map.put([3], "gamma");

		assert(map.get([]), "is equal to", undefined);
		assert(map.get([1, 2]), "is equal to", undefined);
		assert(map.get([1, 2, 3]), "is equal to", "three");
		assert(map.get([1, 2, 3, 4]), "is equal to", "four");
		assert(map.get([1, 2, 4]), "is equal to", undefined);
		assert(map.get([1, 2, 5]), "is equal to", "five");
		assert(map.get([3]), "is equal to", "gamma");

		map.put([], "empty");
		assert(map.get([]), "is equal to", "empty");

		map.put([], "empty2");
		map.put([1, 2, 3], "three2");

		assert(map.get([]), "is equal to", "empty2");
		assert(map.get([1, 2, 3]), "is equal to", "three2");
		assert(map.get([1, 2, 3, 4]), "is equal to", "four");
		assert(map.get([1, 2, 5]), "is equal to", "five");

		const pairs = [];
		for (let [k, v] of map) {
			pairs.push([k.slice(0), v]);
		}
		assert(pairs, "is equal to", [
			[[], "empty2"],
			[[1, 2, 3], "three2"],
			[[1, 2, 3, 4], "four"],
			[[1, 2, 5], "five"],
			[[3], "gamma"],
		]);
	},
	"DisjointSet-basic"() {
		const ds = new DisjointSet();
		assert(ds.compareEqual(0, 0), "is equal to", true);
		assert(ds.representative(0), "is equal to", 0);
		assert(ds.compareEqual(1, 2), "is equal to", false);
		assert(ds.compareEqual(1, 1), "is equal to", true);

		assert(ds.union(1, 1), "is equal to", false);
		assert(ds.union(1, 2), "is equal to", true);
		assert(ds.compareEqual(1, 2), "is equal to", true);

		assert(ds.compareEqual(1, 1), "is equal to", true);
		assert(ds.compareEqual(2, 1), "is equal to", true);

		ds.union(3, 4);
		ds.union(4, 5);
		assert(ds.compareEqual(3, 4), "is equal to", true);
		assert(ds.compareEqual(5, 4), "is equal to", true);
		assert(ds.compareEqual(1, 3), "is equal to", false);
		assert(ds.representative(3), "is equal to", ds.representative(5));

		assert(ds.components(), "is equal to", [
			[0],
			[1, 2],
			[3, 4, 5],
		]);
	},
	"DisjointSet-basic-explainEquality"() {
		const ds = new DisjointSet();
		ds.union(0, 1);
		ds.union(5, 4);
		ds.union(1, 2);
		ds.union(3, 4);
		assert(ds.compareEqual(0, 2), "is equal to", true);
		assert(ds.compareEqual(3, 5), "is equal to", true);
		ds.union(3, 2);
		assert(ds.compareEqual(0, 5), "is equal to", true);
		assert(ds.compareEqual(1, 1), "is equal to", true);
	},
	"DisjointSet-explainEquality-efficient"() {
		const ds = new DisjointSet();

		const count = 1000;
		for (let i = 0; i < count; i++) {
			ds.union(i, i + 1);
		}

		// Querying this should be almost instant.
		const reason = ds.compareEqual(0, count);
		assert(reason, "is equal to", true);

		for (let i = 0; i < count; i++) {
			const reason = ds.compareEqual(i, count - 1 - i);
			assert(reason, "is equal to", true);
		}
	},
};
