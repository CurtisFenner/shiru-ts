import { TrieMap, DisjointSet } from "./data";
import { assert } from "./test";


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

		assert(ds.union(1, 1, "a"), "is equal to", false);
		assert(ds.union(1, 2, "b"), "is equal to", true);
		assert(ds.explainEquality(1, 2), "is equal to", ["b"]);

		assert(ds.compareEqual(1, 1), "is equal to", true);
		assert(ds.compareEqual(2, 1), "is equal to", true);

		ds.union(3, 4, "c");
		ds.union(4, 5, "d");
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
	"DisjointSet-explainEquality"() {
		const ds = new DisjointSet();
		ds.union(0, 1, "a");
		ds.union(5, 4, "e");
		ds.union(1, 2, "b");
		ds.union(3, 4, "d");
		assert(new Set(ds.explainEquality(0, 2)), "is equal to", new Set(["a", "b"]));
		assert(new Set(ds.explainEquality(3, 5)), "is equal to", new Set(["d", "e"]));
		ds.union(3, 2, "c");
		assert(new Set(ds.explainEquality(0, 5)), "is equal to", new Set(["a", "b", "c", "d", "e"]));
		assert(new Set(ds.explainEquality(1, 1)), "is equal to", new Set());
	}
};
