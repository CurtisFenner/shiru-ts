import { Components } from "./components.js";
import { assert, specPredicate, specSetEq } from "./test.js";

export const tests = {
	"simple-search"() {
		const cs = new Components<string, number>();
		const addAB = cs.addCongruence("alpha", "beta", 100, []);
		const addBG = cs.addCongruence("beta", "gamma", 200, []);
		const addGD = cs.addCongruence("delta", "gamma", 300, []);

		assert(cs.areCongruent("alpha", "delta"), "is equal to", true);
		assert(cs.areCongruent("gamma", "beta"), "is equal to", true);
		assert(cs.areCongruent("delta", "beta"), "is equal to", true);
		assert(cs.areCongruent("delta", "alpha"), "is equal to", true);

		assert(cs.findPathAtTime({ left: "alpha", right: "beta" }, 0), "is equal to", null);
		assert(cs.findPathAtTime({ left: "alpha", right: "beta" }, addAB), "is equal to", {
			rs: [100],
			dependencies: [],
		});

		assert(cs.findPathAtTime({ left: "alpha", right: "delta" }, addGD - 0.1), "is equal to", null);
		assert(cs.findPathAtTime({ left: "alpha", right: "delta" }, addGD), "is equal to", {
			rs: specSetEq([100, 200, 300]),
			dependencies: [],
		});
		assert(addAB <= addBG, "is equal to", true);
		assert(addBG <= addGD, "is equal to", true);

		cs.reset();
		assert(cs.areCongruent("alpha", "beta"), "is equal to", false);
		assert(cs.findPathAtTime({ left: "alpha", right: "beta" }, addGD), "is equal to", null);
	},
	"simple-dependencies"() {
		const cs = new Components<string, number>();
		const addAB = cs.addCongruence("a", "b", 100, []);
		assert(cs.areCongruent("f(a)", "f(b)"), "is equal to", false);
		const addFAFB = cs.addCongruence("f(a)", "f(b)", 200, [{ left: "a", right: "b" }]);
		assert(cs.areCongruent("f(a)", "f(b)"), "is equal to", true);
		assert(cs.findPathAtTime({ left: "f(a)", right: "f(b)" }, addAB), "is equal to", null);

		const d = cs.findPathAtTime({ left: "f(a)", right: "f(b)" }, addFAFB);
		assert(d, "is equal to", {
			rs: [200],
			dependencies: [
				{
					time: specPredicate(x => addAB <= x && x < addFAFB ? true : []),
					dependencies: [{ left: "a", right: "b" }],
				},
			],
		});
		assert(cs.findPathAtTime({ left: "f(a)", right: "f(b)" }, d!.dependencies[0].time), "is equal to", null);

		const recursivePath1 = cs.findPath("f(a)", "f(b)");
		assert(recursivePath1, "is equal to", new Set([100, 200]));

		const recursivePath2 = cs.findPath("a", "b");
		assert(recursivePath2, "is equal to", new Set([100]));

		const recursivePath3 = cs.findPath("a", "f(b)");
		assert(recursivePath3, "is equal to", null);
	},
};
