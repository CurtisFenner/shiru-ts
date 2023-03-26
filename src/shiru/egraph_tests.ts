import * as egraph from "./egraph";
import { assert, specSupersetOf } from "./test";

export const tests = {
	"EGraph-basic"() {
		const pairs: [egraph.EObject, egraph.EObject][] = [];
		const eg: egraph.EGraph<number, { "constant": number }, string> = new egraph.EGraph((a, b) => {
			// The callback should be called before they are merged.
			assert(eg.areCongruent(a, b), "is equal to", false);

			// Ensure the callback was called.
			pairs.push([a, b]);
			return null;
		}, {
			"constant"(child, parent) {
				return parent;
			},
		});

		const two = eg.add(2, []);
		eg.addTag(two, "constant", 2);
		const three = eg.add(3, []);
		eg.addTag(three, "constant", 3);
		const four23 = eg.add(4, [two, three]);
		const four32 = eg.add(4, [three, two]);

		assert(eg.areCongruent(two, three), "is equal to", false);
		assert(eg.areCongruent(two, four23), "is equal to", false);
		assert(eg.areCongruent(two, four32), "is equal to", false);
		assert(eg.areCongruent(three, four23), "is equal to", false);
		assert(eg.areCongruent(three, four32), "is equal to", false);
		assert(eg.areCongruent(four23, four32), "is equal to", false);

		assert(pairs, "is equal to", [] as [egraph.EObject, egraph.EObject][]);
		eg.mergeApplications(two, three, "two=three", [], []);
		assert(pairs, "is equal to", [[two, three]]);
		eg.updateCongruence();
		assert(pairs, "is equal to", [[two, three], [four23, four32]]);

		assert(eg.areCongruent(two, three), "is equal to", true);
		assert(eg.explainCongruence(two, three), "is equal to", new Set(["two=three"]));
		assert(eg.areCongruent(two, four23), "is equal to", false);
		assert(eg.areCongruent(two, four32), "is equal to", false);
		assert(eg.areCongruent(three, two), "is equal to", true);
		assert(eg.explainCongruence(three, two), "is equal to", new Set(["two=three"]));
		assert(eg.areCongruent(three, four23), "is equal to", false);
		assert(eg.areCongruent(three, four32), "is equal to", false);
		assert(eg.areCongruent(four23, four32), "is equal to", true);
		assert(eg.explainCongruence(four23, four32), "is equal to", new Set(["two=three"]));
		assert(eg.areCongruent(four32, four23), "is equal to", true);
		assert(eg.explainCongruence(four32, four23), "is equal to", new Set(["two=three"]));
	},
	"EGraph-facts"() {
		const eg: egraph.EGraph<
			string | number,
			{ "constant": { id: egraph.EObject, number: number } },
			string[]
		> = new egraph.EGraph(() => null, {
			constant(child, parent) {
				return parent;
			}
		});

		const zero = eg.add(0, []);
		eg.addTag(zero, "constant", { id: zero, number: 0 });
		const ten = eg.add(10, []);
		eg.addTag(ten, "constant", { id: ten, number: 10 });
		const twenty = eg.add(20, []);
		eg.addTag(twenty, "constant", { id: twenty, number: 20 });
		const alpha = eg.add("var-alpha", []);
		const beta = eg.add("var-beta", []);
		const gamma = eg.add("var-gamma", []);

		const sumZeroAlpha = eg.add("+", [zero, alpha]);
		const sumAlphaBetaZero = eg.add("+", [sumZeroAlpha, beta]);
		const sumAlphaGamma = eg.add("+", [alpha, gamma]);

		const flatten = (a: Set<string[]>): Set<string> => {
			const out = new Set<string>();
			for (const ss of a) {
				for (const s of ss) {
					out.add(s);
				}
			}
			return out;
		}

		function getTag(
			eg: egraph.EGraph<string | number, { "constant": { id: egraph.EObject, number: number } }, string[]>,
			tag: "constant",
			id: egraph.EObject,
		) {
			const tags = eg.getTagged(tag, id);
			if (tags === null) {
				return null;
			}

			const explained = eg.explainCongruence(id, tags.id);
			return {
				value: tags,
				reason: [...flatten(explained)],
			};
		}

		function getTags(
			eg: egraph.EGraph<string | number, { "constant": { id: egraph.EObject, number: number } }, string[]>,
			tag: "constant",
			ids: egraph.EObject[],
		): null | {
			values: { id: egraph.EObject, number: number }[],
			reasons: string[],
		} {
			const values = [];
			const reasons = new Set<string>();
			for (const id of ids) {
				const r = getTag(eg, tag, id);
				if (r === null) {
					return null;
				}
				values.push(r.value);
				for (const reason of r.reason) {
					reasons.add(reason);
				}
			}
			return { values, reasons: [...reasons] };
		}

		function develop() {
			let madeChange = true;
			while (madeChange) {
				madeChange = false;
				for (const [eclass, { members }] of eg.getClasses()) {
					for (const member of members) {
						if (member.term === "+") {
							const cs = getTags(eg, "constant", member.operands);
							if (cs !== null) {
								const sum = cs.values[0].number + cs.values[1].number;
								const sumObject = eg.add(sum, []);
								eg.addTag(sumObject, "constant", { id: sumObject, number: sum });
								madeChange = eg.mergeApplications(sumObject, member.id, cs.reasons, [], []) || madeChange;
							}
						}
					}
				}

				madeChange = eg.updateCongruence() || madeChange;
			}
		}
		develop();

		{
			assert(eg.getTagged("constant", alpha), "is equal to", null);
		}

		eg.mergeApplications(alpha, ten, ["a=10"], [], []);
		eg.mergeApplications(gamma, ten, ["g=10"], [], []);
		eg.mergeApplications(beta, twenty, ["b=20"], [], []);

		develop();

		assert(flatten(eg.explainCongruence(alpha, ten)), "is equal to", specSupersetOf(new Set(["a=10"])));
		assert(flatten(eg.explainCongruence(gamma, ten)), "is equal to", specSupersetOf(new Set(["g=10"])));

		assert(getTag(eg, "constant", alpha), "is equal to", {
			value: { id: ten, number: 10 },
			reason: (["a=10"]),
		});
		assert(getTag(eg, "constant", beta), "is equal to", {
			value: { id: twenty, number: 20 },
			reason: (["b=20"]),
		});
		const thirty = eg.add(30, []);
		eg.addTag(thirty, "constant", { id: thirty, number: 30 });
		assert(getTag(eg, "constant", sumAlphaBetaZero), "is equal to", {
			value: { id: thirty, number: 30 },
			reason: (["a=10", "b=20"]),
		});

		assert(getTag(eg, "constant", sumAlphaGamma), "is equal to", {
			value: { id: twenty, number: 20 },
			reason: ["a=10", "g=10"],
		});
	},
	"EGraph-remembers-path-for-reason"() {
		// Construct nine nodes.
		const eg = new egraph.EGraph<string, {}, number>(() => null, {});
		const n1 = eg.add("1", []);
		const n2 = eg.add("2", []);
		const n3 = eg.add("3", []);
		const n4 = eg.add("4", []);
		const n5 = eg.add("5", []);
		const n6 = eg.add("6", []);
		const n7 = eg.add("7", []);
		const n8 = eg.add("8", []);
		const n9 = eg.add("9", []);

		// Join all consecutive pairs.
		eg.mergeApplications(n3, n4, 34, [], []);
		eg.mergeApplications(n7, n8, 78, [], []);
		eg.mergeApplications(n5, n6, 56, [], []);
		eg.mergeApplications(n4, n5, 45, [], []);
		eg.mergeApplications(n8, n9, 89, [], []);
		eg.mergeApplications(n6, n7, 67, [], []);
		eg.mergeApplications(n1, n2, 12, [], []);
		eg.mergeApplications(n2, n3, 23, [], []);

		// Verify that the reason n1 is equal to n9 includes all pairs, and not
		// just a subset.
		assert(eg.explainCongruence(n1, n9), "is equal to", new Set([
			12, 23, 34, 45, 56, 67, 78, 89
		]));
	},
	"EGraph-multiple-congruent-applications"() {
		const eg = new egraph.EGraph<string, {}, number>(() => null, {});
		const a = eg.add("a", [], "a");
		const b = eg.add("b", [], "b");
		const c = eg.add("c", [], "c");
		const d = eg.add("d", [], "d");

		eg.mergeApplications(a, b, 2, [], []);
		eg.mergeApplications(a, c, 3, [], []);
		eg.mergeApplications(a, d, 4, [], []);

		const fa = eg.add("f", [a], "f a");
		const fb = eg.add("f", [b], "f b");
		const fc = eg.add("f", [c], "f c");
		const fd = eg.add("f", [d], "f d");

		eg.updateCongruence();

		// All three (and not just some) should become equal after a single step
		// of congruence.
		assert(eg.explainCongruence(fa, fb), "is equal to", new Set([2]));
		assert(eg.explainCongruence(fa, fc), "is equal to", new Set([3]));
		assert(eg.explainCongruence(fa, fd), "is equal to", new Set([4]));
	},
};
