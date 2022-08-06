import * as egraph from "./egraph";
import { assert, specSupersetOf } from "./test";

function getTag<Term, Tag, Reason>(eg: egraph.EGraph<Term, Tag, Reason>, tag: Tag, id: egraph.EObject) {
	const tags = eg.getTagged(tag, id);
	if (tags.length === 0) {
		return null;
	}
	return {
		value: tags[0],
		reason: eg.query(id, tags[0].id)!.toSet(),
	};
}

function getTags<Term, Tag, Reason>(eg: egraph.EGraph<Term, Tag, Reason>, tag: Tag, ids: egraph.EObject[]) {
	const values = [];
	const reasons = new Set<Reason>();
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
	return { values, reasons };
}

export const tests = {
	"EGraph-basic"() {
		const eg: egraph.EGraph<number, "constant", string> = new egraph.EGraph();

		const two = eg.add(2, []);
		eg.addTag(two, "constant");
		const three = eg.add(3, []);
		eg.addTag(three, "constant");
		const four23 = eg.add(4, [two, three]);
		const four32 = eg.add(4, [three, two]);

		assert(eg.query(two, three), "is equal to", null);
		assert(eg.query(two, four23), "is equal to", null);
		assert(eg.query(two, four32), "is equal to", null);
		assert(eg.query(three, four23), "is equal to", null);
		assert(eg.query(three, four32), "is equal to", null);
		assert(eg.query(four23, four32), "is equal to", null);

		eg.merge(two, three, new egraph.ReasonTree(["two=three"]));
		eg.updateCongruence();

		assert(eg.query(two, three)?.toSet(), "is equal to", new Set(["two=three"]));
		assert(eg.query(two, four23), "is equal to", null);
		assert(eg.query(two, four32), "is equal to", null);
		assert(eg.query(three, two)?.toSet(), "is equal to", new Set(["two=three"]));
		assert(eg.query(three, four23), "is equal to", null);
		assert(eg.query(three, four32), "is equal to", null);
		assert(eg.query(four23, four32)?.toSet(), "is equal to", new Set(["two=three"]));
		assert(eg.query(four32, four23)?.toSet(), "is equal to", new Set(["two=three"]));
	},
	"EGraph-facts"() {
		const eg: egraph.EGraph<string | number, "constant", string> = new egraph.EGraph();

		const zero = eg.add(0, []);
		eg.addTag(zero, "constant");
		const ten = eg.add(10, []);
		eg.addTag(ten, "constant");
		const twenty = eg.add(20, []);
		eg.addTag(twenty, "constant");
		const alpha = eg.add("var-alpha", []);
		const beta = eg.add("var-beta", []);
		const gamma = eg.add("var-gamma", []);

		const sumZeroAlpha = eg.add("+", [zero, alpha]);
		const sumAlphaBetaZero = eg.add("+", [sumZeroAlpha, beta]);
		const sumAlphaGamma = eg.add("+", [alpha, gamma]);

		function develop() {
			let madeChange = true;
			while (madeChange) {
				madeChange = false;
				for (const [eclass, { members }] of eg.getClasses()) {
					for (const member of members) {
						if (member.term === "+") {
							const cs = getTags(eg, "constant", member.operands);
							if (cs !== null) {
								const sum = (cs.values[0].term as number) + (cs.values[1].term as number);
								const sumObject = eg.add(sum, []);
								eg.addTag(sumObject, "constant");
								madeChange = eg.merge(sumObject, member.id, new egraph.ReasonTree([...cs.reasons])) || madeChange;
							}
						}
					}
				}

				madeChange = eg.updateCongruence() || madeChange;
			}
		}
		develop();

		{
			assert(eg.getTagged("constant", alpha), "is equal to", []);
		}

		eg.merge(alpha, ten, new egraph.ReasonTree(["a=10"]));
		eg.merge(gamma, ten, new egraph.ReasonTree(["g=10"]));
		eg.merge(beta, twenty, new egraph.ReasonTree(["b=20"]));

		develop();

		assert(eg.query(alpha, ten)?.toSet(), "is equal to", specSupersetOf(new Set(["a=10"])));
		assert(eg.query(gamma, ten)?.toSet(), "is equal to", specSupersetOf(new Set(["g=10"])));

		{
			assert(getTag(eg, "constant", alpha), "is equal to", {
				value: { id: ten, term: 10, operands: [] },
				reason: new Set(["a=10"]),
			});
			assert(getTag(eg, "constant", beta), "is equal to", {
				value: { id: twenty, term: 20, operands: [] },
				reason: new Set(["b=20"]),
			});
			const thirty = eg.add(30, []);
			eg.addTag(thirty, "constant");
			assert(getTag(eg, "constant", sumAlphaBetaZero), "is equal to", {
				value: { id: thirty, term: 30, operands: [] },
				reason: new Set(["a=10", "b=20"]),
			});

			assert(getTag(eg, "constant", sumAlphaGamma), "is equal to", {
				value: { id: twenty, term: 20, operands: [] },
				reason: specSupersetOf(new Set(["a=10", "g=10"])),
			});
		}
	},
	"EGraph-remembers-path-for-reason"() {
		// Construct nine nodes.
		const eg = new egraph.EGraph<string, never, number>();
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
		eg.merge(n3, n4, new egraph.ReasonTree([34]));
		eg.merge(n7, n8, new egraph.ReasonTree([78]));
		eg.merge(n5, n6, new egraph.ReasonTree([56]));
		eg.merge(n4, n5, new egraph.ReasonTree([45]));
		eg.merge(n8, n9, new egraph.ReasonTree([89]));
		eg.merge(n6, n7, new egraph.ReasonTree([67]));
		eg.merge(n1, n2, new egraph.ReasonTree([12]));
		eg.merge(n2, n3, new egraph.ReasonTree([23]));

		// Verify that the reason n1 is equal to n9 includes all pairs, and not
		// just a subset.
		assert(eg.query(n1, n9)?.toSet(), "is equal to", new Set([
			12, 23, 34, 45, 56, 67, 78, 89
		]));
	},
	"EGraph-multiple-congruent-applications"() {
		const eg = new egraph.EGraph<string, never, number>();
		const a = eg.add("a", []);
		const b = eg.add("b", []);
		const c = eg.add("c", []);
		const d = eg.add("d", []);

		eg.merge(a, b, new egraph.ReasonTree([2]));
		eg.merge(a, c, new egraph.ReasonTree([3]));
		eg.merge(a, d, new egraph.ReasonTree([4]));

		const fa = eg.add("f", [a]);
		const fb = eg.add("f", [b]);
		const fc = eg.add("f", [c]);
		const fd = eg.add("f", [d]);

		eg.updateCongruence();

		// All three (and not just some) should become equal after a single step
		// of congruence.
		assert(eg.query(fa, fb)?.toSet(), "is equal to", new Set([2]));
		assert(eg.query(fa, fc)?.toSet(), "is equal to", new Set([3]));
		assert(eg.query(fa, fd)?.toSet(), "is equal to", new Set([4]));
	},
};
