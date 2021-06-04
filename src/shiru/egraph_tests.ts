import * as egraph from "./egraph";
import { assert, specSupersetOf } from "./test";

function getTag<Term, Tag, Reason>(eg: egraph.EGraph<Term, Tag, Reason>, tag: Tag, id: symbol) {
	const tags = eg.getTagged(tag, id);
	if (tags.length === 0) {
		return null;
	}
	return {
		value: tags[0],
		reason: eg.query(id, tags[0].id)!,
	};
}

function getTags<Term, Tag, Reason>(eg: egraph.EGraph<Term, Tag, Reason>, tag: Tag, ids: symbol[]) {
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

		const two = eg.add(2, [], "constant");
		const three = eg.add(3, [], "constant");
		const four23 = eg.add(4, [two, three]);
		const four32 = eg.add(4, [three, two]);

		assert(eg.query(two, three), "is equal to", null);
		assert(eg.query(two, four23), "is equal to", null);
		assert(eg.query(two, four32), "is equal to", null);
		assert(eg.query(three, four23), "is equal to", null);
		assert(eg.query(three, four32), "is equal to", null);
		assert(eg.query(four23, four32), "is equal to", null);

		eg.merge(two, three, new Set(["two=three"]));
		eg.updateCongruence();

		assert(eg.query(two, three), "is equal to", new Set(["two=three"]));
		assert(eg.query(two, four23), "is equal to", null);
		assert(eg.query(two, four32), "is equal to", null);
		assert(eg.query(three, two), "is equal to", new Set(["two=three"]));
		assert(eg.query(three, four23), "is equal to", null);
		assert(eg.query(three, four32), "is equal to", null);
		assert(eg.query(four23, four32), "is equal to", new Set(["two=three"]));
		assert(eg.query(four32, four23), "is equal to", new Set(["two=three"]));
	},
	"EGraph-facts"() {
		const eg: egraph.EGraph<string | number, "constant", string> = new egraph.EGraph();

		const zero = eg.add(0, [], "constant");
		const ten = eg.add(10, [], "constant");
		const twenty = eg.add(20, [], "constant");
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
								const sumObject = eg.add(sum, [], "constant");
								madeChange = eg.merge(sumObject, member.id, cs.reasons) || madeChange;
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

		eg.merge(alpha, ten, new Set(["a=10"]));
		eg.merge(gamma, ten, new Set(["g=10"]));
		eg.merge(beta, twenty, new Set(["b=20"]));

		develop();

		assert(eg.query(alpha, ten), "is equal to", specSupersetOf(new Set(["a=10"])));
		assert(eg.query(gamma, ten), "is equal to", specSupersetOf(new Set(["g=10"])));

		{
			assert(getTag(eg, "constant", alpha), "is equal to", {
				value: { id: ten, term: 10, operands: [] },
				reason: new Set(["a=10"]),
			});
			assert(getTag(eg, "constant", beta), "is equal to", {
				value: { id: twenty, term: 20, operands: [] },
				reason: new Set(["b=20"]),
			});
			const thirty = eg.add(30, [], "constant");
			assert(getTag(eg, "constant", sumAlphaBetaZero), "is equal to", {
				value: { id: thirty, term: 30, operands: [] },
				reason: new Set(["a=10", "b=20"]),
			});

			assert(getTag(eg, "constant", sumAlphaGamma), "is equal to", {
				value: { id: twenty, term: 20, operands: [] },
				reason: specSupersetOf(new Set(["a=10", "g=10"])),
			});
		}
	}
};
