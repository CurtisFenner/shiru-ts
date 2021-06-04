import * as ir from "./ir";
import * as uf from "./uf";
import { assert } from "./test";

export const tests = {
	"UFTheory-basic-equality-refuted"() {
		const smt = new uf.UFTheory();
		const x = smt.createVariable(ir.T_INT);
		const y = smt.createVariable(ir.T_INT);
		const z = smt.createVariable(ir.T_INT);
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });

		const xeqy = smt.createApplication(eq, [x, y]);
		const xeqz = smt.createApplication(eq, [x, z]);
		const yeqz = smt.createApplication(eq, [y, z]);
		const yneqz = smt.createApplication(not, [yeqz]);

		smt.addConstraint([xeqy]);
		smt.addConstraint([xeqz]);
		smt.addConstraint([yneqz]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", "refuted");
	},
	"UFTheory-basic-satisfiable"() {
		const smt = new uf.UFTheory();
		const x1 = smt.createVariable(ir.T_INT);
		const x2 = smt.createVariable(ir.T_INT);
		const f = smt.createFunction(ir.T_INT, {});

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });

		const x1eqx2 = smt.createApplication(eq, [x1, x2]);
		const fx1 = smt.createApplication(f, [x1]);
		const fx2 = smt.createApplication(f, [x2]);
		const fx1eqfx2 = smt.createApplication(eq, [fx1, fx2]);
		const fx1neqfx2 = smt.createApplication(not, [fx1eqfx2]);

		smt.addConstraint([x1eqx2, fx1neqfx2]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", {});
	},
	"UFTheory-basic-function-refuted"() {
		const smt = new uf.UFTheory();
		const x1 = smt.createVariable(ir.T_INT);
		const x2 = smt.createVariable(ir.T_INT);
		const f = smt.createFunction(ir.T_INT, {});

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });

		const x1eqx2 = smt.createApplication(eq, [x1, x2]);
		const fx1 = smt.createApplication(f, [x1]);
		const fx2 = smt.createApplication(f, [x2]);
		const fx1eqfx2 = smt.createApplication(eq, [fx1, fx2]);
		const fx1neqfx2 = smt.createApplication(not, [fx1eqfx2]);

		smt.addConstraint([fx1neqfx2]);
		smt.addConstraint([x1eqx2]);

		const result = smt.attemptRefutation();
		assert(result, "is equal to", "refuted");
	},
	"UFTheory-excluded-middle-variables"() {
		const smt = new uf.UFTheory();
		const a = smt.createVariable(ir.T_BOOLEAN);
		const b = smt.createVariable(ir.T_BOOLEAN);
		const c = smt.createVariable(ir.T_BOOLEAN);

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });

		const aeqb = smt.createApplication(eq, [a, b]);
		const aeqc = smt.createApplication(eq, [a, c]);
		const beqc = smt.createApplication(eq, [b, c]);
		const aneqb = smt.createApplication(not, [aeqb]);
		const aneqc = smt.createApplication(not, [aeqc]);
		const bneqc = smt.createApplication(not, [beqc]);

		// Three booleans cannot all be unequal.
		smt.addConstraint([aneqb]);
		smt.addConstraint([aneqc]);
		smt.addConstraint([bneqc]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-excluded-middle-function-of-bool"() {
		const smt = new uf.UFTheory();
		const a = smt.createVariable(ir.T_BOOLEAN);
		const b = smt.createVariable(ir.T_BOOLEAN);
		const c = smt.createVariable(ir.T_BOOLEAN);
		const f = smt.createFunction(ir.T_INT, {});

		const fa = smt.createApplication(f, [a]);
		const fb = smt.createApplication(f, [b]);
		const fc = smt.createApplication(f, [c]);

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const faeqfb = smt.createApplication(eq, [fa, fb]);
		const faeqfc = smt.createApplication(eq, [fa, fc]);
		const fbeqfc = smt.createApplication(eq, [fb, fc]);

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });
		const faneqfb = smt.createApplication(not, [faeqfb]);
		const faneqfc = smt.createApplication(not, [faeqfc]);
		const fbneqfc = smt.createApplication(not, [fbeqfc]);

		// The result of mapping three booleans cannot all be unequal.
		smt.addConstraint([faneqfb]);
		smt.addConstraint([faneqfc]);
		smt.addConstraint([fbneqfc]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-bool-equality-ensures-same-sign"() {
		const smt = new uf.UFTheory();
		const x = smt.createVariable(ir.T_BOOLEAN);
		const y = smt.createVariable(ir.T_BOOLEAN);
		const z = smt.createVariable(ir.T_BOOLEAN);

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const xeqy = smt.createApplication(eq, [x, y]);
		const yeqz = smt.createApplication(eq, [y, z]);

		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });
		const notx = smt.createApplication(not, [x]);

		smt.addConstraint([xeqy]);
		smt.addConstraint([yeqz]);
		smt.addConstraint([notx]);
		smt.addConstraint([z]);

		// Two booleans that are equal must have the same boolean assignment.
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-bool-inequality-ensures-opposite-sign"() {
		const smt = new uf.UFTheory();
		const x = smt.createVariable(ir.T_BOOLEAN);
		const y = smt.createVariable(ir.T_BOOLEAN);
		const z = smt.createVariable(ir.T_BOOLEAN);

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });

		const xeqy = smt.createApplication(eq, [x, y]);
		const xneqy = smt.createApplication(not, [xeqy]);
		const yeqz = smt.createApplication(eq, [y, z]);

		// Two booleans that are inequal must have opposite boolean assignments.
		smt.addConstraint([xneqy]);
		smt.addConstraint([yeqz]);
		smt.addConstraint([x]);
		smt.addConstraint([z]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-equality-between-same-constants"() {
		const smt = new uf.UFTheory();

		const one = smt.createConstant(ir.T_INT, 1);
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const oneeqone = smt.createApplication(eq, [one, one]);

		// A symbol is equal to itself.
		smt.addConstraint([oneeqone]);
		assert(smt.attemptRefutation(), "is equal to", {});
	},
	"UFTheory-equality-between-distinct-constants"() {
		const smt = new uf.UFTheory();

		const one = smt.createConstant(ir.T_INT, 1);
		const two = smt.createConstant(ir.T_INT, 2);

		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });
		const oneeqtwo = smt.createApplication(eq, [one, two]);

		// Two distinct symbols cannot be equal.
		smt.addConstraint([oneeqtwo]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-assert-contradiction"() {
		const smt = new uf.UFTheory();
		const bool = smt.createVariable(ir.T_BOOLEAN);
		const not = smt.createFunction(ir.T_BOOLEAN, { not: true });
		smt.addConstraint([bool]);
		smt.addConstraint([smt.createApplication(not, [bool])]);

		assert(smt.attemptRefutation(), "is equal to", "refuted");
	},
	"UFTheory-pop-contradiction"() {
		const smt = new uf.UFTheory();

		const one = smt.createConstant(ir.T_INT, 1);
		const two = smt.createConstant(ir.T_INT, 2);

		const alpha = smt.createVariable(ir.T_INT);
		const f = smt.createFunction(ir.T_INT, {});
		const eq = smt.createFunction(ir.T_BOOLEAN, { eq: true });

		const fone = smt.createApplication(f, [one]);
		const falpha = smt.createApplication(f, [alpha]);

		smt.addConstraint([smt.createApplication(eq, [fone, one])]);
		smt.addConstraint([smt.createApplication(eq, [falpha, two])]);

		assert(smt.attemptRefutation(), "is equal to", {});

		smt.pushScope();
		smt.addConstraint([smt.createApplication(eq, [one, alpha])]);
		assert(smt.attemptRefutation(), "is equal to", "refuted");
		smt.popScope();

		assert(smt.attemptRefutation(), "is equal to", {});

		smt.pushScope();
		smt.addConstraint([smt.createApplication(eq, [two, alpha])]);
		assert(smt.attemptRefutation(), "is equal to", {});
		smt.popScope();
	},
};
