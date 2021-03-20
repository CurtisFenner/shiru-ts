import { Program } from "./ir";

export const tests = {
	"basic-verification"() {
		const program: Program = {
			records: {},
			functions: {},
			interfaces: {},
			foreign: {},
			globalVTableFactories: {},
		};
	},
};
