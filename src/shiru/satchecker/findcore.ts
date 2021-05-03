import { readFileSync } from "fs";
import { minisat } from "./checker";
const instance = readFileSync("sat-instances/slow3.cnf").toString().split("\n");

// Now, make a queue, filtering out one line at a time until SAT.
let q: string[][] = [instance];

function shrink(parent: string[]) {
	const marginal = 20 / parent.length;

	// Attempt to remove many at once.
	let fraction = 0.85;
	while (fraction < 1 - marginal) {
		console.log("Fraction:", fraction, "on", parent.length - 1 + " clauses.");
		let child = parent.filter((_, i) => i == 0 || Math.random() < fraction);
		if (child.length >= 2 && child.length < parent.length && minisat(child.join("\n")) === "UNSATISFIABLE") {
			return child;
		} else {
			fraction = fraction * (1 - marginal) + marginal * 1;
		}
	}

	// Attempt to remove a single slice.
	for (let i = 1; i < parent.length; i++) {
		const child = parent.slice(0);
		child.splice(i, 1);
		if (minisat(child.join("\n")) === "UNSATISFIABLE") {
			return child;
		}
	}

	// Couldn't be shrunk anymore.
	return null;
}

let smallest = instance;
while (smallest) {
	let smaller = shrink(smallest);
	if (smaller) {
		smallest = smaller;
	} else {
		break;
	}
}

console.log("SMALLEST INSTANCE:");
console.log(smallest.length - 1, "clauses from original of", instance.length - 1, "clauses.");
console.log(smallest.join("\n"));
