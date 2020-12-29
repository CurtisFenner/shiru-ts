function randomSign() {
	return Math.random() < 0.5 ? -1 : +1;
}

export function generateInstance(numTerms: number, numClauses: number): string {
	if (numTerms !== numTerms || numTerms < 4) {
		throw new Error("invalid numTerms");
	} else if (numClauses !== numClauses || numClauses < 1) {
		throw new Error("invalid numClauses");
	}

	let stream = "";

	stream += "p cnf " + numTerms + " " + numClauses + " ";
	for (let i = 0; i < numClauses; i++) {
		let a = Math.floor(Math.random() * numTerms);
		let b = a;
		while (b == a) b = Math.floor(Math.random() * numTerms);
		let c = b;
		while (c == a || c == b) c = Math.floor(Math.random() * numTerms);

		const clause = [
			randomSign() * (a + 1),
			randomSign() * (b + 1),
			randomSign() * (c + 1),
		];

		stream += (clause.join(" ") + " 0 ");
	}

	return stream;
}

if (require.main === module) {
	const commands = process.argv;

	if (commands.length !== 4) {
		throw new Error("USAGE:\n\t<node random_cnf.js> <num terms> <num clauses>");
	}

	const numTerms = parseInt(commands[2]);
	const numClauses = parseInt(commands[3]);
	const instance = generateInstance(numTerms, numClauses);
	console.log(instance);
}
