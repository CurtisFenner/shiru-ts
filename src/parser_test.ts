import { assert } from "./test";
import { RecordParser, TokenParser, ParsersFor, RepeatParser, ChoiceParser, Parser, DebugContext, choice } from "./parser";

interface OpenParen { }

interface CloseParen { }

interface Atom {
	name: string,
	lexeme: string,
}

interface List {
	open: OpenParen,
	elements: Expr[],
	close: CloseParen,
}

type Expr = Atom | List;

type ASTs = {
	OpenParen: OpenParen,
	CloseParen: CloseParen,
	Atom: Atom,
	List: List,
	Expr: Expr,
};

type ErrorElement = string | number;
type Token = { s: string | null, i: number };

function atReference(name: string) {
	return (x: Token[], from: number, props: DebugContext<Token>) => {
		const token = props[name].first;
		if (token === null) {
			return -1;
		} else {
			return token.i;
		}
	}
}

const atHead = (x: Token[], from: number) => {
	const token = x[from];
	if (token === null) {
		return -1;
	} else {
		return token.i;
	}
}

const grammar: ParsersFor<Token, ErrorElement, ASTs> = {
	OpenParen: new TokenParser(({ s }) => s === "(" ? {} : null),
	CloseParen: new TokenParser(({ s }) => s === ")" ? {} : null),
	Atom: new TokenParser(({ s }) => s !== null && s !== "(" && s !== ")" ? { name: s, lexeme: s } : null),
	List: new RecordParser({
		open: () => grammar.OpenParen,
		elements: () => new RepeatParser(grammar.Expr),
		close: () => grammar.CloseParen.required(
			["Expected a `)` at"],
			atHead,
			["to close the `(` at"],
			atReference("open")
		),
	}),
	Expr: choice(() => grammar, "Atom", "List"),
};

export const tests = {
	basic() {
		const stream = ["(", "a", "b", "(", "c", ")", ")", null]
			.map((v, i) => ({ s: v, i }));

		const expr = grammar.Expr.parse(stream, 0, {});

		assert(expr, "is equal to", {
			object: {
				open: {},
				elements: [
					{ name: "a", lexeme: "a" },
					{ name: "b", lexeme: "b" },
					{
						open: {},
						elements: [{ name: "c", lexeme: "c" }],
						close: {},
					},
				],
				close: {},
			},
			rest: stream.length - 1,
		});
	},

	missingCloseParen() {
		const stream = ["(", "a", "b", "(", "(", "c", ")", null]
			.map((v, i) => ({ s: v, i }));

		const expr = grammar.Expr.parse(stream, 0, {});
		assert(expr, "is equal to", {
			message: [
				"Expected a `)` at",
				7,
				"to close the `(` at",
				3,
			]
		});
	}
};
