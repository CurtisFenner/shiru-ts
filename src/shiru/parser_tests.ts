import { assert } from "./test.js";
import * as parser from "./parser.js";

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

type Token = { s: string | null, i: number };

function atReference(name: string) {
	return (x: Token[], from: number, props: parser.DebugContext<Token>) => {
		const token = props[name].first;
		if (token === null) {
			return "eof";
		} else {
			return token.i + "";
		}
	}
}

const atHead = (x: Token[], from: number) => {
	const token = x[from];
	if (token === null) {
		return "eof";
	} else {
		return token.i + "";
	}
}

function parseProblem(...elements: (string | ((stream: Token[], from: number, context: parser.DebugContext<Token>) => string))[]) {
	return (stream: Token[], from: number, context: parser.DebugContext<Token>) => elements.map(x =>
		typeof x === "string" ? x : x(stream, from, context));
}

const grammar: parser.ParsersFor<Token, ASTs> = {
	OpenParen: new parser.TokenParser(({ s }) => s === "(" ? {} : null),
	CloseParen: new parser.TokenParser(({ s }) => s === ")" ? {} : null),
	Atom: new parser.TokenParser(({ s }) => s !== null && s !== "(" && s !== ")" ? { name: s, lexeme: s } : null),
	List: new parser.RecordParser(() => ({
		open: grammar.OpenParen,
		elements: new parser.RepeatParser(grammar.Expr),
		close: grammar.CloseParen.required(parseProblem(
			"Expected a `)` at",
			atHead,
			"to close the `(` at",
			atReference("open")
		)),
	})),
	Expr: parser.choice(() => grammar, "Atom", "List"),
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

		assert(() => grammar.Expr.parse(stream, 0, {}), "throws", [
			"Expected a `)` at",
			"7",
			"to close the `(` at",
			"3",
		]);
	}
};
