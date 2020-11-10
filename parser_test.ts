import { assert } from "./test";
import { RecordParser, TokenParser, Stream, ParsersFor, RepeatParser, ChoiceParser, Parser, DebugContext } from "./parser";

class ArrayStream<T> implements Stream<[T, number]> {
	array: T[];
	index: number;

	constructor(array: T[], index = 0) {
		this.array = array;
		this.index = index;
	}

	read(): [[T, number] | null, ArrayStream<T>] {
		if (this.index < this.array.length) {
			return [[this.array[this.index], this.index], new ArrayStream(this.array, this.index + 1)];
		}
		return [null, this];
	}
}

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
type Token = [string, number];

function atReference(name: string) {
	return (x: any, props: DebugContext<Token>) => {
		const token = props[name].first;
		if (token === null) {
			return -1;
		} else {
			return token[1];
		}
	}
}

const atHead = (x: Stream<Token>) => {
	const token = x.read()[0];
	if (token === null) {
		return -1;
	} else {
		return token[1];
	}
}

const grammar: ParsersFor<Token, ErrorElement, ASTs> = {
	OpenParen: new TokenParser(([s]) => s == "(" ? {} : null),
	CloseParen: new TokenParser(([s]) => s == ")" ? {} : null),
	Atom: new TokenParser(([s]) => s != "(" && s != ")" ? { name: s, lexeme: s } : null),
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
	Expr: new ChoiceParser<Token, ErrorElement, Expr>(() => grammar.Atom, () => grammar.List),
};

export const tests = {
	basic() {
		const stream: Stream<[string, number]> = new ArrayStream(["(", "a", "b", "(", "c", ")", ")"]);

		const expr = grammar.Expr.parse(stream, {});

		assert(expr, "is array");
		assert(expr[1].read(), "is equal to", [null, expr[1]]);
		assert(expr[0], "is equal to", {
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
		});
	},

	missingCloseParen() {
		const stream: Stream<[string, number]> = new ArrayStream(["(", "a", "b", "(", "(", "c", ")"]);

		const expr = grammar.Expr.parse(stream, {});
		assert(expr, "is equal to", {
			message: [
				"Expected a `)` at",
				-1,
				"to close the `(` at",
				3,
			]
		});
	}
};
