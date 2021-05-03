/// `ParsersFor` is a utility type to make it easy to make a recursively defined
/// "grammar" object type-safe.
export type ParsersFor<Token, ASTs> = {
	[P in keyof ASTs]: Parser<Token, ASTs[P]>
};

/// `TokenSpan` represents an contiguous range of tokens within a token stream.
export interface TokenSpan<Token> {
	/// The first Token in this span.
	first: Token,

	/// The Token which immediately follows this span.
	following: Token,
};

export type DebugContext<Token> = Record<string, TokenSpan<Token>>;

/// The result of a parsing operation.
/// `null` represents non-fatal failure to match.
/// `ParseError` represents an illegal program fragment was detected while
/// attempting to parse this object.
export type ParseResult<Result> = { object: Result, rest: number } | null;

/// Parser represents a parser from a stream of `Token`s to a particular
/// `Result` AST.
export abstract class Parser<Token, Result> {
	abstract parse(stream: Token[], from: number, debugContext: DebugContext<Token>): ParseResult<Result>;

	map<Q>(f: (r: Result, stream: Token[], from: number) => Q): Parser<Token, Q> {
		return new MapParser<Token, Result, Q>(this, f);
	}

	required(f: FailHandler<Token, unknown>): Parser<Token, Result> {
		return new ChoiceParser(() => [this, new FailParser(f)]);
	}

	otherwise<Q>(q: Q): Parser<Token, Result | Q> {
		return new ChoiceParser(() => [this, new ConstParser<Token, Result | Q>(q)]);
	}
}

export class MapParser<T, A, B> extends Parser<T, B> {
	parser: Parser<T, A>;
	f: (a: A, stream: T[], from: number) => B;

	constructor(parser: Parser<T, A>, f: (a: A, stream: T[], from: number) => B) {
		super();
		this.parser = parser;
		this.f = f;
	}

	parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<B> {
		const result = this.parser.parse(stream, from, debugContext);
		if (result && "object" in result) {
			const mapped = this.f(result.object, stream, from);
			return { object: mapped, rest: result.rest };
		} else {
			return result;
		}
	}
}

export class EndOfStreamParser<T> extends Parser<T, {}> {
	parse(stream: T[], from: number): { object: {}, rest: number } | null {
		if (from === stream.length) {
			return { object: {}, rest: stream.length };
		}
		return null;
	}
}

export class ConstParser<T, R> extends Parser<T, R> {
	constructor(private value: R) {
		super();
	}

	parse(stream: T[], from: number): { object: R, rest: number } {
		return { object: this.value, rest: from };
	}
}

export class TokenParser<T, R> extends Parser<T, R> {
	f: (t: T) => (null | R);

	constructor(f: (t: T) => (null | R)) {
		super();
		this.f = f;
	}

	parse(stream: T[], from: number): null | { object: R, rest: number } {
		if (from >= stream.length) {
			return null;
		}
		const front = stream[from];
		const value = this.f(front);
		if (value === null) return null;
		return { object: value, rest: from + 1 };
	}
}

export class RepeatParser<T, R> extends Parser<T, R[]> {
	element: Parser<T, R>;
	min?: number;
	max?: number;

	constructor(element: Parser<T, R>, min?: number, max?: number) {
		super();
		this.element = element;
		this.min = min;
		this.max = max;
	}

	parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<R[]> {
		const list: R[] = [];
		while (this.max === undefined || list.length < this.max) {
			const result = this.element.parse(stream, from, debugContext);
			if (result === null) {
				break;
			} else {
				list.push(result.object);
				if (result.rest <= from) {
					throw new Error("Encountered zero-token element in RepeatParser `" + JSON.stringify(result) + "`");
				}
				from = result.rest;
			}
		}

		if (this.min !== undefined && list.length < this.min) {
			return null;
		}

		return { object: list, rest: from };
	}
};

export type RecordParserDescription<T, R> = { [P in keyof R]: (Parser<T, R[P]>) };

export class RecordParser<T, R> extends Parser<T, R> {
	private description: () => RecordParserDescription<T, R>;
	private mem: null | RecordParserDescription<T, R> = null;

	constructor(description: () => RecordParserDescription<T, R>) {
		super();
		this.description = description;
	}

	parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<R> {
		// Each RecordParser opens a new debug context.
		// TODO: Link the debug context to the parent context.
		debugContext = {};

		let mem = this.mem;
		if (mem === null) {
			mem = this.description();
			this.mem = mem;
		}

		let record: Partial<R> = {};
		for (let p in mem) {
			let firstToken = stream[from];
			const parser = mem[p];
			let result = parser.parse(stream, from, debugContext);
			if (result === null) {
				return null;
			}

			if (p[0] !== "_") {
				record[p] = result.object;
			}
			from = result.rest;
			const followingToken = stream[from];
			debugContext[p] = { first: firstToken, following: followingToken };
		}
		return { object: record as R, rest: from };
	}
}

/// ChoiceParser implements *ordered* choice. The first constituent parser that
/// accepts the input results in a parse.
export class ChoiceParser<T, U> extends Parser<T, U> {
	parsers: () => Parser<T, U>[];
	constructor(parsers: () => Parser<T, U>[]) {
		super();
		this.parsers = parsers;
	}

	parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<U> {
		for (let parser of this.parsers()) {
			let result = parser.parse(stream, from, debugContext);
			if (result === null) {
				continue;
			}
			return result;
		}
		return null;
	}
}

/// choice is a convenience function for getting terse inference.
export function choice<T, As, K extends keyof As>(grammar: () => ParsersFor<T, As>, ...keys: K[]) {
	return new ChoiceParser<T, As[K]>(() => {
		const g = grammar();
		return keys.map(k => g[k]);
	});
}

export type FailHandler<T, Q> = (stream: T[], from: number, context: DebugContext<T>) => Q;

export class FailParser<T> extends Parser<T, never> {
	constructor(private f: FailHandler<T, unknown>) {
		super();
	}

	parse(stream: T[], from: number, debugContext: Record<string, TokenSpan<T>>): ParseResult<never> {
		throw this.f(stream, from, debugContext);
	}
}
