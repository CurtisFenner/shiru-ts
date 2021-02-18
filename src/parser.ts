/// `ParseError` represents a problem hit while parsing.
export type ParseError<M> = {
  message: M[],
};

/// `ParsersFor` is a utility type to make it easy to make a recursively defined
/// "grammar" object type-safe.
export type ParsersFor<Token, M, ASTs> = {
  [P in keyof ASTs]: Parser<Token, M, ASTs[P]>
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
export type ParseResult<M, Result> = { object: Result, rest: number } | null | ParseError<M>;

/// Parser represents a parser from a stream of `Token`s to a particular 
/// `Result` AST.
export abstract class Parser<Token, M, Result> {
  abstract parse(stream: Token[], from: number, debugContext: DebugContext<Token>): ParseResult<M, Result>;

  map<Q>(f: (r: Result) => Q): Parser<Token, M, Q> {
    return new MapParser<Token, M, Result, Q>(this, f);
  }
  
  required(...fragments: (MessageFragment<Token, M> | M[])[]): Parser<Token, M, Result> {
    return new ChoiceParser(() => [this, new BaseFailParser(...fragments)]);
  }
}

export class MapParser<T, M, A, B> extends Parser<T, M, B> {
  parser: Parser<T, M, A>;
  f: (a: A) => B;

  constructor(parser: Parser<T, M, A>, f: (a: A) => B) {
    super();
    this.parser = parser;
    this.f = f;
  }

  parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<M, B> {
    const result = this.parser.parse(stream, from, debugContext);
    if (result && "object" in result) {
      const mapped = this.f(result.object);
      return { object: mapped, rest: result.rest };
    } else {
      return result;
    }
  }
}

export class EndOfStreamParser<T, M> extends Parser<T, M, {}> {
  parse(stream: T[], from: number): { object: {}, rest: number } | null {
    if (from === stream.length) {
      return { object: {}, rest: stream.length };
    }
    return null;
  }
}

export class ConstParser<T, M, R> extends Parser<T, M, R> {
  constructor(private value: R) {
    super();
  }

  parse(stream: T[], from: number): { object: R, rest: number } {
    return { object: this.value, rest: from };
  }
}

export class TokenParser<T, M, R> extends Parser<T, M, R> {
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

export class RepeatParser<T, M, R> extends Parser<T, M, R[]> {
  element: Parser<T, M, R>;
  min?: number;
  max?: number;

  constructor(element: Parser<T, M, R>, min?: number, max?: number) {
    super();
    this.element = element;
    this.min = min;
    this.max = max;
  }

  parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<M, R[]> {
    const list: R[] = [];
    while (this.max === undefined || list.length < this.max) {
      const result = this.element.parse(stream, from, debugContext);
      if (result === null) {
        break;
      } else if ("message" in result) {
        return result;
      } else {
        list.push(result.object);
        from = result.rest;
      } 
    }

    if (this.min !== undefined && list.length < this.min) {
      return null;
    }

    return { object: list, rest: from };
  }
};

export type RecordParserDescription<T, M, R> = { [P in keyof R]: (() => Parser<T, M, R[P]>) };

export class RecordParser<T, M, R> extends Parser<T, M, R> {
  description: RecordParserDescription<T, M, R>;

  constructor(description: RecordParserDescription<T, M, R>) {
    super();
    this.description = description;
  }

  parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<M, R> {
    // Each RecordParser opens a new debug context.
    // TODO: Link the debug context to the parent context.
    debugContext = {};

    let record: Partial<R> = {};
    for (let p in this.description) {
      let firstToken = stream[from];
      const d = this.description[p];
      const parser = d();
      let result = parser.parse(stream, from, debugContext);
      if (result === null) {
        return null;
      } else if ("message" in result) {
        return result;
      }

      record[p] = result.object;
      from = result.rest;
      const followingToken = stream[from];
      debugContext[p] = { first: firstToken, following: followingToken };
    }
    return { object: record as R, rest: from };
  }
}

/// ChoiceParser implements *ordered* choice. The first constituent parser that
/// accepts the input results in a parse.
export class ChoiceParser<T, M, U> extends Parser<T, M, U> {
  parsers: () => Parser<T, M, U>[];
  constructor(parsers: () => Parser<T, M, U>[]) {
    super();
    this.parsers = parsers;
  }

  parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseResult<M, U> {
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
export function choice<T, M, As, K extends keyof As>(grammar: () => ParsersFor<T, M, As>, ...keys: K[]) {
  return new ChoiceParser<T, M, As[K]>(() => {
    const g = grammar();
    return keys.map(k => g[k]);
  });
}

export type MessageFragment<T, M> = (head: T[], from: number, debugContext: DebugContext<T>) => M;

export class BaseFailParser<T, M> extends Parser<T, M, any> {
  fragments: (MessageFragment<T, M> | M[])[];

  constructor(...fragments: (MessageFragment<T, M> | M[])[]) {
    super();
    this.fragments = fragments;
  }

  parse(stream: T[], from: number, debugContext: DebugContext<T>): ParseError<M> {
    let joined: M[] = [];
    for (let fragment of this.fragments) {
      if (Array.isArray(fragment)) {
        joined.push(...fragment);
      } else {
        joined.push(fragment(stream, from, debugContext));
      }
    }
    return {
      message: joined,
    };
  }
}
