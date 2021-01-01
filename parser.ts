/// `ParseError` represents a problem hit while parsing.
export type ParseError<M> = {
  message: M[],
};

/// `ParsersFor` is a utility type to make it easy to make a recursively defined
/// "grammar" object type-safe.
export type ParsersFor<Token, M, ASTs> = {
  [P in keyof ASTs]: Parser<Token, M, ASTs[P]>
};

/// `Stream` represents an immutable cursor into a (possibly lazily loaded)
/// sequence of tokens.
export interface Stream<Token> {
  /// `read()` returns `null` when there are no more tokens in this string.
  /// Otherwise, it returns the next token, and a cursor into the remainder of
  /// the stream.
  read(): [Token | null, Stream<Token>],
}

/// `TokenSpan` represents an contiguous range of tokens within a token stream.
export interface TokenSpan<Token> {
  /// The first Token in this span.
  first: Token | null,

  /// The Token which immediately follows this span.
  following: Token | null,
};


export type DebugContext<Token> = Record<string, TokenSpan<Token>>;

/// Parser represents a parser from a stream of `Token`s to a particular 
/// `Result` AST.
export abstract class Parser<Token, M, Result> {
  abstract parse(stream: Stream<Token>, debugContext: DebugContext<Token>): [Result, Stream<Token>] | null | ParseError<M>;

  map<Q>(f: (r: Result) => Q) {
    return new MapParser<Token, M, Result, Q>(this, f);
  }

  required(...fragments: (MessageFragment<Token, M> | M[])[]): Parser<Token, M, Result> {
    return new ChoiceParser(() => this, () => new BaseFailParser(...fragments));
  }
};

export class MapParser<T, M, A, B> extends Parser<T, M, B> {
  parser: Parser<T, M, A>;
  f: (a: A) => B;

  constructor(parser: Parser<T, M, A>, f: (a: A) => B) {
    super();
    this.parser = parser;
    this.f = f;
  }

  parse(stream: Stream<T>, debugContext: DebugContext<T>): null | ParseError<M> | [B, Stream<T>] {
    const result = this.parser.parse(stream, debugContext);
    if (Array.isArray(result)) {
      const mapped = this.f(result[0]);
      return [mapped, result[1]];
    } else {
      return result;
    }
  }
}

export class EndOfStreamParser<T, M> extends Parser<T, M, {}> {
  parse(stream: Stream<T>): [{}, Stream<T>] | null {
    if (stream.read() === null) {
      return [{}, stream];
    }
    return null;
  }
}

export class TokenParser<T, M, R> extends Parser<T, M, R> {
  f: (t: T) => (null | R);

  constructor(f: (t: T) => (null | R)) {
    super();
    this.f = f;
  }

  parse(stream: Stream<T>): null | [R, Stream<T>] {
    const front = stream.read();
    if (front[0] === null) return null;
    const value = this.f(front[0]);
    if (value === null) return null;
    return [value, front[1]];
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

  parse(stream: Stream<T>, debugContext: DebugContext<T>): (ParseError<M> | null | [R[], Stream<T>]) {
    const list: R[] = [];
    while (!this.max || list.length < this.max) {
      const result = this.element.parse(stream, debugContext);
      if (result === null) {
        break;
      } else if (Array.isArray(result)) {
        list.push(result[0]);
        stream = result[1];
      } else {
        return result;
      }
    }

    if (this.min && list.length < this.min) {
      return null;
    }

    return [list, stream];
  }
};

type RecordParserDescription<T, M, R> = { [P in keyof R]: (() => Parser<T, M, R[P]>) };

export class RecordParser<T, M, R> extends Parser<T, M, R> {
  description: RecordParserDescription<T, M, R>;

  constructor(description: RecordParserDescription<T, M, R>) {
    super();
    this.description = description;
  }

  parse(stream: Stream<T>, debugContext: DebugContext<T>): (ParseError<M> | null | [R, Stream<T>]) {
    // Each RecordParser opens a new debug context.
    // TODO: Link the debug context to the parent context.
    debugContext = {};

    let obj: R = {} as R;
    let first = stream.read()[0];
    for (let p in this.description) {
      const d = this.description[p];
      const parser = d();
      let result = parser.parse(stream, debugContext);
      if (result === null) {
        return null;
      } else if (!Array.isArray(result)) {
        return result;
      }

      obj[p] = result[0];
      stream = result[1];
      const next = stream.read()[0];
      debugContext[p] = { first, following: next };
      first = next;
    }
    return [obj, stream];
  }
}

export class ChoiceParser<T, M, U> extends Parser<T, M, U> {
  parsers: (() => Parser<T, M, U>)[];
  constructor(...parsers: (() => Parser<T, M, U>)[]) {
    super();
    this.parsers = parsers;
  }

  parse(stream: Stream<T>, debugContext: DebugContext<T>): null | ParseError<M> | [U, Stream<T>] {
    for (let parser of this.parsers) {
      let result = parser().parse(stream, debugContext);
      if (result === null) {
        continue;
      }
      return result;
    }
    return null;
  }
}

export type MessageFragment<T, M> = (head: Stream<T>, debugContext: DebugContext<T>) => M;

export class BaseFailParser<T, M> extends Parser<T, M, any> {
  fragments: (MessageFragment<T, M> | M[])[];

  constructor(...fragments: (MessageFragment<T, M> | M[])[]) {
    super();
    this.fragments = fragments;
  }

  parse(stream: Stream<T>, debugContext: DebugContext<T>): ParseError<M> {
    let joined: M[] = [];
    for (let fragment of this.fragments) {
      if (Array.isArray(fragment)) {
        joined.push(...fragment);
      } else {
        joined.push(fragment(stream, debugContext));
      }
    }
    return {
      message: joined,
    };
  }
}
