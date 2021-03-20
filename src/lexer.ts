import { SourceLocation } from "./ir";

export type ErrorElement = string | SourceLocation;

export interface IdenToken {
	tag: "iden",
	name: string,
	location: SourceLocation,
};

export interface TypeIdenToken {
	tag: "type-iden",
	name: string,
	location: SourceLocation,
};

export interface TypeKeywordToken {
	tag: "type-keyword",
	keyword: keyof typeof TYPE_KEYWORDS,
	location: SourceLocation,
};

export interface KeywordToken {
	tag: "keyword",
	keyword: keyof typeof KEYWORDS,
	location: SourceLocation,
};

export interface TypeVarToken {
	tag: "type-var",
	// N.B.: This does NOT include the "#".
	name: string,
	location: SourceLocation,
};

export interface StringLiteralToken {
	tag: "string-literal",
	// TODO: Encoding?
	value: string,
	location: SourceLocation,
}

export interface NumberLiteralToken {
	tag: "number-literal",
	// TODO: Precision?
	value: number,
	location: SourceLocation,
}

export interface PunctuationToken {
	tag: "punctuation",
	symbol: keyof typeof PUNCTUATION,
	location: SourceLocation,
}

export interface OperatorToken {
	tag: "operator",
	operator: keyof typeof OPERATORS,
	location: SourceLocation,
}

export interface EOFToken {
	tag: "eof",
	location: SourceLocation,
}

// These keywords are reserved, but unused. Using them in a program is a syntax
// error.
export const RESERVED = {
	"Never": true,

	"async": true,
	"await": true,
	"break": true,
	"enum": true,
	"for": true,
	"function": true,
	"of": true,
	"record": true,
	"resource": true,
	"resume": true,
	"service": true,
	"test": true,
	"type": true,
	"until": true,
	"while": true,
	"yield": true,
};

export const TYPE_KEYWORDS = {
	"Unit": true,
	"Boolean": true,
	"Int": true,
	"String": true,
	"This": true,
};

export const KEYWORDS = {
	"and": true,
	"assert": true,
	"case": true,
	"class": true,
	"do": true,
	"else": true,
	"elseif": true,
	"ensures": true,
	"false": true,
	"fn": true,
	"forall": true,
	"foreign": true,
	"if": true,
	"import": true,
	"implies": true,
	"interface": true,
	"is": true,
	"isa": true,
	"match": true,
	"method": true,
	"new": true,
	"not": true,
	"or": true,
	"package": true,
	"proof": true,
	"record": true,
	"requires": true,
	"return": true,
	"this": true,
	"true": true,
	"union": true,
	"unit": true,
	"var": true,
	"when": true,
};

export const OPERATORS = {
	// N.B.: Iteration order determines 'priority', so longer sequences MUST
	// come first.
	// N.B.: Sequences must NOT contain `//`, so that they remain comments.

	"==": true,
	"!=": true,
	"<=": true,
	">=": true,
	"++": true,

	"+": true,
	"-": true,
	"/": true,
	"*": true,
	"%": true,
	"<": true,
	">": true,
};

export const PUNCTUATION = {
	"=": true,
	"(": true,
	")": true,
	"{": true,
	"}": true,
	"[": true,
	"]": true,
	"|": true,
	".": true,
	",": true,
	":": true,
	";": true,
};

export type Token = IdenToken | TypeIdenToken | TypeVarToken
	| KeywordToken | TypeKeywordToken
	| StringLiteralToken | NumberLiteralToken
	| PunctuationToken | OperatorToken
	| EOFToken;

/// THROWS LexError
export function tokenize(blob: string, fileID: string): Token[] {
	let tokens: Token[] = [];
	let from = 0;
	while (from < blob.length) {
		const result = parseToken(blob, from, fileID);
		if (result.token !== null) {
			tokens.push(result.token);
		}
		from += result.consumed;
	}
	tokens.push({
		tag: "eof",
		location: { fileID, offset: blob.length, length: 0 },
	});
	return tokens;
}

/// THROWS LexError
function parseToken(blob: string, from: number, fileID: string): { token: Token | null, consumed: number } {
	const head = blob[from];
	if (head === " " || head === "\n" || head == "\t" || head == "\r") {
		return { token: null, consumed: 1 };
	} else if ("a" <= head && head <= "z") {
		// Parse an identifier or a keyword.
		const breaks = findWordBreak(blob, from, fileID);
		const location = {
			fileID,
			offset: from,
			length: breaks - from,
		};
		const word = blob.substring(from, breaks);
		if (word in KEYWORDS) {
			return {
				token: {
					tag: "keyword",
					keyword: word as keyof typeof KEYWORDS,
					location,
				},
				consumed: breaks - from,
			};
		} else if (word in RESERVED) {
			throw new LexError([
				"Found the reserved term `" + word + "` at",
				location,
			]);
		} else {
			return {
				token: {
					tag: "iden",
					name: word,
					location,
				},
				consumed: breaks - from,
			};
		}
	} else if ("A" <= head && head <= "Z") {
		// Parse a type-identifier or a type keyword.
		const breaks = findWordBreak(blob, from, fileID);
		const location = {
			fileID,
			offset: from,
			length: breaks - from,
		};
		const word = blob.substring(from, breaks);
		if (word in TYPE_KEYWORDS) {
			return {
				token: {
					tag: "type-keyword",
					keyword: word as keyof typeof TYPE_KEYWORDS,
					location,
				},
				consumed: breaks - from,
			};
		} else if (word in RESERVED) {
			throw new LexError([
				"Found the reserved term `" + word + "` at",
				location,
			]);
		} else {
			return {
				token: {
					tag: "type-iden",
					name: word,
					location,
				},
				consumed: breaks - from,
			};
		}
	} else if (head === "/" && blob[from + 1] === "/") {
		// Parse a line comment.
	} else if ("0" <= head && head <= "9") {
		// Parse a number literal.
		const breaks = findWordBreak(blob, from, fileID);
		const location = {
			fileID, offset: from, length: breaks - from,
		};

		const slice = blob.substr(from, breaks - from);
		if (!/^[0-9]+$/.test(blob.substr(from, breaks - from)) || slice.length > 10) {
			throw new LexError([
				"Found a malformed integer literal at",
				location,
			]);
		}

		const value = parseInt(slice);

		return {
			token: {
				tag: "number-literal",
				value,
				location,
			},
			consumed: breaks - from,
		};
	} else if (head === "#") {
		// Parse a type variable or keyword.
		const first = blob[from + 1];
		if (!("A" <= first && first <= "Z")) {
			const location = {
				fileID,
				offset: from,
				length: 2,
			};
			throw new LexError([
				"Expected a capital letter after `#` at",
				location
			]);
		}

		const breaks = findWordBreak(blob, from + 1, fileID);
		const location = {
			fileID,
			offset: from,
			length: breaks - from,
		};
		return {
			token: {
				tag: "type-var",
				name: blob.substring(from + 1, breaks),
				location,
			},
			consumed: breaks - from,
		};
	} else if (head === "\"") {
		// Parse a string literal.
		let content = "";
		let escaped = false;
		let end = null;
		for (let i = from + 1; i < blob.length; i++) {
			const at = blob[i];
			if (at === "\n") {
				throw new LexError([
					"Found string literal interrupted by newline at",
					{
						fileID,
						offset: from,
						length: i - from,
					},
				]);
			} else if (at === "\r") {
				throw new LexError([
					"Found string literal interrupted by carriage return at",
					{
						fileID,
						offset: from,
						length: i - from,
					},
				]);
			} else if (escaped) {
				if (at === "n") {
					content += "\n";
				} else if (at === "r") {
					content += "\r";
				} else if (at === "t") {
					content += "\t";
				} else if (at === "\"") {
					content += "\"";
				} else if (at === "\\") {
					content += "\\";
				} else {
					throw new LexError([
						"Found invalid escape in string literal at",
						{
							fileID,
							offset: i - 1,
							length: 2,
						},
					]);
				}
				escaped = false;
				continue;
			} else if (at === "\\") {
				escaped = true;
			} else if (at === "\"") {
				end = i + 1;
				break;
			} else {
				content += at;
			}
		}

		if (end === null) {
			throw new LexError([
				"Found unfinished string literal at",
				{
					fileID,
					offset: from,
					length: blob.length - from,
				},
			]);
		}
		return {
			token: {
				tag: "string-literal",
				value: content,
				location: {
					fileID,
					offset: from,
					length: end - from,
				},
			},
			consumed: end - from,
		};
	} else {
		// Attempt to parse punctuations.
		for (let k = Math.min(blob.length - from, 2); k >= 1; k--) {
			const lexeme = blob.substr(from, k);
			if (lexeme in PUNCTUATION) {
				return {
					token: {
						tag: "punctuation",
						symbol: lexeme as keyof typeof PUNCTUATION,
						location: {
							fileID,
							offset: from,
							length: k,
						},
					},
					consumed: k,
				};
			} else if (lexeme in OPERATORS) {
				return {
					token: {
						tag: "operator",
						operator: lexeme as keyof typeof OPERATORS,
						location: {
							fileID,
							offset: from,
							length: k,
						},
					},
					consumed: k,
				};
			}
		}
	}

	const location: SourceLocation = {
		fileID,
		offset: from,
		length: 1,
	};
	throw new LexError(["Found an unexpected symbol at", location]);
}

/// RETURNS the first index after from which is not a letter/number/underscore 
/// that is valid within Shiru identifiers.
function findWordBreak(blob: string, from: number, fileID: string) {
	let end = blob.length;
	for (let i = from + 1; i < blob.length; i++) {
		const c = blob[i];
		const lower = "a" <= c && c <= "z";
		const upper = "A" <= c && c <= "Z";
		const digit = "0" <= c && c <= "9";
		const under = c === "_";
		if (!lower && !upper && !digit && !under) {
			end = i;
			break;
		}
	}
	const doubleUnder = blob.substring(from, end).indexOf("__", from);
	if (doubleUnder >= 0) {
		throw new LexError([
			"Found invalid double underscore in identifier at",
			{
				fileID,
				offset: from + doubleUnder,
				length: 2,
			},
		]);
	}
	return end;
}

export class LexError {
	constructor(public message: ErrorElement[]) { }

	toString() {
		return JSON.stringify(this.message);
	}
}
