export interface BuiltFile {
	/**
	 * The relative path for the file.
	 */
	path: string,

	/**
	 * The contents of the file.
	 */
	content: Uint8Array,

	tags: string[],
}

const asciiMapping: Record<string, string> = {
	"+": "plus",
	"-": "dash",
	"$": "dollar",
	"/": "slash",
	"\\": "backslash",
	"=": "equal",
	":": "colon",
	"*": "star",
	"@": "at",
	"!": "bang",
	"?": "question",
	".": "dot",
	",": "comma",
	"|": "pipe",
	"<": "less",
	">": "greater",
	"'": "prime",
};

/**
 * Turn a string (with some restrictions) into an ASCII identifier that can be
 * used in most programming languages.
 * 
 * This transformation is not guaranteed to be stable and could change between
 * different versions or implementations of the compiler.
 */
export function asciiNameMangle(prefix: string, s: string): string {
	if (s === "") {
		throw new Error("asciiNameMangle: name must not be empty");
	} else if (s.indexOf(" ") >= 0) {
		throw new Error("asciiNameMangle: name must not contain ASCII space");
	}

	const safe = /[a-zA-Z0-9_]/;
	const out = [];
	for (let i = 0; i < s.length; i++) {
		const c = s[i];
		if (c in asciiMapping) {
			out.push("__" + asciiMapping[c]);
		} else if (c.match(safe)) {
			out.push(c);
		} else {
			out.push("__" + c.charCodeAt(0));
		}
	}

	return prefix + out.join("");
}

export class SourceUTF8Generator {
	private lines: string[] = [""];
	private indenting: string[] = [];

	append(text: string): this {
		if (!text) {
			return this;
		}

		let top = this.lines[this.lines.length - 1];
		if (top === "") {
			top = this.indenting.join("");
		}
		this.lines[this.lines.length - 1] = top + text;
		return this;
	}

	newLine(indent?: string): this {
		if (indent) {
			this.indenting.push(indent);
		}
		this.lines.push("");
		return this;
	}

	dedent(indent: string): this {
		const top = this.indenting.pop();
		if (top !== indent) {
			throw new Error("SourceUTF8Generator.dedent: indent `" + indent + "` does not last `" + top + "`");
		}
		return this;
	}

	encode(): Uint8Array {
		return new TextEncoder().encode(this.lines.join("\n"));
	}
}
