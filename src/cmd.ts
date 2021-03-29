import * as fs from "fs";
import * as process from "process";
import * as diagnostics from "./diagnostics";
import * as grammar from "./grammar";
import * as interpreter from "./interpreter";
import * as ir from "./ir";
import * as lexer from "./lexer";
import * as semantics from "./semantics";
import * as verify from "./verify";

export function processCommands(args: string[]): number {
	if (args[0] === "interpret") {
		return processInterpretCommand(args.slice(1));
	}

	console.error("Unknown command `" + args[0] + "`");
	console.error("Supported commands:");
	console.error("\tinterpret <main> - <files>");
	return 1;
}

interface SourceFile {
	path: string,
	content: string,
}

function processInterpretCommand(args: string[]): number {
	if (args[1] !== "-") {
		console.error("Expected `-` in interpret command");
		return 1;
	}

	const mainFunction = args[0];
	const sourcePaths = args.slice(2);
	if (new Set(sourcePaths).size !== sourcePaths.length) {
		console.error("Do not repeat south paths");
		return 1;
	}

	const sourceFiles = [];
	for (let sourcePath of sourcePaths) {
		const content = fs.readFileSync(sourcePath, { encoding: "utf-8" });
		sourceFiles.push({
			path: sourcePath,
			content,
		});
	}

	const asts = [];
	for (let sourceFile of sourceFiles) {
		try {
			const ast = grammar.parseSource(sourceFile.content, sourceFile.path);
			asts.push(ast);
		} catch (e) {
			if (e instanceof lexer.LexError || e instanceof grammar.ParseError) {
				printError(e, sourceFiles);
				return 2;
			} else {
				throw e;
			}
		}
	}

	let compiled;
	try {
		compiled = semantics.compileSources(asts);
	} catch (e) {
		if (e instanceof diagnostics.SemanticError) {
			printError(e, sourceFiles);
			return 3;
		} else {
			throw e;
		}
	}

	const lines: string[] = [];
	interpreter.printProgram(compiled, lines);
	for (const line of lines) {
		console.log(line);
	}

	const verificationErrors = verify.verifyProgram(compiled);
	for (let v of verificationErrors) {
		let err: diagnostics.SemanticError;
		if (v.tag === "failed-assert") {
			err = {
				message: [
					"An assert has not been shown to hold at",
					v.assertLocation ? v.assertLocation : " (unknown location)",
				],
			};
		} else if (v.tag === "failed-precondition") {
			err = {
				message: [
					"A precondition has not been shown to hold at",
					v.callLocation,
					"The precondition was defined at",
					v.preconditionLocation,
				],
			};
		} else if (v.tag === "failed-return") {
			err = {
				message: [
					"A function has not been shown to always return a value at",
					v.blockEndLocation ? v.blockEndLocation : " (unknown location)",
				],
			};
		} else {
			const _: never = v;
			throw new Error("unhandled `" + v["tag"] + "`");
		}
		printError(err, sourceFiles);
		console.error("");
	}
	if (verificationErrors.length !== 0) {
		return 4;
	}

	const result = interpreter.interpret(mainFunction, [], compiled, {
		"Int+": ([a, b]: interpreter.Value[]) => {
			if (a.sort !== "int") throw new Error("bad argument");
			if (b.sort !== "int") throw new Error("bad argument");
			return [{ sort: "int", int: a.int + b.int }];
		},
		"Int-": ([a, b]: interpreter.Value[]) => {
			if (a.sort !== "int") throw new Error("bad argument");
			if (b.sort !== "int") throw new Error("bad argument");
			return [{ sort: "int", int: a.int - b.int }];
		},
		"Int==": ([a, b]: interpreter.Value[]) => {
			if (a.sort !== "int") throw new Error("bad argument");
			if (b.sort !== "int") throw new Error("bad argument");
			return [{ sort: "boolean", boolean: a.int == b.int }];
		},
	});
	console.log(JSON.stringify(result, null, "\t"));
	return 0;
}

class TextDocument {
	public lines: { content: string, offset: number }[] = [];
	constructor(private path: string, private content: string) {
		let offset = 0;
		for (let line of content.split("\n")) {
			this.lines.push({
				content: line + " ",
				offset,
			});
			offset += line.length + 1;
		}
	}

	locate(query: number): { offset: number, line0: number, char0: number } {
		if (query <= 0) {
			return { offset: 0, line0: 0, char0: 0 };
		}
		for (let i = 0; i < this.lines.length; i++) {
			let next = this.lines[i].offset + this.lines[i].content.length;
			if (query <= next) {
				return { offset: query, line0: i, char0: query - this.lines[i].offset };
			}
		}
		const lastLine = this.lines[this.lines.length - 1];
		return {
			offset: lastLine.offset + lastLine.content.length,
			line0: this.lines.length - 1,
			char0: lastLine.content.length,
		};
	}

	/// `getLocus` returns a brief "one word" description of the given location.
	getLocus(location: ir.SourceLocation): string {
		const start = this.locate(location.offset);
		const end = this.locate(location.offset + location.length);
		if (start.line0 === end.line0) {
			return `${this.path}:${start.line0 + 1}:${start.char0 + 1}-${end.char0 + 1}`;
		} else {
			return `${this.path}:${start.line0 + 1}:${start.char0 + 1}-${end.line0 + 1}:${end.line0 + 1}`;
		}
	}

	getSnippetLine(
		line0: number,
		highlightStart: { offset: number, line0: number, char0: number },
		highlightEnd: { offset: number, line0: number, char0: number },
		options: { tabSize: number },
	) {
		let offset = this.lines[line0].offset;
		const source = this.lines[line0].content;
		const beforeHighlighted = source.substring(0, highlightStart.offset - offset);
		const highlighted = source.substring(highlightStart.offset - offset, highlightEnd.offset - offset);
		const afterHighlighted = source.substring(highlightEnd.offset - offset);
		const groups = [beforeHighlighted, highlighted, afterHighlighted];
		let carets = "";
		let formatted = "";
		let column = 0;
		for (let i = 0; i < 3; i++) {
			const group = groups[i];
			const caret = (i === 1) ? "^" : " ";
			const TAB_OR_NONTABS = /(?:\t|[^\t]+)/g;
			let match;
			while ((match = TAB_OR_NONTABS.exec(group)) !== null) {
				let word = match[0];
				if (word === "\t") {
					const w = options.tabSize - column % options.tabSize;
					word = " ".repeat(w);
				}

				formatted += word;
				column += word.length;
				carets += caret.repeat(word.length);
				column += word.length;
			}
		}

		return {
			formatted: formatted,
			carets: carets,
		};
	}

	getSnippet(highlighting: ir.SourceLocation, options: { tabSize: number }) {
		const start = this.locate(highlighting.offset);
		const end = this.locate(highlighting.offset + highlighting.length);

		const rows: ({ tag: "ellipses" } | { tag: "content", line0: number, formatted: string, carets: string | null })[] = [];
		for (let y of new Set([start.line0 - 1, start.line0, start.line0 + 1, end.line0 - 1, end.line0, end.line0 + 1])) {
			if (y < 0 || y >= this.lines.length) {
				continue;
			}

			if (rows.length !== 0) {
				const previous = rows[rows.length - 1];
				if (previous.tag === "content" && previous.line0 < y - 1) {
					rows.push({ tag: "ellipses" });
				}
			}

			const row = this.getSnippetLine(y, start, end, options);
			rows.push({
				tag: "content",
				line0: y,
				formatted: row.formatted,
				carets: row.carets.trim() !== "" ? row.carets : null,
			});
		}
		return rows;
	}
}

function printError(e: { message: lexer.ErrorElement[] }, sourceList: SourceFile[]) {
	const sources: Record<string, TextDocument> = {};

	let s = "ERROR: ";
	for (let m of e.message) {
		if (typeof m === "string") {
			s += m;
		} else {
			const fileID = m.fileID;
			if (!sources[fileID]) {
				const source = sourceList.find(x => x.path === fileID);
				if (!source) {
					s += fileID + ":?" + "\n";
					continue;
				}
				sources[fileID] = new TextDocument(fileID, source.content);
			}
			const source = sources[fileID];
			s += " " + source.getLocus(m);
			s += ":\n";
			const mWide: ir.SourceLocation = {
				fileID: m.fileID,
				offset: m.offset,
				length: Math.max(1, m.length),
			};
			const rows = source.getSnippet(mWide, { tabSize: 4 });
			const NUMBER_TRAY = 8;
			for (let row of rows) {
				if (row.tag === "content") {
					const n = (row.line0 + 1).toFixed(0);
					s += "\t" + " ".repeat(NUMBER_TRAY - n.length) + n + " | ";
					s += row.formatted;
					if (row.carets !== null) {
						s += "\n";
						s += "\t" + " ".repeat(NUMBER_TRAY) + " | ";
						s += row.carets;
					}
				} else {
					s += "\t" + " ".repeat(NUMBER_TRAY - 3) + "... |"
				}
				s += "\n";
			}
			s += "\n";
		}
	}
	console.error(s);
}


if (require.main === module) {
	processCommands(process.argv.slice(2));
}
