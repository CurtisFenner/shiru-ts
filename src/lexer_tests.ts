import { LexError, tokenize } from "./lexer";
import { assert } from "./test";

export const tests = {
	"simple"() {
		const blob = `class Something {}`;
		const tokens = tokenize(blob, "test-file");
		assert(tokens, "is equal to", [
			{
				tag: "keyword",
				keyword: "class",
				location: { fileID: "test-file", offset: 0, length: 5 },
			},
			{
				tag: "type-iden",
				name: "Something",
				location: { fileID: "test-file", offset: 6, length: 9 },
			},
			{
				tag: "punctuation",
				symbol: "{",
				location: { fileID: "test-file", offset: 16, length: 1 },
			},
			{
				tag: "punctuation",
				symbol: "}",
				location: { fileID: "test-file", offset: 17, length: 1 },
			},
		]);
	},
	"type-var-number"() {
		const blob = `#0`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Expected a capital letter after `#` at",
			{ fileID: "test-file", offset: 0, length: 2 },
		]));
	},
	"type-var-lowercase"() {
		const blob = `#a`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Expected a capital letter after `#` at",
			{ fileID: "test-file", offset: 0, length: 2 },
		]));
	},
	"type-var-space"() {
		const blob = `# a`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Expected a capital letter after `#` at",
			{ fileID: "test-file", offset: 0, length: 2 },
		]));
	},
	"string-literal-interrupted-newline"() {
		const blob = `"hello\nworld"`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Found string literal interrupted by newline at",
			{ fileID: "test-file", offset: 0, length: 6 },
		]));
	},
	"string-literal-interrupted-carriage-return"() {
		const blob = `"hello\rworld"`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Found string literal interrupted by carriage return at",
			{ fileID: "test-file", offset: 0, length: 6 },
		]));
	},
	"string-literal-bad-escape"() {
		const blob = `"hello\\'world"`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Found invalid escape in string literal at",
			{ fileID: "test-file", offset: 6, length: 2 },
		]));
	},
	"string-literal-unfinished"() {
		const blob = `"hello world`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Found unfinished string literal at",
			{ fileID: "test-file", offset: 0, length: 12 },
		]));
	},
	"unexpected-dollar"() {
		const blob = "hello $ world";
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Found an unexpected symbol at",
			{ fileID: "test-file", offset: 6, length: 1 },
		]));
	}
};
