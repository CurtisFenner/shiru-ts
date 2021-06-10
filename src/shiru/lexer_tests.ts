import { LexError, tokenize } from "./lexer";
import { assert } from "./test";

export const tests = {
	"simple"() {
		const blob = `class Something[#T] {}`;
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
				symbol: "[",
				location: { fileID: "test-file", offset: 15, length: 1 },
			},
			{
				tag: "type-var",
				name: "T",
				location: { fileID: "test-file", offset: 16, length: 2 },
			},
			{
				tag: "punctuation",
				symbol: "]",
				location: { fileID: "test-file", offset: 18, length: 1 },
			},
			{
				tag: "punctuation",
				symbol: "{",
				location: { fileID: "test-file", offset: 20, length: 1 },
			},
			{
				tag: "punctuation",
				symbol: "}",
				location: { fileID: "test-file", offset: 21, length: 1 },
			},
			{
				tag: "eof",
				location: { fileID: "test-file", offset: 22, length: 0 },
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
	},
	"basic-integer"() {
		const blob = `1 12`;
		const tokens = tokenize(blob, "test-file");
		assert(tokens, "is equal to", [
			{
				tag: "number-literal",
				int: "1",
				location: { fileID: "test-file", offset: 0, length: 1 },
			},
			{
				tag: "number-literal",
				int: "12",
				location: { fileID: "test-file", offset: 2, length: 2 },
			},
			{
				tag: "eof",
				location: { fileID: "test-file", offset: 4, length: 0 },
			},
		]);
	},
	"invalid-integer"() {
		const blob = `1b2`;
		assert(() => tokenize(blob, "test-file"), "throws", new LexError([
			"Found a malformed integer literal at",
			{ fileID: "test-file", offset: 0, length: 3 }
		]));
	},
	"comments"() {
		const blob = `
		one // alpha beta
		two // gamma delta`;
		const tokens = tokenize(blob, "test-file");
		assert(tokens, "is equal to", [
			{
				tag: "iden",
				name: "one",
				location: { fileID: "test-file", offset: 3, length: 3 },
			},
			{
				tag: "iden",
				name: "two",
				location: { fileID: "test-file", offset: 23, length: 3 },
			},
			{
				tag: "eof",
				location: { fileID: "test-file", offset: 41, length: 0 },
			},
		]);
	},
};
