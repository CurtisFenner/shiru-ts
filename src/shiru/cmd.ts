import * as fs from "fs";
import path = require("path");
import * as process from "process";
import { codegenJs } from "./codegen_js.js";
import * as diagnostics from "./diagnostics.js";
import * as grammar from "./grammar.js";
import * as ir from "./ir.js";
import * as lexer from "./lexer.js";
import * as library from "./library.js";

export function processCommands(args: string[]): number {
	if (args[0] === "interpret") {
		return processInterpretCommand(args.slice(1));
	} else if (args[0] === "compile") {
		return processCompileCommand(args.slice(1));
	}

	console.error("Unknown command `" + args[0] + "`");
	console.error("Supported commands:");
	console.error("\tinterpret <main> - <files>");
	console.error("\tcompile js <target dir> - <files>");
	return 1;
}

function printError(e: { message: lexer.ErrorElement[] }, sourceList: library.SourceFile[]) {
	console.error(library.displayError(e, sourceList));
}

function processCompileCommand(args: string[]): number {
	if (args[0] !== "js") {
		console.error("Unknown compile target `" + args[0] + "` in compile command");
		console.error("\tSupported targets:\n\t\tjs");
		return 1;
	}
	const targetDirectory = args[1];
	if (!targetDirectory) {
		console.error("Expected target directory in compile command");
		return 1;
	}

	if (args[2] !== "-") {
		console.error("Expected `-` in compile command");
		return 1;
	}

	const sourcePaths = args.slice(3);
	const compiled = compileSourcePaths(sourcePaths);
	if (typeof compiled === "number") {
		return compiled;
	}

	const files = codegenJs(compiled);
	for (const file of files) {
		const resolved = path.resolve(targetDirectory, file.path);
		fs.writeFileSync(resolved, file.content);
	}
	return 0;
}

function processInterpretCommand(args: string[]): number {
	if (args[1] !== "-") {
		console.error("Expected `-` in interpret command");
		return 1;
	}

	const mainFunction = args[0];
	const sourcePaths = args.slice(2);
	const compiled = compileSourcePaths(sourcePaths);
	if (typeof compiled === "number") {
		return compiled;
	}

	const result = library.interpret(compiled, mainFunction as library.FunctionID, []);
	console.log(JSON.stringify(result, (key, value) => typeof value === "bigint" ? String(value) : value, "\t"));
	return 0;
}

function compileSourcePaths(sourcePaths: string[]): number | ir.Program {
	if (new Set(sourcePaths).size !== sourcePaths.length) {
		console.error("Do not repeat source paths");
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

	const asts: Record<string, grammar.Source> = {};
	for (let i = 0; i < sourceFiles.length; i++) {
		const sourceFile = sourceFiles[i];
		const ast = library.parseSource(sourceFile);
		if (ast instanceof lexer.LexError || ast instanceof grammar.ParseError) {
			printError(ast, sourceFiles);
			return 2;
		}
		asts[i.toFixed(0)] = ast;
	}

	const compiled = library.compileASTs(asts);
	if (compiled instanceof diagnostics.SemanticError) {
		printError(compiled, sourceFiles);
		return 3;
	}

	const verificationErrors = library.verifyProgram(compiled);
	if (verificationErrors instanceof diagnostics.SemanticError) {
		printError(verificationErrors, sourceFiles);
		return 4;
	}

	for (let v of verificationErrors) {
		printError(library.formatVerificationFailure(v), sourceFiles);
		console.error("");
	}
	if (verificationErrors.length !== 0) {
		return 5;
	}

	return compiled;
}

if (require.main === module) {
	processCommands(process.argv.slice(2));
}
