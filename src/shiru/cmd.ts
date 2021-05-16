import * as fs from "fs";
import * as process from "process";
import * as diagnostics from "./diagnostics";
import * as grammar from "./grammar";
import * as interpreter from "./interpreter";
import * as lexer from "./lexer";
import * as library from "./library";

export function processCommands(args: string[]): number {
	if (args[0] === "interpret") {
		return processInterpretCommand(args.slice(1));
	}

	console.error("Unknown command `" + args[0] + "`");
	console.error("Supported commands:");
	console.error("\tinterpret <main> - <files>");
	return 1;
}

function printError(e: { message: lexer.ErrorElement[] }, sourceList: library.SourceFile[]) {
	console.error(library.displayError(e, sourceList));
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

	const lines: string[] = [];
	interpreter.printProgram(compiled, lines);
	for (const line of lines) {
		console.log(line);
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

	const result = library.interpret(compiled, mainFunction as library.FunctionID, []);
	console.log(JSON.stringify(result, null, "\t"));
	return 0;
}

if (require.main === module) {
	processCommands(process.argv.slice(2));
}
