import * as ir from "./ir.js";
import * as codegen from "./codegen.js";

export function codegenJs(program: ir.Program): codegen.BuiltFile[] {
	const implementation = new codegen.SourceUTF8Generator();
	const names = [];

	implementation.append(`
function Bytes__plus__plus(a, b) {
	return a + b;
}

function Int__equal__equal(a, b) {
	return a === b;
}

function Int__dash(a, b) {
	return a - b;
}

function Int__plus(a, b) {
	return a + b;
}
`);

	// Generate all functions
	for (const [fnID, fnDefinition] of Object.entries(program.functions)) {
		const name = codegenFn(program, implementation, fnID as ir.FunctionID, fnDefinition);
		names.push(name);
	}

	// Generate all vtables
	for (const [vtableID, vtable] of Object.entries(program.globalVTableFactories)) {
		const name = codegenVtable(program, implementation, vtableID, vtable);
	}

	return [
		{
			path: "impl.mjs",
			content: implementation.encode(),
			tags: ["mjs"],
		},
	];
}

function globalVtableName(name: string): string {
	return codegen.asciiNameMangle("vtable_", name);
}

function fnName(name: ir.FunctionID): string {
	return codegen.asciiNameMangle("fn_", name);
}

function varName(name: ir.VariableID): string {
	return codegen.asciiNameMangle("var_", name);
}

function vtableMemberName(name: string): string {
	return codegen.asciiNameMangle("v_", name);
}

class VariableScope {
	private frames: string[][] = [[]];
	private shadows: Map<string, string[]> = new Map();
	constraints: Array<{ jsName: string, constraint: ir.ConstraintParameter }> = [];

	open(): void {
		this.frames.push([]);
	}

	close(): void {
		const top = this.frames.pop();
		if (top === undefined) {
			throw new Error("VariableScope.close: no open scopes");
		}
		for (const name of top) {
			const seq = this.shadows.get(name)!;
			seq.pop();
			if (seq.length === 0) {
				this.shadows.delete(name);
			}
		}
	}

	read(variable: ir.VariableID): string {
		const shadows = this.shadows.get(variable);
		if (!shadows) {
			throw new Error("VariableScope.read: no such variable `" + variable + "`");
		}
		return shadows[shadows.length - 1];
	}

	define(variable: ir.VariableID): string {
		let shadows = this.shadows.get(variable);
		if (shadows === undefined) {
			shadows = [];
			this.shadows.set(variable, shadows);
		}
		const mangle = varName(variable);
		const uniqueMangle = shadows.length === 0 ? mangle : mangle + "_" + (shadows.length + 1);
		shadows.push(uniqueMangle);
		return uniqueMangle;
	}

	addConstraint(constraint: ir.ConstraintParameter): string {
		const jsName = this.define("constraint" as ir.VariableID);
		this.constraints.push({ jsName, constraint });
		return jsName;
	}
}

function codegenVtable(
	program: ir.Program,
	implementation: codegen.SourceUTF8Generator,
	vtableID: string,
	vtable: ir.VTableFactory,
): string {
	const jsVtableName = globalVtableName(vtableID);
	const trait = program.interfaces[vtable.provides.interface];
	const closureVtableNames = [];
	for (let i = 0; i < vtable.closures.length; i++) {
		const closure = vtable.closures[i];
		const parameterName = codegen.asciiNameMangle("closure" + i, closure.interface);
		closureVtableNames.push(parameterName);
	}

	implementation.newLine()
		.append("// impl ")
		.append(vtableID)
		.newLine()
		.append("export function ")
		.append(jsVtableName)
		.append("(")
		.append(closureVtableNames.join(", "))
		.append(") {")
		.newLine("\t")
		.append("return {")
		.newLine("\t");

	for (const [memberName, member] of Object.entries(vtable.entries)) {
		const traitSignature = trait.signatures[memberName];
		if (traitSignature === undefined) {
			throw new Error("no such interface member `" + memberName + "`");
		}

		// Generate the uniform parameter list for dynamic calls.
		const traitValueParameters = [];
		for (const parameter of traitSignature.parameters) {
			const prefix = "param" + traitValueParameters.length;
			const mangled = codegen.asciiNameMangle(prefix, parameter.variable);
			traitValueParameters.push(mangled);
		}
		const traitConstraintParameters = [];
		for (const constraintParameter of traitSignature.constraint_parameters) {
			const mangled: string = "constraint" + traitConstraintParameters.length;
			traitConstraintParameters.push(mangled);
		}

		// Generate the internal argument list for this specific implementation.
		const memberParameters = traitValueParameters.concat(traitConstraintParameters);
		const implArguments = [...traitValueParameters];
		for (const constraintSource of member.constraint_parameters) {
			if (constraintSource.source === "closure") {
				implArguments.push(closureVtableNames[constraintSource.closureIndex]);
			} else {
				implArguments.push(traitConstraintParameters[constraintSource.signatureIndex]);
			}
		}

		implementation.append(vtableMemberName(memberName))
			.append("(")
			.append(memberParameters.join(", "))
			.append(") {")
			.newLine("\t")
			.append("return ")
			.append(fnName(member.implementation))
			.append("(")
			.append(implArguments.join(", "))
			.append(");")
			.newLine()
			.dedent("\t")
			.append("},")
			.newLine();
	}

	implementation.dedent("\t")
		.append("};")
		.newLine()
		.dedent("\t")
		.append("}")
		.newLine();

	return jsVtableName;
}

function codegenFn(
	program: ir.Program,
	implementation: codegen.SourceUTF8Generator,
	fnID: ir.FunctionID,
	definition: ir.IRFunction,
): string {
	const scope = new VariableScope();
	const parameters = [];
	for (const parameter of definition.signature.parameters) {
		const jsName = scope.define(parameter.variable);
		parameters.push(jsName);
	}

	for (const constraint of definition.signature.constraint_parameters) {
		const jsName = scope.addConstraint(constraint);
		parameters.push(jsName);
	}

	const jsFnName = fnName(fnID);
	implementation.newLine()
		.append("// fn ")
		.append(fnID)
		.newLine()
		.append("export function ")
		.append(jsFnName)
		.append("(")
		.append(parameters.join(", "))
		.append(") {");
	codegenBlock(program, implementation, definition.body, scope);
	implementation.append("}")
		.newLine();
	return jsFnName;
}

function codegenBlock(
	program: ir.Program,
	implementation: codegen.SourceUTF8Generator,
	block: ir.OpBlock,
	scope: VariableScope,
	cleanup?: () => void,
): void {
	implementation.newLine("\t");
	scope.open();
	for (const op of block.ops) {
		codegenOp(program, implementation, op, scope);
	}
	if (cleanup) {
		cleanup();
	}
	scope.close();
	implementation.dedent("\t");
}

function codegenOp(
	program: ir.Program,
	implementation: codegen.SourceUTF8Generator,
	op: ir.Op,
	scope: VariableScope,
): void {
	if (op.tag === "op-branch") {
		const destinations: string[] = [];
		for (const destination of op.destinations) {
			const destinationJsName = scope.define(destination.destination.variable);
			destinations.push(destinationJsName);
			implementation.append("let ")
				.append(destinationJsName)
				.append(";")
				.newLine();
		}
		implementation.append("if (")
			.append(scope.read(op.condition))
			.append(") {");
		codegenBlock(program, implementation, op.trueBranch, scope, () => {
			for (let i = 0; i < destinations.length; i++) {
				const source = op.destinations[i].trueSource;
				if (source === "undef") {
					continue;
				} else if (source.tag === "variable") {
					implementation.append(destinations[i])
						.append(" = ")
						.append(scope.read(source.variable))
						.append(";")
						.newLine();
				} else {
					const _: never = source.tag;
					throw new Error("codegenOp: unhandled op-branch source tag `" + source["tag"] + "`");
				}
			}
		});
		implementation.append("} else {");
		codegenBlock(program, implementation, op.falseBranch, scope, () => {
			for (let i = 0; i < destinations.length; i++) {
				const source = op.destinations[i].falseSource;
				if (source === "undef") {
					continue;
				} else if (source.tag === "variable") {
					implementation.append(destinations[i])
						.append(" = ")
						.append(scope.read(source.variable))
						.append(";")
						.newLine();
				} else {
					const _: never = source.tag;
					throw new Error("codegenOp: unhandled op-branch source tag `" + source["tag"] + "`");
				}
			}
		});
		implementation.append("}")
			.newLine("");
		return;
	} else if (op.tag == "op-const") {
		const destination = scope.define(op.destination.variable);
		implementation.append("let " + destination + " = ");
		if (op.type === "Boolean") {
			implementation.append(op.boolean ? "true" : "false");
		} else if (op.type === "Bytes") {
			// TODO: Properly handle bytes.
			implementation.append(JSON.stringify(op.bytes));
		} else if (op.type === "Int") {
			implementation.append("BigInt(" + op.int + ")");
		} else {
			const _: never = op;
			throw new Error("codegenOp: unhandled op-const type `" + op["type"] + "`");
		}
		implementation.append(";")
			.newLine();
		return;
	} else if (op.tag === "op-copy") {
		for (const copy of op.copies) {
			implementation.append("let ")
				.append(scope.define(copy.destination.variable))
				.append(" = ")
				.append(scope.read(copy.source))
				.append(";")
				.newLine();
		}
		return;
	} else if (op.tag === "op-foreign") {
		implementation.append("let ");
		if (op.destinations.length === 1) {
			implementation.append(scope.define(op.destinations[0].variable));
		} else {
			implementation.append("[")
				.append(op.destinations.map(x => scope.define(x.variable)).join(", "))
				.append("]");
		}
		const mangled = codegen.asciiNameMangle("", op.operation);
		implementation.append(" = ")
			.append(mangled)
			.append("(")
			.append(op.arguments.map(x => scope.read(x)).join(", "))
			.append(");")
			.newLine();
		return;
	} else if (op.tag === "op-proof") {
		// No code generation for proofs.
		return;
	} else if (op.tag === "op-proof-bounds") {
		throw new Error("codegenOp: op-proof-bounds outside proof context");
	} else if (op.tag === "op-proof-eq") {
		throw new Error("codegenOp: op-proof-eq outside proof context");
	} else if (op.tag === "op-return") {
		implementation.append("return ");
		if (op.sources.length === 1) {
			implementation.append(scope.read(op.sources[0]));
		} else {
			implementation.append("[");
			let first = true;
			for (const source of op.sources) {
				if (!first) {
					implementation.append(", ");
				}
				first = false;
				implementation.append(scope.read(source));
			}
			implementation.append("]");
		}
		implementation.append(";")
			.newLine();
		return;
	} else if (op.tag === "op-dynamic-call") {
		implementation.append("let ");
		if (op.destinations.length === 1) {
			const destination = op.destinations[0];
			implementation.append(scope.define(destination.variable));
		} else {
			implementation.append("[")
				.append(op.destinations.map(x => scope.define(x.variable)).join(", "))
				.append("]");
		}

		const jsArguments = [];

		// Collect value arguments
		for (const arg of op.arguments) {
			jsArguments.push(scope.read(arg));
		}

		// Find non-closure constraint arguments:
		const trait = program.interfaces[op.constraint.interface];
		const genericSignature = trait.signatures[op.signature_id];
		const combinedTypeParameters = trait.type_parameters.concat(genericSignature.type_parameters);
		const combinedTypeArguments = op.constraint.subjects.concat(op.signature_type_arguments);
		const instantiation = ir.typeArgumentsMap(combinedTypeParameters, combinedTypeArguments);
		for (const genericConstraint of genericSignature.constraint_parameters) {
			const requiredConstraint = ir.constraintSubstitute(genericConstraint, instantiation);
			jsArguments.push(resolveConstraint(program, scope, requiredConstraint));
		}

		const jsConstraint = resolveConstraint(program, scope, op.constraint);
		implementation.append(" = ")
			.append(jsConstraint)
			.append(".")
			.append(vtableMemberName(op.signature_id))
			.append("(")
			.append(jsArguments.join(", "))
			.append(")")
			.append(";")
			.newLine();
		return;
	} else if (op.tag === "op-static-call") {
		implementation.append("let ");
		if (op.destinations.length === 1) {
			const destination = op.destinations[0];
			implementation.append(scope.define(destination.variable));
		} else {
			implementation.append("[")
				.append(op.destinations.map(x => scope.define(x.variable)).join(", "))
				.append("]");
		}
		implementation.append(" = ");
		const operands = [];
		for (let i = 0; i < op.arguments.length; i++) {
			operands.push(scope.read(op.arguments[i]));
		}
		const fnDef = program.functions[op.function];
		if (fnDef === undefined) {
			throw new Error("codegenOp: undefined function `" + op.function + "`");
		}
		const typeArguments = ir.typeArgumentsMap(fnDef.signature.type_parameters, op.type_arguments);
		for (const constraint of fnDef.signature.constraint_parameters) {
			const required = ir.constraintSubstitute(constraint, typeArguments);
			operands.push(resolveConstraint(program, scope, required));
		}

		implementation.append(fnName(op.function))
			.append("(")
			.append(operands.join(", "))
			.append(");")
			.newLine();
		return;
	} else if (op.tag === "op-unreachable") {
		implementation.append("throw new Error(\"unreachable(")
			.append(op.diagnostic_kind)
			.append("): ")
			.append(op.diagnostic_location.fileID)
			.append(":offset=")
			.append(op.diagnostic_location.offset.toFixed(0))
			.append(", length=")
			.append(op.diagnostic_location.length.toFixed(0))
			.append("\");")
			.newLine();
		return;
	} else if (op.tag === "op-new-record") {
		implementation.append("let ")
			.append(scope.define(op.destination.variable))
			.append(" = {")
			.newLine("\t");
		for (const field in op.fields) {
			implementation
				.append(JSON.stringify(field))
				.append(": ")
				.append(scope.read(op.fields[field]))
				.append(",")
				.newLine();
		}
		implementation.dedent("\t")
			.append("};")
			.newLine();
		return;
	} else if (op.tag === "op-field") {
		implementation.append("let ")
			.append(scope.define(op.destination.variable))
			.append(" = ")
			.append(scope.read(op.object))
			.append("[")
			.append(JSON.stringify(op.field))
			.append("];")
			.newLine();
		return;
	} else if (op.tag === "op-new-enum") {
		implementation.append("let ")
			.append(scope.define(op.destination.variable))
			.append("= {")
			.newLine("\t")
			.append(JSON.stringify(op.variant))
			.append(": ")
			.append(scope.read(op.variantValue))
			.append(",")
			.newLine()
			.dedent("\t")
			.append("};")
			.newLine();
		return;
	} else if (op.tag === "op-variant") {
		implementation.append("let ")
			.append(scope.define(op.destination.variable))
			.append(" = ")
			.append(scope.read(op.object))
			.append("[")
			.append(JSON.stringify(op.variant))
			.append("];")
			.newLine();
		return;
	} else if (op.tag === "op-is-variant") {
		implementation.append("let ")
			.append(scope.define(op.destination.variable))
			.append(" = ")
			.append(JSON.stringify(op.variant))
			.append(" in ")
			.append(scope.read(op.base))
			.append(";")
			.newLine();
		return;
	}

	const _: never = op;
	throw new Error("codegenOp: unhandled tag `" + op["tag"] + "`");
}

function resolveConstraint(
	program: ir.Program,
	scope: VariableScope,
	constraint: ir.ConstraintParameter,
): string {
	// Search for impls on the stack.
	for (const available of scope.constraints) {
		if (available.constraint.interface !== constraint.interface) {
			continue;
		}
		const unification = ir.unifyTypes([], available.constraint.subjects, [], constraint.subjects);
		if (unification === null) {
			continue;
		}
		if (unification.instantiations.size !== 0) {
			throw new Error("expected no type variables");
		}
		return available.jsName;
	}

	// Search for global impls.
	for (const vtableID in program.globalVTableFactories) {
		const vtable = program.globalVTableFactories[vtableID];
		if (vtable.provides.interface !== constraint.interface) {
			continue;
		}
		const unification = ir.unifyTypes(vtable.for_any, vtable.provides.subjects, [], constraint.subjects);
		if (unification === null) {
			continue;
		}

		const instantiationMapping = new Map<ir.TypeVariableID, ir.Type>();
		for (const [sourceParameter, intermediate] of unification.leftRenaming) {
			const result = unification.instantiations.get(intermediate.id);
			if (!result) {
				throw new Error("unexpected missing instantiation for sourceParameter " + sourceParameter);
			}
			instantiationMapping.set(sourceParameter, result);
		}

		// TODO: Share v-tables to avoid exponential explosion.
		const recursion = vtable.closures.map(generic => {
			const instantiated = ir.constraintSubstitute(generic, instantiationMapping);
			return resolveConstraint(program, scope, instantiated);
		});
		return globalVtableName(vtableID) + "(" + recursion.join(", ") + ")";
	}

	throw new Error("constraint `" + constraint.interface + "` not satisfied");
}
