import * as grammar from "./grammar";
import * as ir from "./ir";
import * as diagnostics from "./diagnostics";
import * as lexer from "./lexer";

interface FieldBinding {
	nameLocation: ir.SourceLocation,
	t: ir.Type,
	typeLocation: ir.SourceLocation,
}

interface TypeBinding {
	t: ir.Type,
	location: ir.SourceLocation,
}

interface FnBinding {
	nameLocation: ir.SourceLocation,
	parameters: TypeBinding[],
	returns: TypeBinding[],
	ast: grammar.Fn,
}

interface ClassEntityDef {
	tag: "class",
	ast: grammar.ClassDefinition,
	sourceContext: SourceContext,
	bindingLocation: ir.SourceLocation,

	typeScope: TypeScope,
	fields: Record<string, FieldBinding>,

	fns: Record<string, FnBinding>,
}

interface InterfaceEntityDef {
	tag: "interface",
	ast: grammar.InterfaceDefinition,
	sourceContext: SourceContext,
	bindingLocation: ir.SourceLocation,

	typeScope: TypeScope,
}

type EntityDef = ClassEntityDef | InterfaceEntityDef;

interface EntityBinding {
	canonicalName: string,
	bindingLocation: ir.SourceLocation,
}

interface PackageBinding {
	packageName: string,
	bindingLocation: ir.SourceLocation,
}

/// `ProgramContext` is built up over time to include the "signature" 
/// information needed to check references of one entity by another.
interface ProgramContext {
	/// `canonicalByQualifiedName` is map from package name to entity name to
	/// canonical name.
	canonicalByQualifiedName: Record<string, Record<string, string>>,

	/// `entitiesByCanonical` identifies information of the entity with the 
	/// given "canonical" name.of the entity.
	entitiesByCanonical: Record<string, EntityDef>,
}

/// `SourceContext` represents the "view" of the program from the perspective of
/// an individual source file. Currently, that is limited to aliases of objects
/// and namespaces, which are driven primarily by import declarations.
interface SourceContext {
	/// `entityAliases` maps an unqualified name to a canonical entity.
	/// This includes an entry for each entity defined within this source's
	/// package.
	entityAliases: Record<string, EntityBinding>,

	/// `namespaces` maps a qualifier on a name to a package name.
	/// This does NOT include an entry for the current package, as explicit
	/// qualification in that form is not allowed.
	namespaces: Record<string, PackageBinding>,

	/// `programContext` is a reference to the single common `ProgramContext`.
	programContext: ProgramContext,
}

// Collects the set of entities defined across all given sources.
function collectAllEntities(sources: grammar.Source[]) {
	const programContext: ProgramContext = {
		canonicalByQualifiedName: {},
		entitiesByCanonical: {},
	};

	for (const source of sources) {
		const packageName = source.package.packageName.name;
		const pack = programContext.canonicalByQualifiedName[packageName] || {};
		programContext.canonicalByQualifiedName[packageName] = pack;
		for (let definition of source.definitions) {
			const entityName = definition.entityName.name;
			const bindingLocation = definition.entityName.location;
			if (pack[entityName] !== undefined) {
				const firstCanonical = pack[entityName];
				const firstBinding = programContext.entitiesByCanonical[firstCanonical];
				throw new diagnostics.EntityRedefinedErr({
					name: `${packageName}.${entityName}`,
					firstBinding: firstBinding.bindingLocation,
					secondBinding: bindingLocation,
				})
			}
			const canonicalName = packageName + "." + entityName;

			let entity: EntityDef;
			entity = {
				tag: "class",
				ast: definition,
				bindingLocation,

				// TODO:
				sourceContext: null as any,

				typeScope: {
					// The `This` type keyword cannot be used in class 
					// definitions.
					thisType: null,

					constraints: [],
					typeVariables: {},
					typeVariableDebugNames: [],
				},

				// These are filled in by `collectMembers`.
				fields: {},
				fns: {},
			};
			programContext.entitiesByCanonical[canonicalName] = entity;
			pack[entityName] = canonicalName;
		}
	}
	return programContext;
}

interface TypeVariableBinding {
	bindingLocation: ir.SourceLocation,
	variable: ir.TypeVariable,
}

interface TypeScope {
	thisType: null | ir.TypeVariable,

	/// `typeVariables` maps from the `TypeVarToken.name` to the ID in IR.
	typeVariables: Record<string, TypeVariableBinding>,

	constraints: ir.ConstraintParameter[],

	// These names do NOT include "#".
	typeVariableDebugNames: string[],
}

function resolveEntity(
	t: grammar.TypeNamed,
	sourceContext: Readonly<SourceContext>
) {
	if (t.packageQualification !== null) {
		const namespaceQualifier = t.packageQualification.package.name;
		const namespace = sourceContext.namespaces[namespaceQualifier];
		if (!namespace) {
			throw new diagnostics.NoSuchPackageErr({
				packageName: namespaceQualifier,
				reference: t.packageQualification.location,
			});
		}

		const entitiesInNamespace = sourceContext.programContext.canonicalByQualifiedName[namespaceQualifier];
		const canonicalName = entitiesInNamespace[t.entity.name];
		if (!canonicalName) {
			throw new diagnostics.NoSuchEntityErr({
				entityName: namespace.packageName + "." + t.entity.name,
				reference: t.entity.location,
			});
		}
		return canonicalName;
	} else {
		const bound = sourceContext.entityAliases[t.entity.name];
		if (!bound) {
			throw new diagnostics.NoSuchEntityErr({
				entityName: t.entity.name,
				reference: t.entity.location,
			});
		}
		return bound.canonicalName;
	}
}

function compileConstraint(t: grammar.TypeNamed,
	sourceContext: Readonly<SourceContext>,
	scope: TypeScope,
	programContext: Readonly<ProgramContext>): ir.ConstraintParameter {
	// Resolve the entity.
	const canonicalName = resolveEntity(t, sourceContext);
	const entity = programContext.entitiesByCanonical[canonicalName];
	if (entity.tag !== "interface") {
		throw new diagnostics.TypeUsedAsConstraintErr({
			name: canonicalName,
			kind: "class",
			typeLocation: t.location,
		});
	}

	const args = t.arguments.map(a => compileType(a, scope, sourceContext));

	return {
		constraint: { interface_id: canonicalName },
		subjects: args,
	};
}

function compileType(
	t: grammar.Type,
	scope: TypeScope,
	sourceContext: Readonly<SourceContext>): ir.Type {
	if (t.tag === "type-keyword") {
		if (t.keyword === "This") {
			if (scope.thisType === null) {
				throw new diagnostics.InvalidThisTypeErr({
					referenced: t.location,
				});
			}
			return scope.thisType;
		} else if (t.keyword === "String") {
			return {
				tag: "type-primitive",
				primitive: "Bytes",
			};
		} else {
			return {
				tag: "type-primitive",
				primitive: t.keyword,
			};
		}
	} else if (t.tag === "named") {
		// Resolve the entity.
		const canonicalName = resolveEntity(t, sourceContext);
		const entity = sourceContext.programContext.entitiesByCanonical[canonicalName];
		// TODO: Check that entity is a class, etc.

		if (entity.tag !== "class") {
			throw new diagnostics.NonTypeEntityUsedAsTypeErr({
				entity: canonicalName,
				entityTag: entity.tag,
				useLocation: t.entity.location,
				entityBinding: entity.bindingLocation,
			});
		}

		const typeArguments = t.arguments.map(a =>
			compileType(a, scope, sourceContext));
		return {
			tag: "type-compound",
			record: { record_id: canonicalName },
			type_arguments: typeArguments,
		};
	}
	throw new Error("Unhandled tag in compileType: " + t);
}

/// `resolveImport` MODIFIES the given `sourceContext` to include the 
/// entity or namespace introduced by the given import.
function resolveImport(
	imported: grammar.ImportOfObject | grammar.ImportOfPackage,
	sourcePackage: grammar.PackageDef,
	sourceContext: Readonly<SourceContext>,
	programContext: ProgramContext) {
	if (imported.tag === "of-object") {
		const packageName = imported.packageName.name;
		const packageEntities = programContext.canonicalByQualifiedName[packageName];
		if (packageEntities === undefined) {
			throw new diagnostics.NoSuchPackageErr({
				packageName,
				reference: imported.packageName.location,
			});
		}
		const entityName = imported.objectName.name;
		const canonicalName = packageEntities[entityName];
		if (canonicalName === undefined) {
			throw new diagnostics.NoSuchEntityErr({
				entityName: `${packageName}.${entityName}`,
				reference: imported.location,
			});
		}
		if (sourceContext.entityAliases[entityName] !== undefined) {
			throw new diagnostics.EntityRedefinedErr({
				name: entityName,
				firstBinding: sourceContext.entityAliases[entityName].bindingLocation,
				secondBinding: imported.objectName.location,
			});
		}
		sourceContext.entityAliases[entityName] = {
			canonicalName,
			bindingLocation: imported.objectName.location,
		};
	} else if (imported.tag === "of-package") {
		const packageName = imported.packageName.name;
		if (packageName === sourcePackage.packageName.name) {
			throw new diagnostics.NamespaceAlreadyDefinedErr({
				namespace: packageName,
				firstBinding: sourcePackage.packageName.location,
				secondBinding: imported.packageName.location,
			});
		} else if (sourceContext.namespaces[packageName] !== undefined) {
			throw new diagnostics.NamespaceAlreadyDefinedErr({
				namespace: packageName,
				firstBinding: sourceContext.namespaces[packageName].bindingLocation,
				secondBinding: imported.packageName.location,
			});
		}
		sourceContext.namespaces[packageName] = {
			packageName,
			bindingLocation: imported.packageName.location,
		};
	}
}

function resolveSourceContext(
	source: grammar.Source,
	programContext: Readonly<ProgramContext>) {
	const packageName = source.package.packageName.name;
	const pack = programContext.canonicalByQualifiedName[packageName];

	const sourceContext: SourceContext = {
		entityAliases: {},
		namespaces: {},
		programContext,
	};

	// Bring all entities defined within this package into scope.
	for (let entityName in pack) {
		const canonicalName = pack[entityName];
		const binding = programContext.entitiesByCanonical[canonicalName];
		sourceContext.entityAliases[entityName] = {
			canonicalName,
			bindingLocation: binding.bindingLocation,
		};

		// TODO: Do this in a more straightforward way.
		programContext.entitiesByCanonical[canonicalName].sourceContext = sourceContext;
	}

	// Bring all imports into scope.
	for (const { imported } of source.imports) {
		resolveImport(imported, source.package, sourceContext, programContext);
	}

	return sourceContext;
}

// Calculates "signatures" such that references to this entity within other 
// entities can be type-checked. NOTE that this does NOT include compiling pre-
// and post-conditions, which are instead compiled separately and only 
// instantiated by the verifier.
function collectMembers(programContext: ProgramContext, entityName: string) {
	const entity = programContext.entitiesByCanonical[entityName];
	if (entity.tag === "class") {
		// Bring the type parameters into scope.
		for (let parameter of entity.ast.typeParameters.parameters) {
			const existingBinding = entity.typeScope.typeVariables[parameter.name];
			if (existingBinding !== undefined) {
				throw new diagnostics.TypeVariableRedefinedErr({
					typeVariableName: parameter.name,
					firstBinding: existingBinding.bindingLocation,
					secondBinding: parameter.location,
				});
			}
			entity.typeScope.typeVariables[parameter.name] = {
				variable: {
					tag: "type-variable",
					id: {
						type_variable_id: entity.typeScope.typeVariableDebugNames.length,
					},
				},
				bindingLocation: parameter.location,
			};
			entity.typeScope.typeVariableDebugNames.push(parameter.name);
		}
		for (let c of entity.ast.typeParameters.constraints) {
			if (c.constraint.tag === "type-keyword") {
				throw new diagnostics.TypeUsedAsConstraintErr({
					kind: "keyword",
					typeLocation: c.constraint.location,
				});
			}
			const constraint = compileConstraint(c.constraint,
				entity.sourceContext, entity.typeScope, programContext);
		}

		// Collect the defined fields.
		for (let field of entity.ast.fields) {
			const fieldName = field.name.name;
			const existingField = entity.fields[fieldName];
			if (existingField !== undefined) {
				throw new diagnostics.MemberRedefinedErr({
					memberName: fieldName,
					firstBinding: existingField.nameLocation,
					secondBinding: field.name.location,
				});
			}

			const fieldType = compileType(field.t,
				entity.typeScope, entity.sourceContext);

			entity.fields[fieldName] = {
				nameLocation: field.name.location,
				t: fieldType,
				typeLocation: field.t.location,
			};
		}

		// Collect the defined methods.
		for (let fn of entity.ast.fns) {
			const fnName = fn.signature.name.name;
			const existingField = entity.fields[fnName];
			if (existingField !== undefined) {
				throw new diagnostics.MemberRedefinedErr({
					memberName: fnName,
					firstBinding: existingField.nameLocation,
					secondBinding: fn.signature.name.location,
				});
			}
			const existingFn = entity.fns[fnName];
			if (existingFn !== undefined) {
				throw new diagnostics.MemberRedefinedErr({
					memberName: fnName,
					firstBinding: existingFn.nameLocation,
					secondBinding: fn.signature.name.location,
				});
			}

			const parameterTypes: TypeBinding[] = fn.signature.parameters.map(t => ({
				t: compileType(t.t, entity.typeScope, entity.sourceContext),
				location: t.t.location,
			}));

			const returnTypes: TypeBinding[] = fn.signature.returns.map(t => ({
				t: compileType(t, entity.typeScope, entity.sourceContext),
				location: t.location,
			}));

			entity.fns[fnName] = {
				nameLocation: fn.signature.name.location,
				parameters: parameterTypes,
				returns: returnTypes,
				ast: fn,
			};
		}

		return;
	}
	throw new Error("TODO: collectMembers for unhandled " + entity.ast.tag);
}

function canonicalFunctionName(entityName: string, memberName: string) {
	return entityName + "." + memberName;
}

interface FunctionContext {
	/// `returnsTo` indicates the types that the containing function returns,
	/// and where those return types can be found annotated in the source.
	returnsTo: { t: ir.Type, location: ir.SourceLocation }[],

	sourceContext: SourceContext,
}

interface VariableBinding {
	bindingLocation: ir.SourceLocation,
	t: ir.Type,
	id: ir.VariableID,
}

class VariableStack {
	private variables: Record<string, VariableBinding> = {};
	private stack: string[] = [];
	private blocks: number[] = [];

	/// THROWS SemanticError when a variable of this name is already in scope.
	defineVariable(name: string, t: ir.Type, location: ir.SourceLocation): VariableBinding {
		const existing = this.variables[name]
		if (existing !== undefined) {
			throw new diagnostics.VariableRedefinedErr({
				name,
				firstLocation: existing.bindingLocation,
				secondLocation: location,
			});
		}
		this.variables[name] = {
			bindingLocation: location,
			t,
			id: { variable_id: this.stack.length },
		};
		this.stack.push(name);
		return this.variables[name];
	}

	defineTemporary(t: ir.Type, location: ir.SourceLocation) {
		const name = "$" + this.stack.length;
		return this.defineVariable(name, t, location);
	}

	/// THROWS SemanticError when a variable of this name is not in scope.
	resolve(variable: lexer.IdenToken): VariableBinding {
		const def = this.variables[variable.name];
		if (def === undefined) {
			throw new diagnostics.VariableNotDefinedErr({
				name: variable.name,
				referencedAt: variable.location,
			});
		}
		return def;
	}

	openBlock() {
		this.blocks.push(this.stack.length);
	}

	closeBlock() {
		const start = this.blocks.pop();
		if (start === undefined) throw new Error("block is not open");
		const removed = this.stack.splice(start);
		for (const r of removed) {
			delete this.variables[r];
		}
	}
}

interface ValueInfo {
	values: { t: ir.Type, id: ir.VariableID }[],
	location: ir.SourceLocation,
}

function compileExpressionAtom(
	e: grammar.ExpressionAtom,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext): ValueInfo {
	if (e.tag === "iden") {
		const v = stack.resolve(e);
		return {
			values: [{ t: v.t, id: v.id }],
			location: e.location,
		};
	} else if (e.tag === "paren") {
		const component = compileExpression(e.expression, ops, stack, typeScope, context);
		if (component.values.length !== 1) {
			// TODO: Include information from the value info to explain why this
			// has multiple values.
			throw new diagnostics.MultiExpressionGroupedErr({
				valueCount: component.values.length,
				location: e.location,
				grouping: "parens",
			});
		}
		return component;
	} else if (e.tag === "number-literal") {
		const v = stack.defineTemporary(ir.T_INT, e.location);
		ops.push({
			tag: "op-var",
			type: v.t,
		});
		ops.push({
			tag: "op-const",
			destination: v.id,
			value: e.value,
		});
		return { values: [{ t: v.t, id: v.id }], location: e.location };
	}

	throw new Error("TODO: Unhandled tag `" + e.tag + "` in compileExpressionAtom");
}

function compileOperand(
	e: grammar.ExpressionOperand,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext): ValueInfo {
	let value = compileExpressionAtom(e.atom, ops, stack, typeScope, context);
	for (const access of e.accesses) {
		if (value.values.length !== 1) {
			throw new diagnostics.MultiExpressionGroupedErr({
				location: value.location,
				valueCount: value.values.length,
				grouping: access.tag,
			});
		}
		const base = value.values[0];

		if (access.tag === "field") {
			if (base.t.tag !== "type-compound") {
				throw new diagnostics.FieldAccessOnNonCompoundErr({
					accessedType: displayType(base.t, typeScope, context.sourceContext),
					accessedLocation: access.fieldName.location,
				});
			}
			throw new Error("TODO: compileOperand field access");
		} else if (access.tag === "method") {
			throw new Error("TODO: compileOperand method access");
		} else {
			throw new Error("unhandled access tag `" + access["tag"] + "` in compileOperand");
		}
	}

	return value;

	throw new Error("TODO:");
}

function compileExpression(
	e: grammar.Expression,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext): ValueInfo {

	let left = compileOperand(e.left, ops, stack, typeScope, context);

	if (e.operations.length !== 0) {
		if (e.operations.length > 1) {
			throw new Error("TODO: Handle more than 1 operation. (Use parentheses)");
		}

		const operand = e.operations[1];
		const right = compileOperand(operand.right, ops, stack, typeScope, context);
		throw new Error("TODO: Invoke correct method/foreign");
	}

	return left;
}

/// `displayType` formats the given IR `Type` as a string, potentially formatted
/// for the given `SourceContext` (considering import aliases and such).
function displayType(t: ir.Type, typeScope: Readonly<TypeScope>, sourceContext: Readonly<SourceContext>): string {
	if (t.tag === "type-compound") {
		const base = t.record.record_id;
		const args = t.type_arguments.map(x => displayType(x, typeScope, sourceContext));
		if (args.length === 0) {
			return base;
		} else {
			return base + "[" + args.join(", ") + "]";
		}
	} else if (t.tag === "type-primitive") {
		// TODO: Text vs String vs Bytes?
		return t.primitive;
	} else if (t.tag == "type-variable") {
		return "#" + typeScope.typeVariableDebugNames[t.id.type_variable_id];
	} else {
		throw new Error("displayType: unhandled tag `" + t["tag"] + "`");
	}
}

/// `compileAssignment` adds operations to `ops` to move the value from the 
/// source variable to the destination variable.
/// THROWS a `SemanticError` if doing such is a type error.
function compileAssignment(
	value: { tuple: ValueInfo, i: number },
	destination: VariableBinding,
	ops: ir.Op[],
	typeScope: Readonly<TypeScope>,
	context: FunctionContext,
) {
	const sourceType = value.tuple.values[value.i].t;

	if (!ir.equalTypes(sourceType, destination.t)) {
		throw new diagnostics.TypeMismatchErr({
			givenType: displayType(sourceType, typeScope, context.sourceContext),
			givenLocation: value.tuple.location,
			expectedType: displayType(destination.t, typeScope, context.sourceContext),
			expectedLocation: destination.bindingLocation,
		});
	}

	ops.push({
		tag: "op-assign",
		destination: destination.id,
		source: value.tuple.values[value.i].id,
	});
}

function compileVarSt(
	statement: grammar.VarSt,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext) {
	const values = [];
	for (const e of statement.initialization) {
		const tuple = compileExpression(e, ops, stack, typeScope, context);
		for (let i = 0; i < tuple.values.length; i++) {
			values.push({ tuple, i });
		}
	}

	const destinations = [];
	for (const v of statement.variables) {
		const t = compileType(v.t, typeScope, context.sourceContext);
		const d = stack.defineVariable(v.variable.name, t, v.variable.location);
		destinations.push(d);
	}

	if (values.length !== destinations.length) {
		throw new diagnostics.ValueCountMismatchErr({
			actualCount: values.length,
			actualLocation: ir.locationsSpan(statement.initialization),
			expectedCount: destinations.length,
			expectedLocation: ir.locationsSpan(statement.variables),
		});
	}

	for (let i = 0; i < values.length; i++) {
		compileAssignment(values[i], destinations[i], ops, typeScope, context);
	}
}

function compileReturnSt(
	statement: grammar.ReturnSt,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext) {
	const values = [];
	for (const e of statement.values) {
		const tuple = compileExpression(e, ops, stack, typeScope, context);
		for (let i = 0; i < tuple.values.length; i++) {
			values.push({ tuple, i });
		}
	}

	if (values.length !== context.returnsTo.length) {
		const signatureReturn = ir.locationsSpan(context.returnsTo);
		throw new diagnostics.ValueCountMismatchErr({
			actualCount: values.length,
			actualLocation: ir.locationsSpan(statement.values),
			expectedCount: context.returnsTo.length,
			expectedLocation: signatureReturn,
		});
	}
	let op: ir.OpReturn = { tag: "op-return", sources: [] };
	for (let i = 0; i < values.length; i++) {
		const v = values[i];
		const source = v.tuple.values[v.i];
		op.sources.push(source.id);

		const destination = context.returnsTo[i];
		if (!ir.equalTypes(source.t, destination.t)) {
			throw new diagnostics.TypeMismatchErr({
				givenType: displayType(source.t, typeScope, context.sourceContext),
				givenLocation: v.tuple.location,
				givenIndex: { index0: v.i, count: v.tuple.values.length },
				expectedType: displayType(destination.t, typeScope, context.sourceContext),
				expectedLocation: destination.location,
			});
		}
	}
	ops.push(op);
}

function compileStatement(
	statement: grammar.Statement,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext) {
	if (statement.tag === "var") {
		compileVarSt(statement, ops, stack, typeScope, context);
		return;
	} else if (statement.tag === "return") {
		compileReturnSt(statement, ops, stack, typeScope, context);
	}
	throw new Error("Unhandled tag in compileStatement `" + statement.tag + "`");
}

function compileBlock(
	block: grammar.Block,
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext): ir.OpBlock {
	const ops: ir.Op[] = [];
	stack.openBlock();

	for (const s of block.statements) {
		compileStatement(s, ops, stack, typeScope, context);
	}

	stack.closeBlock();
	return {
		tag: "op-block",
		ops: ops,
	};
}

function compileFunction(
	program: ir.Program,
	def: FnBinding,
	fName: string,
	sourceContext: SourceContext,
	typeScope: TypeScope) {
	const signature: ir.FunctionSignature = {
		type_parameters: typeScope.typeVariableDebugNames,
		constraint_parameters: typeScope.constraints,

		parameters: [],
		return_types: [],

		// TODO:
		preconditions: [],
		postconditions: [],
	};
	const stack = new VariableStack();
	for (const p of def.ast.signature.parameters) {
		const t = compileType(p.t, typeScope, sourceContext);
		signature.parameters.push(t);
		stack.defineVariable(p.name.name, t, p.name.location);
	}
	const context: FunctionContext = {
		returnsTo: [],
		sourceContext,
	};
	for (const r of def.ast.signature.returns) {
		const t = compileType(r, typeScope, sourceContext);
		signature.return_types.push(t);
		context.returnsTo.push({ t, location: r.location });
	}
	const body = compileBlock(def.ast.body, stack, typeScope, context);
	program.functions[fName] = { signature, body };
}

function compileClassEntity(
	program: ir.Program,
	entity: ClassEntityDef,
	entityName: string) {
	// Layout storage for this class.
	program.records[entityName] = {
		type_parameters: entity.ast.typeParameters.parameters.map(x => x.name),
		fields: {},
	};
	for (const f in entity.fields) {
		program.records[entityName].fields[f] = entity.fields[f].t;
	}

	// Implement functions.
	for (const f in entity.fns) {
		const def = entity.fns[f];
		const fName = canonicalFunctionName(entityName, f);
		compileFunction(program, def, fName, entity.sourceContext, entity.typeScope);
	}

	// TODO: Implement vtable factories.
}

/// `compileEntity` compiles the indicated entity into classes, functions,
/// interfaces, vtable-factories, etc in the given `program`.
/// THROWS `SemanticError` if a type-error is discovered within the 
/// implementation of this entity.
function compileEntity(
	program: ir.Program,
	programContext: Readonly<ProgramContext>,
	entityName: string) {
	const entity = programContext.entitiesByCanonical[entityName];
	if (entity.tag === "class") {
		compileClassEntity(program, entity, entityName);
	} else {
		throw new Error("Unhandled tag in compileEntity: " + entity.tag);
	}
}

/// `compileSources` transforms the ASTs making up a Shiru program into a
/// `ir.Program`.
/// THROWS `SemanticError` if a type-error is discovered within the given source
/// files.
export function compileSources(sources: grammar.Source[]): ir.Program {
	const programContext = collectAllEntities(sources);

	// Collect all entities and source contexts.
	const sourceContexts = [];
	for (const source of sources) {
		sourceContexts.push(resolveSourceContext(source, programContext));
	}

	// Resolve members of entities, without checking the validity of
	// type-constraints.
	for (let canonicalEntityName in programContext.entitiesByCanonical) {
		collectMembers(programContext, canonicalEntityName);
	}

	const program: ir.Program = {
		functions: {},
		interfaces: {},
		records: {},
		foreign: {},
		globalVTableFactories: {},
	};

	for (let canonicalEntityName in programContext.entitiesByCanonical) {
		compileEntity(program, programContext, canonicalEntityName);
	}
	return program;
}
