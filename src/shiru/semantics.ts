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

	id: ir.FunctionID,
}

interface InterfaceFnBinding {
	nameLocation: ir.SourceLocation,
	parameters: TypeBinding[],
	returns: TypeBinding[],
	ast: grammar.InterfaceMember,
}

interface RecordEntityDef {
	tag: "record",
	ast: grammar.RecordDefinition,
	sourceID: string,
	bindingLocation: ir.SourceLocation,

	/// `typeScope` indicates the type-parameters (and their available
	/// constraints) within each member of `fields`, `implements`, and `fns`.
	typeScope: TypeScope,
	fields: Record<string, FieldBinding>,

	/// The set of constraints that this entity is the method-subject of.
	implements: ConstraintBinding[],

	fns: Record<string, FnBinding>,
}

interface InterfaceEntityDef {
	tag: "interface",
	ast: grammar.InterfaceDefinition,
	sourceID: string,
	bindingLocation: ir.SourceLocation,

	typeScope: TypeScope,
	fns: Record<string, InterfaceFnBinding>,
}

type EntityDef = RecordEntityDef | InterfaceEntityDef;

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

	foreignSignatures: Record<string, ir.FunctionSignature>,

	sourceContexts: Record<string, SourceContext>,

	/// `uncheckedTypes` and `uncheckedConstraints` are initially `[]`, and
	/// become `null` once  enough members have been collected to check that
	/// type arguments implement the required constraints.
	uncheckedTypes: null | {
		t: grammar.Type,
		scope: TypeScope,
		sourceContext: SourceContext,
	}[],
	uncheckedConstraints: null | {
		c: grammar.TypeNamed,
		methodSubject: ir.Type,
		sourceContext: Readonly<SourceContext>,
		scope: TypeScope,
	}[],
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
function collectAllEntities(sources: Record<string, grammar.Source>) {
	const programContext: ProgramContext = {
		canonicalByQualifiedName: {},
		entitiesByCanonical: {},
		foreignSignatures: getBasicForeign(),
		sourceContexts: {},

		uncheckedTypes: [],
		uncheckedConstraints: [],
	};

	for (const sourceID in sources) {
		const source = sources[sourceID];
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
			if (definition.tag === "record-definition") {
				const thisType: ir.Type = {
					tag: "type-compound",
					record: { record_id: canonicalName },
					type_arguments: definition.typeParameters.parameters.map((_, i) => ({
						tag: "type-variable",
						id: { type_variable_id: i },
					})),
				};

				entity = {
					tag: "record",
					ast: definition,
					bindingLocation,
					sourceID,

					typeScope: {
						thisType,

						constraints: [],
						typeVariables: {},
						typeVariableDebugNames: [],
					},

					// These are filled in by `collectMembers`.
					fields: {},
					fns: {},
					implements: [],
				};
			} else {
				entity = {
					tag: "interface",
					ast: definition,
					bindingLocation,
					sourceID,

					// The "first" type-parameter is `This` rather than a named
					// `#T` type-variable.
					typeScope: {
						thisType: {
							tag: "type-variable",
							id: { type_variable_id: 0 },
						},
						constraints: [],
						typeVariables: {},
						typeVariableDebugNames: ["This"],
					},

					// These are filled in by `collectMembers`.
					fns: {},
				};
			}
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

interface ConstraintBinding {
	/// The "method subject" of this constraint binding is the first element of
	/// `constraint.subjects`.
	constraint: ir.ConstraintParameter,
	location: ir.SourceLocation,
}

interface TypeScope {
	thisType: ir.Type,

	/// `typeVariables` maps from the `TypeVarToken.name` to the ID in IR.
	typeVariables: Record<string, TypeVariableBinding>,

	constraints: ConstraintBinding[],

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

function compileConstraint(
	// TODO: Use a `grammar.TypeConstraint` instead.
	c: grammar.TypeNamed,
	methodSubject: ir.Type,
	sourceContext: Readonly<SourceContext>,
	scope: TypeScope,
	checkConstraints: "check" | "skip" | "skip-internal",
): ir.ConstraintParameter {
	const programContext = sourceContext.programContext;
	if (programContext.uncheckedConstraints !== null) {
		if (checkConstraints === "skip") {
			programContext.uncheckedConstraints.push({
				c,
				methodSubject,
				sourceContext,
				scope,
			});
			checkConstraints = "skip-internal";
		}
	} else if (checkConstraints !== "check") {
		throw new Error("compileConstraint: invalid `checkConstraints` argument.");
	}

	// Resolve the entity.
	const canonicalName = resolveEntity(c, sourceContext);
	const interfaceEntity = programContext.entitiesByCanonical[canonicalName];
	if (interfaceEntity.tag !== "interface") {
		throw new diagnostics.TypeUsedAsConstraintErr({
			name: canonicalName,
			kind: "record",
			typeLocation: c.location,
		});
	}

	const subjects = [methodSubject];
	subjects.push(...c.arguments.map(a =>
		compileType(a, scope, sourceContext, checkConstraints)));

	if (checkConstraints === "check") {
		const expectedLocations = [];
		for (let v in interfaceEntity.typeScope.typeVariables) {
			expectedLocations.push({
				location: interfaceEntity.typeScope.typeVariables[v].bindingLocation,
			});
		}

		if (c.arguments.length !== expectedLocations.length) {
			throw new diagnostics.TypeParameterCountMismatchErr({
				entityType: "interface",
				entityName: canonicalName,
				expectedCount: expectedLocations.length,
				expectedLocation: ir.locationsSpan(expectedLocations),
				givenCount: c.arguments.length,
				givenLocation: c.location,
			});
		}

		const map = new Map();
		for (let i = 0; i < subjects.length; i++) {
			map.set(i, subjects[i]);
		}
		for (const requiredConstraint of interfaceEntity.typeScope.constraints) {
			const instantiated: ir.ConstraintParameter = {
				interface: requiredConstraint.constraint.interface,
				subjects: requiredConstraint.constraint.subjects.map(s => ir.typeSubstitute(s, map)),
			};
			checkConstraintSatisfied(instantiated, scope, sourceContext, {
				constraintDeclaredAt: requiredConstraint.location,
				neededAt: c.location,
			});
		}
	}

	return {
		interface: { interface_id: canonicalName },
		subjects: subjects,
	};
}

function allEqualTypes(a: ir.Type[], b: ir.Type[]): boolean {
	if (a.length !== b.length) {
		throw new Error("length mismatch");
	}
	for (let i = 0; i < a.length; i++) {
		if (!ir.equalTypes(a[i], b[i])) {
			return false;
		}
	}
	return true;
}

function checkConstraintSatisfied(
	requiredConstraint: ir.ConstraintParameter,
	typeScope: TypeScope,
	sourceContext: SourceContext,
	{ constraintDeclaredAt, neededAt }: {
		constraintDeclaredAt: ir.SourceLocation,
		neededAt: ir.SourceLocation,
	},
) {
	if (requiredConstraint.subjects.length === 0) {
		throw new Error("ICE: Expected at least one subject");
	}
	const methodSubject = requiredConstraint.subjects[0];
	if (methodSubject === undefined) {
		throw new Error("ICE: Constraint requires at least one subject.");
	} else if (methodSubject.tag === "type-compound") {
		const programContext = sourceContext.programContext;
		const recordEntity = programContext.entitiesByCanonical[methodSubject.record.record_id];
		if (recordEntity.tag !== "record") {
			throw new Error("ICE: non-record referenced by record type");
		}
		for (const implementation of recordEntity.implements) {
			if (implementation.constraint.interface.interface_id !== requiredConstraint.interface.interface_id) {
				continue;
			}
			const map = new Map();
			for (let i = 0; i < methodSubject.type_arguments.length; i++) {
				map.set(i, methodSubject.type_arguments[i]);
			}
			const provided = implementation.constraint.subjects.map(s => ir.typeSubstitute(s, map));
			if (allEqualTypes(provided, requiredConstraint.subjects)) {
				return;
			}
		}

		// No implementation was found in the record entity.
	} else if (methodSubject.tag === "type-variable") {
		// Consult the typeScope.
		for (const { constraint } of typeScope.constraints) {
			if (allEqualTypes(constraint.subjects, requiredConstraint.subjects)) {
				return;
			}
		}
		// No implementation was found in the type scope.
	} else if (methodSubject.tag === "type-primitive") {
		// TODO: Defer to the "built in" set of constraints (Eq, etc).
	} else {
		const _: never = methodSubject;
		throw new Error("checkConstraintSatisfied: Unhandled methodSubject tag `" + methodSubject["tag"] + "`");
	}

	throw new diagnostics.TypesDontSatisfyConstraintErr({
		neededConstraint: displayConstraint(requiredConstraint, typeScope, sourceContext),
		neededLocation: neededAt,
		constraintLocation: constraintDeclaredAt,
	});
}

/// `compileType` transforms an AST type into an IR type.
/// When `checkConstraints` is `"check"`, type arguments must satisfy the
/// constraints indicated by the base type. However, this cannot be `"skip"`
/// until `ProgramContext.hasCollectedMembers` becomes `true`.
function compileType(
	t: grammar.Type,
	scope: TypeScope,
	sourceContext: Readonly<SourceContext>,
	checkConstraints: "check" | "skip" | "skip-internal",
): ir.Type {
	if (sourceContext.programContext.uncheckedTypes !== null) {
		if (checkConstraints === "skip") {
			sourceContext.programContext.uncheckedTypes.push({
				t, scope, sourceContext
			});
			checkConstraints = "skip-internal";
		}
	} else if (checkConstraints !== "check") {
		throw new Error("compileType: invalid `checkConstraints` argument");
	}

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
		if (entity.tag !== "record") {
			throw new diagnostics.NonTypeEntityUsedAsTypeErr({
				entity: canonicalName,
				entityTag: entity.tag,
				useLocation: t.entity.location,
				entityBinding: entity.bindingLocation,
			});
		}

		const typeArguments = t.arguments.map(a =>
			compileType(a, scope, sourceContext, checkConstraints));

		if (checkConstraints === "check") {
			const expectedTypeParameterCount = entity.typeScope.typeVariableDebugNames.length;
			if (typeArguments.length !== expectedTypeParameterCount) {
				const typeVariableLocations = [];
				for (let v in entity.typeScope.typeVariables) {
					typeVariableLocations.push({
						location: entity.typeScope.typeVariables[v].bindingLocation,
					});
				}
				throw new diagnostics.TypeParameterCountMismatchErr({
					entityType: "record",
					entityName: t.entity.name,
					expectedCount: expectedTypeParameterCount,
					expectedLocation: ir.locationsSpan(typeVariableLocations),
					givenCount: t.arguments.length,
					givenLocation: t.location,
				});
			}

			const map = new Map();
			for (let i = 0; i < typeArguments.length; i++) {
				map.set(i, typeArguments[i]);
			}
			for (let requiredConstraint of entity.typeScope.constraints) {
				const instantiated: ir.ConstraintParameter = {
					interface: requiredConstraint.constraint.interface,
					subjects: requiredConstraint.constraint.subjects.map(s => ir.typeSubstitute(s, map)),
				};
				checkConstraintSatisfied(instantiated, scope, sourceContext, {
					constraintDeclaredAt: requiredConstraint.location,
					neededAt: t.location,
				});
			}
		}

		return {
			tag: "type-compound",
			record: { record_id: canonicalName },
			type_arguments: typeArguments,
		};
	} else if (t.tag === "type-var") {
		const id = scope.typeVariables[t.name];
		if (id === undefined) {
			throw new diagnostics.NoSuchTypeVariableErr({
				typeVariableName: t.name,
				location: t.location,
			});
		}
		return id.variable;
	}

	const _: never = t;
	throw new Error("compileType: unhandled tag `" + t["tag"] + "`");
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
	sourceID: string,
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
	}

	// Bring all imports into scope.
	for (const { imported } of source.imports) {
		resolveImport(imported, source.package, sourceContext, programContext);
	}

	programContext.sourceContexts[sourceID] = sourceContext;
}

function collectTypeScope(
	programContext: ProgramContext,
	sourceID: string,
	typeScope: TypeScope,
	typeParameters: grammar.TypeParameters,
) {
	for (const parameter of typeParameters.parameters) {
		const existingBinding = typeScope.typeVariables[parameter.name];
		if (existingBinding !== undefined) {
			throw new diagnostics.TypeVariableRedefinedErr({
				typeVariableName: parameter.name,
				firstBinding: existingBinding.bindingLocation,
				secondBinding: parameter.location,
			});
		}
		typeScope.typeVariables[parameter.name] = {
			variable: {
				tag: "type-variable",
				id: {
					type_variable_id: typeScope.typeVariableDebugNames.length,
				},
			},
			bindingLocation: parameter.location,
		};
		typeScope.typeVariableDebugNames.push(parameter.name);
	}
	for (let c of typeParameters.constraints) {
		const sourceContext = programContext.sourceContexts[sourceID];
		const methodSubject = compileType(c.methodSubject, typeScope,
			sourceContext, "skip")
		const constraint = compileConstraint(c.constraint, methodSubject,
			sourceContext, typeScope, "skip");
		typeScope.constraints.push({
			constraint,
			location: c.location,
		});
	}
}

/// Collects enough information to determine which types satisfy which
/// interfaces, so that types collected in `collectMembers` can be ensured to be
/// valid.
function collectTypeScopesAndConstraints(programContext: ProgramContext, entityName: string) {
	const entity = programContext.entitiesByCanonical[entityName];
	const sourceContext = programContext.sourceContexts[entity.sourceID];
	if (entity.tag === "record") {
		collectTypeScope(programContext, entity.sourceID,
			entity.typeScope, entity.ast.typeParameters);

		for (let claimAST of entity.ast.implementations.claimed) {
			const constraint = compileConstraint(claimAST, entity.typeScope.thisType,
				sourceContext, entity.typeScope, "skip");
			entity.implements.push({
				constraint,
				location: claimAST.location,
			});
		}
		return;
	} else if (entity.tag === "interface") {
		collectTypeScope(programContext, entity.sourceID,
			entity.typeScope, entity.ast.typeParameters);
		return;
	}

	const _: never = entity;
	throw new Error("collectTypeScopesAndConstraints: unhandled tag `" + entity["tag"] + "`");
}

/// Collects the "signatures" such that references to this entity within the
/// bodies of other entities can be type-checked.
/// Constraints must have already been collected in all entities using
/// `collectTypeScopesAndConstraints` prior to invoking `collectMembers`.
/// NOTE that this does NOT include compiling "requires" and "ensures" clauses,
/// which are compiled alongside function bodies in a later pass.
function collectMembers(programContext: ProgramContext, entityName: string) {
	const entity = programContext.entitiesByCanonical[entityName];
	const sourceContext = programContext.sourceContexts[entity.sourceID];
	if (entity.tag === "record") {
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
				entity.typeScope, sourceContext, "check");

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

			const parameterTypes = fn.signature.parameters.map(p => ({
				t: compileType(p.t, entity.typeScope, sourceContext, "check"),
				location: p.t.location,
			}));

			const returnTypes = fn.signature.returns.map(r => ({
				t: compileType(r, entity.typeScope, sourceContext, "check"),
				location: r.location,
			}));

			entity.fns[fnName] = {
				nameLocation: fn.signature.name.location,
				parameters: parameterTypes,
				returns: returnTypes,
				ast: fn,
				id: { function_id: canonicalFunctionName(entityName, fnName) },
			};
		}

		return;
	} else if (entity.tag === "interface") {
		// Collect the defined methods.
		for (const member of entity.ast.members) {
			const fnName = member.signature.name.name;
			const existingFn = entity.fns[fnName];
			if (existingFn !== undefined) {
				throw new diagnostics.MemberRedefinedErr({
					memberName: fnName,
					firstBinding: existingFn.nameLocation,
					secondBinding: member.signature.name.location,
				});
			}

			const parameterTypes = member.signature.parameters.map(p => ({
				t: compileType(p.t, entity.typeScope, sourceContext, "check"),
				location: p.t.location,
			}));

			const returnTypes = member.signature.returns.map(r => ({
				t: compileType(r, entity.typeScope, sourceContext, "check"),
				location: r.location,
			}));

			entity.fns[fnName] = {
				nameLocation: member.signature.name.location,
				parameters: parameterTypes,
				returns: returnTypes,
				ast: member,
			};
		}

		return;
	}

	const _: never = entity;
	throw new Error("collectMembers: unhandled tag `" + entity["tag"] + "`");
}

function canonicalFunctionName(entityName: string, memberName: string) {
	return entityName + "." + memberName;
}

interface FunctionContext {
	/// `returnsTo` indicates the types that an `op -return ` returns to,
	/// and where those return types can be found annotated in the source.
	returnsTo: { t: ir.Type, location: ir.SourceLocation }[],

	/// `ensuresReturnExpression` indicates the variables  that a `return `
	/// expression refers to. It is `null` if a `return ` expression is not valid
	/// in the given context (i.e., it's not in an `ensures` clause).
	ensuresReturnExpression: null | ValueInfo,

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

	defineTemporary(t: ir.Type, location: ir.SourceLocation, ops: ir.Op[] | null) {
		const name = "$" + this.stack.length;
		const id = this.defineVariable(name, t, location);
		if (ops !== null) {
			ops.push({
				tag: "op-var",
				type: t,
			});
		}
		return id;
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

function getRecord(context: FunctionContext, record: ir.RecordID): RecordEntityDef {
	const entity = context.sourceContext.programContext.entitiesByCanonical[record.record_id];
	if (entity.tag !== "record") {
		throw new Error("ICE: Bad record ID");
	}
	return entity;
}

function compileCallExpression(
	e: grammar.ExpressionCall,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	const baseType = compileType(e.t, typeScope, context.sourceContext, "check");
	if (baseType.tag !== "type-compound") {
		// TODO: Handle dynamic dispatch on type parameters.
		throw new diagnostics.CallOnNonCompoundErr({
			baseType: displayType(baseType, typeScope, context.sourceContext),
			location: e.t.location,
		});
	}

	const record = getRecord(context, baseType.record);
	const fn = record.fns[e.methodName.name];
	if (fn === undefined) {
		throw new diagnostics.NoSuchFnErr({
			baseType: displayType(baseType, typeScope, context.sourceContext),
			methodName: e.methodName.name,
			methodNameLocation: e.methodName.location,
		});
	}

	const argValues = [];
	for (let arg of e.arguments) {
		const tuple = compileExpression(arg, ops, stack, typeScope, context);
		for (let i = 0; i < tuple.values.length; i++) {
			argValues.push({ tuple, i });
		}
	}

	if (argValues.length !== fn.parameters.length) {
		throw new diagnostics.ValueCountMismatchErr({
			actualCount: argValues.length,
			actualLocation: ir.locationsSpan(e.arguments),
			expectedCount: fn.parameters.length,
			expectedLocation: ir.locationsSpan(fn.parameters),
		});
	}

	const typeArgumentMapping: Map<number, ir.Type> = new Map();
	for (let i = 0; i < baseType.type_arguments.length; i++) {
		typeArgumentMapping.set(i, baseType.type_arguments[i]);
	}

	const argumentSources = [];
	for (let i = 0; i < argValues.length; i++) {
		const value = argValues[i];
		const valueType = value.tuple.values[value.i].t;
		const templateType = fn.parameters[i].t;

		const expectedType = ir.typeSubstitute(templateType, typeArgumentMapping);

		if (!ir.equalTypes(expectedType, valueType)) {
			throw new diagnostics.TypeMismatchErr({
				givenType: displayType(valueType, typeScope, context.sourceContext),
				givenLocation: value.tuple.location,
				givenIndex: { index0: value.i, count: value.tuple.values.length },
				expectedType: displayType(expectedType, typeScope, context.sourceContext),
				expectedLocation: fn.parameters[i].location,
			});
		}
		argumentSources.push(value.tuple.values[value.i].id);
	}

	const destinations = [];
	const info = [];
	for (let i = 0; i < fn.returns.length; i++) {
		const templateType = fn.returns[i].t;
		const returnType = ir.typeSubstitute(templateType, typeArgumentMapping);

		const result = stack.defineTemporary(returnType, e.location, ops);
		destinations.push(result.id);
		info.push({
			t: returnType,
			id: result.id,
		});
	}
	ops.push({
		tag: "op-static-call",
		function: fn.id,

		arguments: argumentSources,
		type_arguments: baseType.type_arguments,
		destinations: destinations,

		diagnostic_callsite: e.location,
	});

	return {
		values: info,
		location: e.location,
	};
}

function compileRecordLiteral(
	e: grammar.ExpressionRecordLiteral,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	const t = compileType(e.t, typeScope, context.sourceContext, "check");
	if (t.tag !== "type-compound") {
		throw new diagnostics.NonCompoundInRecordLiteralErr({
			t: displayType(t, typeScope, context.sourceContext),
			location: e.t.location,
		});
	}
	const programContext = context.sourceContext.programContext;
	const record = programContext.entitiesByCanonical[t.record.record_id];
	if (record === undefined || record.tag !== "record") {
		throw new Error("ICE: invalid record from compileType");
	}

	const map = new Map();
	for (let i = 0; i < t.type_arguments.length; i++) {
		map.set(i, t.type_arguments[i]);
	}

	const initializations: Record<string, ValueInfo & { fieldLocation: ir.SourceLocation }> = {};
	for (let initAST of e.initializations) {
		const fieldName = initAST.fieldName.name;
		if (initializations[fieldName] !== undefined) {
			throw new diagnostics.FieldRepeatedInRecordLiteralErr({
				fieldName,
				firstLocation: initializations[fieldName].location,
				secondLocation: initAST.fieldName.location,
			});
		}
		const fieldDefinition = record.fields[fieldName];
		if (fieldDefinition === undefined) {
			throw new diagnostics.NoSuchFieldErr({
				recordType: displayType(t, typeScope, context.sourceContext),
				fieldName,
				location: initAST.fieldName.location,
				type: "initialization",
			});
		}

		const value = compileExpression(initAST.value, ops, stack, typeScope, context);
		if (value.values.length !== 1) {
			throw new diagnostics.MultiExpressionGroupedErr({
				location: value.location,
				valueCount: value.values.length,
				grouping: "field-init",
			});
		}
		const givenType = value.values[0].t;
		const expectedType = ir.typeSubstitute(fieldDefinition.t, map);

		if (!ir.equalTypes(expectedType, givenType)) {
			throw new diagnostics.TypeMismatchErr({
				givenType: displayType(givenType, typeScope, context.sourceContext),
				givenLocation: value.location,
				expectedType: displayType(expectedType, typeScope, context.sourceContext),
				expectedLocation: fieldDefinition.typeLocation,
			});
		}

		initializations[fieldName] = {
			...value,
			fieldLocation: initAST.fieldName.location,
		};
	}

	const fields: Record<string, ir.VariableID> = {};
	for (let required in record.fields) {
		if (initializations[required] === undefined) {
			throw new diagnostics.UninitializedFieldErr({
				recordType: displayType(t, typeScope, context.sourceContext),
				missingFieldName: required,
				definedLocation: record.fields[required].nameLocation,
				initializerLocation: e.location,
			});
		}
		fields[required] = initializations[required].values[0].id;
	}


	const destination = stack.defineTemporary(t, e.location, ops);
	ops.push({
		tag: "op-new-record",
		record: t.record,
		destination: destination.id,
		fields,
	});
	return {
		values: [{ t: destination.t, id: destination.id }],
		location: e.location,
	};
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
		const v = stack.defineTemporary(ir.T_INT, e.location, ops);
		ops.push({
			tag: "op-const",
			destination: v.id,
			value: e.value,
		});
		return { values: [{ t: v.t, id: v.id }], location: e.location };
	} else if (e.tag === "call") {
		return compileCallExpression(e, ops, stack, typeScope, context);
	} else if (e.tag === "keyword") {
		if (e.keyword === "false" || e.keyword === "true") {
			const v = stack.defineTemporary(ir.T_BOOLEAN, e.location, ops);
			ops.push({
				tag: "op-const",
				destination: v.id,
				value: e.keyword === "true",
			});
			return { values: [{ t: v.t, id: v.id }], location: e.location };
		} else if (e.keyword === "return") {
			if (context.ensuresReturnExpression === null) {
				throw new diagnostics.ReturnExpressionUsedOutsideEnsuresErr({
					returnLocation: e.location,
				});
			}
			return {
				values: context.ensuresReturnExpression.values,
				location: e.location,
			};
		} else {
			const _: never = e.keyword;
			throw new Error("compileExpressionAtom: keyword `" + e["keyword"] + "`");
		}
	} else if (e.tag === "record-literal") {
		return compileRecordLiteral(e, ops, stack, typeScope, context);
	} else if (e.tag === "string-literal") {
		const v = stack.defineTemporary(ir.T_BYTES, e.location, ops);
		ops.push({
			tag: "op-const",
			destination: v.id,
			value: e.value,
		});
		return { values: [{ t: v.t, id: v.id }], location: e.location };
	}

	const _: never = e;
	throw new Error("TODO: Unhandled tag `" + e["tag"] + "` in compileExpressionAtom");
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

			const programContext = context.sourceContext.programContext;
			const record = programContext.entitiesByCanonical[base.t.record.record_id];
			if (record.tag !== "record") {
				throw new Error("ICE: non-record referenced by compound type");
			}

			const map = new Map();
			for (let i = 0; i < base.t.type_arguments.length; i++) {
				map.set(i, base.t.type_arguments[i]);
			}

			const field = record.fields[access.fieldName.name];
			if (field === undefined) {
				throw new diagnostics.NoSuchFieldErr({
					recordType: displayType(base.t, typeScope, context.sourceContext),
					fieldName: access.fieldName.name,
					location: access.fieldName.location,
					type: "access",
				});
			}

			const fieldType = ir.typeSubstitute(field.t, map);
			const location = ir.locationSpan(value.location, access.fieldName.location);
			const temporary = stack.defineTemporary(fieldType, location, ops);
			ops.push({
				tag: "op-field",
				object: base.id,
				field: access.fieldName.name,
				destination: temporary.id,
			});
			value = {
				values: [{ id: temporary.id, t: temporary.t }],
				location: location,
			};
		} else if (access.tag === "method") {
			throw new Error("TODO: compileOperand method access");
		} else {
			const _: never = access;
			throw new Error("unhandled access tag `" + access["tag"] + "` in compileOperand");
		}
	}

	return value;
}

/// Throws `MultiExpressionGroupedErr` if `lhs` does not have exactly 1 value.
function resolveOperator(
	lhs: ValueInfo,
	operator: lexer.OperatorToken,
	typeScope: TypeScope,
	context: FunctionContext): ir.FunctionID {
	const opStr = operator.operator;
	if (lhs.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: lhs.location,
			valueCount: lhs.values.length,
			grouping: "op",
			op: opStr,
		});
	}
	const value = lhs.values[0];
	if (ir.equalTypes(ir.T_INT, value.t)) {
		if (opStr === "+") {
			return { function_id: "Int+" };
		} else if (opStr === "-") {
			return { function_id: "Int-" };
		} else if (opStr === "==") {
			return { function_id: "Int==" };
		}
	}

	throw new diagnostics.TypeDoesNotProvideOperatorErr({
		lhsType: displayType(value.t, typeScope, context.sourceContext),
		operator: opStr,
		operatorLocation: operator.location,
	});
}

const operatorPrecedence = {
	precedences: {
		"implies": 0,
		"and": 0,
		"or": 0,
		"==": 1,
		"<": 1,
		">": 1,
		"<=": 1,
		">=": 1,
		"!=": 1,
		"_default": 2,
	} as Record<string, number>,
	associativities: {
		implies: "right",
		and: "left",
		or: "left",
		"<": "left",
		">": "left",
	} as Record<string, "left" | "right" | "none">,
	associateGroups: {
		"<=": "<",
		">=": ">",
	} as Record<string, string>,
};

interface OperatorTreeLeaf {
	tag: "leaf",
	left: number,
	right: number,

	operand: grammar.ExpressionOperand,
	location: ir.SourceLocation,
}

interface OperatorTreeJoin {
	index: number,

	opToken: lexer.OperatorToken | grammar.BinaryLogicalToken,
	associativity: "none" | "left" | "right",

	/// Only operations with the same `associates` can associate without
	/// parenthesization.
	associates: string,

	precedence: number,
}

interface OperatorTreeBranch {
	tag: "branch",
	left: number,
	right: number,

	join: OperatorTreeJoin,
	leftBranch: OperatorTree,
	rightBranch: OperatorTree,

	location: ir.SourceLocation,
}

type OperatorTree = OperatorTreeLeaf | OperatorTreeBranch;

function checkTreeCompatible(subtree: OperatorTree, parent: OperatorTreeJoin) {
	if (subtree.tag === "leaf") {
		return;
	} else if (subtree.join.precedence < parent.precedence) {
		throw new Error("unreachable");
	} else if (subtree.join.precedence > parent.precedence) {
		return;
	} else if (subtree.join.associates !== parent.associates) {
		throw new diagnostics.OperationRequiresParenthesizationErr({
			op1: {
				str: subtree.join.opToken.tag === "keyword"
					? subtree.join.opToken.keyword
					: subtree.join.opToken.operator,
				location: subtree.join.opToken.location,
			},
			op2: {
				str: parent.opToken.tag === "keyword"
					? parent.opToken.keyword
					: parent.opToken.operator,
				location: parent.opToken.location,
			},
			reason: "unordered",
		});
	} else if (parent.associativity === "none") {
		throw new diagnostics.OperationRequiresParenthesizationErr({
			op1: {
				str: subtree.join.opToken.tag === "keyword"
					? subtree.join.opToken.keyword
					: subtree.join.opToken.operator,
				location: subtree.join.opToken.location,
			},
			op2: {
				str: parent.opToken.tag === "keyword"
					? parent.opToken.keyword
					: parent.opToken.operator,
				location: parent.opToken.location,
			},
			reason: "non-associative",
		});
	}
}

function applyOrderOfOperations(
	operators: (lexer.OperatorToken | grammar.BinaryLogicalToken)[],
	operands: grammar.ExpressionOperand[],
): OperatorTree {
	if (operators.length !== operands.length - 1) {
		throw new Error();
	}

	let joins: OperatorTreeJoin[] = [];
	for (let i = 0; i < operators.length; i++) {
		const operator = operators[i];
		const opStr = operator.tag === "keyword" ? operator.keyword : operator.operator;

		let precedence = operatorPrecedence.precedences[opStr];
		if (precedence === undefined) {
			precedence = operatorPrecedence.precedences._default;
		}

		const associativity = operatorPrecedence.associativities[opStr] || "none";
		const associates = operatorPrecedence.associateGroups[opStr] || opStr;
		joins.push({
			index: i,
			opToken: operator,
			associativity, precedence, associates,
		});
	}

	joins.sort((a, b) => {
		if (a.precedence !== b.precedence) {
			return b.precedence - a.precedence;
		} else if (a.associativity !== b.associativity) {
			return a.associativity.localeCompare(b.associativity);
		} else if (a.associativity === "right") {
			return b.index - a.index;
		} else {
			return b.index - a.index;
		}
	});

	const branches: OperatorTree[] = [];
	for (let i = 0; i < operands.length; i++) {
		branches.push({
			tag: "leaf",
			left: i,
			right: i,
			operand: operands[i],
			location: operands[i].location,
		});
	}
	let branch = branches[0];
	for (let join of joins) {
		const toLeft = join.index;
		const toRight = join.index + 1;
		const left = branches[toLeft];
		const right = branches[toRight];
		branch = {
			tag: "branch",
			join,
			leftBranch: left, rightBranch: right,
			left: left.left,
			right: right.right,
			location: ir.locationSpan(left.location, right.location),
		};

		checkTreeCompatible(left, join);
		checkTreeCompatible(right, join);

		branches[branch.left] = branch;
		branches[branch.right] = branch;
	}
	return branch;
}

function expectOneBooleanForContract(
	values: ValueInfo,
	typeScope: TypeScope,
	context: FunctionContext,
	contract: "assert" | "requires" | "ensures"
): { t: ir.Type, id: ir.VariableID } {
	if (values.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: values.location,
			valueCount: values.values.length,
			grouping: "op",
			op: contract,
		});
	}

	const value = values.values[0];
	if (!ir.equalTypes(ir.T_BOOLEAN, value.t)) {
		throw new diagnostics.BooleanTypeExpectedErr({
			givenType: displayType(value.t, typeScope, context.sourceContext),
			location: values.location,
			reason: "contract",
			contract: contract,
		});
	}
	return value;
}

function expectOneBooleanForLogical(
	values: ValueInfo,
	typeScope: TypeScope,
	context: FunctionContext,
	op: { opStr: string, location: ir.SourceLocation },
): { t: ir.Type, id: ir.VariableID } {
	if (values.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: values.location,
			valueCount: values.values.length,
			grouping: "op",
			op: op.opStr,
		});
	}

	const value = values.values[0];
	if (!ir.equalTypes(ir.T_BOOLEAN, value.t)) {
		throw new diagnostics.BooleanTypeExpectedErr({
			givenType: displayType(value.t, typeScope, context.sourceContext),
			location: values.location,
			reason: "logical-op",
			op: op.opStr,
			opLocation: op.location,
		});
	}
	return value;
}

function compileExpressionTree(
	tree: OperatorTree,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	if (tree.tag === "leaf") {
		return compileOperand(tree.operand, ops, stack, typeScope, context);
	}

	const left = compileExpressionTree(tree.leftBranch, ops, stack, typeScope, context);
	if (tree.join.opToken.tag === "keyword") {
		// Compile a logical binary operation.
		const opStr = tree.join.opToken.keyword;

		const leftValue = expectOneBooleanForLogical(left, typeScope, context, {
			opStr: tree.join.opToken.keyword,
			location: tree.join.opToken.location,
		});

		const result = stack.defineTemporary(ir.T_BOOLEAN, tree.location, ops);

		const branch: ir.OpBranch = {
			tag: "op-branch",
			condition: leftValue.id,
			trueBranch: { ops: [] },
			falseBranch: { ops: [] },
		};
		ops.push(branch);

		if (opStr === "or") {
			branch.trueBranch.ops.push({
				tag: "op-assign",
				destination: result.id,
				source: leftValue.id,
			});

			stack.openBlock();
			const right = compileExpressionTree(tree.rightBranch, branch.falseBranch.ops, stack, typeScope, context);
			const rightValue = expectOneBooleanForLogical(right, typeScope, context, {
				opStr: "or",
				location: tree.join.opToken.location,
			});

			branch.falseBranch.ops.push({
				tag: "op-assign",
				destination: result.id,
				source: rightValue.id,
			});
			stack.closeBlock();
		} else if (opStr === "and") {
			branch.falseBranch.ops.push({
				tag: "op-assign",
				destination: result.id,
				source: leftValue.id,
			});

			stack.openBlock();
			const right = compileExpressionTree(tree.rightBranch, branch.trueBranch.ops, stack, typeScope, context);
			const rightValue = expectOneBooleanForLogical(right, typeScope, context, {
				opStr: "and",
				location: tree.join.opToken.location,
			});

			branch.trueBranch.ops.push({
				tag: "op-assign",
				destination: result.id,
				source: rightValue.id,
			});
			stack.closeBlock();
		} else if (opStr === "implies") {
			branch.falseBranch.ops.push({
				tag: "op-const",
				value: true,
				destination: result.id,
			});

			stack.openBlock();
			const right = compileExpressionTree(tree.rightBranch, branch.trueBranch.ops, stack, typeScope, context);
			const rightValue = expectOneBooleanForLogical(right, typeScope, context, {
				opStr: "implies",
				location: tree.join.opToken.location,
			});

			branch.trueBranch.ops.push({
				tag: "op-assign",
				destination: result.id,
				source: rightValue.id,
			});

			stack.closeBlock();
		} else {
			const _: never = opStr;
			throw new Error("Unhandled logical operator `" + opStr + "`");
		}

		return { values: [{ t: result.t, id: result.id }], location: tree.location };
	} else {
		// Compile an arithmetic operation.
		const right = compileExpressionTree(tree.rightBranch, ops, stack, typeScope, context);

		const opStr = tree.join.opToken.operator;
		const fn = resolveOperator(left, tree.join.opToken, typeScope, context);
		const foreign = context.sourceContext.programContext.foreignSignatures[fn.function_id];
		if (foreign === undefined) {
			throw new Error(
				"resolveOperator produced a bad foreign signature (`" + fn.function_id
				+ "`) for `" + displayType(left.values[0].t, typeScope, context.sourceContext)
				+ "` `" + opStr + "`");
		} else if (foreign.parameters.length !== 2) {
			throw new Error(
				"Foreign signature `" + fn.function_id + "` cannot be used as"
				+ "an operator since it doesn't take exactly 2 parameters");
		}
		const expectedRhsType = foreign.parameters[1];

		if (right.values.length !== 1) {
			throw new diagnostics.MultiExpressionGroupedErr({
				location: right.location,
				valueCount: right.values.length,
				grouping: "op",
				op: opStr,
			});
		}

		if (!ir.equalTypes(expectedRhsType, right.values[0].t)) {
			throw new diagnostics.OperatorTypeMismatchErr({
				lhsType: displayType(left.values[0].t, typeScope, context.sourceContext),
				operator: opStr,
				givenRhsType: displayType(right.values[0].t, typeScope, context.sourceContext),
				expectedRhsType: displayType(foreign.parameters[1], typeScope, context.sourceContext),
				rhsLocation: right.location,
			});
		}

		if (foreign.return_types.length !== 1) {
			throw new Error(
				"Foreign signature `" + fn.function_id
				+ "` cannot be used as an operator since it produces "
				+ foreign.return_types.length + " values");
		}
		const result = stack.defineTemporary(foreign.return_types[0],
			ir.locationSpan(left.location, right.location), ops);

		ops.push({
			tag: "op-foreign",
			operation: fn.function_id,
			arguments: [left.values[0].id, right.values[0].id],
			destinations: [result.id],
		});

		return {
			values: [result],
			location: result.bindingLocation,
		};
	}
}

function compileExpression(
	e: grammar.Expression,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {

	const operands = [e.left, ...e.operations.map(x => x.right)];
	const operators = e.operations.map(x => x.operator);
	const tree = applyOrderOfOperations(operators, operands);
	return compileExpressionTree(tree, ops, stack, typeScope, context);

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
		const _: never = t;
		throw new Error("displayType: unhandled tag `" + t["tag"] + "`");
	}
}

/// `displayConstraint` formats the given IR constraint as a string, potentially
/// formatted for the given `SourceContext` (considering import aliases and
/// such).
function displayConstraint(
	c: ir.ConstraintParameter,
	typeScope: Readonly<TypeScope>,
	sourceContext: Readonly<SourceContext>,
): string {
	const base = c.interface.interface_id;
	if (c.subjects.length === 0) {
		throw new Error("ICE: Invalid constraint `" + base + "`");
	}

	const lhs = displayType(c.subjects[0], typeScope, sourceContext);
	const rhs = c.subjects.slice(1).map(t =>
		displayType(t, typeScope, sourceContext));
	if (rhs.length === 0) {
		return `${lhs} is ${base}`;
	} else {
		return `${lhs} is ${base}[${rhs.join(", ")}]`;
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
		const t = compileType(v.t, typeScope, context.sourceContext, "check");
		const d = stack.defineVariable(v.variable.name, t, v.variable.location);
		ops.push({
			tag: "op-var",
			type: t,
		});
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

	if (values.length === 0) {
		throw new Error("ICE: return must take at least 1 value");
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
	let op: ir.OpReturn = {
		tag: "op-return",
		sources: [],
		diagnostic_return_site: statement.location,
	};
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

function compileIfClause(
	clause: grammar.ElseIfClause,
	rest: grammar.ElseIfClause[],
	restIndex: number,
	elseClause: grammar.ElseClause | null,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext) {
	const condition = compileExpression(clause.condition, ops, stack, typeScope, context);
	if (condition.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: clause.condition.location,
			valueCount: condition.values.length,
			grouping: "if",
		});
	}
	const conditionValue = condition.values[0];
	if (!ir.equalTypes(ir.T_BOOLEAN, conditionValue.t)) {
		throw new diagnostics.BooleanTypeExpectedErr({
			givenType: displayType(conditionValue.t, typeScope, context.sourceContext),
			location: clause.condition.location,
			reason: "if",
		});
	}

	const trueBranch: ir.OpBlock = compileBlock(clause.body, stack, typeScope, context);

	stack.openBlock();
	let falseBranch: ir.OpBlock = { ops: [] };
	if (restIndex >= rest.length) {
		// Reached else clause.
		if (elseClause !== null) {
			falseBranch = compileBlock(elseClause.body, stack, typeScope, context);
		}
	} else {
		compileIfClause(rest[restIndex], rest, restIndex + 1, elseClause,
			falseBranch.ops, stack, typeScope, context);
	}
	stack.closeBlock();

	ops.push({
		tag: "op-branch",
		condition: conditionValue.id,
		trueBranch,
		falseBranch,
	});
}

function compileIfSt(
	statement: grammar.IfSt,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext) {
	compileIfClause(statement, statement.elseIfClauses, 0, statement.elseClause,
		ops, stack, typeScope, context);
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
		return;
	} else if (statement.tag === "if") {
		compileIfSt(statement, ops, stack, typeScope, context);
		return;
	} else if (statement.tag === "unreachable") {
		ops.push({
			tag: "op-unreachable",
			diagnostic_kind: "unreachable",
			diagnostic_location: statement.location,
		});
		return;
	}

	const _: never = statement;
	throw new Error("Unhandled tag in compileStatement `" + statement["tag"] + "`");
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
		ops: ops,
	};
}

function compileFunctionSignature(
	signatureAST: grammar.FnSignature,
	typeScope: TypeScope,
	sourceContext: SourceContext,
): {
	signature: ir.FunctionSignature,
	stack: VariableStack,
	context: FunctionContext,
} {
	const signature: ir.FunctionSignature = {
		type_parameters: typeScope.typeVariableDebugNames,
		constraint_parameters: typeScope.constraints.map(c => c.constraint),

		parameters: [],
		return_types: [],

		preconditions: [],
		postconditions: [],
	};

	const stack = new VariableStack();
	for (const parameterAST of signatureAST.parameters) {
		const t = compileType(parameterAST.t, typeScope, sourceContext, "check");
		signature.parameters.push(t);
		stack.defineVariable(parameterAST.name.name, t, parameterAST.name.location);
	}

	const context: FunctionContext = {
		returnsTo: [],
		sourceContext,
		ensuresReturnExpression: null,
	};
	for (const r of signatureAST.returns) {
		const t = compileType(r, typeScope, sourceContext, "check");
		signature.return_types.push(t);
		context.returnsTo.push({ t, location: r.location });
	}

	for (let precondition of signatureAST.requires) {
		const block: ir.OpBlock = { ops: [] };
		stack.openBlock();
		const result = compileExpression(precondition.expression, block.ops, stack, typeScope, context);
		const asserted = expectOneBooleanForContract(result, typeScope, context, "requires");
		stack.closeBlock();
		signature.preconditions.push({
			block,
			result: asserted.id,
			location: precondition.expression.location,
		});
	}

	if (signatureAST.ensures.length !== 0) {
		stack.openBlock();
		// The variables in a "return" expression are treated as "parameter"
		// variables for the ensures block.
		const ensuresReturnExpression: ValueInfo = {
			location: ir.locationsSpan(signatureAST.returns),
			values: [],
		};
		for (let i = 0; i < signature.return_types.length; i++) {
			const v = stack.defineTemporary(signature.return_types[i], signatureAST.returns[i].location, null);
			ensuresReturnExpression.values.push(v);
		}

		for (let postcondition of signatureAST.ensures) {
			const block: ir.OpBlock = { ops: [] };
			stack.openBlock();
			const result = compileExpression(postcondition.expression, block.ops, stack, typeScope, {
				...context,
				ensuresReturnExpression,
			});
			const asserted = expectOneBooleanForContract(result, typeScope, context, "ensures");
			stack.closeBlock();
			signature.postconditions.push({
				block,
				result: asserted.id,
				location: postcondition.expression.location,
			});
		}
		stack.closeBlock();
	}

	return { signature, stack, context };
}

function compileFunction(
	program: ir.Program,
	def: FnBinding,
	fName: string,
	sourceContext: SourceContext,
	typeScope: TypeScope) {

	const { signature, stack, context } = compileFunctionSignature(
		def.ast.signature, typeScope, sourceContext);
	const body = compileBlock(def.ast.body, stack, typeScope, context);

	// Make the verifier prove that this function definitely does not exit
	// without returning.
	if (body.ops.length === 0 || !ir.opTerminates(body.ops[body.ops.length - 1])) {
		body.ops.push({
			tag: "op-unreachable",
			diagnostic_kind: "return",
			diagnostic_location: def.ast.body.closing,
		});
	}

	program.functions[fName] = { signature, body };
}

function compileInterfaceEntity(
	program: ir.Program,
	entity: InterfaceEntityDef,
	entityName: string,
	programContext: ProgramContext,
) {
	const compiled: ir.IRInterface = {
		type_parameters: entity.ast.typeParameters.parameters.map(x => x.name),
		signatures: {},
	};
	const sourceContext = programContext.sourceContexts[entity.sourceID];
	for (const fnName in entity.fns) {
		const fn = entity.fns[fnName];
		const signature = compileFunctionSignature(
			fn.ast.signature, entity.typeScope, sourceContext);
		compiled.signatures[fnName] = signature.signature;
	}

	program.interfaces[entityName] = compiled;
}

function compileRecordEntity(
	program: ir.Program,
	entity: RecordEntityDef,
	entityName: string,
	programContext: ProgramContext,
) {
	// Layout storage for this record.
	program.records[entityName] = {
		type_parameters: entity.ast.typeParameters.parameters.map(x => x.name),
		fields: {},
	};
	for (const fieldName in entity.fields) {
		program.records[entityName].fields[fieldName] = entity.fields[fieldName].t;
	}

	// Implement functions.
	for (const f in entity.fns) {
		const def = entity.fns[f];
		const fName = def.id.function_id;
		compileFunction(program, def, fName,
			programContext.sourceContexts[entity.sourceID], entity.typeScope);
	}

	// TODO: Implement vtable factories.
}

/// `compileEntity` compiles the indicated entity into records, functions,
/// interfaces, vtable-factories, etc in the given `program`.
/// THROWS `SemanticError` if a type-error is discovered within the
/// implementation of this entity.
function compileEntity(
	program: ir.Program,
	programContext: Readonly<ProgramContext>,
	entityName: string) {
	const entity = programContext.entitiesByCanonical[entityName];
	if (entity.tag === "record") {
		return compileRecordEntity(program, entity, entityName, programContext);
	} else if (entity.tag === "interface") {
		return compileInterfaceEntity(program, entity, entityName, programContext);
	}

	const _: never = entity;
	throw new Error("compileEntity: unhandled tag `" + entity["tag"] + "`");
}

function getBasicForeign(): Record<string, ir.FunctionSignature> {
	return {
		"Int==": {
			// Equality
			parameters: [ir.T_INT, ir.T_INT],
			return_types: [ir.T_BOOLEAN],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [],
			semantics: {
				eq: true,
			},
		},
		"Int+": {
			// Addition
			parameters: [ir.T_INT, ir.T_INT],
			return_types: [ir.T_INT],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [],
		},
		"Int-": {
			// Subtract
			parameters: [ir.T_INT, ir.T_INT],
			return_types: [ir.T_INT],
			type_parameters: [],
			constraint_parameters: [],
			preconditions: [],
			postconditions: [],
		},
	};
}

/// `compileSources` transforms the ASTs making up a Shiru program into a
/// `ir.Program`.
/// THROWS `SemanticError` if a type-error is discovered within the given source
/// files.
export function compileSources(sources: Record<string, grammar.Source>): ir.Program {
	const programContext = collectAllEntities(sources);

	// Collect all entities and source contexts.
	for (const sourceID in sources) {
		resolveSourceContext(sourceID, sources[sourceID], programContext);
	}

	// Resolve type scopes and constraints.
	for (let canonicalEntityName in programContext.entitiesByCanonical) {
		collectTypeScopesAndConstraints(programContext, canonicalEntityName);
	}

	// Recheck all the unchecked types & constraints found in the above step:
	const uncheckedTypes = programContext.uncheckedTypes!;
	const uncheckedConstraints = programContext.uncheckedConstraints!;
	programContext.uncheckedTypes = [];
	programContext.uncheckedConstraints = [];
	for (const { t, scope, sourceContext } of uncheckedTypes) {
		compileType(t, scope, sourceContext, "check");
	}
	for (const { c, methodSubject, sourceContext, scope } of uncheckedConstraints) {
		compileConstraint(c, methodSubject, sourceContext, scope, "check");
	}

	// Resolve members of entities. Type arguments must be validated based on
	// collected constraints.
	for (let canonicalEntityName in programContext.entitiesByCanonical) {
		collectMembers(programContext, canonicalEntityName);
	}

	const program: ir.Program = {
		functions: {},
		interfaces: {},
		records: {},
		foreign: programContext.foreignSignatures,
		globalVTableFactories: {},
	};

	for (let canonicalEntityName in programContext.entitiesByCanonical) {
		compileEntity(program, programContext, canonicalEntityName);
	}
	return program;
}
