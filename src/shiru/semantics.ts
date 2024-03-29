import * as grammar from "./grammar.js";
import * as ir from "./ir.js";
import * as diagnostics from "./diagnostics.js";
import * as lexer from "./lexer.js";
import { DefaultMap } from "./data.js";
import * as builtin from "./builtin.js";

interface FieldBinding {
	nameLocation: ir.SourceLocation,
	t: ir.Type,
	typeLocation: ir.SourceLocation,
}

interface TypeBinding {
	t: ir.Type,
	nameLocation: ir.SourceLocation,
	typeLocation: ir.SourceLocation,
}

interface FnBinding {
	tag: "fn-binding",

	nameLocation: ir.SourceLocation,
	parameters: TypeBinding[],
	parametersLocation: ir.SourceLocation,
	returns: TypeBinding[],
	ast: grammar.Fn,

	/// The type variables bound by the containing entity (e.g., record).
	entityTypeVariables: ir.TypeVariableID[],

	/// The type variables bound specifically to this signature.
	signatureTypeVariables: ir.TypeVariableID[],

	id: ir.FunctionID,
}

interface InterfaceFnBinding {
	tag: "vtable-binding",
	signature_id: string,

	nameLocation: ir.SourceLocation,
	parameters: TypeBinding[],
	parametersLocation: ir.SourceLocation,
	returns: TypeBinding[],
	ast: grammar.InterfaceMember,

	interfaceTypeVariables: ir.TypeVariableID[],
	signatureTypeVariables: ir.TypeVariableID[],
}

interface RecordEntityDef {
	tag: "record",
	ast: grammar.RecordDefinition,
	sourceID: string,
	bindingLocation: ir.SourceLocation,

	/// `typeScope` indicates the type-parameters (and their available
	/// constraints) within each member of `fields`, `implements`, and `fns`.
	typeScope: TypeScopeI<ir.TypeCompound>,
	fields: Record<string, FieldBinding>,

	/// The set of constraints that this record type is the method-subject of.
	implsByInterface: DefaultMap<ir.InterfaceID, ImplEntityDef[]>,

	fns: Record<string, FnBinding>,
}

interface EnumEntityDef {
	tag: "enum",
	ast: grammar.EnumDefinition,
	sourceID: string,
	bindingLocation: ir.SourceLocation,

	typeScope: TypeScopeI<ir.TypeCompound>,
	variants: Record<string, FieldBinding>,

	implsByInterface: DefaultMap<ir.InterfaceID, ImplEntityDef[]>,

	fns: Record<string, FnBinding>,
}

interface InterfaceEntityDef {
	tag: "interface",
	ast: grammar.InterfaceDefinition,
	sourceID: string,
	bindingLocation: ir.SourceLocation,

	typeScope: TypeScopeI<ir.TypeVariable>,
	fns: Record<string, InterfaceFnBinding>,
}

interface ImplEntityDef {
	tag: "impl",
	ast: grammar.ImplDefinition,
	headLocation: ir.SourceLocation,
	sourceID: string,

	typeScope: TypeScopeI<null>,
	constraint: ir.ConstraintParameter,
}

type NamedEntityDef = RecordEntityDef | EnumEntityDef | InterfaceEntityDef;
type EntityDef = NamedEntityDef | ImplEntityDef;

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
class ProgramContext {
	/// `canonicalByQualifiedName` is map from package name to entity name to
	/// canonical name.
	canonicalByQualifiedName: Record<string, Record<string, string>> = {};

	/// `entitiesByCanonical` identifies information of the entity with the
	/// given "canonical" name.of the entity.
	private entitiesByCanonical: Record<string, NamedEntityDef> = {};

	sourceContexts: Record<string, SourceContext> = {};

	/// `uncheckedTypes` and `uncheckedConstraints` are initially `[]`, and
	/// become `null` once  enough members have been collected to check that
	/// type arguments implement the required constraints.
	uncheckedTypes: null | {
		t: grammar.Type,
		scope: TypeScope,
		sourceContext: SourceContext,
	}[] = [];
	uncheckedConstraints: null | {
		c: grammar.TypeNamed,
		methodSubject: ir.Type,
		sourceContext: Readonly<SourceContext>,
		scope: TypeScope,
		/// The location of the constraint, including the method subject and
		/// `is`.
		constraintLocation: ir.SourceLocation,
	}[] = [];

	*namedEntities(): Generator<[string, NamedEntityDef]> {
		for (const key in this.entitiesByCanonical) {
			yield [key, this.entitiesByCanonical[key as any]];
		}
	}

	getDataEntity(id: ir.RecordID | ir.EnumID): RecordEntityDef | EnumEntityDef {
		const entity = this.entitiesByCanonical[id as string];
		if (entity === undefined || entity.tag !== "enum" && entity.tag !== "record") {
			throw new Error("getDataEntity: bad id");
		}
		return entity;
	}

	getNamedEntity(canonicalName: string): NamedEntityDef | null {
		const entity = this.entitiesByCanonical[canonicalName];
		if (entity === undefined) {
			return null;
		}
		return entity;
	}

	defineEntity(canonicalName: string, entity: NamedEntityDef) {
		if (canonicalName in this.entitiesByCanonical) {
			throw new Error("ProgramContext.defineEntity: entity already exists");
		}

		this.entitiesByCanonical[canonicalName] = entity;
	}

	getRecord(recordID: ir.RecordID): RecordEntityDef {
		const entity = this.entitiesByCanonical[recordID];
		if (entity === undefined || entity.tag !== "record") {
			throw new Error("ICE: unexpected non-record ID `" + recordID + "`");
		}
		return entity;
	}

	getInterface(interfaceID: ir.InterfaceID): InterfaceEntityDef {
		const entity = this.entitiesByCanonical[interfaceID];
		if (entity === undefined || entity.tag !== "interface") {
			throw new Error("ICE: unexpected non-interface ID `" + interfaceID + "`");
		}
		return entity;
	}
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

	implASTs: grammar.ImplDefinition[],

	/// `programContext` is a reference to the single common `ProgramContext`.
	programContext: ProgramContext,
}

function collectInterfaceRecordEntity(
	programContext: ProgramContext,
	pack: Record<string, string>,
	packageName: string,
	sourceID: string,
	definition: grammar.InterfaceDefinition | grammar.RecordDefinition | grammar.EnumDefinition,
) {
	const entityName = definition.entityName.name;
	const bindingLocation = definition.entityName.location;
	if (pack[entityName] !== undefined) {
		const firstCanonical = pack[entityName];
		const firstBinding = programContext.getNamedEntity(firstCanonical)!;
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
			base: canonicalName as ir.RecordID,
			type_arguments: definition.typeParameters.parameters.map(t => ({
				tag: "type-variable",
				id: t.name as ir.TypeVariableID,
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
				typeVariables: new Map(),
				typeVariableList: [],
			},

			// These are filled in by `collectMembers`.
			fields: {},
			fns: {},
			implsByInterface: new DefaultMap<ir.InterfaceID, ImplEntityDef[]>(() => []),
		};
	} else if (definition.tag === "enum-definition") {
		const thisType: ir.Type = {
			tag: "type-compound",
			base: canonicalName as ir.RecordID,
			type_arguments: definition.typeParameters.parameters.map(t => ({
				tag: "type-variable",
				id: t.name as ir.TypeVariableID,
			})),
		};

		entity = {
			tag: "enum",
			ast: definition,
			bindingLocation,
			sourceID,

			typeScope: {
				thisType,

				constraints: [],
				typeVariables: new Map(),
				typeVariableList: [],
			},

			// These are filled in by `collectMembers`.
			variants: {},
			fns: {},
			implsByInterface: new DefaultMap<ir.InterfaceID, ImplEntityDef[]>(() => []),
		};
	} else {
		const thisType = "This" as ir.TypeVariableID;
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
					id: thisType,
				},
				constraints: [],
				typeVariables: new Map(),
				typeVariableList: [thisType],
			},

			// These are filled in by `collectMembers`.
			fns: {},
		};
	}

	programContext.defineEntity(canonicalName, entity);
	pack[entityName] = canonicalName;
}

// Collects the set of entities defined across all given sources.
function collectAllEntities(sources: Record<string, grammar.Source>) {
	const programContext = new ProgramContext();
	for (const sourceID in sources) {
		const source = sources[sourceID];
		const packageName = source.package.packageName.name;
		const pack = programContext.canonicalByQualifiedName[packageName] || {};
		programContext.canonicalByQualifiedName[packageName] = pack;
		for (let definition of source.definitions) {
			if (definition.tag === "impl-definition") {
				// These are instead collected in `resolveSourceContext`.
			} else {
				collectInterfaceRecordEntity(programContext, pack, packageName, sourceID, definition);
			}
		}
	}
	return programContext;
}

interface TypeVariableBinding {
	bindingLocation: ir.SourceLocation,
	variable: ir.TypeVariable,
}

interface TypeScopeI<This extends ir.Type | null> {
	thisType: This,

	/// `typeVariables` maps from the `TypeVarToken.name` to the ID in IR.
	typeVariables: Map<ir.TypeVariableID, TypeVariableBinding>,
	typeVariableList: ir.TypeVariableID[],

	constraints: TypeArgumentConstraint[],
}

interface TypeArgumentConstraint {
	constraint: ir.ConstraintParameter,
	location: ir.SourceLocation,
}

type TypeScope = TypeScopeI<ir.Type | null>;

/// RETURNS the canonicalized version of the given entity name within the given
/// source context.
function resolveEntity(
	t: grammar.TypeNamed,
	sourceContext: Readonly<SourceContext>
): string {
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
	/// The location of the constraint, including the method subject.
	constraintLocation: ir.SourceLocation,
): ir.ConstraintParameter {
	const programContext = sourceContext.programContext;
	if (programContext.uncheckedConstraints !== null) {
		if (checkConstraints === "skip") {
			programContext.uncheckedConstraints.push({
				c,
				methodSubject,
				sourceContext,
				scope,
				constraintLocation,
			});
			checkConstraints = "skip-internal";
		}
	} else if (checkConstraints !== "check") {
		throw new Error("compileConstraint: invalid `checkConstraints` argument.");
	}

	// Resolve the entity.
	const canonicalName = resolveEntity(c, sourceContext);
	const interfaceEntity = programContext.getNamedEntity(canonicalName)!;
	if (interfaceEntity.tag !== "interface") {
		throw new diagnostics.TypeUsedAsConstraintErr({
			name: canonicalName,
			kind: interfaceEntity.tag,
			typeLocation: c.location,
		});
	}

	const argumentSubjects = c.arguments.map(a =>
		compileType(a, scope, sourceContext, checkConstraints));

	if (checkConstraints === "check") {
		const expectedLocations = [];
		for (let [_, binding] of interfaceEntity.typeScope.typeVariables) {
			expectedLocations.push({
				location: binding.bindingLocation,
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

		const allArguments = [methodSubject, ...argumentSubjects];
		if (interfaceEntity.typeScope.typeVariableList[0] !== interfaceEntity.typeScope.thisType!.id) {
			throw new Error("ICE: First InterfaceEntity type parameter must be `this` type")
		}
		const instantiation = ir.typeArgumentsMap(interfaceEntity.typeScope.typeVariableList, allArguments);
		const thisType = interfaceEntity.typeScope.thisType;
		if (thisType === null) {
			throw new Error("compileConstraint: InterfaceEntity thisType must be a type variable.");
		}
		for (const requirementBinding of interfaceEntity.typeScope.constraints) {
			const genericConstraint = requirementBinding.constraint;
			const instantiated: ir.ConstraintParameter = ir.constraintSubstitute(genericConstraint, instantiation);
			checkConstraintSatisfied(instantiated, scope, sourceContext, {
				constraintDeclaredAt: requirementBinding.location,
				neededAt: constraintLocation,
			});
		}
	}

	return {
		interface: canonicalName as ir.InterfaceID,
		subjects: [methodSubject, ...argumentSubjects],
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
		constraintDeclaredAt: ir.SourceLocation | null,
		neededAt: ir.SourceLocation,
	},
) {
	const programContext = sourceContext.programContext;
	const methodSubject = requiredConstraint.subjects[0];
	if (methodSubject === undefined) {
		throw new Error("ICE: Constraint requires at least one subject.");
	} else if (methodSubject.tag === "type-compound") {
		const baseEntity = programContext.getDataEntity(methodSubject.base);

		const implCandidates = baseEntity.implsByInterface.get(requiredConstraint.interface);
		for (const impl of implCandidates) {
			// Check whether `impl.constraint` may be instantiated by replacing
			// `impl.typeScope`'s variables to become `requiredConstraint`.
			const unifier = ir.unifyTypes(
				impl.typeScope.typeVariableList,
				impl.constraint.subjects,
				[],
				requiredConstraint.subjects,
			);

			if (unifier !== null) {
				// This instantiation was possible.
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
	} else if (methodSubject.tag === "type-any") {
		// TODO: Emit a custom message indicating that a cast is required.
	} else {
		const _: never = methodSubject;
		throw new Error("checkConstraintSatisfied: Unhandled methodSubject tag `" + methodSubject["tag"] + "`");
	}

	throw new diagnostics.TypesDontSatisfyConstraintErr({
		neededConstraint: displayConstraint(requiredConstraint),
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
		} else if (t.keyword === "Any") {
			return ir.T_ANY;
		} else {
			return {
				tag: "type-primitive",
				primitive: t.keyword,
			};
		}
	} else if (t.tag === "named") {
		// Resolve the entity.
		const canonicalName = resolveEntity(t, sourceContext);
		const entity = sourceContext.programContext.getNamedEntity(canonicalName)!;
		if (entity.tag === "interface") {
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
			const expectedTypeParameterCount = entity.typeScope.typeVariableList.length;
			if (typeArguments.length !== expectedTypeParameterCount) {
				const typeVariableLocations = [];
				for (let [_, binding] of entity.typeScope.typeVariables) {
					typeVariableLocations.push({
						location: binding.bindingLocation,
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

			const instantiation = ir.typeArgumentsMap(entity.typeScope.typeVariableList, typeArguments);
			for (let requirementBinding of entity.typeScope.constraints) {
				const instantiated = ir.constraintSubstitute(requirementBinding.constraint, instantiation);
				checkConstraintSatisfied(instantiated, scope, sourceContext, {
					constraintDeclaredAt: requirementBinding.location,
					neededAt: t.location,
				});
			}
		}

		return {
			tag: "type-compound",
			base: canonicalName as ir.RecordID | ir.EnumID,
			type_arguments: typeArguments,
		};
	} else if (t.tag === "type-var") {
		const id = scope.typeVariables.get(t.name as ir.TypeVariableID);
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
	programContext: ProgramContext,
) {
	const packageName = source.package.packageName.name;
	const pack = programContext.canonicalByQualifiedName[packageName];

	const sourceContext: SourceContext = {
		entityAliases: {},
		namespaces: {},
		implASTs: [],
		programContext,
	};

	for (const definition of source.definitions) {
		if (definition.tag === "impl-definition") {
			// impls will only be processed after all available types have been
			// resolved.
			sourceContext.implASTs.push(definition);
		}
	}

	// Bring all entities defined within this package into scope.
	for (let entityName in pack) {
		const canonicalName = pack[entityName];
		const binding = programContext.getNamedEntity(canonicalName)!;
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
	sourceContext: SourceContext,
	typeScope: TypeScope,
	typeParameters: grammar.TypeParameters,
): void {
	for (const parameter of typeParameters.parameters) {
		const id = parameter.name as ir.TypeVariableID;
		const existingBinding = typeScope.typeVariables.get(id);
		if (existingBinding !== undefined) {
			throw new diagnostics.TypeVariableRedefinedErr({
				typeVariableName: parameter.name,
				firstBinding: existingBinding.bindingLocation,
				secondBinding: parameter.location,
			});
		}
		typeScope.typeVariables.set(id, {
			variable: { tag: "type-variable", id },
			bindingLocation: parameter.location,
		});
		typeScope.typeVariableList.push(parameter.name as ir.TypeVariableID);
	}
	for (let c of typeParameters.constraints) {
		const methodSubject = compileType(c.methodSubject, typeScope,
			sourceContext, "skip")
		const constraint = compileConstraint(c.constraint, methodSubject,
			sourceContext, typeScope, "skip", c.location);
		typeScope.constraints.push({
			constraint,
			location: c.location,
		});
	}
}

/// Collects enough information to determine which types satisfy which
/// interfaces, so that types collected in `collectMembers` can be ensured to be
/// valid.
function resolveAvailableTypes(
	programContext: ProgramContext,
	entity: NamedEntityDef,
) {
	if (entity.tag === "record") {
		collectTypeScope(programContext.sourceContexts[entity.sourceID],
			entity.typeScope, entity.ast.typeParameters);
		return;
	} else if (entity.tag === "enum") {
		collectTypeScope(programContext.sourceContexts[entity.sourceID],
			entity.typeScope, entity.ast.typeParameters);
		return;
	} else if (entity.tag === "interface") {
		collectTypeScope(programContext.sourceContexts[entity.sourceID],
			entity.typeScope, entity.ast.typeParameters);
		return;
	}

	const _: never = entity;
	throw new Error("collectTypeScopesAndConstraints: unhandled tag `" + entity["tag"] + "`");
}

function resolveMemberFn(
	canonicalName: ir.FunctionID,
	fn: grammar.Fn,
	entityTypeScope: TypeScopeI<ir.TypeCompound>,
	sourceContext: SourceContext,
): FnBinding {

	const parameterTypes = fn.signature.parameters.list.map(p => ({
		t: compileType(p.t, entityTypeScope, sourceContext, "check"),
		nameLocation: p.name.location,
		typeLocation: p.t.location,
	}));

	const returnTypes = fn.signature.returns.map(r => ({
		t: compileType(r, entityTypeScope, sourceContext, "check"),
		nameLocation: r.location,
		typeLocation: r.location,
	}));

	return {
		tag: "fn-binding",
		id: canonicalName,

		nameLocation: fn.signature.name.location,
		parameters: parameterTypes,
		parametersLocation: fn.signature.parameters.location,
		returns: returnTypes,
		ast: fn,

		entityTypeVariables: entityTypeScope.typeVariableList,
		signatureTypeVariables: [],
	};
}

function resolveRecordMemberSignatures(
	entity: RecordEntityDef,
	sourceContext: SourceContext,
	entityName: string,
) {
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

		const canonicalName = canonicalFunctionName(entityName, fnName);
		entity.fns[fnName] = resolveMemberFn(canonicalName, fn, entity.typeScope, sourceContext);
	}
}

function resolveEnumMemberSignatures(
	entity: EnumEntityDef,
	sourceContext: SourceContext,
	entityName: string,
) {
	// Collect the defined variants.
	for (const variant of entity.ast.variants) {
		const variantName = variant.name.name;
		const existingVariant = entity.variants[variantName];
		if (existingVariant !== undefined) {
			throw new diagnostics.MemberRedefinedErr({
				memberName: variantName,
				firstBinding: existingVariant.nameLocation,
				secondBinding: variant.name.location,
			});
		}

		const variantType = compileType(variant.t,
			entity.typeScope, sourceContext, "check");

		entity.variants[variantName] = {
			nameLocation: variant.name.location,
			t: variantType,
			typeLocation: variant.t.location,
		};
	}

	// Collect the defined methods.
	for (const fn of entity.ast.fns) {
		const fnName = fn.signature.name.name;

		const existingVariant = entity.variants[fnName];
		if (existingVariant !== undefined) {
			throw new diagnostics.MemberRedefinedErr({
				memberName: fnName,
				firstBinding: existingVariant.nameLocation,
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

		const canonicalName = canonicalFunctionName(entityName, fnName);
		entity.fns[fnName] = resolveMemberFn(canonicalName, fn, entity.typeScope, sourceContext);
	}
}

function resolveInterfaceMemberSignatures(
	entity: InterfaceEntityDef,
	sourceContext: SourceContext,
) {
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

		const parameterTypes = member.signature.parameters.list.map(p => ({
			t: compileType(p.t, entity.typeScope, sourceContext, "check"),
			nameLocation: p.name.location,
			typeLocation: p.t.location,
		}));

		const returnTypes = member.signature.returns.map(r => ({
			t: compileType(r, entity.typeScope, sourceContext, "check"),
			nameLocation: r.location,
			typeLocation: r.location,
		}));

		entity.fns[fnName] = {
			tag: "vtable-binding",
			signature_id: fnName,

			nameLocation: member.signature.name.location,
			parameters: parameterTypes,
			parametersLocation: member.signature.parameters.location,
			returns: returnTypes,
			ast: member,
			interfaceTypeVariables: entity.typeScope.typeVariableList,
			signatureTypeVariables: [],
		};
	}
}

/// Collects the "signatures" such that references to this entity within the
/// bodies of other entities can be type-checked.
/// Constraints must have already been collected in all entities using
/// `collectTypeScopesAndConstraints` prior to invoking `collectMembers`.
/// NOTE that this does NOT include compiling "requires" and "ensures" clauses,
/// which are compiled alongside function bodies in a later pass.
function resolveMemberSignatures(
	programContext: ProgramContext,
	entityName: string,
	entity: NamedEntityDef,
) {
	const sourceContext = programContext.sourceContexts[entity.sourceID];
	if (entity.tag === "record") {
		resolveRecordMemberSignatures(entity, sourceContext, entityName);
		return;
	} else if (entity.tag === "enum") {
		resolveEnumMemberSignatures(entity, sourceContext, entityName);
		return;
	} else if (entity.tag === "interface") {
		resolveInterfaceMemberSignatures(entity, sourceContext);
		return;
	}

	const _: never = entity;
	throw new Error("collectMembers: unhandled tag `" + entity["tag"] + "`");
}

function canonicalFunctionName(entityName: string, memberName: string): ir.FunctionID {
	return entityName + "." + memberName as ir.FunctionID;
}

interface FunctionContext {
	/// `returnsTo` indicates the types that an `op-return` returns to,
	/// and where those return types can be found annotated in the source.
	returnsTo: { t: ir.Type, location: ir.SourceLocation }[],

	/// `ensuresReturnExpression` indicates the variables  that a `return`
	/// expression refers to. It is `null` if a `return` expression is not valid
	/// in the given context (i.e., it's not in an `ensures` clause).
	ensuresReturnExpression: null | ValueInfo,

	sourceContext: SourceContext,
}

interface VariableBinding {
	localName: string,
	bindingLocation: ir.SourceLocation,
	t: ir.Type,
	currentValue: ir.VariableID,
}

interface VariableStackInfo {
	bindingLocation: ir.SourceLocation,
	t: ir.Type,
	currentValue: ir.VariableID,
	block: number,
}

interface VariableStackBlock {
	stackStart: number,
	assignments: Record<string, { originalValue: ir.VariableID, latestValue: ir.VariableID }>,
	isProofBlock: boolean,
}

class VariableStack {
	private variables: Record<string, VariableStackInfo> = {};
	private variableStack: string[] = [];
	private blocks: VariableStackBlock[] = [];
	private program: ir.Program;

	private nextUnique = 1;

	constructor(program: ir.Program) {
		this.program = program;
	}

	getForeignSignature(foreignID: string): ir.FunctionSignature {
		const signature = this.program.foreign[foreignID];
		if (signature === undefined) {
			throw new Error("VariableStack.getForeignSignature: no such operation `" + foreignID + "`");
		}
		return signature;
	}

	uniqueID(hint: string): ir.VariableID {
		if (hint.indexOf("'") >= 0) {
			throw new Error("hint must not contain `'`");
		}
		const id = hint + "'" + this.nextUnique;
		this.nextUnique += 1;
		return id as ir.VariableID;
	}

	defineLocal(
		local: string,
		t: ir.Type,
		location: ir.SourceLocation,
		initialValue: ir.VariableID,
	) {
		const existing = this.variables[local];
		if (existing !== undefined) {
			throw new diagnostics.VariableRedefinedErr({
				name: local,
				firstLocation: existing.bindingLocation,
				secondLocation: location,
			});
		}
		this.variables[local] = {
			bindingLocation: location,
			t,
			currentValue: initialValue,
			block: this.blocks.length,
		};
		this.variableStack.push(local);
	}

	/// THROWS SemanticError when a variable of this name is not in scope.
	resolve(local: lexer.IdenToken): VariableBinding {
		const def = this.variables[local.name];
		if (def === undefined) {
			throw new diagnostics.VariableNotDefinedErr({
				name: local.name,
				referencedAt: local.location,
			});
		}
		return {
			localName: local.name,
			bindingLocation: def.bindingLocation,
			t: def.t,
			currentValue: def.currentValue,
		};
	}

	/// `openBlock(proofBlock)` opens a new scope. Variables added after this
	/// call will be deleted when a corresponding `closeBlock()` call is made.
	/// If `proofBlock` is `true`, `isInProofBlock()` will return `true` until
	/// the corresponding `closeBlock()` call is made.
	openBlock(proofBlock: boolean) {
		this.blocks.push({
			stackStart: this.variableStack.length,
			assignments: {},
			isProofBlock: proofBlock || this.isInProofBlock(),
		});
	}

	/// `isInProofBlock()` returns `true` when a currently open block passed
	/// `true` as the parameter to `openBlock`.
	isInProofBlock(): boolean {
		const top = this.blocks[this.blocks.length - 1];
		return top !== undefined && top.isProofBlock;
	}

	updateLocal(local: string, newValue: ir.VariableID) {
		const variable = this.variables[local];
		if (variable.block < this.blocks.length) {
			const currentBlock = this.blocks[this.blocks.length - 1];
			if (currentBlock.assignments[local] === undefined) {
				currentBlock.assignments[local] = {
					originalValue: variable.currentValue,
					latestValue: newValue,
				};
			} else {
				currentBlock.assignments[local].latestValue = newValue;
			}
		}
		variable.currentValue = newValue;
	}

	/// RETURNS the assignments made to Shiru local variables that live longer
	/// than this block.
	closeBlock(): Record<string, ir.VariableID> {
		const block = this.blocks.pop();
		if (block === undefined) throw new Error("block is not open");
		const removed = this.variableStack.splice(block.stackStart);
		for (const r of removed) {
			delete this.variables[r];
		}

		const assignments: Record<string, ir.VariableID> = {};
		for (const k in block.assignments) {
			// Revert the variable to its assignment before the block, but return
			// the current assignment (for branching).
			const status = block.assignments[k];
			this.variables[k].currentValue = status.originalValue;
			assignments[k] = status.latestValue;
		}
		return assignments;
	}
}

interface ValueInfo {
	values: ir.VariableDefinition[],
	location: ir.SourceLocation,
}

function compileCall(
	ops: ir.Op[],
	stack: VariableStack,
	args: ValueInfo[],
	fn: FnBinding | InterfaceFnBinding,

	/// An assignment for all the signatureTypeVariables and
	/// entityTypeVariables/interfaceTypeVariables.
	typeArgumentMapping: Map<ir.TypeVariableID, ir.Type>,

	location: ir.SourceLocation,
	constraint: ir.ConstraintParameter | null,
): ValueInfo {
	const argValues = [];
	for (const tuple of args) {
		for (let i = 0; i < tuple.values.length; i++) {
			argValues.push({ tuple, i });
		}
	}

	if (argValues.length !== fn.parameters.length) {
		throw new diagnostics.ValueCountMismatchErr({
			actualCount: argValues.length,
			actualLocation: ir.locationsSpan(args),
			expectedCount: fn.parameters.length,
			expectedLocation: fn.parametersLocation,
		});
	}

	const argumentSources = [];
	for (let i = 0; i < argValues.length; i++) {
		const value = argValues[i];
		const valueType = value.tuple.values[value.i].type;
		const templateType = fn.parameters[i].t;

		const expectedType = ir.typeSubstitute(templateType, typeArgumentMapping);

		if (!ir.equalTypes(expectedType, valueType)) {
			throw new diagnostics.TypeMismatchErr({
				givenType: displayType(valueType),
				givenLocation: value.tuple.location,
				givenIndex: {
					index0: value.i,
					count: value.tuple.values.length,
				},
				expectedType: displayType(expectedType),
				expectedLocation: fn.parameters[i].nameLocation,
			});
		}
		argumentSources.push(value.tuple.values[value.i].variable);
	}

	const destinations: ir.VariableDefinition[] = [];
	for (let i = 0; i < fn.returns.length; i++) {
		const templateType = fn.returns[i].t;
		const returnType = ir.typeSubstitute(templateType, typeArgumentMapping);

		const destination = stack.uniqueID("fncall" + i);
		destinations.push({
			variable: destination,
			type: returnType,
			location,
		});
	}


	if (fn.tag === "fn-binding") {
		const typeArgumentList = [];
		for (const typeParameter of fn.entityTypeVariables) {
			typeArgumentList.push(typeArgumentMapping.get(typeParameter)!);
		}
		for (const typeParameter of fn.signatureTypeVariables) {
			typeArgumentList.push(typeArgumentMapping.get(typeParameter)!);
		}

		ops.push({
			tag: "op-static-call",
			function: fn.id,

			arguments: argumentSources,
			type_arguments: typeArgumentList,
			destinations: destinations,

			diagnostic_callsite: location,
		});

		if (constraint !== null) {
			throw new Error("compileCall: expected `null` constraint for fn-binding")
		}
	} else {
		if (constraint === null) {
			throw new Error("compileCall: expected non-null constraint for vtable-binding");
		}

		const typeArgumentList = [];
		for (const typeParameter of fn.signatureTypeVariables) {
			typeArgumentList.push(typeArgumentMapping.get(typeParameter)!);
		}

		ops.push({
			tag: "op-dynamic-call",
			constraint,
			signature_id: fn.signature_id,

			arguments: argumentSources,
			signature_type_arguments: typeArgumentList,
			destinations,

			diagnostic_callsite: location,
		});
	}

	return {
		values: destinations,
		location: location,
	};
}

function compileTypeCallExpression(
	e: grammar.ExpressionTypeCall,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	const baseType = compileType(e.t, typeScope, context.sourceContext, "check");
	if (baseType.tag !== "type-compound") {
		throw new diagnostics.CallOnNonCompoundErr({
			baseType: displayType(baseType),
			location: e.t.location,
		});
	}

	const base = context.sourceContext.programContext.getDataEntity(baseType.base);
	const fn = base.fns[e.methodName.name];
	if (fn === undefined) {
		throw new diagnostics.NoSuchFnErr({
			baseType: displayType(baseType),
			methodName: e.methodName.name,
			methodNameLocation: e.methodName.location,
		});
	}

	const args = [];
	for (const arg of e.arguments) {
		args.push(compileExpression(arg, ops, stack, typeScope, context));
	}

	const typeArgumentMapping: Map<ir.TypeVariableID, ir.Type> = new Map();
	if (fn.signatureTypeVariables.length !== 0) {
		throw new Error("TODO: Handle member-scoped type arguments.");
	}
	for (let i = 0; i < baseType.type_arguments.length; i++) {
		typeArgumentMapping.set(fn.entityTypeVariables[i], baseType.type_arguments[i]);
	}
	return compileCall(ops, stack, args, fn, typeArgumentMapping, e.location, null);
}

function compileConstraintCallExpression(
	e: grammar.ExpressionConstraintCall,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	const subject = compileType(e.constraint.subject, typeScope, context.sourceContext, "check");
	const constraint = compileConstraint(e.constraint.constraint, subject, context.sourceContext, typeScope, "check", e.constraint.location);

	checkConstraintSatisfied(constraint, typeScope, context.sourceContext, {
		neededAt: e.constraint.location,
		constraintDeclaredAt: null,
	});

	const int = context.sourceContext.programContext.getInterface(constraint.interface);
	const fn = int.fns[e.methodName.name];
	if (fn === undefined) {
		throw new diagnostics.NoSuchFnErr({
			baseType: displayConstraint(constraint),
			methodName: e.methodName.name,
			methodNameLocation: e.methodName.location,
		});
	}

	const args = [];
	for (const arg of e.arguments) {
		args.push(compileExpression(arg, ops, stack, typeScope, context));
	}

	const typeArgumentMapping = new Map<ir.TypeVariableID, ir.Type>();
	for (let i = 0; i < constraint.subjects.length; i++) {
		typeArgumentMapping.set(fn.interfaceTypeVariables[i], constraint.subjects[i]);
	}
	if (fn.signatureTypeVariables.length !== 0) {
		throw new Error("TODO: Handle member scoped dynamic type arguments");
	}
	return compileCall(ops, stack, args, fn, typeArgumentMapping, e.location, constraint);
}

function compileEnumLiteral(
	baseEntity: EnumEntityDef,
	baseType: ir.TypeCompound,
	initializations: Record<string, ValueInfo & { fieldLocation: ir.SourceLocation }>,
	ops: ir.Op[],
	stack: VariableStack,
	location: ir.SourceLocation,
): ValueInfo {
	const variants: Record<string, ir.VariableID> = {};
	let first = null;
	for (let provided in initializations) {
		const initialization = initializations[provided];
		if (first !== null) {
			throw new diagnostics.MultipleVariantsErr({
				enumType: displayType(baseType),
				firstVariant: first.name,
				firstLocation: first.location,
				secondVariant: provided,
				secondLocation: initialization.fieldLocation,
			});
		}
		first = { name: provided, location: initialization.fieldLocation };

		variants[provided] = initialization.values[0].variable;
	}

	if (first === null) {
		throw new diagnostics.EnumLiteralMissingVariantErr({
			enumType: displayType(baseType),
			location,
		});
	}

	const destination = {
		variable: stack.uniqueID("enum" + baseType.base),
		type: baseType,
		location,
	};

	ops.push({
		tag: "op-new-enum",
		enum: baseType.base as ir.EnumID,
		destination,
		variant: first.name,
		variantValue: variants[first.name],
	});

	return {
		values: [destination],
		location,
	};
}

function compileRecordLiteral(
	baseEntity: RecordEntityDef,
	baseType: ir.TypeCompound,
	initializations: Record<string, ValueInfo & { fieldLocation: ir.SourceLocation }>,
	ops: ir.Op[],
	stack: VariableStack,
	location: ir.SourceLocation,
): ValueInfo {
	const fields: Record<string, ir.VariableID> = {};
	for (let required in baseEntity.fields) {
		if (initializations[required] === undefined) {
			throw new diagnostics.UninitializedFieldErr({
				recordType: displayType(baseType),
				missingFieldName: required,
				definedLocation: baseEntity.fields[required].nameLocation,
				initializerLocation: location,
			});
		}
		fields[required] = initializations[required].values[0].variable;
	}

	const destination = {
		variable: stack.uniqueID("record" + baseType.base),
		type: baseType,
		location,
	};

	ops.push({
		tag: "op-new-record",
		record: baseType.base as ir.RecordID,
		destination: destination,
		fields,
	});
	return {
		values: [destination],
		location,
	};
}

function compileCompoundLiteral(
	e: grammar.ExpressionRecordLiteral,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	const t = compileType(e.t, typeScope, context.sourceContext, "check");
	if (t.tag !== "type-compound") {
		throw new diagnostics.NonCompoundInRecordLiteralErr({
			t: displayType(t),
			location: e.t.location,
		});
	}

	const programContext = context.sourceContext.programContext;
	const baseEntity = programContext.getDataEntity(t.base);

	const instantiation = ir.typeArgumentsMap(baseEntity.typeScope.typeVariableList, t.type_arguments);
	const initializations: Record<string, ValueInfo & { fieldLocation: ir.SourceLocation }> = {};
	for (let initAST of e.initializations) {
		const fieldName = initAST.fieldName.name;
		if (initializations[fieldName] !== undefined) {
			throw new diagnostics.MemberRepeatedInCompoundLiteralErr({
				kind: baseEntity.tag === "enum" ? "variant" : "field",
				fieldName,
				firstLocation: initializations[fieldName].fieldLocation,
				secondLocation: initAST.fieldName.location,
			});
		}
		const fieldDefinition = baseEntity.tag === "record"
			? baseEntity.fields[fieldName]
			: baseEntity.variants[fieldName];
		if (fieldDefinition === undefined) {
			if (baseEntity.tag === "record") {
				throw new diagnostics.NoSuchFieldErr({
					kind: "initialization",
					recordType: displayType(t),
					fieldName,
					location: initAST.fieldName.location,
				});
			} else {
				throw new diagnostics.NoSuchVariantErr({
					kind: "initialization",
					enumType: displayType(t),
					variantName: fieldName,
					location: initAST.fieldName.location,
				});
			}
		}

		const value = compileExpression(initAST.value, ops, stack, typeScope, context);
		if (value.values.length !== 1) {
			throw new diagnostics.MultiExpressionGroupedErr({
				location: value.location,
				valueCount: value.values.length,
				grouping: "field-init",
			});
		}
		const givenType = value.values[0].type;
		const expectedType = ir.typeSubstitute(fieldDefinition.t, instantiation);

		if (!ir.equalTypes(expectedType, givenType)) {
			throw new diagnostics.TypeMismatchErr({
				givenType: displayType(givenType),
				givenLocation: value.location,
				expectedType: displayType(expectedType),
				expectedLocation: fieldDefinition.typeLocation,
			});
		}

		initializations[fieldName] = {
			...value,
			fieldLocation: initAST.fieldName.location,
		};
	}

	if (baseEntity.tag === "record") {
		return compileRecordLiteral(
			baseEntity, t, initializations, ops, stack, e.location);
	} else {
		return compileEnumLiteral(
			baseEntity, t, initializations, ops, stack, e.location);
	}
}

function compileExpressionAtom(
	e: grammar.ExpressionAtom,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext): ValueInfo {
	if (e.tag === "iden") {
		const v = stack.resolve(e);
		const destination = {
			variable: stack.uniqueID("var"),
			type: v.t,
			location: e.location,
		};
		ops.push({
			tag: "op-copy",
			copies: [
				{
					source: v.currentValue,
					destination,
				}
			],
		});
		return {
			values: [{
				type: v.t,
				variable: destination.variable,
				location: e.location,
			}],
			location: e.location,
		};
	} else if (e.tag === "paren") {
		const component = compileExpression(e.expression, ops, stack, typeScope, context);
		if (component.values.length !== 1) {
			throw new diagnostics.MultiExpressionGroupedErr({
				valueCount: component.values.length,
				location: e.location,
				grouping: "parens",
			});
		}
		return component;
	} else if (e.tag === "number-literal") {
		const destination = {
			variable: stack.uniqueID("number"),
			type: ir.T_INT,
			location: e.location,
		};
		ops.push({
			tag: "op-const",
			destination,
			type: "Int",
			int: e.int,
		});
		return { values: [destination], location: e.location };
	} else if (e.tag === "type-call") {
		return compileTypeCallExpression(e, ops, stack, typeScope, context);
	} else if (e.tag === "constraint-call") {
		return compileConstraintCallExpression(e, ops, stack, typeScope, context);
	} else if (e.tag === "keyword") {
		if (e.keyword === "false" || e.keyword === "true") {
			const destination = {
				variable: stack.uniqueID("boolean"),
				type: ir.T_BOOLEAN,
				location: e.location,
			};
			ops.push({
				tag: "op-const",
				destination,
				type: "Boolean",
				boolean: e.keyword === "true",
			});
			return { values: [destination], location: e.location };
		} else if (e.keyword === "return") {
			if (context.ensuresReturnExpression === null) {
				throw new diagnostics.ReturnExpressionUsedOutsideEnsuresErr({
					returnLocation: e.location,
				});
			}

			const destinations = [];
			const copies = [];
			for (const source of context.ensuresReturnExpression.values) {
				const destination = {
					variable: stack.uniqueID("return"),
					type: source.type,
					location: e.location,
				};
				copies.push({
					source: source.variable,
					destination,
				});
				destinations.push(destination);
			}
			ops.push({
				tag: "op-copy",
				copies,

			});
			return {
				values: destinations,
				location: e.location,
			};
		} else {
			const _: never = e.keyword;
			throw new Error("compileExpressionAtom: keyword `" + e["keyword"] + "`");
		}
	} else if (e.tag === "record-literal") {
		return compileCompoundLiteral(e, ops, stack, typeScope, context);
	} else if (e.tag === "string-literal") {
		const destination = {
			variable: stack.uniqueID("string"),
			type: ir.T_BYTES,
			location: e.location,
		};
		ops.push({
			tag: "op-const",
			destination,
			type: "Bytes",
			bytes: e.value,
		});
		return { values: [destination], location: e.location };
	}

	const _: never = e;
	throw new Error("compileExpressionAtom: Unhandled tag `" + e["tag"] + "`");
}

function compileFieldAccess(
	base: ir.VariableDefinition,
	access: grammar.ExpressionAccessField,
	baseLocation: ir.SourceLocation,
	ops: ir.Op[],
	stack: VariableStack,
	context: FunctionContext,
) {
	if (base.type.tag !== "type-compound") {
		throw new diagnostics.FieldAccessOnNonCompoundErr({
			accessedType: displayType(base.type),
			accessedLocation: access.fieldName.location,
		});
	}

	const programContext = context.sourceContext.programContext;
	const baseEntity = programContext.getDataEntity(base.type.base);

	const instantiation = ir.typeArgumentsMap(baseEntity.typeScope.typeVariableList, base.type.type_arguments);

	const fieldDeclaration = baseEntity.tag === "enum"
		? baseEntity.variants[access.fieldName.name]
		: baseEntity.fields[access.fieldName.name];
	if (fieldDeclaration === undefined) {
		if (baseEntity.tag === "enum") {
			throw new diagnostics.NoSuchVariantErr({
				enumType: displayType(base.type),
				variantName: access.fieldName.name,
				location: access.fieldName.location,
				kind: "variant access",
			});
		} else {
			throw new diagnostics.NoSuchFieldErr({
				recordType: displayType(base.type),
				fieldName: access.fieldName.name,
				location: access.fieldName.location,
				kind: "access",
			});
		}
	}

	const fieldType = ir.typeSubstitute(fieldDeclaration.t, instantiation);
	const location = ir.locationSpan(baseLocation, access.fieldName.location);
	const destination = {
		variable: stack.uniqueID("field"),
		type: fieldType,
		location,
	};

	if (baseEntity.tag === "enum") {
		ops.push({
			tag: "op-variant",
			object: base.variable,
			variant: access.fieldName.name,
			destination,
			diagnostic_location: access.fieldName.location,
		});
	} else {
		ops.push({
			tag: "op-field",
			object: base.variable,
			field: access.fieldName.name,
			destination,
		});
	}

	return {
		values: [destination],
		location,
	};
}

function compileSuffixIs(
	base: ir.VariableDefinition,
	suffixIs: grammar.ExpressionSuffixIs,
	baseLocation: ir.SourceLocation,
	ops: ir.Op[],
	stack: VariableStack,
	context: FunctionContext,
): ValueInfo {
	if (base.type.tag !== "type-compound") {
		throw new diagnostics.VariantTestOnNonEnumErr({
			testedType: displayType(base.type),
			testLocation: suffixIs.location,
		});
	}

	const programContext = context.sourceContext.programContext;
	const baseEntity = programContext.getDataEntity(base.type.base);
	if (baseEntity.tag !== "enum") {
		throw new diagnostics.VariantTestOnNonEnumErr({
			testedType: displayType(base.type),
			testLocation: suffixIs.location,
		});
	}

	const variantDefinition = baseEntity.variants[suffixIs.variant.name];
	if (variantDefinition === undefined) {
		throw new diagnostics.NoSuchVariantErr({
			kind: "is test",
			enumType: displayType(base.type),
			variantName: suffixIs.variant.name,
			location: suffixIs.variant.location,
		});
	}

	const location = ir.locationSpan(baseLocation, suffixIs.location);
	const destination = {
		variable: stack.uniqueID("is_" + suffixIs.variant.name),
		type: ir.T_BOOLEAN,
		location,
	};
	ops.push({
		tag: "op-is-variant",
		base: base.variable,
		variant: suffixIs.variant.name,
		destination,
	});

	return { values: [destination], location };
}

function compileExpressionAccess(
	value: ValueInfo,
	access: grammar.ExpressionAccess,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	if (value.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: value.location,
			valueCount: value.values.length,
			grouping: access.tag,
		});
	}
	const base = value.values[0];

	if (access.tag === "field") {
		return compileFieldAccess(base, access, value.location, ops, stack, context);
	} else if (access.tag === "method") {
		if (base.type.tag !== "type-compound") {
			// TODO: Support method calls on type parameters.
			throw new diagnostics.MethodAccessOnNonCompoundErr({
				accessedType: displayType(base.type),
				accessedLocation: access.methodName.location,
			});
		}

		const programContext = context.sourceContext.programContext;
		const baseEntity = programContext.getDataEntity(base.type.base);
		const fn = baseEntity.fns[access.methodName.name];
		if (fn === undefined) {
			throw new diagnostics.NoSuchFnErr({
				baseType: displayType(base.type),
				methodName: access.methodName.name,
				methodNameLocation: access.methodName.location,
			});
		}

		const location = ir.locationSpan(value.location, access.location);

		const args = [value];
		for (const arg of access.args) {
			args.push(compileExpression(arg, ops, stack, typeScope, context));
		}

		const typeArgumentMapping: Map<ir.TypeVariableID, ir.Type> = new Map();
		for (let i = 0; i < fn.entityTypeVariables.length; i++) {
			typeArgumentMapping.set(fn.entityTypeVariables[i], base.type.type_arguments[i]);
		}
		if (fn.signatureTypeVariables.length !== 0) {
			throw new Error("TODO: Handle member-scoped type arguments.");
		}

		return compileCall(ops, stack, args, fn, typeArgumentMapping, location, null);
	} else {
		const _: never = access;
		throw new Error("unhandled access tag `" + access["tag"] + "` in compileOperand");
	}
}

type ResolvedOperator = ResolvedOperatorForeign | ResolvedOperatorProofEquality;

interface ResolvedOperatorForeign {
	tag: "foreign-op",
	foreignID: ir.FunctionID,
	wrap: null | "negate",
}

interface ResolvedOperatorProofEquality {
	tag: "proof-equal-op",
	wrap: null | "negate",
}

function expectOneBooleanForContract(
	values: ValueInfo,
	typeScope: TypeScope,
	context: FunctionContext,
	contract: "assert" | "requires" | "ensures"
): ir.VariableDefinition {
	if (values.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: values.location,
			valueCount: values.values.length,
			grouping: "op",
			op: contract,
		});
	}

	const value = values.values[0];
	if (!ir.equalTypes(ir.T_BOOLEAN, value.type)) {
		throw new diagnostics.BooleanTypeExpectedErr({
			givenType: displayType(value.type),
			location: values.location,
			reason: "contract",
			contract: contract,
		});
	}
	return value;
}

function expectOneBooleanForLogical(
	values: ValueInfo,
	op: { opStr: string, location: ir.SourceLocation },
): ir.VariableDefinition {
	if (values.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: values.location,
			valueCount: values.values.length,
			grouping: "op",
			op: op.opStr,
		});
	}

	const value = values.values[0];
	if (!ir.equalTypes(ir.T_BOOLEAN, value.type)) {
		throw new diagnostics.BooleanTypeExpectedErr({
			givenType: displayType(value.type),
			location: values.location,
			reason: "logical-op",
			op: op.opStr,
			opLocation: op.location,
		});
	}
	return value;
}

/// Throws `MultiExpressionGroupedErr` if `lhs` does not have exactly 1 value.
function resolveArithmeticOperator(
	value: ir.VariableDefinition,
	operator: lexer.OperatorToken,
): ResolvedOperator {
	const opStr = operator.operator;
	if (ir.equalTypes(ir.T_INT, value.type)) {
		if (opStr === "+") {
			return { tag: "foreign-op", foreignID: "Int+" as ir.FunctionID, wrap: null };
		} else if (opStr === "-") {
			return { tag: "foreign-op", foreignID: "Int-" as ir.FunctionID, wrap: null };
		} else if (opStr === "==") {
			return { tag: "foreign-op", foreignID: "Int==" as ir.FunctionID, wrap: null };
		} else if (opStr === "!=") {
			return { tag: "foreign-op", foreignID: "Int==" as ir.FunctionID, wrap: "negate" };
		} else if (opStr === "<") {
			return { tag: "foreign-op", foreignID: "Int<" as ir.FunctionID, wrap: null };
		} else if (opStr === "<=") {
			return { tag: "foreign-op", foreignID: "Int<=" as ir.FunctionID, wrap: null };
		}
	}

	if (ir.equalTypes(ir.T_BOOLEAN, value.type)) {
		if (opStr === "==") {
			return { tag: "foreign-op", foreignID: "Boolean==" as ir.FunctionID, wrap: null };
		} else if (opStr === "!=") {
			return { tag: "foreign-op", foreignID: "Boolean==" as ir.FunctionID, wrap: null };
		}
	}

	if (ir.equalTypes(ir.T_BYTES, value.type)) {
		if (opStr === "++") {
			return { tag: "foreign-op", foreignID: "Bytes++" as ir.FunctionID, wrap: null };
		}
	}

	if (opStr === "==") {
		return { tag: "proof-equal-op", wrap: null };
	} else if (opStr === "!=") {
		return { tag: "proof-equal-op", wrap: "negate" };
	}

	throw new diagnostics.TypeDoesNotProvideOperatorErr({
		lhsType: displayType(value.type),
		operator: opStr,
		operatorLocation: operator.location,
	});
}

const infixOperatorPrecedence = {
	precedences: {
		"implies": 10,
		"and": 10,
		"or": 10,
		"bounds": 20,
		"==": 20,
		"<": 20,
		">": 20,
		"<=": 20,
		">=": 20,
		"!=": 20,
		"_default": 30,
	} as Record<string, number>,
	associativities: {
		"implies": "right",
		"and": "left",
		"or": "left",
		"<": "left",
		"<=": { group: "<" },
		">": "left",
		">=": { group: ">" },
	} as Record<string, "left" | "right" | { group: string }>,
};

type OperatorPacketElement = { tag: "prefix", prefix: grammar.ExpressionPrefixOperator }
	| { tag: "suffix", suffix: grammar.ExpressionSuffixOperator }
	| { tag: "infix", infix: grammar.ExpressionInfixOperator };

function getOperatorPacketPrecedence(
	packet: OperatorPacketElement[],
	side: "left" | "right",
): {
	precedence: number,
	grouping: string | null,
	associates: "left" | "right" | null,
	element: OperatorPacketElement,
} {
	if (packet.length === 0) {
		return {
			precedence: 0,
			grouping: null,
			associates: null,
			element: null as any,
		};
	}
	const operator = side === "left" ? packet[packet.length - 1] : packet[0];
	if (operator.tag === "prefix") {
		const prefix = operator.prefix;
		if (prefix.tag === "keyword") {
			if (prefix.keyword === "not") {
				return {
					precedence: infixOperatorPrecedence.precedences.or,
					grouping: null,
					associates: null,
					element: operator,
				};
			}
			const _: never = prefix.keyword;
			throw new Error("getOperatorPacketPrecedence: unexpected prefix keyword `" + prefix.keyword + "`");
		}
		const _: never = prefix.tag;
		throw new Error("getOperatorPacketPrecedence: unexpected prefix tag `" + prefix.tag + "`");
	} else if (operator.tag === "infix") {
		const infix = operator.infix;
		const key = infix.tag === "keyword" ? infix.keyword : infix.operator;
		const precedence = infixOperatorPrecedence.precedences[key] || infixOperatorPrecedence.precedences._default;
		let associates: "left" | "right" | { group: string } | undefined = infixOperatorPrecedence.associativities[key];
		let grouping = associates === undefined
			? null
			: typeof associates === "string"
				? key
				: associates.group;
		while (typeof associates !== "string" && associates !== undefined) {
			const next: "left" | "right" | { group: string } = infixOperatorPrecedence.associativities[associates.group];

			if (typeof next !== "string" && associates.group === next.group) {
				throw new Error("getOperatorPacketPrecedence: infinite loop in associates group `" + next.group + "`");
			}

			associates = next;
		}

		return {
			precedence,
			grouping,
			associates: associates || null,
			element: operator,
		};
	} else if (operator.tag === "suffix") {
		const suffix = operator.suffix;
		if (suffix.tag === "is") {
			return {
				precedence: infixOperatorPrecedence.precedences["=="],
				grouping: null,
				associates: null,
				element: operator,
			};
		}

		const _: never = suffix["tag"];
		throw new Error("getOperatorPacketPrecedence: unexpected suffix tag `" + suffix["tag"] + "`");
	}
	const _: never = operator;
	throw new Error("getOperatorPacketPrecedence: unexpected tag `" + operator["tag"] + "`");
}

type Operand = {
	// left and right index into the operatorPackets array.
	left: number,
	right: number,

	location: ir.SourceLocation,

	operand: {
		tag: "leaf",
		leaf: {
			atom: grammar.ExpressionAtom,
			accesses: grammar.ExpressionAccess[],
		},
	} | {
		tag: "operation",
		operator: { tag: "infix", infix: grammar.ExpressionInfixOperator }
		| { tag: "prefix"; prefix: grammar.ExpressionPrefixOperator; }
		| { tag: "suffix"; suffix: grammar.ExpressionSuffixOperator; },
		operands: Operand[],
	},
};

function compileOperandLeaf(
	operand: {
		tag: "leaf",
		leaf: {
			atom: grammar.ExpressionAtom,
			accesses: grammar.ExpressionAccess[],
		},
	},
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	let value = compileExpressionAtom(operand.leaf.atom, ops, stack, typeScope, context);
	for (const access of operand.leaf.accesses) {
		value = compileExpressionAccess(value, access, ops, stack, typeScope, context);
	}
	return value;
}

function compileUnaryOperator(
	operation: OperatorPacketElement & { tag: "suffix" | "prefix" },
	ops: ir.Op[],
	operand: { subops: ir.Op[], subresult: ValueInfo },
	stack: VariableStack,
	location: ir.SourceLocation,
	context: FunctionContext,
): ValueInfo {
	if (operation.tag === "prefix") {
		const prefix = operation.prefix;
		if (prefix.keyword === "not") {
			ops.push(...operand.subops);
			const value = expectOneBooleanForLogical(operand.subresult, { opStr: "not", location: prefix.location });
			return {
				values: [compileNegation(ops, stack, location, value.variable)],
				location,
			};
		}

		throw new Error("compileUnaryOperator: unknown prefix `" + prefix.keyword + "`");
	} else {
		const suffix = operation.suffix;
		if (suffix.tag === "is") {
			if (operand.subresult.values.length !== 1) {
				throw new diagnostics.MultiExpressionGroupedErr({
					location: operand.subresult.location,
					valueCount: operand.subresult.values.length,
					grouping: "is",
				});
			}

			ops.push(...operand.subops);
			return compileSuffixIs(
				operand.subresult.values[0], suffix, operand.subresult.location, ops, stack, context);
		}
		const _: never = suffix.tag;
		throw new Error("compileUnaryOperator: unknown suffix tag `" + suffix.tag + "`");
	}
}

function compileNegation(
	ops: ir.Op[],
	stack: VariableStack,
	location: ir.SourceLocation,
	value: ir.VariableID,
): ir.VariableDefinition {
	const negation: ir.VariableDefinition = {
		variable: stack.uniqueID("negation"),
		type: ir.T_BOOLEAN,
		location,
	};
	const booleanConstant = {
		variable: stack.uniqueID("boolean"),
		type: ir.T_BOOLEAN,
		location: ir.NONE,
	};
	ops.push({
		tag: "op-branch",
		condition: value,
		trueBranch: {
			ops: [
				{
					tag: "op-const",
					destination: booleanConstant,
					type: "Boolean",
					boolean: false,
				},
			],
		},
		falseBranch: {
			ops: [
				{
					tag: "op-const",
					destination: booleanConstant,
					type: "Boolean",
					boolean: true,
				},
			],
		},
		destinations: [
			{
				destination: negation,
				trueSource: { tag: "variable", variable: booleanConstant.variable },
				falseSource: { tag: "variable", variable: booleanConstant.variable },
			},
		],
	});
	return negation;
}

function compileAndShortCircuit(
	ops: ir.Op[],
	stack: VariableStack,
	left: ir.VariableID,
	leftCompute: ir.Op[],
	right: ir.VariableID,
	rightCompute: ir.Op[],
	location: ir.SourceLocation,
): ValueInfo {
	ops.push(...leftCompute);
	const conjunction: ir.VariableDefinition = {
		variable: stack.uniqueID("conjunction"),
		type: ir.T_BOOLEAN,
		location,
	};
	ops.push({
		tag: "op-branch",
		condition: left,
		trueBranch: { ops: rightCompute },
		falseBranch: { ops: [] },
		destinations: [
			{
				destination: conjunction,
				trueSource: { tag: "variable", variable: right },
				falseSource: { tag: "variable", variable: left },
			}
		],
	});
	return {
		values: [conjunction],
		location,
	};
}

function compileImpliesShortCircuit(
	ops: ir.Op[],
	stack: VariableStack,
	left: ir.VariableID,
	leftCompute: ir.Op[],
	right: ir.VariableID,
	rightCompute: ir.Op[],
	location: ir.SourceLocation,
): ValueInfo {
	ops.push(...leftCompute);
	const implication: ir.VariableDefinition = {
		variable: stack.uniqueID("implication"),
		type: ir.T_BOOLEAN,
		location,
	};
	const vacuous: ir.VariableDefinition = {
		variable: stack.uniqueID("vacuous"),
		type: ir.T_BOOLEAN,
		location: ir.NONE,
	};
	ops.push({
		tag: "op-branch",
		condition: left,
		trueBranch: { ops: rightCompute },
		falseBranch: {
			ops: [
				{
					tag: "op-const",
					destination: vacuous,
					type: "Boolean",
					boolean: true,
				},
			]
		},
		destinations: [
			{
				destination: implication,
				trueSource: { tag: "variable", variable: right },
				falseSource: { tag: "variable", variable: vacuous.variable },
			}
		],
	});
	return {
		values: [implication],
		location,
	};
}

function compileOrShortCircuit(
	ops: ir.Op[],
	stack: VariableStack,
	left: ir.VariableID,
	leftCompute: ir.Op[],
	right: ir.VariableID,
	rightCompute: ir.Op[],
	location: ir.SourceLocation,
): ValueInfo {
	ops.push(...leftCompute);
	const disjunction: ir.VariableDefinition = {
		variable: stack.uniqueID("disjunction"),
		type: ir.T_BOOLEAN,
		location,
	};
	ops.push({
		tag: "op-branch",
		condition: left,
		trueBranch: { ops: [] },
		falseBranch: { ops: rightCompute },
		destinations: [
			{
				destination: disjunction,
				trueSource: { tag: "variable", variable: left },
				falseSource: { tag: "variable", variable: right },
			}
		],
	});
	return {
		values: [disjunction],
		location,
	};
}

function compileBinaryOperator(
	operation: grammar.ExpressionInfixOperator,
	ops: ir.Op[],
	stack: VariableStack,
	left: { subops: ir.Op[], subresult: ValueInfo },
	right: { subops: ir.Op[], subresult: ValueInfo },
	location: ir.SourceLocation,
	context: FunctionContext,
): ValueInfo {
	const opStr = operation.tag === "keyword" ? operation.keyword : operation.operator;

	// Check that each operand is a single value.
	if (left.subresult.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: left.subresult.location,
			valueCount: left.subresult.values.length,
			grouping: "op",
			op: opStr,
		});
	} else if (right.subresult.values.length !== 1) {
		throw new diagnostics.MultiExpressionGroupedErr({
			location: right.subresult.location,
			valueCount: right.subresult.values.length,
			grouping: "op",
			op: opStr,
		});
	}

	const leftResult = left.subresult.values[0];
	const rightResult = right.subresult.values[0];
	if (operation.tag === "operator") {
		let destination: ir.VariableDefinition;
		ops.push(...left.subops);
		ops.push(...right.subops);
		const resolvedOperator = resolveArithmeticOperator(leftResult, operation);

		let expectedLhsType: ir.Type;
		let expectedRhsType: ir.Type;
		if (resolvedOperator.tag === "foreign-op") {
			const signature = stack.getForeignSignature(resolvedOperator.foreignID);
			if (signature.parameters.length !== 2) {
				throw new Error(
					"Foreign signature `" + resolvedOperator + "` cannot be used as"
					+ "an operator since it doesn't take exactly 2 parameters");
			} else if (signature.return_types.length !== 1) {
				throw new Error(
					"Foreign signature `" + resolvedOperator
					+ "` cannot be used as an operator since it produces "
					+ signature.return_types.length + " values");
			}

			expectedLhsType = signature.parameters[0].type;
			expectedRhsType = signature.parameters[1].type;

			destination = {
				variable: stack.uniqueID("operation-foreign"),
				type: signature.return_types[0],
				location,
			};
			ops.push({
				tag: "op-foreign",
				operation: resolvedOperator.foreignID,
				arguments: [leftResult.variable, rightResult.variable],
				destinations: [destination],
			});
		} else if (resolvedOperator.tag === "proof-equal-op") {
			expectedLhsType = leftResult.type;
			expectedRhsType = expectedLhsType;

			destination = {
				variable: stack.uniqueID("proofeq"),
				type: ir.T_BOOLEAN,
				location,
			};
			ops.push({
				tag: "op-proof-eq",
				left: leftResult.variable,
				right: rightResult.variable,
				destination,
			});

			if (!stack.isInProofBlock()) {
				throw new diagnostics.ProofMemberUsedOutsideProofContextErr({
					operation: operation.operator,
					location: operation.location,
				});
			}
		} else {
			const _: never = resolvedOperator;
			throw new Error("compileArithmeticExpressionTree: unhandled operator type");
		}

		if (!ir.equalTypes(expectedRhsType, rightResult.type)) {
			throw new diagnostics.OperatorTypeMismatchErr({
				lhsType: displayType(leftResult.type),
				operator: opStr,
				givenRhsType: displayType(rightResult.type),
				expectedRhsType: displayType(expectedRhsType),
				rhsLocation: right.subresult.location,
			});
		}

		if (resolvedOperator.wrap === "negate") {
			// Negate the result.
			destination = compileNegation(ops, stack, location, destination.variable);
		}

		return {
			values: [destination],
			location,
		};
	} else {
		if (operation.keyword === "and") {
			const leftValue = expectOneBooleanForLogical(left.subresult, { opStr: "and", location: operation.location });
			const rightValue = expectOneBooleanForLogical(right.subresult, { opStr: "and", location: operation.location });
			return compileAndShortCircuit(ops, stack, leftValue.variable, left.subops, rightValue.variable, right.subops, location);
		} else if (operation.keyword === "implies") {
			const leftValue = expectOneBooleanForLogical(left.subresult, { opStr: "implies", location: operation.location });
			const rightValue = expectOneBooleanForLogical(right.subresult, { opStr: "implies", location: operation.location });
			return compileImpliesShortCircuit(ops, stack, leftValue.variable, left.subops, rightValue.variable, right.subops, location);
		} else if (operation.keyword === "or") {
			const leftValue = expectOneBooleanForLogical(left.subresult, { opStr: "or", location: operation.location });
			const rightValue = expectOneBooleanForLogical(right.subresult, { opStr: "or", location: operation.location });
			return compileOrShortCircuit(ops, stack, leftValue.variable, left.subops, rightValue.variable, right.subops, location);
		} else if (operation.keyword === "bounds") {
			ops.push(...left.subops);
			ops.push(...right.subops);

			const destination: ir.VariableDefinition = {
				variable: stack.uniqueID("proofbounds"),
				type: ir.T_BOOLEAN,
				location,
			};

			ops.push({
				tag: "op-proof-bounds",
				smaller: rightResult.variable,
				larger: leftResult.variable,
				destination,
			});

			if (!stack.isInProofBlock()) {
				throw new diagnostics.ProofMemberUsedOutsideProofContextErr({
					operation: "bounds",
					location: operation.location,
				});
			}

			return {
				values: [destination],
				location,
			};
		}

		const _: never = operation.keyword;
		throw new Error("compileBinaryOperator: unknown keyword operator `" + operation.keyword + "`");
	}
}

function compileOperandJoin(
	operand: {
		tag: "operation",
		operator: OperatorPacketElement,
		operands: Operand[],
	},
	location: ir.SourceLocation,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	const subexpressions = [];
	for (const operation of operand.operands) {
		const subops: ir.Op[] = [];
		const subresult = compileOperandTree(operation, subops, stack, typeScope, context);
		subexpressions.push({
			subops,
			subresult,
		});
	}

	if (operand.operator.tag === "infix") {
		return compileBinaryOperator(
			operand.operator.infix, ops, stack,
			subexpressions[0], subexpressions[1], location, context);
	} else {
		return compileUnaryOperator(operand.operator, ops, subexpressions[0], stack, location, context);
	}
}

function compileOperandTree(
	operand: Operand,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
): ValueInfo {
	if (operand.operand.tag === "leaf") {
		return compileOperandLeaf(operand.operand, ops, stack, typeScope, context);
	} else {
		return compileOperandJoin(operand.operand, operand.location, ops, stack, typeScope, context);
	}
}

function operatorToString(
	operator: { tag: "infix", infix: grammar.ExpressionInfixOperator }
		| { tag: "prefix"; prefix: grammar.ExpressionPrefixOperator; }
		| { tag: "suffix"; suffix: grammar.ExpressionSuffixOperator; },
): { str: string, location: ir.SourceLocation } {
	if (operator.tag === "infix") {
		return {
			str: operator.infix.tag === "keyword" ? operator.infix.keyword : operator.infix.operator,
			location: operator.infix.location,
		};
	} else if (operator.tag === "prefix") {
		return {
			str: operator.prefix.keyword,
			location: operator.prefix.location,
		};
	} {
		return {
			str: operator.suffix.operator.keyword,
			location: operator.suffix.location,
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
	const leafs = [e.left];
	const operands: Operand[] = [{
		left: 0,
		right: 1,
		operand: {
			tag: "leaf",
			leaf: {
				atom: e.left.atom,
				accesses: e.left.accesses,
			},
		},
		location: ir.locationsSpan([e.left.atom, ...e.left.accesses]),
	}];
	for (let i = 0; i < e.operations.length; i++) {
		const obj = e.operations[i];
		leafs.push(obj.right);
		operands.push({
			left: i + 1,
			right: i + 2,
			operand: {
				tag: "leaf",
				leaf: {
					atom: obj.right.atom,
					accesses: obj.right.accesses,
				},
			},
			location: ir.locationsSpan([obj.right.atom, ...obj.right.accesses]),
		});
	}

	// Group adjacent operations into (suffixes, infix, prefixes) "packets".
	const operatorPackets: OperatorPacketElement[][] = [];
	const initialPacket: OperatorPacketElement[] = [];
	for (const prefix of e.left.prefixes) {
		initialPacket.push({ tag: "prefix", prefix });
	}
	operatorPackets.push(initialPacket);
	for (let i = 1; i < leafs.length; i++) {
		const left = leafs[i - 1];
		const infix = e.operations[i - 1].operator;
		const right = leafs[i];
		const packet: OperatorPacketElement[] = [];
		for (const suffix of left.suffixes) {
			packet.push({ tag: "suffix", suffix });
		}
		packet.push({ tag: "infix", infix });
		for (const prefix of right.prefixes) {
			packet.push({ tag: "prefix", prefix });
		}
		operatorPackets.push(packet);
	}
	const finalPacket: OperatorPacketElement[] = [];
	for (const suffix of leafs[leafs.length - 1].suffixes) {
		finalPacket.push({ tag: "suffix", suffix });
	}
	operatorPackets.push(finalPacket);

	while (operatorPackets.flat().length !== 0) {
		// Find operators which are higher precedence than their neighbors.
		const pointing = new DefaultMap<OperatorPacketElement, Operand[]>(() => []);
		const unclear = [];
		for (const operand of operands) {
			const leftPacket = operatorPackets[operand.left];
			const rightPacket = operatorPackets[operand.right];

			const leftOperator = getOperatorPacketPrecedence(leftPacket, "left");
			const rightOperator = getOperatorPacketPrecedence(rightPacket, "right");
			if (leftOperator.precedence === rightOperator.precedence) {
				if (leftOperator.grouping === rightOperator.grouping && leftOperator.grouping !== null) {
					if (leftOperator.associates !== rightOperator.associates) {
						throw new Error("compileExpression: unexpected variation in associates");
					} else if (leftOperator.associates === "left") {
						// Combine with the operator on the left.
						pointing.get(leftOperator.element).push(operand);
					} else {
						// Combine with the operator on the right.
						pointing.get(rightOperator.element).push(operand);
					}
				} else {
					unclear.push(operand);
				}
			} else if (leftOperator.precedence < rightOperator.precedence) {
				// Combine with the operator on the right.
				pointing.get(rightOperator.element).push(operand);
			} else {
				// Combine with the operator on the left.
				pointing.get(leftOperator.element).push(operand);
			}
		}

		const replacements = new Map<Operand, Operand | null>();
		for (const [operator, operands] of pointing) {
			if (operator.tag === "infix") {
				if (operands.length === 2) {
					// Both operands combine to this operator.
					const lhs = operands[0];
					const rhs = operands[1];

					replacements.set(lhs, {
						left: lhs.left,
						right: rhs.right,
						operand: {
							tag: "operation",
							operator,
							operands: [lhs, rhs],
						},
						location: ir.locationSpan(lhs.location, rhs.location),
					});
					replacements.set(rhs, null);

					// Remove the operator from its packet.
					const removed = operatorPackets[rhs.left].pop();
					if (removed !== operator) {
						throw new Error("compileExpression: unexpected operator in packet");
					}
				}
			} else {
				const operand = operands[0];
				replacements.set(operand, {
					left: operand.left,
					right: operand.right,
					operand: {
						tag: "operation",
						operator,
						operands: [operand],
					},
					location: operator.tag === "prefix"
						? ir.locationSpan(operator.prefix.location, operand.location)
						: ir.locationSpan(operand.location, operator.suffix.location),
				});

				// Remove the operator from its packet.
				const removed = operator.tag === "prefix"
					? operatorPackets[operand.left].pop()
					: operatorPackets[operand.right].shift();
				if (removed !== operator) {
					throw new Error("compileExpression: unexpected operator in packet");
				}
			}
		}

		if (replacements.size === 0) {
			for (const operand of unclear) {
				const leftOps = operatorPackets[operand.left];
				const rightOps = operatorPackets[operand.right];
				if (leftOps.length !== 0 && rightOps.length !== 0) {
					const first = leftOps[leftOps.length - 1];
					const second = rightOps[0];
					throw new diagnostics.OperationRequiresParenthesizationErr({
						op1: operatorToString(first),
						op2: operatorToString(second),
						reason: "unordered",
					});
				}
			}
			throw new Error("compileExpression: unexpected lone unconsumed operator packet");
		}

		// Replace operands with their combined operands.
		for (const operand of operands.splice(0)) {
			const replacement = replacements.get(operand);
			if (replacement === undefined) {
				operands.push(operand);
			} else if (replacement !== null) {
				operands.push(replacement);
			}
		}
	}

	return compileOperandTree(operands[0], ops, stack, typeScope, context);
}

/// `displayType` formats the given IR `Type` as a string of (fully qualified)
/// Shiru code.
export function displayType(t: ir.Type): string {
	if (t.tag === "type-compound") {
		const base = t.base;
		const args = t.type_arguments.map(displayType);
		if (args.length === 0) {
			return base;
		} else {
			return base + "[" + args.join(", ") + "]";
		}
	} else if (t.tag === "type-primitive") {
		// TODO: Text vs String vs Bytes?
		return t.primitive;
	} else if (t.tag == "type-variable") {
		return "#" + t.id;
	} else if (t.tag === "type-any") {
		return "Any";
	} else {
		const _: never = t;
		throw new Error("displayType: unhandled tag `" + t["tag"] + "`");
	}
}

/// `displayConstraint` formats the given IR constraint as a string, potentially
/// formatted for the given `SourceContext` (considering import aliases and
/// such).
export function displayConstraint(c: ir.ConstraintParameter): string {
	const base = c.interface;
	if (c.subjects.length === 0) {
		throw new Error("ICE: Invalid constraint `" + base + "`");
	}

	const lhs = displayType(c.subjects[0]);
	const rhs = c.subjects.slice(1).map(t => displayType(t));
	if (rhs.length === 0) {
		return `${lhs} is ${base}`;
	} else {
		return `${lhs} is ${base}[${rhs.join(", ")}]`;
	}
}

export function displayTypeScope(c: TypeScope, opt: { space: boolean }) {
	if (c.typeVariableList.length === 0) {
		return "";
	} else {
		return "[" + c.typeVariableList.map(x => "#" + x).join(", ") + "]" +
			(opt.space ? " " : "");
	}
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

	if (values.length !== statement.variables.length) {
		throw new diagnostics.ValueCountMismatchErr({
			actualCount: values.length,
			actualLocation: ir.locationsSpan(statement.initialization),
			expectedCount: statement.variables.length,
			expectedLocation: ir.locationsSpan(statement.variables),
		});
	}

	for (let i = 0; i < statement.variables.length; i++) {
		const v = statement.variables[i];
		const t = compileType(v.t, typeScope, context.sourceContext, "check");

		const pair = values[i];
		const value = pair.tuple.values[pair.i];

		if (!ir.equalTypes(value.type, t)) {
			throw new diagnostics.TypeMismatchErr({
				givenType: displayType(value.type),
				givenLocation: pair.tuple.location,
				givenIndex: { index0: pair.i, count: pair.tuple.values.length },
				expectedType: displayType(t),
				expectedLocation: v.t.location,
			});
		}

		stack.defineLocal(v.variable.name, t, v.variable.location, value.variable);
	}
}

function compileAssertSt(
	statement: grammar.AssertSt,
	ops: ir.Op[],
	stack: VariableStack,
	typeScope: TypeScope,
	context: FunctionContext,
) {
	const proof: ir.OpProof = {
		tag: "op-proof",
		body: {
			ops: [],
		},
	};
	// Compile the asserted expression in a proof context.
	stack.openBlock(true);
	const conditionTuple = compileExpression(statement.expression, proof.body.ops, stack, typeScope, context);
	stack.closeBlock();

	const asserted = expectOneBooleanForContract(conditionTuple, typeScope, context, "assert");
	proof.body.ops.push({
		tag: "op-branch",
		condition: asserted.variable,
		trueBranch: { ops: [] },
		falseBranch: {
			ops: [
				{
					tag: "op-unreachable",
					diagnostic_kind: "contract",
					diagnostic_location: statement.location,
				},
			],
		},
		destinations: [],
	});
	ops.push(proof);
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
		op.sources.push(source.variable);

		const destination = context.returnsTo[i];
		if (!ir.equalTypes(source.type, destination.t)) {
			throw new diagnostics.TypeMismatchErr({
				givenType: displayType(source.type),
				givenLocation: v.tuple.location,
				givenIndex: { index0: v.i, count: v.tuple.values.length },
				expectedType: displayType(destination.t),
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
	if (!ir.equalTypes(ir.T_BOOLEAN, conditionValue.type)) {
		throw new diagnostics.BooleanTypeExpectedErr({
			givenType: displayType(conditionValue.type),
			location: clause.condition.location,
			reason: "if",
		});
	}

	let trueAssignments: Record<string, ir.VariableID> = {};
	const trueBranch: ir.OpBlock = compileBlock(clause.body, stack, typeScope, context, (assignments) => {
		trueAssignments = assignments;
	});

	stack.openBlock(false);
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
	const falseAssignments = stack.closeBlock();

	const destinations: ir.BranchPhi[] = [];
	for (const key in trueAssignments) {
		throw new Error("TODO");
	}
	for (const key in falseAssignments) {
		throw new Error("TODO");
	}

	ops.push({
		tag: "op-branch",
		condition: conditionValue.variable,
		trueBranch,
		falseBranch,
		destinations,
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
	} else if (statement.tag === "assert") {
		compileAssertSt(statement, ops, stack, typeScope, context);
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
	context: FunctionContext,
	callback?: (assignments: Record<string, ir.VariableID>) => void,
): ir.OpBlock {
	const ops: ir.Op[] = [];
	stack.openBlock(false);

	for (const s of block.statements) {
		compileStatement(s, ops, stack, typeScope, context);
	}


	const assignments = stack.closeBlock();
	if (callback !== undefined) {
		callback(assignments);
	}
	return {
		ops: ops,
	};
}

function compileFunctionSignature(
	program: ir.Program,
	signatureAST: grammar.FnSignature,
	typeScope: TypeScope,
	typeVariablesArePreBound: boolean,
	sourceContext: SourceContext,
): {
	signature: ir.FunctionSignature,
	stack: VariableStack,
	context: FunctionContext,
} {
	const typeVariables = typeVariablesArePreBound
		? []
		: typeScope.typeVariableList.slice(0);
	const signature: ir.FunctionSignature = {
		type_parameters: typeVariables,
		constraint_parameters: typeScope.constraints.map(c => c.constraint),

		parameters: [],
		return_types: [],

		preconditions: [],
		postconditions: [],
	};

	const stack = new VariableStack(program);
	for (const parameterAST of signatureAST.parameters.list) {
		const t = compileType(parameterAST.t, typeScope, sourceContext, "check");
		const parameterVariableID = parameterAST.name.name as ir.VariableID;
		stack.defineLocal(parameterAST.name.name, t, parameterAST.name.location, parameterVariableID);
		signature.parameters.push({
			variable: parameterVariableID,
			type: t,
			location: parameterAST.name.location,
		});
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

		// Compile the precondition in a proof context.
		stack.openBlock(true);
		const result = compileExpression(precondition.expression, block.ops, stack, typeScope, context);
		const asserted = expectOneBooleanForContract(result, typeScope, context, "requires");
		stack.closeBlock();

		signature.preconditions.push({
			block,
			precondition: asserted.variable,
			location: precondition.expression.location,
		});
	}

	if (signatureAST.ensures.length !== 0) {
		// Compile the postcondition in a proof context.
		stack.openBlock(true);

		// The variables in a "return" expression are treated as "parameter"
		// variables for the ensures block.
		const ensuresReturnExpression: ValueInfo = {
			location: ir.locationsSpan(signatureAST.returns),
			values: [],
		};
		for (let i = 0; i < signature.return_types.length; i++) {
			ensuresReturnExpression.values.push({
				variable: stack.uniqueID("return" + i),
				type: signature.return_types[i],
				// TODO:
				location: ir.NONE,
			});
		}

		for (let postcondition of signatureAST.ensures) {
			const block: ir.OpBlock = { ops: [] };

			stack.openBlock(true);
			const result = compileExpression(postcondition.expression, block.ops, stack, typeScope, {
				...context,
				ensuresReturnExpression,
			});
			const asserted = expectOneBooleanForContract(result, typeScope, context, "ensures");
			stack.closeBlock();

			signature.postconditions.push({
				block,
				returnedValues: ensuresReturnExpression.values,
				postcondition: asserted.variable,
				location: postcondition.expression.location,
			});
		}
		stack.closeBlock();
	}

	return { signature, stack, context };
}

function compileMemberFunction(
	program: ir.Program,
	def: FnBinding,
	fName: string,
	sourceContext: SourceContext,
	typeScope: TypeScope) {
	const { signature, stack, context } = compileFunctionSignature(
		program, def.ast.signature, typeScope, false, sourceContext);
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

function checkImplMemberConformance(
	int: InterfaceEntityDef,
	fnName: { name: string, location: ir.SourceLocation },
	constraint: ir.ConstraintParameter,
	signature: ir.FunctionSignature,
	signatureAST: grammar.FnSignature,
): void {
	const corresponding = int.fns[fnName.name];

	// Check that a corresponding member exists.
	if (corresponding === undefined) {
		throw new diagnostics.ImplMemberDoesNotExistOnInterface({
			impl: displayConstraint(constraint),
			member: fnName.name,
			memberLocation: fnName.location,
			interface: constraint.interface,
			interfaceLocation: int.bindingLocation,
		});
	}

	// Determine the expected signatures.
	if (corresponding.signatureTypeVariables.length !== 0) {
		throw new Error("TODO: interface member with type parameters");
	}
	const instantiation = ir.typeArgumentsMap(corresponding.interfaceTypeVariables, constraint.subjects);

	// Check the parameter types.
	if (corresponding.parameters.length !== signature.parameters.length) {
		throw new diagnostics.ImplParameterCountMismatch({
			impl: displayConstraint(constraint),
			member: fnName.name,
			implCount: signature.parameters.length,
			interfaceCount: corresponding.parameters.length,
			implLocation: signatureAST.parameters.location,
			interfaceLocation: corresponding.parametersLocation,
		});
	}
	for (let i = 0; i < corresponding.parameters.length; i++) {
		const expected = ir.typeSubstitute(corresponding.parameters[i].t, instantiation);
		if (!ir.equalTypes(expected, signature.parameters[i].type)) {
			throw new diagnostics.ImplParameterTypeMismatch({
				impl: displayConstraint(constraint),
				parameterIndex0: i,
				memberName: fnName.name,
				implType: displayType(signature.parameters[i].type),
				interfaceType: displayType(expected),
				implLocation: signatureAST.parameters.list[i].t.location,
				interfaceLocation: corresponding.parameters[i].typeLocation,
			});
		}
	}

	// Check the return types.
	if (corresponding.returns.length !== signature.return_types.length) {
		throw new diagnostics.ImplReturnCountMismatch({
			impl: displayConstraint(constraint),
			member: fnName.name,
			implCount: signature.return_types.length,
			interfaceCount: corresponding.returns.length,
			implLocation: ir.locationsSpan(signatureAST.returns),
			interfaceLocation: ir.locationsSpan(corresponding.returns.map(x => ({ location: x.typeLocation }))),
		});
	}
	for (let i = 0; i < corresponding.returns.length; i++) {
		const expected = ir.typeSubstitute(corresponding.returns[i].t, instantiation);
		if (!ir.equalTypes(expected, signature.return_types[i])) {
			throw new diagnostics.ImplReturnTypeMismatch({
				impl: displayConstraint(constraint),
				returnIndex0: i,
				memberName: fnName.name,
				implType: displayType(signature.return_types[i]),
				interfaceType: displayType(expected),
				implLocation: signatureAST.returns[i].location,
				interfaceLocation: corresponding.returns[i].typeLocation,
			});
		}
	}

	if (signature.preconditions.length !== 0) {
		throw new diagnostics.ImplMayNotHavePreconditionErr({
			impl: displayConstraint(constraint),
			memberName: fnName.name,
			preconditionLocation: signature.preconditions[0].location,
		});
	}
}

function compileImpl(
	program: ir.Program,
	impl: ImplEntityDef,
	namingInterface: ir.InterfaceID,
	namingRecord: string,
	namingCount: string,
	programContext: ProgramContext,
) {
	const sourceContext = programContext.sourceContexts[impl.sourceID];
	const int = programContext.getInterface(impl.constraint.interface);

	const closureConstraints = impl.typeScope.constraints.map(x => x.constraint);

	const vtable: ir.VTableFactory = {
		for_any: impl.typeScope.typeVariableList,
		provides: impl.constraint,
		entries: {},
		closures: closureConstraints,
	};

	const canonicalImplName = `impl__${namingInterface}__${namingRecord}__${namingCount}`;

	const memberBindings = new Map<string, ir.SourceLocation>();
	for (const fnAST of impl.ast.fns) {
		const fnName = fnAST.signature.name;
		const existingBinding = memberBindings.get(fnName.name);
		if (existingBinding !== undefined) {
			throw new diagnostics.MemberRedefinedErr({
				memberName: fnName.name,
				firstBinding: existingBinding,
				secondBinding: fnName.location,
			});
		}
		memberBindings.set(fnName.name, fnName.location);
		const { signature, stack, context } = compileFunctionSignature(
			program, fnAST.signature, impl.typeScope, false, sourceContext);

		checkImplMemberConformance(int, fnName, impl.constraint, signature, fnAST.signature);

		const body = compileBlock(fnAST.body, stack, impl.typeScope, context);

		// Make the verifier prove that this function definitely does not exit
		// without returning.
		if (body.ops.length === 0 || !ir.opTerminates(body.ops[body.ops.length - 1])) {
			body.ops.push({
				tag: "op-unreachable",
				diagnostic_kind: "return",
				diagnostic_location: fnAST.body.closing,
			});
		}

		const canonicalMemberName = `${canonicalImplName}__${fnName.name}`;
		program.functions[canonicalMemberName] = { signature, body };
		const constraintParameters: ir.VTableEntryConstraintSource[] = [];
		for (let i = 0; i < impl.typeScope.constraints.length; i++) {
			// TODO: Handle signature constraint parameters.
			constraintParameters.push({ source: "closure", closureIndex: i });
		}
		vtable.entries[fnName.name] = {
			implementation: canonicalMemberName as ir.FunctionID,
			constraint_parameters: constraintParameters,
		};
	}

	for (const expected in int.fns) {
		if (memberBindings.get(expected) === undefined) {
			throw new diagnostics.ImplMissingInterfaceMember({
				impl: displayConstraint(impl.constraint),
				member: expected,
				implLocation: impl.headLocation,
				interface: impl.constraint.interface,
				memberLocation: int.fns[expected].nameLocation,
			});
		}
	}

	program.globalVTableFactories[canonicalImplName] = vtable;
}

function compileInterfaceEntity(
	program: ir.Program,
	entity: InterfaceEntityDef,
	entityName: string,
	programContext: ProgramContext,
) {
	const compiled: ir.IRInterface = {
		type_parameters: entity.typeScope.typeVariableList,
		signatures: {},
	};
	const sourceContext = programContext.sourceContexts[entity.sourceID];
	for (const fnName in entity.fns) {
		const fn = entity.fns[fnName];
		const signature = compileFunctionSignature(
			program, fn.ast.signature, entity.typeScope, true, sourceContext);
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
		type_parameters: entity.typeScope.typeVariableList,
		fields: {},
	};
	for (const fieldName in entity.fields) {
		program.records[entityName].fields[fieldName] = entity.fields[fieldName].t;
	}

	// Compile member functions.
	for (const f in entity.fns) {
		const def = entity.fns[f];
		const fName = def.id;
		compileMemberFunction(program, def, fName,
			programContext.sourceContexts[entity.sourceID], entity.typeScope);
	}

	// Compile impls.
	for (const [interfaceID, impls] of entity.implsByInterface) {
		for (let i = 0; i < impls.length; i++) {
			compileImpl(program, impls[i], interfaceID, entityName, i + "", programContext);
		}
	}
}

function compileEnumEntity(
	program: ir.Program,
	entity: EnumEntityDef,
	entityName: string,
	programContext: ProgramContext,
): void {
	program.enums[entityName] = {
		type_parameters: entity.typeScope.typeVariableList,
		variants: {},
	};

	for (const variantName in entity.variants) {
		program.enums[entityName].variants[variantName] = entity.variants[variantName].t;
	}

	// Compile member functions.
	for (const f in entity.fns) {
		const def = entity.fns[f];
		const fName = def.id;
		compileMemberFunction(program, def, fName,
			programContext.sourceContexts[entity.sourceID], entity.typeScope);
	}

	// Compile impls.
	for (const [interfaceID, impls] of entity.implsByInterface) {
		for (let i = 0; i < impls.length; i++) {
			compileImpl(program, impls[i], interfaceID, entityName, i + "", programContext);
		}
	}
}

/// `compileEntity` compiles the indicated entity into records, functions,
/// interfaces, vtable-factories, etc in the given `program`.
/// THROWS `SemanticError` if a type-error is discovered within the
/// implementation of this entity.
function compileEntity(
	program: ir.Program,
	programContext: ProgramContext,
	entityName: string,
	entity: NamedEntityDef,
): void {
	if (entity.tag === "record") {
		return compileRecordEntity(program, entity, entityName, programContext);
	} else if (entity.tag === "enum") {
		return compileEnumEntity(program, entity, entityName, programContext);
	} else if (entity.tag === "interface") {
		return compileInterfaceEntity(program, entity, entityName, programContext);
	}

	const _: never = entity;
	throw new Error("compileEntity: unhandled tag `" + entity["tag"] + "`");
}

function associateImplWithBase(
	record: RecordEntityDef | EnumEntityDef,
	constraint: ir.ConstraintParameter,
	sourceID: string,
	typeScope: TypeScopeI<null>,
	implAST: grammar.ImplDefinition,
): void {
	const headLocation = ir.locationSpan(implAST.impl.location, implAST.constraint.location);

	// Check if an existing impl conflicts with this one.
	const existingImpls = record.implsByInterface.get(constraint.interface);
	for (const candidate of existingImpls) {
		const unifier = ir.unifyTypes(
			candidate.typeScope.typeVariableList,
			candidate.constraint.subjects,
			typeScope.typeVariableList,
			constraint.subjects,
		);
		if (unifier !== null) {
			const firstImpl =
				displayTypeScope(candidate.typeScope, { space: true }) +
				displayConstraint(candidate.constraint);
			const secondImpl =
				displayTypeScope(typeScope, { space: true }) +
				displayConstraint(constraint);
			throw new diagnostics.OverlappingImplsErr({
				firstImpl,
				firstLocation: candidate.headLocation,
				secondImpl,
				secondLocation: headLocation,
			});
		}
	}

	// TODO: Check for "orphan" instances.

	// Record this impl.
	record.implsByInterface.get(constraint.interface).push({
		tag: "impl",
		ast: implAST,
		headLocation,
		sourceID,
		typeScope,
		constraint,
	});
}

function compileForeignSignatures(program: ir.Program): void {
	for (const operation in builtin.foreignOperations) {
		program.foreign[operation] = builtin.foreignOperations[operation].signature;
	}
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
	for (let [_, entity] of programContext.namedEntities()) {
		resolveAvailableTypes(programContext, entity);
	}

	// Resolve all impl blocks.
	for (const sourceID in programContext.sourceContexts) {
		const sourceContext = programContext.sourceContexts[sourceID];
		for (const implAST of sourceContext.implASTs) {
			const typeScope: TypeScopeI<null> = {
				thisType: null,
				typeVariables: new Map(),
				typeVariableList: [],
				constraints: [],
			};
			collectTypeScope(sourceContext, typeScope, implAST.typeParameters);

			const baseType = compileType(implAST.base, typeScope, sourceContext, "skip");
			if (baseType.tag !== "type-compound") {
				throw new Error("compileSources: ICE");
			}
			const baseEntity = programContext.getDataEntity(baseType.base);
			const constraint = compileConstraint(implAST.constraint, baseType, sourceContext, typeScope, "skip",
				ir.locationSpan(implAST.base.location, implAST.constraint.location));

			// Associate the impl with its base record type.
			associateImplWithBase(baseEntity, constraint, sourceID, typeScope, implAST);
		}
	}

	// Recheck all the unchecked types & constraints found in the above step:
	const uncheckedTypes = programContext.uncheckedTypes!;
	const uncheckedConstraints = programContext.uncheckedConstraints!;
	programContext.uncheckedTypes = [];
	programContext.uncheckedConstraints = [];
	for (const { t, scope, sourceContext } of uncheckedTypes) {
		compileType(t, scope, sourceContext, "check");
	}
	for (const { c, methodSubject, sourceContext, scope, constraintLocation } of uncheckedConstraints) {
		compileConstraint(c, methodSubject, sourceContext, scope, "check",
			constraintLocation);
	}

	// Resolve members of entities. Type arguments must be validated based on
	// collected constraints.
	for (const [canonicalEntityName, entity] of programContext.namedEntities()) {
		resolveMemberSignatures(programContext, canonicalEntityName, entity);
	}

	const program: ir.Program = {
		functions: {},
		interfaces: {},
		records: {},
		enums: {},
		foreign: {},
		globalVTableFactories: {},
	};

	compileForeignSignatures(program);

	for (let [canonicalEntityName, entity] of programContext.namedEntities()) {
		compileEntity(program, programContext, canonicalEntityName, entity);
	}
	return program;
}
