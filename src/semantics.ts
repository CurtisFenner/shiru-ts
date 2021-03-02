import * as grammar from "./grammar";
import * as ir from "./ir";
import * as diagnostics from "./diagnostics";

interface EntityDef {
	ast: grammar.Definition,
	bindingLocation: ir.SourceLocation,
}

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
			programContext.entitiesByCanonical[canonicalName] = {
				ast: definition,
				bindingLocation,
			};
			pack[entityName] = canonicalName;
		}
	}
	return programContext;
}

interface TypeScope {
	thisType: null | ir.TypeVariable,
}

function compileType(t: grammar.Type,
	sourceContext: Readonly<SourceContext>,
	scope: TypeScope,
	programContext: Readonly<ProgramContext>): ir.Type {
	if (t.tag === "keyword") {
		if (t.keyword === "This") {
			if (scope.thisType === null) {
				throw new diagnostics.InvalidThisType({
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
	} else if (t.tag === "class") {
		// Resolve the entity.
		let canonicalName: string;
		if (t.packageQualification !== null) {
			const namespaceQualifier = t.packageQualification.package.name;
			const namespace = sourceContext.namespaces[namespaceQualifier];
			if (!namespace) {
				throw new diagnostics.NoSuchPackageErr({
					packageName: namespaceQualifier,
					reference: t.packageQualification.location,
				});
			}

			const entitiesInNamespace = programContext.canonicalByQualifiedName[namespaceQualifier];
			canonicalName = entitiesInNamespace[t.class.name];
			if (!canonicalName) {
				throw new diagnostics.NoSuchEntityErr({
					entityName: namespace.packageName + "." + t.class.name,
					reference: t.class.location,
				});
			}
		} else {
			const bound = sourceContext.entityAliases[t.class.name];
			if (!bound) {
				throw new diagnostics.NoSuchEntityErr({
					entityName: t.class.name,
					reference: t.class.location,
				});
			}
			canonicalName = bound.canonicalName;
		}

		const entity = programContext.entitiesByCanonical[canonicalName];
		// TODO: Check that entity is a class, etc.

		const typeArguments = t.arguments.map(a => compileType(a, sourceContext, scope, programContext));
		return {
			tag: "type-class",
			class: { class_id: canonicalName },
			type_arguments: typeArguments,
		};
	}
	throw new Error("TODO: " + t);
}

/// `resolveImport` MODIFIES the given `sourceContext` to include the 
/// entity or namespace introduced by the given import.
function resolveImport(imported: grammar.ImportOfObject | grammar.ImportOfPackage,
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
			throw new diagnostics.NamespaceAlreadyDefined({
				namespace: packageName,
				firstBinding: sourcePackage.packageName.location,
				secondBinding: imported.packageName.location,
			});
		} else if (sourceContext.namespaces[packageName] !== undefined) {
			throw new diagnostics.NamespaceAlreadyDefined({
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

function resolveSourceContext(source: grammar.Source, programContext: Readonly<ProgramContext>) {
	const packageName = source.package.packageName.name;
	const pack = programContext.canonicalByQualifiedName[packageName];

	const sourceContext: SourceContext = {
		entityAliases: {},
		namespaces: {},
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

	return sourceContext;
}

// Calculates "signatures" such that references to this entity within other 
// entities can be type-checked. NOTE that this does NOT include compiling pre-
// and post-conditions, which are instead compiled separately and only 
// instantiated by the verifier.
function collectMembers(programContext: ProgramContext, entityName: string) {
	const entity = programContext.entitiesByCanonical[entityName];
	if (entity.ast.tag === "class-definition") {
		// 1) Prepare the stack of type parameters and their constraints.
		throw new Error("TODO: collectMembers for class-definition");
	}
	throw new Error("TODO: collectMembers for unhandled " + entity.ast.tag);
}

/// `compileEntity` compiles the indicated entity into classes, functions,
/// interfaces, vtable-factories, etc in the given `program`.
/// THROWS `SemanticError` if a type-error is discovered within the 
/// implementation of this entity.
function compileEntity(
	program: ir.Program,
	programContext: Readonly<ProgramContext>,
	entityName: string) {
	throw new Error("TODO");
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
		classes: {},
		foreign: {},
		globalVTableFactories: {},
	};

	for (let canonicalEntityName in programContext.entitiesByCanonical) {
		compileEntity(program, programContext, canonicalEntityName);
	}
	return program;
}
