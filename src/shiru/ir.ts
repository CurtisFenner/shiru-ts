/// `SourceLocation` represents a span of a file.
export interface SourceLocation {
	fileID: string,

	// The offset from the first character, measured in UTF-16 code-units
	// (JavaScript "characters").
	offset: number,

	// The length of the span, measured in UTF-16 code-units (JavaScript
	// "characters")
	length: number,
}

export const NONE: SourceLocation = {
	fileID: "unknown",
	offset: 0,
	length: 0,
}

export function locationSpan(from: SourceLocation, to: SourceLocation) {
	return {
		fileID: from.fileID,
		offset: from.offset,
		length: to.offset + to.length - from.offset,
	};
}

export function locationsSpan(set: { location: SourceLocation }[]): SourceLocation {
	const smallest = Math.min(...set.map(x => x.location.offset));
	const largest = Math.max(...set.map(x => x.location.offset + x.location.length));
	return {
		fileID: set[0].location.fileID,
		offset: smallest,
		length: largest - smallest,
	};
}

/// `TypePrimitive` represents one of the "built-in" primitive types:
/// `"Bytes"` is the type of immutable finite sequences of octets.
/// `"Unit"` is the type of a single value: "unit".
/// `"Boolean"` is the type of two values: "true" and "false".
/// `"Int"` is the type of unbounded integers: ..., -3, -2, -1, 0, 1, 2, 3, ...
export interface TypePrimitive {
	tag: "type-primitive",
	primitive: "Bytes" | "Unit" | "Boolean" | "Int",
};

export const T_INT: TypePrimitive = { tag: "type-primitive", primitive: "Int" };
export const T_BOOLEAN: TypePrimitive = { tag: "type-primitive", primitive: "Boolean" };
export const T_BYTES: TypePrimitive = { tag: "type-primitive", primitive: "Bytes" };
export const T_UNIT: TypePrimitive = { tag: "type-primitive", primitive: "Unit" };
export const T_ANY: TypeAny = { tag: "type-any" };

/// `TypeCompound` represents the type which is an instance of a given entity
/// type.
export interface TypeCompound {
	tag: "type-compound",

	/// `base` references a `RecordDefinition` in a `Program`.
	base: RecordID | EnumID,

	type_arguments: Type[],
};

/// `TypeVariable` represents the type which is a parameter of a function or
/// compound type.
export interface TypeVariable {
	tag: "type-variable",
	id: TypeVariableID,
};

export interface TypeAny {
	tag: "type-any",
};

export type Type = TypePrimitive | TypeCompound | TypeVariable | TypeAny;

export type FunctionID = string & { __brand: "function-id" };
export type VariableID = string & { __brand: "variable-id" };
export type RecordID = string & { __brand: "record-id" };
export type EnumID = string & { __brand: "enum-id" };
export type InterfaceID = string & { __brand: "interface-id" };
export type TypeVariableID = string & { __brand: "type-variable-id" };

export interface VariableDefinition {
	variable: VariableID,
	type: Type,
	// The location of this variable, for basic IDE support.
	location: SourceLocation,
}

/// `OpConst` defines a primitive-typed destination variable with a constant.
export type OpConst = {
	tag: "op-const",
	destination: VariableDefinition,
} & (OpConstInt | OpConstBytes | OpConstBoolean);

export interface OpConstInt {
	type: "Int",

	// `int` is encoded as ASCII digits.
	int: string,
}

export interface OpConstBytes {
	type: "Bytes",
	// TODO: Encoding
	bytes: string,
}

export interface OpConstBoolean {
	type: "Boolean",
	boolean: boolean,
}

export interface Copy {
	source: VariableID,
	destination: VariableDefinition,
}

/// `OpCopy` copies a value from one variable to a new variable.
export interface OpCopy {
	tag: "op-copy",

	copies: Copy[],
}

/// `OpBranch` chooses which branch to execute depending on the current value of
/// a `condition` variable.
/// It defines a set of variables, with values selected by the branches.
export interface OpBranch {
	tag: "op-branch",

	/// The condition must have type boolean.
	condition: VariableID,

	trueBranch: OpBlock,
	falseBranch: OpBlock,

	destinations: BranchPhi[],
};

export interface BranchPhi {
	destination: VariableDefinition,

	/// `trueSource` is the local variable within the `trueBranch` block which
	/// contains this value of this variable if the `true` branch was taken.
	trueSource: { tag: "variable", variable: VariableID } | "undef",

	/// `falseSource` is the local variable within the `falseBranch` block which
	/// contains the vlaue of this variable if the `false` branch was taken.
	falseSource: { tag: "variable", variable: VariableID } | "undef",
}

/// `OpNewRecord` defines a new variable with a newly created instance of a
/// specified record.
export interface OpNewRecord {
	tag: "op-new-record",
	record: RecordID,

	/// The types of the fields must be the same as the types of the
	/// `destination` variable's fields (with appropriate instantiation of any
	/// `parameter`s in the record type).
	fields: { [fieldName: string]: VariableID },

	/// The destination must have a type of the specified record.
	destination: VariableDefinition,
};

/// `OpNewEnum` defines a new variable with a newly created instance of a
/// specified enum.
export interface OpNewEnum {
	tag: "op-new-enum",
	enum: EnumID,

	/// The type of the variant value must be the same as the type of the enum's
	/// variant (with appropriate instantiation of any `parameter`s in the enum
	/// type)
	variant: string,
	variantValue: VariableID,

	/// The destination must have a type of the specified enum.
	destination: VariableDefinition,
};

export interface OpIsVariant {
	tag: "op-is-variant",

	/// The base must have enum type.
	base: VariableID,

	/// The variant must be a variant of the base's type.
	variant: string,

	/// The test result must have Boolean type.
	destination: VariableDefinition,
};

/// `OpField` defines a new `destination` variable with the field extracted from
/// an indicated record variable.
export interface OpField {
	tag: "op-field",

	/// The `object` variable must be a record type.
	object: VariableID,

	/// The `field` must be one of the keys in the `fields` map of the
	/// `RecordDefinition` corresponding to the record type of this `object`.
	field: string,

	/// The type of the `destination` variable must be the same as the type of
	/// the `field` within the `object` variable (with appropriate instantiation
	/// of any `parameter`s in the record type).
	destination: VariableDefinition,
};

/// `OpVariant` defines a new `destination` variable with the variant extracted
/// from an indicated enum variable.
export interface OpVariant {
	tag: "op-variant",

	/// The `object` variable must be a enum type.
	object: VariableID,

	/// The `variant` must be one of the keys in the `fields` map of the
	/// `EnumDefinition` corresponding to the enum
	/// type of this `object`.
	variant: string,

	/// The type of the `destination` variable must be the same as the type of
	/// the `variant` within the `object` variable (with appropriate
	/// instantiation of any `parameter`s in the enum type).
	destination: VariableDefinition,

	/// The location of the access.
	diagnostic_location: SourceLocation,
};

export interface OpStaticCall {
	tag: "op-static-call",
	function: FunctionID,

	/// The types of arguments must be equal to the types of the `parameters` in
	/// the corresponding `parameters` of the `FunctionSignature` for this
	/// function call (with appropriate instantiation of any `type_arguments`).
	arguments: VariableID[],
	type_arguments: Type[],

	/// The types of destinations must be equal to the types of the
	/// `return_types` of the `FunctionSignature` for this function call (with
	/// appropriate instantiation of any `type_arguments`).
	destinations: VariableDefinition[],

	diagnostic_callsite: SourceLocation,
};

export interface OpDynamicCall {
	tag: "op-dynamic-call",
	constraint: ConstraintParameter,

	// The index of the function to call within the interface's signature list.
	signature_id: string,

	/// The type arguments to pass, corresponding to the `type_parameters` array
	/// of the corresponding constraint signature.
	/// Note that the v-table closure may use only some of these, in addition to
	/// others stored in the closure context.
	signature_type_arguments: Type[],

	arguments: VariableID[],
	destinations: VariableDefinition[],

	diagnostic_callsite: SourceLocation;
};

export interface OpReturn {
	tag: "op-return",
	sources: VariableID[],

	diagnostic_return_site: SourceLocation,
};

export interface OpBlock {
	ops: Op[],
};

/// `OpProof` represents a "proof" -- code that isn't run. All statements (i.e.,
/// function calls) in the body of an OpProof must be total (terminate).
export interface OpProof {
	tag: "op-proof",
	body: OpBlock,
};

/// `OpUnreachable` indicates a point in the program which is unreachable
/// assuming static analysis was properly performed. If reached at runtime (this
/// should only be possible when verification is skipped), the interpreter will
/// crash. However, a "fast" backend may instead choose to invoke undefined
/// behavior.
export interface OpUnreachable {
	tag: "op-unreachable",

	diagnostic_kind: "contract" | "return" | "match" | "unreachable";
	diagnostic_location: SourceLocation,
};

/// `OpForeign` represents a call to a pure function provided by the host of the
/// interpreter. This includes the operations on primitive types, like
/// arithmetic and byte-slicing.
export interface OpForeign {
	tag: "op-foreign",
	operation: string,
	arguments: VariableID[],
	destinations: VariableDefinition[],
};

export type LeafOp = OpConst
	| OpCopy
	| OpNewRecord | OpNewEnum | OpField | OpVariant | OpIsVariant
	| OpStaticCall | OpDynamicCall
	| OpForeign
	| OpReturn
	| OpUnreachable;

export type Op = OpBranch | OpProof | LeafOp;

export interface IRInterface {
	/// The type-parameters of this interface.
	/// All interfaces have at least one type-parameter (the "this" parameter).
	type_parameters: TypeVariableID[],

	/// N.B.: The `type_parameters` array of each member does not include the
	/// `type_parameters` of the interface.
	signatures: Record<string, FunctionSignature>,
};

export interface ConstraintParameter {
	interface: InterfaceID,
	subjects: Type[],
};

export interface Precondition {
	block: OpBlock,

	// Executing `block` results in a assignment to the boolean `precondition`
	// variable, which is defined by an op-var and visible within this block.
	precondition: VariableID,

	location: SourceLocation,
}

export interface Postcondition {
	block: OpBlock,

	// Bindings for the returned values. (The parameters of the containing
	// `FunctionSignature` are also in scope for a `Postcondition`)
	returnedValues: VariableDefinition[],

	// Executing `block` results in an assignment to the boolean `postcondition`
	// variable, which is defined by an op-var and visible within this block.
	// Callsites may assume that the result is true.
	// Implementations must verify that the result is true.
	postcondition: VariableID,

	location: SourceLocation,
}

export interface FunctionSignature {
	/// The type-parameters bound by this signature.
	/// For a IRInterface signature, this does NOT include the type-parameters
	/// of the interface.
	/// For an impl function, these correspond to
	/// <`for_any` of containing impl>.concat(<type_parameters of interface signature>)
	/// but the names may be different.
	type_parameters: TypeVariableID[],

	/// A v-table is passed at runtime for each constraint in
	/// `constraint_parameters`.
	constraint_parameters: ConstraintParameter[],

	/// `parameters` is the sequence of types for each function parameter.
	parameters: VariableDefinition[],

	/// `returns` is the sequence of types for each function return.
	return_types: Type[],

	// TODO: Add termination-measure function.

	preconditions: Precondition[],
	postconditions: Postcondition[],

	semantics?: {
		/// Indicates that this is a congruence relation, which is an
		/// equivalence relation that respects extensionality.
		/// That is, a == b implies f(a) == f(b).
		eq?: true,
	},
};

export interface IRFunction {
	signature: FunctionSignature,
	body: OpBlock,
};

export interface RecordDefinition {
	/// N.B.: Records are NOT existential types; while they have type
	/// parameters, they do NOT hold constraint implementations. Instead, those
	/// are passed by callers of methods.
	type_parameters: TypeVariableID[],

	/// The fields defined by this record.
	fields: {
		[field: string]: Type,
	},
};

export interface EnumDefinition {
	type_parameters: TypeVariableID[],

	/// The variants defined by this enum.
	variants: {
		[variant: string]: Type,
	},
}

export interface VTableFactory {
	// The number of type arguments that the v-table factory takes.
	// These are instantiated in `interface_arguments`.
	for_any: TypeVariableID[],

	/// `provides` is the `ConstraintParameter` that this `VTableFactory`
	/// provides.
	provides: ConstraintParameter,

	// The functions to call for the corresponding signatures in the interface.
	entries: Record<string, VTableFactoryEntry>,
};

export interface VTableFactoryEntry {
	implementation: FunctionID,

	/// `constraint_parameters` has one element for each of the
	/// `constraint_parameters` in the `FunctionSignature` of the
	/// implementating function.
	/// A `number` element indicates the index within the _interface_'s
	/// signature to use; a `ConstraintParameter` indicates a v-table to be
	/// captured as a closure when this v-table entry is constructed. These
	/// specifications may reference variables from the `for_any`
	/// parameterization of the containing `VTableFactory`.
	constraint_parameters: (number | ConstraintParameter)[],
};

/// `Program` represents a Shiru program: a collection of function definitions
/// and type and constraint definitions. This description is intended to allow
/// efficient and straightforward typechecking, verification, and runtime
/// execution.
export interface Program {
	functions: Record<string, IRFunction>,
	interfaces: Record<string, IRInterface>,
	records: Record<string, RecordDefinition>,
	enums: Record<string, EnumDefinition>,

	foreign: Record<string, FunctionSignature>,

	globalVTableFactories: Record<string, VTableFactory>,
};

export function opTerminates(op: Op) {
	return op.tag === "op-return" || op.tag === "op-unreachable";
}

export function equalTypes(pattern: Type, passed: Type): boolean {
	if (pattern.tag === "type-variable") {
		// TODO: Switch to unification?
		return passed.tag === "type-variable" && passed.id === pattern.id;
	} else if (pattern.tag === "type-compound" && passed.tag === "type-compound") {
		if (pattern.base !== passed.base) {
			return false;
		}
		for (let i = 0; i < pattern.type_arguments.length; i++) {
			if (!equalTypes(pattern.type_arguments[i], passed.type_arguments[i])) {
				return false;
			}
		}
		return true;
	} else if (pattern.tag === "type-primitive" && passed.tag === "type-primitive") {
		return pattern.primitive === passed.primitive;
	}

	return false;
}

function typeContainsVariable(
	t: Type,
	v: TypeVariableID,
	assignments: Map<TypeVariableID, Type | null>,
): boolean {
	if (t.tag === "type-compound") {
		for (const arg of t.type_arguments) {
			if (typeContainsVariable(arg, v, assignments)) {
				return true;
			}
		}
		return false;
	} else if (t.tag === "type-primitive") {
		return false;
	} else if (t.tag === "type-variable") {
		if (t.id === v) {
			return true;
		}
		const assigned = assignments.get(t.id);
		if (assigned !== null && assigned !== undefined) {
			return typeContainsVariable(assigned, v, assignments);
		}
		return false;
	} else if (t.tag === "type-any") {
		return false;
	}

	const _: never = t;
	throw new Error("typeContainsVariable: unreachable `" + t["tag"] + "`");
}

function unifyTypeArrayHelper(
	lefts: Type[],
	rights: Type[],
	assignments: Map<TypeVariableID, Type | null>,
): Map<TypeVariableID, Type | null> | null {
	for (let i = 0; i < lefts.length; i++) {
		if (unifyTypePairHelper(lefts[i], rights[i], assignments) === null) {
			return null;
		}
	}
	return assignments;
}

function unifyTypePairHelper(
	left: Type,
	right: Type,
	assignments: Map<TypeVariableID, Type | null>,
): Map<TypeVariableID, Type | null> | null {
	if (left.tag === "type-variable") {
		const mapping = assignments.get(left.id);
		if (mapping === null) {
			if (typeContainsVariable(right, left.id, assignments)) {
				return null;
			}
			assignments.set(left.id, right);
			return assignments;
		} else if (mapping !== undefined) {
			return unifyTypePairHelper(mapping, right, assignments);
		}
	}
	if (right.tag === "type-variable") {
		const mapping = assignments.get(right.id);
		if (mapping === null) {
			if (typeContainsVariable(left, right.id, assignments)) {
				return null;
			}
			assignments.set(right.id, left);
			return assignments;
		} else if (mapping !== undefined) {
			return unifyTypePairHelper(left, mapping, assignments);
		}
	}

	if (left.tag === "type-compound") {
		if (right.tag !== "type-compound") {
			return null;
		} else if (left.base !== right.base) {
			return null;
		}
		return unifyTypeArrayHelper(left.type_arguments, right.type_arguments, assignments);
	} else if (left.tag === "type-primitive") {
		if (right.tag !== "type-primitive") {
			return null;
		}
		return left.primitive !== right.primitive ? null : assignments;
	} else if (left.tag === "type-variable") {
		if (right.tag !== "type-variable") {
			return null;
		}
		return left.id !== right.id ? null : assignments;
	} else if (left.tag === "type-any") {
		if (right.tag !== "type-any") {
			return null;
		}
		return assignments;
	}

	const _: never = left;
	throw new Error("unifyTypesHelper: unreachable `" + left["tag"] + "`");
}

export interface UnificationResult {
	leftRenaming: Map<TypeVariableID, TypeVariable>,
	rightRenaming: Map<TypeVariableID, TypeVariable>,

	/// A `null` instantiation is "free".
	/// Instantiations may reference other type-variables, but these references
	/// will not be cyclic.
	instantiations: Map<TypeVariableID, Type | null>,
}

/// RETURNS the most-general unification of the two types.
export function unifyTypes(
	leftVars: TypeVariableID[],
	lefts: Type[],
	rightVars: TypeVariableID[],
	rights: Type[],
): UnificationResult | null {
	const assignments = new Map<TypeVariableID, Type | null>();

	// Rename variables so that they are distinct.
	const leftRenaming = new Map<TypeVariableID, TypeVariable>();
	for (const leftVar of leftVars) {
		const id = "unify_" + leftVar + Math.random() as TypeVariableID;
		assignments.set(id, null);
		leftRenaming.set(leftVar, { tag: "type-variable", id });
	}

	const rightRenaming = new Map<TypeVariableID, TypeVariable>();
	for (const rightVar of rightVars) {
		const id = "unify_" + rightVar + Math.random() as TypeVariableID;
		assignments.set(id, null);
		rightRenaming.set(rightVar, { tag: "type-variable", id });
	}

	lefts = lefts.map(t => typeSubstitute(t, leftRenaming));
	rights = rights.map(t => typeSubstitute(t, rightRenaming));

	const out = unifyTypeArrayHelper(lefts, rights, assignments);
	if (out === null) {
		return null;
	}
	return {
		leftRenaming,
		rightRenaming,
		instantiations: assignments,
	};
}

export function typeArgumentsMap(
	parameters: TypeVariableID[],
	args: Type[],
): Map<TypeVariableID, Type> {
	if (parameters.length !== args.length) {
		throw new Error("typeArgumentsMap: length mismatch");
	}
	const map: Map<TypeVariableID, Type> = new Map();
	for (let i = 0; i < parameters.length; i++) {
		map.set(parameters[i], args[i]);
	}
	return map;
}

export function typeSubstitute(t: Type, map: Map<TypeVariableID, Type>): Type {
	if (t.tag === "type-compound") {
		return {
			tag: t.tag,
			base: t.base,
			type_arguments: t.type_arguments.map(a => typeSubstitute(a, map)),
		};
	} else if (t.tag === "type-primitive") {
		return t;
	} else if (t.tag === "type-variable") {
		const existing = map.get(t.id);
		if (existing !== undefined) {
			return existing;
		}
		return t;
	} else if (t.tag === "type-any") {
		return t;
	}

	const _: never = t;
	throw new Error(`unhandled type tag \`${t}\`.`);
}

export function typeRecursiveSubstitute(t: Type, map: Map<TypeVariableID, Type | null>): Type {
	if (t.tag === "type-variable") {
		const e = map.get(t.id);
		if (e === undefined) {
			return t;
		} else if (e === null) {
			return t;
		} else {
			const r = typeRecursiveSubstitute(e, map);
			map.set(t.id, r);
			return r;
		}
	} else if (t.tag === "type-compound") {
		return {
			tag: t.tag,
			base: t.base,
			type_arguments: t.type_arguments.map(a => typeRecursiveSubstitute(a, map)),
		};
	} else if (t.tag === "type-primitive") {
		return t;
	} else if (t.tag === "type-any") {
		return t;
	}

	const _: never = t;
	throw new Error(`unhandled type tag \`${t["tag"]}\`.`);
}

export function constraintSubstitute(
	c: ConstraintParameter,
	map: Map<TypeVariableID, Type>,
): ConstraintParameter {
	return {
		interface: c.interface,
		subjects: c.subjects.map(x => typeSubstitute(x, map)),
	};
}
