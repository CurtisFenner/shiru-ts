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

/// `TypeCompound` represents the type which is an instance of a given entity
/// type.
export interface TypeCompound {
	tag: "type-compound",

	/// `record` references a `RecordDefinition` in a `Program`.
	record: RecordID,

	type_arguments: Type[],
};

/// `TypeVariable` represents the type which is a parameter of a function or
/// compound type.
export interface TypeVariable {
	tag: "type-variable",
	id: TypeVariableID,
};

export type Type = TypePrimitive | TypeCompound | TypeVariable;

export type FunctionID = { function_id: string };
export type VariableID = { variable_id: number };
export type RecordID = { record_id: string };
export type ConstraintID = { constraint_id: number };
export type InterfaceID = { interface_id: string };
export type TypeVariableID = { type_variable_id: number };

/// `OpVar` makes a new slot available at the top of the currently active stack
/// frame.
export interface OpVar {
	tag: "op-var",
	type: Type,
	debug_name?: string,
};

/// `OpConst` overwrites a primitive-typed destination variable with a constant.
export interface OpConst {
	tag: "op-const",
	destination: VariableID,
	value: number | boolean,
};

/// `OpAssign` overwrites a destination variable with the current value of a
/// `source` variable.
export interface OpAssign {
	tag: "op-assign",

	/// The source & destination variables must have the same type.
	source: VariableID,
	destination: VariableID,
};

/// `OpBranch` chooses which branch to execute depending on the current value of
/// a `condition` variable.
export interface OpBranch {
	tag: "op-branch",

	/// The condition must have type boolean.
	condition: VariableID,

	trueBranch: OpBlock,
	falseBranch: OpBlock,
};

/// `OpNewRecord` overwrites a `destination` variable with a newly created 
/// instance of a specified record.
export interface OpNewRecord {
	tag: "op-new-record",
	record: RecordID,

	/// The types of the fields must be the same as the types of the
	/// `destination` variable's fields (with appropriate instantiation of any
	/// `parameter`s in the record type).
	fields: { [fieldName: string]: VariableID },

	/// The destination must have a type of the specified record.
	destination: VariableID,
};

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
	destination: VariableID,
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
	destinations: VariableID[],

	diagnostic_callsite?: SourceLocation,
};

export interface OpDynamicCall {
	tag: "op-dynamic-call",
	interface: InterfaceID,
	interface_arguments: Type[],

	// The index of the function to call within the interface's signature list.
	signature_id: number,

	// TODO: The type parameters as declared in the interface's signature.
	// Note that the v-table closure may ultimately pass different constraints
	// to the underlying implementation.
	signature_type_arguments: Type[],

	arguments: VariableID[],
	destinations: VariableID[],

	diagnostic_callsite?: SourceLocation;
};

export interface OpReturn {
	tag: "op-return",
	sources: VariableID[],
};

export interface OpBlock {
	tag: "op-block",
	ops: Op[],
};

/// `OpProof` represents a "proof" -- code that isn't run. All statements (i.e., 
/// function calls) in the body of an OpProof must be total (terminate).
export interface OpProof {
	tag: "op-proof",
	body: Op,
};

/// `OpUnreachable` indicates a point in the program which is unreachable 
/// assuming static analysis was properly performed. If reached at runtime (this
/// should only be possible when verification is skipped), the interpreter will 
/// crash. However, a "fast" backend may instead choose to invoke undefined
/// behavior.
export interface OpUnreachable {
	tag: "op-unreachable",

	diagnostic_kind: "contract" | "return" | "match";
	diagnostic_location?: SourceLocation,
};

/// `OpForeign` represents a call to a pure function provided by the host of the 
/// interpreter. This includes the operations on primitive types, like 
/// arithmetic and byte-slicing.
export interface OpForeign {
	tag: "op-foreign",
	operation: string,
	arguments: VariableID[],
	destinations: VariableID[],
};

/// `OpEq` is used in specifications of functions to indicate that they produce
/// an equivalence relation that is _extensional_ with respect to all other 
/// operations.
/// TODO: Pin down how this works with 'quotient' types.
export interface OpEq {
	tag: "op-eq",
	left: VariableID,
	right: VariableID,
	destination: VariableID,
};

export type LeafOp = OpVar
	| OpConst
	| OpAssign
	| OpNewRecord | OpField
	| OpStaticCall | OpDynamicCall
	| OpForeign
	| OpReturn
	| OpUnreachable
	| OpEq;

export type Op = OpBranch | OpProof | LeafOp;

export interface IRInterface {
	// type_parameters.length is the number of type arguments.
	// The names in this array are currently unused.
	type_parameters: string[],

	/// N.B.: The type_parameters method of each is the same as the inteface's.
	signatures: FunctionSignature[],
};

export interface ConstraintParameter {
	constraint: InterfaceID,
	subjects: Type[],
};

export interface FunctionSignature {
	/// The length of `type_parameters` indicates the number of type parameters.
	/// The names in this array are currently unused.
	type_parameters: string[],

	/// A v-table is passed at runtime for each constraint in 
	/// `constraint_parameters`.
	constraint_parameters: ConstraintParameter[],

	/// `parameters` is the sequence of types for each function parameter.
	parameters: Type[],

	/// `returns` is the sequence of types for each function return.
	return_types: Type[],

	// TODO: Add termination-measure function.

	/// The first `parameters.length` variables are the arguments.
	/// The Op returns a single boolean, which must be _verified_ to be true at
	/// callsites, and may be _assumed_ to be true in subsequent preconditions
	/// and measures, and the implementation.
	preconditions: Op[],

	/// The first `parameters.length` variables are the arguments.
	/// The next `return_types.length` variables are the returned values.
	/// The Op returns a single boolean, which must be _verified_ to be true in
	/// the implementation, and may be _assumed_ to be true in subsequent 
	/// postconditions and at callsites.
	postconditions: Op[],
};

export interface IRFunction {
	signature: FunctionSignature,
	body: OpBlock,
};

export interface RecordDefinition {
	/// N.B.: Records are NOT existential types; while they have type
	/// parameters, they do NOT hold constraint implementations. Instead, those
	/// are passed by callers of methods.
	// The names in this array are currently unused.
	type_parameters: string[],

	/// The fields defined by this record.
	fields: {
		[field: string]: Type,
	},
};

export interface VTableFactory {
	// The interface that this v-table factory is for.
	interface: InterfaceID,

	// The number of type arguments that the v-table factory takes.
	// These are instantiated in `interface_arguments`.
	for_any: TypeVariable[],

	// The arguments to this interface. At least one must be provided.
	// This array may reference variables in the `for_any` field.
	interface_arguments: Type[],

	// The functions to call for the corresponding signatures in the interface.
	implementations: VTableEntry[],
};

export interface VTableEntry {
	implementation: FunctionID,

	// These constraint parameters are captured as "closures" at time of 
	// construction of the v-table. They may reference variables in the 
	// `for_any` parameterization.
	constraint_parameters: ConstraintParameter[],
};

/// `Program` represents a Shiru program: a collection of function definitions
/// and type and constraint definitions. This description is intended to allow
/// efficient and straightforward typechecking, verification, and runtime
/// execution.
export interface Program {
	functions: Record<string, IRFunction>,
	interfaces: Record<string, IRInterface>,
	records: Record<string, RecordDefinition>,

	foreign: Record<string, FunctionSignature>,

	globalVTableFactories: Record<string, VTableFactory>,
};

type Problem = {
	tag: string,
	message: string,
};

export function typecheckProgram(program: Program): Problem[] {
	const problems: Problem[] = [];

	// 1) Type check all functions
	for (let k in program.functions) {
		problems.push(...typecheckFunction(program, k));
	}

	// 2) Type check all interfaces
	for (let k in program.interfaces) {
		problems.push(...typecheckInterface(program, k));
	}

	return problems;
}

function typecheckFunction(program: Program, fid: string): Problem[] {
	const fDef = program.functions[fid];
	throw new Error("TODO");
}

function typecheckInterface(program: Program, iid: string): Problem[] {
	const iDef = program.interfaces[iid];
	throw new Error("TODO");
}

export function equalTypes(pattern: Type, passed: Type): boolean {
	if (pattern.tag === "type-variable") {
		// TODO: Switch to unification?
		return passed.tag === "type-variable"
			&& passed.id.type_variable_id === pattern.id.type_variable_id;
	} else if (pattern.tag === "type-compound" && passed.tag === "type-compound") {
		if (pattern.record.record_id !== passed.record.record_id) {
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

export function typeSubstitute(t: Type, map: Map<number, Type>): Type {
	if (t.tag === "type-compound") {
		return {
			tag: t.tag,
			record: t.record,
			type_arguments: t.type_arguments.map(a => typeSubstitute(a, map)),
		};
	} else if (t.tag === "type-primitive") {
		return t;
	} else if (t.tag === "type-variable") {
		const existing = map.get(t.id.type_variable_id);
		if (existing !== undefined) {
			return existing;
		}
		return t;
	}
	throw new Error(`unhandled type tag \`${t}\`.`);
}
