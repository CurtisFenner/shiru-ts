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
	value: number | boolean | string,
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

	diagnostic_callsite: SourceLocation,
};

export interface OpDynamicCall {
	tag: "op-dynamic-call",
	constraint: InterfaceID,
	subjects: Type[],

	// The index of the function to call within the interface's signature list.
	signature_id: string,

	/// The type arguments to pass, corresponding to the `type_parameters` array
	/// of the corresponding constraint signature.
	/// Note that the v-table closure may use only some of these, in addition to
	/// others stored in the closure context.
	signature_type_arguments: Type[],

	arguments: VariableID[],
	destinations: VariableID[],

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
	destinations: VariableID[],
};

export type LeafOp = OpVar
	| OpConst
	| OpAssign
	| OpNewRecord | OpField
	| OpStaticCall | OpDynamicCall
	| OpForeign
	| OpReturn
	| OpUnreachable;

export type Op = OpBranch | OpProof | LeafOp;

export interface IRInterface {
	// type_parameters.length is the number of type arguments.
	// The names in this array are currently unused.
	type_parameters: string[],

	/// N.B.: The type_parameters of each method is the same as the inteface's.
	signatures: Record<string, FunctionSignature>,
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
	/// The block computes a boolean variable stored in `result`.
	/// At callsites, it must be _verified_ that this result is `true`.
	/// In subsequent preconditions and the function's implementation,
	/// it may be _assumed_ to be `true`.
	preconditions: { block: OpBlock, result: VariableID, location: SourceLocation }[],

	/// The first `parameters.length` variables are the arguments.
	/// The next `return_types.length` variables are the returned values.
	/// The block computes a boolean variable stored in `result`.
	/// At callsites, it may be _assumed_ that this result is `true`.
	/// In implementations, it must be  _verified_ that this result is `true`.
	postconditions: { block: OpBlock, result: VariableID, location: SourceLocation }[],

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
	subjects: Type[],

	// The functions to call for the corresponding signatures in the interface.
	entries: Record<string, VTableEntry>,
};

export interface VTableEntry {
	implementation: FunctionID,

	/// `constraint_parameters` has one entry for each of the 
	/// `constraint_parameters` in the `FunctionSignature` of the 
	/// implementating function.
	/// A `number` element indicates the index within the _interface_'s 
	/// signature to use; a `ConstraintParameter` indicates a v-table to be 
	/// captured as a closure when this v-table entry is constructed. These
	/// specifications may reference variables from the `for_any` 
	/// parameterization.
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

export function opTerminates(op: Op) {
	return op.tag === "op-return" || op.tag === "op-unreachable";
}

function typecheckFunction(program: Program, fid: string): Problem[] {
	const fDef = program.functions[fid];
	const body = fDef.body;

	const problems = [];

	if (body.ops.length === 0 || !opTerminates(body.ops[body.ops.length - 1])) {
		problems.push({
			tag: "missing-return",
			message: "Function `" + fid + "` does not end with op-return/op-unreachable",
		});
	}

	throw new Error("TODO");
	return problems;
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
