/// `TypePrimitive` represents one of the "built-in" primitive types:
/// `"Bytes"` is the type of immutable finite sequences of octets.
/// `"Unit"` is the type of a single value: "unit".
/// `"Boolean"` is the type of two values: "true" and "false".
/// `"Int"` is the type of unbounded integers: ..., -3, -2, -1, 0, 1, 2, 3, ...
export interface TypePrimitive {
	tag: "type-primitive",
	primitive: "Bytes" | "Unit" | "Boolean" | "Int",
};

/// `TypeClass` represents the type which is instances of a given class.
/// A "class" is a product (and "quotient") of fields.
export interface TypeClass {
	tag: "type-class",

	/// `class` references a `ClassDefinition` in a `Program`.
	class: ClassID,

	parameter: Type[],
};

/// `TypeVariable` represents the type which is a parameter of a function or
/// compound type.
export interface TypeVariable {
	tag: "type-variable",
	id: TypeVariableID,
};

export type Type = TypePrimitive | TypeClass | TypeVariable;

export type FunctionID = { function_id: string };
export type VariableID = { variable_id: number };
export type ClassID = { class_id: string };
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

/// `OpNewClass` overwrites a `destination` variable with a newly created 
/// instance of a specified class.
export interface OpNewClass {
	tag: "op-new-class",
	class: ClassID,

	/// The types of the fields must be the same as the types of the
	/// `destination` variable's fields (with appropriate instantiation of any
	/// `parameter`s in the class type).
	fields: { [fieldName: string]: VariableID },

	/// The destination must have a class type for the given id.
	destination: VariableID,
};

export interface OpField {
	tag: "op-field",

	/// The `object` variable must be a class type.
	object: VariableID,

	/// The `field` must be one of the keys in the `fields` map of the 
	/// `ClassDefinition` corresponding to the class type of this `object`.
	field: string,

	/// The type of the `destination` variable must be the same as the type of
	/// the `field` within the `object` variable (with appropriate instantiation
	/// of any `parameter`s in the class type).
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
};

export interface OpDynamicCall {
	tag: "op-dynamic-call",
	constraint: ConstraintParameter,
	constraint_implementer: Type,
	signature_id: number,
	arguments: VariableID[],
	destinations: VariableID[],
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
	ops: Op[],
};

/// `OpUnreachable` indicates a point in the program which is unreachable 
/// assuming static analysis was properly performed. If reached at runtime (this
/// should only be possible when verification is skipped), the interpreter will 
/// crash. However, a "fast" backend may instead choose to invoke undefined
/// behavior.
export interface OpUnreachable {
	tag: "op-unreachable",
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
	| OpNewClass | OpField
	| OpStaticCall | OpDynamicCall
	| OpForeign
	| OpReturn
	| OpUnreachable
	| OpEq;

export type Op = OpBlock | OpBranch | OpProof | LeafOp;

export interface IRInterface {
	// type_parameters.length is the number of type arguments.
	// An empty array is used for an unconstraint (totally parametric) type
	// parameter.
	type_parameters: ConstraintParameter[][],

	/// N.B.: The type_parameters method of each is the same as the inteface's.
	signatures: FunctionSignature[],
};

export interface ConstraintParameter {
	interface: InterfaceID,
	interface_arguments: Type[],
};

export interface FunctionSignature {
	parameters: Type[],
	type_parameters: ConstraintParameter[][],
	return_types: Type[],

	/// The first `parameters.length` variables are the arguments.
	/// Unreachable statements in preconditions are to be _checked_ to be
	/// unreachable at callsites, and to be _assumed_ to be unreachable in 
	/// implementations.
	preconditions: Op[],

	/// The first `parameters.length` variables are the arguments.
	/// The next `return_types.length` variables are the returned values.
	/// Unreachable statements in postconditions are to be _assumed_ unreachable
	/// at callsites, and to be _checked_ to be unreachable in implementations.
	postconditions: Op[],
};

export interface IRFunction {
	signature: FunctionSignature,
	body: Op,
};

export interface ClassDefinition {
	/// N.B.: Classes are NOT existential types; while they have type
	/// parameters, they do NOT hold constraint implementations. Instead, those
	/// are passed by callers of methods.
	parameters: Type[],

	/// The fields defined by this class.
	fields: {
		[field: string]: Type,
	},
};

/// `Program` represents a Smol program: a collection of function definitions
/// and type and constraint definitions. This description is intended to allow
/// efficient and straightforward typechecking, verification, and runtime
/// execution.
export interface Program {
	functions: Record<string, IRFunction>,
	interfaces: Record<string, IRInterface>,
	classes: Record<string, ClassDefinition>,

	foreign: Record<string, FunctionSignature>,
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
