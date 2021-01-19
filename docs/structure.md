# The Structure of the Shiru Compiler

This document briefly describes the structure of the compiler, explaining the
way the different components fit together.

* `src/data.ts` defines generic data-structures used by other parts of the
  compiler and interpreter. This file can be used as a standalone library.
* `src/dimacs.ts` defines a command line utility to parse CNF files in the
  "DIMACS" format.
* `src/interpreter.ts` defines an interpreter that can run intermediate
  representations of Shiru programs.
* `src/ir.ts` defines an *intermediate representation* (*IR*) for the Shiru
  language. This file can be used as a standalone library.
* `src/parser.ts` defines a parser-combinator library for parsing expression
  grammars (PEG), which are recursive-descent like. This file can be used as a
  standalone library.
* `src/sat.ts` defines a `sat.SATSolver` class which solves the
  *Boolean conjunctive-normal-form satisfiability problem* (*CNF-SAT*).
* `src/smt.ts` defines a `smt.SMTSolver` class / `smt.UFTheory` class which
  can solve *satisfiability modulo theories* (*SMT*) problems.
* `src/test.ts` defines a script to run tests.

## The Shiru Intermediate Representation

Shiru's intermediate representation (IR) is defined in `src/ir.ts`. A Shiru
program is represented by the `ir.Program` interface.

The Shiru IR is designed so that it can be type-checked and verified. Within the
IR, functions, variables, and type-definitions are annotated with nominal types,
as well as pre-conditions, post-conditions, and invariants.

The Shiru IR is high-level, but intended to be straightforward to compile to
most targets (modulo the need to generate garbage collection information).
