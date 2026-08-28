# AY OCaml binding

An OCaml binding over AY's C API (`crates/ay-ffi/include/ay.h`),
analogous to the OCaml binding that ships with Z3. It is **purely additive**:
new files under `bindings/ocaml/`, no change to the solver or the C API.

## Design and correctness boundary

This is a *thin* wrapper. Every `sat`/`unsat`/`unknown` verdict and every model
is produced by the AY solver itself. The OCaml layer only:

1. builds **SMT-LIB term strings** with a small typed combinator API
   (`Ay.int_const`, `Ay.and_`, `Ay.add`, `Ay.lt`, ...), and
2. marshals those strings across the FFI to `ay_assert` / `ay_check_sat` /
   `ay_get_model`, mapping the integer result codes back to a `result` variant.

No solving or simplification happens in OCaml, but the binding is still part of
the correctness boundary: its SMT-LIB rendering, result-code mapping, C stubs,
and handle lifetimes must agree with AY's ABI. A bug in any of those layers can
change the problem AY receives or the result the caller observes. When AY's C
API signals an error (non-zero / `AY_ERROR`), the binding raises `Failure`
rather than guessing a verdict.

## Files

| File          | Purpose                                                            |
|---------------|-------------------------------------------------------------------|
| `ay.mli`      | Public interface (solver, sorts, term builders, check/model).     |
| `ay.ml`       | Implementation: raw `external`s + SMT-LIB term builders.          |
| `ay_stubs.c`  | C stubs bridging OCaml values to `ay.h`; GC-finalized handle.     |
| `test_ay.ml`  | End-to-end test: SAT + UNSAT problems, push/pop, prints a model.  |
| `run.sh`      | Build + run the test against `libay_ffi` (no findlib/ctypes).     |

No external OCaml packages are required — the binding uses raw `external`
declarations plus a C stub, so only the base `ocamlopt`/`ocamlc` toolchain is
needed (Ctypes/findlib are *not* dependencies).

## Coverage

- **Context / solver**: `mk_solver ?logic`, `free` (also GC-finalized),
  `reset`, `version`.
- **Sorts / constants**: `Bool`, `Int`, `Real` via `declare_const` /
  `bool_const` / `int_const` / `real_const`.
- **Literals**: `true_`, `false_`, `bool_lit`, `int_lit` (negatives as `(- n)`).
- **Boolean**: `not_`, `and_`, `or_`, `implies`, `iff`, `ite` (with the standard
  0/1-arg identities for `and`/`or`).
- **Equality / comparison**: `eq`, `neq`, `lt`, `le`, `gt`, `ge`.
- **Arithmetic**: `add`, `sub`, `mul`, `neg`.
- **Assert / check / model**: `assert_`, `check_sat`, `get_model`,
  `last_error`.
- **Incremental**: `push`, `pop`.
- **Escape hatch**: `solve_smtlib` runs a raw SMT-LIB command block for anything
  the typed builders do not yet cover (e.g. bit-vectors, arrays, datatypes,
  quantifiers). It is routed through AY; the caller remains responsible for the
  validity and intended meaning of the raw SMT-LIB input.

## Build & run

```sh
# 1. Build the AY FFI library (produces target/debug/libay_ffi.{a,dylib}).
cargo build -p ay-ffi

# 2. Build and run the OCaml test (statically links libay_ffi.a).
bash bindings/ocaml/run.sh           # or: bash bindings/ocaml/run.sh --release
```

Expected output for the named test cases:

```
AY OCaml binding test
  linked AY version: <workspace version>+build....
  PASS: lia_sat -> sat
  PASS: lia_sat:model_present
    model: (model   (define-fun y () Int 2)   (define-fun x () Int 1) )
  PASS: lia_unsat -> unsat
  PASS: bool_sat -> sat
  PASS: bool_unsat -> unsat
  PASS: implies_unsat -> unsat
  PASS: push_pop:base_sat -> sat
  PASS: push_pop:scoped_unsat -> unsat
  PASS: push_pop:after_pop_sat -> sat
All OCaml binding tests passed.
```

`test_ay.ml`, run by `bindings/ocaml/run.sh`, exercises SAT and UNSAT result
mapping, model retrieval, and incremental push/pop through the compiled C
stubs. These named tests cover the examples above; they are not a proof that
every possible SMT-LIB rendering or ABI interaction is correct.

## Example

```ocaml
let s = Ay.mk_solver ~logic:"QF_LIA" () in
let x = Ay.int_const s "x" in
Ay.assert_ s (Ay.gt x (Ay.int_lit 0));
Ay.assert_ s (Ay.lt x (Ay.int_lit 5));
match Ay.check_sat s with
| Ay.Sat   -> Printf.printf "sat: %s\n" (Option.value ~default:"" (Ay.get_model s))
| Ay.Unsat -> print_endline "unsat"
| _        -> print_endline "unknown/error"
```
