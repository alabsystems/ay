# ayz3

A **z3py-shaped core subset** backed by the [AY solver](https://github.com/alabsystems/ay).

`ayz3` mirrors the shapes and names of [z3py](https://github.com/Z3Prover/z3)
for the documented subset, so scripts confined to that subset generally need
only an import change. It solves with **AY**, not Z3. Under the hood it is a thin
`ctypes` binding over AY's Z3-shaped C ABI (`libay_ffi`).

```python
from ayz3 import Int, Solver, sat

x, y = Int('x'), Int('y')
s = Solver()
s.add(x > 0, y > 0, x + y == 10, x < y)
assert s.check() == sat
print(s.model())          # e.g. [x = 1, y = 9]
```

The same wheel also includes `aysearch`, a smaller API for applications that
would otherwise need custom backtracking, branch-and-bound, or search code:

```python
from aysearch import Model

m = Model("assignment")
worker = m.choice("worker", ["cpu", "gpu"])
cost = m.int("cost", 0, 20)
m.table([worker, cost], [["cpu", 7], ["gpu", 3]])
m.minimize(cost)

result = m.solve()
if result.status != "optimal":
    raise RuntimeError(f"need a proved optimum, got {result.status}")
print(result.require_solution()[worker])  # gpu
```

Equation strings passed to `Model.add()` use AY's restricted linear grammar;
they remain data across the JSON ABI and are never passed to Python `eval`.
`aysearch` has inline annotations plus a `py.typed` marker. Complete worked
examples for Sudoku, an LLM token router, and Minesweeper live in
`examples/search_*.py`.

From the repository root, after `cargo build -p ay-ffi`:

```bash
PYTHONPATH=bindings/python python3 bindings/python/examples/search_sudoku.py
PYTHONPATH=bindings/python python3 bindings/python/examples/search_token_router.py
PYTHONPATH=bindings/python python3 bindings/python/examples/search_minesweeper.py
```

Enumeration is satisfaction-only: `enumerate()` rejects a model after
`minimize()` or `maximize()` instead of silently changing the requested mode.

## Install

The wheel **bundles the AY shared library** (`libay_ffi`) inside the package, so an installed `ayz3` is self-contained — it does not need the AY source tree at runtime.

Building the wheel requires a Rust toolchain (`cargo`), because the build step compiles `libay_ffi` from the AY source tree and copies it into the package:

```bash
# from bindings/python, inside an AY checkout
pip install .
```

This runs `cargo build -p ay-ffi --release` and folds the resulting
`libay_ffi.{dylib,so}` into the wheel. Then, from anywhere:

```python
import ayz3
from ayz3 import Int, Solver, sat
x = Int('x'); s = Solver(); s.add(x > 0, x < 5)
assert s.check() == sat
print(s.model())
```

### Library resolution order

`ayz3/_lib.py` locates the shared library in this order:

1. `AYZ3_LIB` environment variable (full path to the dylib/so), if set.
2. The cdylib **bundled in the package directory** (next to `ayz3/_lib.py`) — this is the installed-wheel path.
3. The in-tree dev fallback: walk up to the Cargo workspace root and probe `target/release/` then `target/debug/`.

So both workflows work: an installed wheel uses (2); a source checkout with `cargo build -p ay-ffi` uses (3).
The `aysearch` loader follows the same bundled/source paths and additionally
honors `AYSEARCH_LIB` before the shared `AYZ3_LIB` fallback.

## Scope

This is a **core slice** of z3py, not a complete reimplementation. It contains
no substitute solver: AY computes verdicts and models for requests sent through
the C ABI. Correctness also depends on this wrapper's term encoding, `ctypes`
signatures, context handling, and result mapping. Operations without an
implemented C-ABI route raise `NotImplementedError` naming the gap.

### Supported

- **Sorts:** `BoolSort`, `IntSort`, `RealSort`, `BitVecSort`, `ArraySort`, `StringSort`, `SetSort`, `FPSort` (`Float16`/`Float32`/`Float64`/`Float128`).
- **Constants / values:** `Int`, `Real`, `Bool`, `BitVec`, `Const`, `Array`, `String`; `IntVal`, `RealVal`, `BoolVal`, `BitVecVal`, `StringVal`.
- **Booleans:** `And`, `Or`, `Not`, `Implies`, `Xor`, `If`, `Distinct`, plus Python operators (`&`, `|`, `~`, comparisons).
- **Arithmetic:** `+ - * / %`, comparisons over Int/Real; `Sum`, `Product` aggregates.
- **Bitvectors:** arithmetic/bitwise/shift ops, signed and unsigned comparisons (`ULT`/`ULE`/`UGT`/`UGE`).
- **Arrays:** `Array`, `Select`, `Store`, `K` (const array).
- **Finite sets (sets-as-arrays, z3py's own encoding):** `SetSort`, `EmptySet`, `FullSet`, `SetAdd`, `SetDel`, `IsMember`, and the algebra ops `SetUnion`, `SetIntersect`, `SetDifference`, `SetComplement` (lazy, membership-reducible). `IsSubset` is **deferred** (needs quantified array reasoning AY cannot soundly decide).
- **Floating point (IEEE-754, native `Z3_mk_fpa_*` handles):** `FPSort`/`Float16`/`Float32`/`Float64`/`Float128`; `FP`/`FPs`/`FPVal`; rounding modes `RNE`/`RNA`/`RTP`/`RTN`/`RTZ`; the listed arithmetic, comparison, predicate, and conversion constructors in `ayz3/fp.py`. Representative FP and mixed-theory combinations are regression-tested; arbitrary combinations are not implied by this constructor inventory.
- **Algebraic datatypes:** `Datatype` (including single self-recursive datatypes such as `List`), `EnumSort`, `TupleSort`, `CreateDatatypes` — constructors, recognizers and accessors are real datatype ops with model readout. Mutually recursive datatype *groups* are unsupported (`CreateDatatypes` raises `NotImplementedError`; see below).
- **Uninterpreted functions:** `Function` → `FuncDeclRef`, applied like z3py.
- **Quantifier terms:** `ForAll`, `Exists` construction and introspection over declared bound variables. Solving is experimental; quantified-array formulas fail closed to `unknown` at the wrapper boundary.
- **Strings / sequences:** `String`, `StringVal`, `Concat`, `Length`, `Contains`, `PrefixOf`, `SuffixOf`, `IndexOf`, `SubString` (= `Extract`), `Replace`.
- **Solver:** `Solver` with `add`/`assert_and_track`, `push`/`pop`, `check` (with assumptions), `model`, `unsat_core`, `reason_unknown`, `to_string`, `set` (incl. `timeout`).
- **Optimize:** `Optimize` with `add`, `maximize`/`minimize`, `add_soft`, `check`, `model`, objective bounds.
- **Models (z3py-style):** `ModelRef` indexing by const ref (`m[x]`) **or** declaration (`m[d]`), `eval`/`evaluate`, `len(m)`, `m.decls()`, iteration (`for d in m: ...` yields `FuncDeclRef`s), `FuncDeclRef.name()`, and a z3py-shaped `repr(m)` → `[x = 4, y = 6]` (numbers bare, `True`/`False` for Bool, quoted strings; sorted for a stable order). `m.sexpr()` exposes AY's raw SMT-LIB model text.
- **Misc:** `is_true`, `is_false`, `simplify`, `set_param`/`get_param`, `parse_smtlib2_string`/`parse_smtlib2_file`.

The suite in `tests/` contains representative verdict and value cross-checks
against the required `z3-solver==5.0.0.0` oracle. It does not establish
equivalence over every input in the operation domains above.

### Example applications

`examples/` holds **real, idiomatic z3py programs** — the same body runs unchanged on `import ayz3 as z` or `import z3 as z`. Each is cross-checked against z3py and its solution is **independently re-validated** (not merely trusted):

- `examples/nqueens.py` — N-Queens (4/6/8 queens sat with valid placements; 3-Queens unsat).
- `examples/graph_coloring.py` — k-coloring the Petersen graph (3-colorable sat, 2-colorable unsat).
- `examples/bmc.py` — bounded model checking of a bounded counter (invariant unsat; buggy variant sat with a real counterexample trace).
- `examples/sudoku.py` — Sudoku (4x4 solved + validated, matches z3py's unique solution).

From the repository root, run e.g.:

```bash
cd bindings/python
python3 -m examples.nqueens
```

### Known divergences and fail-closed limitations

- **Unsat-core minimization is fail-closed.** `unsat_core()` deletion-minimizes the solver-reported core when its incremental checks are definitive. It drops an element only when the remainder is still `unsat`; an `unknown` deletion check keeps the element. The result remains a sound unsatisfiable subset, but is not claimed deletion-minimal unless every kept-element check was `sat`.
- **`simplify` is identity.** AY simplifies eagerly during term construction, so `simplify(e)` returns `e` unchanged rather than a separately rewritten form.
- **Mutually recursive `Datatype` groups are unsupported.** Single (self-recursive) datatypes, `EnumSort` and `TupleSort` work with full model readout, but `CreateDatatypes` over datatypes that reference *each other* raises `NotImplementedError` rather than mis-encoding the cross-references.
- **One context per `Solver`.** In AY's C ABI a `Z3_solver` aliases the context's single solver, so `ayz3` creates one `Z3_context` per `Solver`/`Optimize` and uses a current-context model for bare constructors. For the common "build vars, then make a `Solver`" script this is invisible and matches z3py; mixing expressions across solvers raises a clear error instead of misbehaving.
- **String `Distinct` over length-constrained strings** may return `unknown` where z3 decides `sat`; callers must preserve that third result rather than treating it as a Boolean answer.
- **`SeqRef.as_string()`** returns the raw literal/model bytes; ASCII content matches z3py exactly, but AY does not parse SMT-LIB escape sequences, so non-ASCII/escaped content may differ.
- **Finite-domain performance:** the full **9x9 Sudoku** (81 Int vars, 27 nine-way `Distinct` over linear integer arithmetic) is a known weak spot for AY's CDCL(LIA) engine without dedicated finite-domain reasoning: under the test budget AY returns `unknown`, while the reference z3py run solves it. The 4x4 instance is the bounded, validated example. See `examples/sudoku.py`.
- **Nonlinear arithmetic** (e.g. `Product(x, y)` of two variables) is not decided; AY reports `unknown` on this wrapper path.
- **Set `IsSubset` is deferred.** It requires quantified array reasoning (`forall x. a[x] => b[x]`), so `IsSubset` raises `NotImplementedError`. Direct quantified-array formulas return `unknown` at the wrapper boundary. The other set operations listed above reduce to quantifier-free membership formulas.

The C ABI uses the non-reference-counted context; AY terms are arena-interned and never individually freed, so this binding never relies on `inc_ref`/`dec_ref`. Each native `Z3_context` (and everything interned in it) is freed by a Python finalizer once no wrapper object references its `Context` anymore.

## Platform scope & future work

The build produces a wheel for the **current platform only** (the platform you build on). It is **not** a cross-platform / `manylinux` wheel.

Out of scope for this package (future work):

- Cross-platform / `manylinux` / `delocate`-repaired wheels and CI wheel building.
- Publishing to PyPI.

To use `ayz3` on another OS/arch, build the wheel on that platform from an AY checkout (with a Rust toolchain), or point `AYZ3_LIB` at a `libay_ffi` you built there.

## Development

Run the in-tree test suite against a local `cargo build -p ay-ffi`:

```bash
cargo build -p ay-ffi          # builds target/debug/libay_ffi.{dylib,so}
cd bindings/python
python3 -m pip install -e '.[dev]'
python3 -m pytest tests/       # cross-checked vs real z3py
```

`tests/` and `conftest.py` are dev-only and are not shipped in the wheel.

### Differential verdict/model fuzzer (`ayz3_fuzz/`)

`ayz3_fuzz/` is a differential finding generator: it generates random,
well-typed SMT formulas over toggleable fragments, builds the *same* formula
through both `ayz3` and real `z3py` with a single module-parameterized builder,
checks each, and flags **wrong answers**. Generation is seeded and deterministic,
so any finding reproduces from its `(fragment, seed)`.

**Fragments.** The registered generators cover:

- `qf_lia`, `qf_nia`, `qf_lra`, `qf_bv`, and `arrays`;
- `qf_uflia`, `arr_lia`, `qf_bv_bool`, and `quant_lia` for combined and
  quantified formulas;
- `quant_lra_isint` for quantified real arithmetic with built-in and
  user-shadowed integrality predicates;
- `qf_fp` for Float32/Float64 operations and symbolic rounding modes;
- `sequences` for `(Seq Int)` / `(Seq Bool)` formulas, parsed from the same
  canonical SMT-LIB by both solvers; and
- `recfun` for recursive integer function definitions.

`datatypes` is **skipped honestly**: ayz3 ships a z3py-style `Datatype` builder,
but the fuzzer's datatype formula generator is not implemented yet. Term depth
is configurable via `AYZ3_FUZZ_DEPTH=N`.

**Categorized comparison.** Verdicts:
both-sat / both-unsat = AGREE; either side `unknown` or a binding gap = SKIP.
Findings are classified:

- **A: sat-vs-unsat** — high-priority verdict dispute. Z3 is a cross-check;
  the split alone does not identify the wrong solver.
- **B: wrong-model** — AY returns `sat` but its model FALSIFIES the formula
  (cross-checked by an in-memory pin, rendered-SMT-LIB reparse, and AY's own
  `model.eval(formula)` == False; for array models, AY's self-contradiction plus
  a scalars-pinned/array-free z3 re-check that a valid completion exists).
- **C: partial / unreduced model** — `sat` with a model that can't be pinned (an
  array interp, an unconstrained var, an opaque value). **Not a bug** — counted
  separately, never reported as a finding. The UF arbiter demotes a partial UF
  model (e.g. `f(3*i0) > f(i0)` with only `i0=0` pinned) to C, never B.

```bash
# manual run: agreement / skip / DISAGREE + wrong-model + partial-model counts
python3 -m ayz3_fuzz --fragment qf_lia --count 1000 --seed 0
python3 -m ayz3_fuzz --fragment all --count 1000        # all fragments
# reproduce one exact historical seed
python3 -m ayz3_fuzz --fragment arrays --count 1 --seed 341 --timeout-ms 10000
# categorized inventory campaign -> writes ayz3_fuzz/FINDINGS.md
python3 -m ayz3_fuzz --inventory
python3 -m pytest tests/test_diff_fuzz.py               # bounded pytest gate
```

The pytest gate makes the formerly failing array wrong-`unsat` cases (seeds
341/500/561) and BV wrong-model cases (seeds 5/432/439) hard regression pins.
The array pins require z3 to prove each formula satisfiable and forbid AY from
returning a contradictory definitive verdict. The BV pins require AY's model to
validate through an in-memory z3 pin, a rendered-SMT-LIB reparse, and AY's own
evaluator.

The inventory command writes a local `ayz3_fuzz/FINDINGS.md` report with its
seed ranges, timeout, reference version, agreement/skip counts, and minimized
repros. Preserve that report with the raw run data you intend to cite. A clean
bounded campaign is evidence only for the inputs it actually ran.

## License

Apache-2.0. Copyright 2026 Andrew Yates.
