# ayz3 — JavaScript/Node binding for the AY SMT solver

A z3-shaped JavaScript API over **AY**'s Z3-shaped C API (`libay_ffi`). The
binding builds AST handles and marshals requests; AY computes verdicts and
models for the requests it receives. Correctness also depends on the wrapper's
term encoding, FFI signatures, handle conversions, and ABI assumptions: an
adapter bug can change a problem or result even though JavaScript does not run
the solver algorithm itself.

The source checkout contains **two** working loaders:

1. **Source-checkout WASM harness** (`wasm.mjs` + `test-wasm.mjs`) — a real
   `ay_ffi.wasm` with **no native dependency**, running solves in Node. The npm
   package does not bundle this large build artifact or export the harness;
   build and exercise it from an AY checkout:
   ```sh
   rustup target add wasm32-unknown-unknown
   cargo build --release --target wasm32-unknown-unknown -p ay-ffi --lib --no-default-features
   node bindings/js/test-wasm.mjs      # real sat/unsat/model from the .wasm
   ```
   The module imports one host function (`env.ay_wasm_now_ms`, wired to
   `performance.now()`) and exports the solve surface + an `ay_malloc`/`ay_free`
   staging allocator. Every JIT path falls back to AY's interpreter tier on
   wasm (those fallbacks already run on x86_64 hosts). `test-wasm.mjs` exercises
   this solver path rather than a mock or fixture result.
2. **Node native-FFI** (`_lib.mjs` + `ayz3.mjs`, via [koffi](https://koffi.dev)) —
   the fuller 168-function z3-shaped API, loading the prebuilt `libay_ffi` dylib.

The 168-function signature list is a subset ported from
`bindings/python/ayz3/_lib.py`'s `_SIGS`. The exported C headers and ABI are the
authority; each language binding exposes its own documented subset.

## Declarative search API

The package exports a typed, finite-domain application API at `ayz3/search`:

```js
import { Model } from "ayz3/search";

const m = new Model("assignment");
const worker = m.choice("worker", ["cpu", "gpu"]);
const cost = m.int("cost", 0, 20);
m.table(
  [worker, cost],
  [
    ["cpu", 7],
    ["gpu", 3],
  ],
);
m.minimize(cost);

const result = m.solve();
if (result.status !== "optimal")
  throw new Error(`need a proved optimum, got ${result.status}`);
console.log(result.requireSolution().get(worker)); // gpu
```

`search.d.ts` is a first-class declaration surface. Equation strings are data
parsed by AY's restricted grammar—never JavaScript passed to `eval`. The
`examples/search-*.mjs` programs cover 4x4 Sudoku, an LLM token router, and
Minesweeper.

```sh
# after cargo build -p ay-ffi && (cd bindings/js && npm install)
node bindings/js/examples/search-sudoku.mjs
node bindings/js/examples/search-token-router.mjs
node bindings/js/examples/search-minesweeper.mjs
```

Enumeration is satisfaction-only: `enumerate()` rejects a model after
`minimize()` or `maximize()` instead of silently changing the requested mode.

## Requirements

- Node.js ≥ 18 (developed/verified on Node v26).
- The `libay_ffi` shared library. Build it once from the repo root:
  ```sh
  cargo build -p ay-ffi          # debug -> target/debug/libay_ffi.{dylib,so}
  # or: cargo build -p ay-ffi --release
  ```

## Install & run

```sh
cd bindings/js
npm install          # installs koffi
npm test             # runs the z3-shaped and declarative APIs against AY
```

The loader finds the library via, in order:

1. `AYSEARCH_LIB`, then `AYZ3_LIB` — full path to the
   `.dylib`/`.so`/`.dll` (highest priority);
2. a library bundled next to `_lib.mjs` (installed-package layout);
3. the in-tree Cargo output: `target/{debug,release}/libay_ffi.*`.

## Usage

```js
import { Context } from "./ayz3.mjs";

const ctx = new Context();

// SAT: 3 < x < 6 over the integers
const x = ctx.Int("x");
const s = ctx.Solver();
s.add(x.gt(3), x.lt(6));
console.log(s.check()); // "sat"  (from AY)
console.log(s.model().eval(x).asNumber()); // 4 or 5

// Bit-vectors (8-bit)
const a = ctx.BitVec("a", 8);
const b = ctx.BitVec("b", 8);
const bv = ctx.Solver();
bv.add(a.add(b).eq(ctx.BitVecVal(16, 8)), a.eq(ctx.BitVecVal(10, 8)));
bv.check(); // "sat"
bv.model().eval(b).asNumber(); // 6

// Uninterpreted functions
const Int = ctx.IntSort();
const f = ctx.Function("f", Int, Int);
ctx
  .Solver()
  .add(f.call(x).eq(f.call(ctx.Int("y"))))
  .check();
```

Each `Context` (like a Z3 context) interns a declared constant by its symbol
name, so give each independent problem its **own** `Context` (or use unique
names) to avoid sort clashes.

### API shape (mirrors z3's JS/Python API)

- **`Context(params?)`** — factory. Sorts: `BoolSort/IntSort/RealSort/BitVecSort(n)/ArraySort(d,r)`.
  Constants: `Bool/Int/Real/BitVec(name[,bits])`, `Const(name, sort)`, `FreshConst(sort)`.
  Values: `BoolVal/IntVal/RealVal/BitVecVal/StringVal`.
  Builders: `And/Or/Not/Implies/Xor/Distinct/If/Eq`, `Function(name, ...dom, range)`.
  `Solver()`, `Optimize()`, `version()`, `dispose()`.
- **`Expr`** — `eq/neq`, `add/sub/mul/div/mod/neg`, `lt/le/gt/ge` (Int/Real),
  BV `ult/ule/ugt/uge/slt/sle/sgt/sge/shl/lshr/ashr/extract/concat`,
  `and/or/xor/not` (routed by sort), `select`; inspection
  `isNumeral/asString/asNumber/asBool/sort/toString`. JS numbers are auto-coerced
  to same-sort numerals.
- **`Solver`** — `add/assert`, `push/pop/reset`, `check() → "sat"|"unsat"|"unknown"`,
  `model()`, `reasonUnknown()`, `numScopes()`, `toString()`.
- **`Model`** — `eval(expr, completion=true)`, `numConsts()`, `toString()`.
- **`Sort`**, **`FuncDecl`** (`call(...args)`), **`Optimize`** (`maximize/minimize/check/model`).

## ABI notes (why libz3's own JS binding can't be used)

AY's C ABI is **not** libz3-ABI-compatible: `Z3_ast` is a **`uint64` handle**,
not a `void*` pointer. This binding declares `Z3_ast` as koffi `'uint64'`
(marshaled to/from a JS `Number`, exact for AY's small interned ids); all other
opaque handles are real pointers (`'void *'`). Return code convention is Z3's
`lbool`: `Z3_L_TRUE=1` (sat), `Z3_L_FALSE=-1` (unsat), `Z3_L_UNDEF=0` (unknown).

`_lib.mjs` binds **168** `Z3_*` functions today — config/context, symbols, all
core sorts (bool/int/real/bv/array/string), consts/numerals, boolean &
control ops, full arithmetic, the bit-vector core + extended ops, AST/numeral
inspection, uninterpreted functions, quantifiers, arrays, the solver surface
(assert/push/pop/check/check-assumptions/model/unsat-core), model eval, AST
vectors, params, simplify/substitute, and a core Optimize subset. The dylib
exports ~800 `Z3_*` symbols in total; extend `SIGS` in `_lib.mjs` to bind more.

## Files

| File              | Purpose                                                                 |
| ----------------- | ----------------------------------------------------------------------- |
| `ayz3.mjs`        | Idiomatic, z3-shaped wrapper (Context/Sort/Expr/FuncDecl/Model/Solver). |
| `search.mjs`      | Declarative finite-domain modeling, solving, and optimization API.      |
| `search.d.ts`     | TypeScript declarations for `ayz3/search`.                              |
| `_lib.mjs`        | Low-level koffi binding: library loader + native function signatures.   |
| `test.mjs`        | Node test: SAT (x∈{4,5}), UNSAT, BitVector, Real+push/pop, UF.          |
| `test-search.mjs` | Search API, ownership, status, enumeration, and hardening tests.        |
| `package.json`    | Package metadata; `npm test` runs both API suites.                      |

`test.mjs` exercises the native-FFI encoding and result mapping for the cases
listed above. `test-wasm.mjs` separately exercises SAT, UNSAT, and model cases
through the WASM loader. They test named slices of the adapter boundary; they
do not establish correctness for all 168 bindings or every supported term.

## WASM (working)

A pure `ay_ffi.wasm` with **no native dependency** now builds and runs real
solves. What it took (all `cfg(target_arch = "wasm32")`-gated, so the host build
is byte-identical):

- **`ay-jit`** — the native machine-code JIT — is arch-gated to native ISAs. AY
  already keeps an **interpreter fast-path for every JIT entry point** (the
  conflict/minimize/simplex JITs are aarch64-only, so those interpreters already
  run on x86_64 hosts). On wasm every path takes the interpreter; the
  `test-wasm.mjs` SAT/UNSAT/model cases exercise that path. Correctness remains
  subject to the WASM adapter and host ABI. `executable.rs` reports
  `NoNativeIsa` on non-macos/linux.
- **Clock** — `Instant::now()` panics on wasm32-unknown-unknown, so a shim
  (`ay_core::time::Instant`, host = `std::time::Instant` re-export) backs it with
  an imported `env.ay_wasm_now_ms` (wired to `performance.now()`).
- **Threads** — the solve path is single-threaded; the two deadline/watchdog
  `thread::spawn` sites are wasm-gated (wall-clock timeouts are simply not
  installed on wasm). `test-wasm.mjs` covers terminating examples, not timeout
  behavior.
- **Allocator** — `ay_malloc`/`ay_free` are exported so JS can stage input SMT
  strings into linear memory.

```sh
rustup target add wasm32-unknown-unknown
cargo build --release --target wasm32-unknown-unknown -p ay-ffi --lib --no-default-features
node bindings/js/test-wasm.mjs   # → real sat/unsat/model from ay_ffi.wasm
```

| file            | role                                                                       |
| --------------- | -------------------------------------------------------------------------- |
| `wasm.mjs`      | Instantiates `ay_ffi.wasm` (imports `ay_wasm_now_ms`) + string marshaling. |
| `test-wasm.mjs` | Exercises SAT, UNSAT, and model cases inside the `.wasm`.                  |
