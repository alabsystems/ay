# AY Java binding

A Java binding over AY's **Z3-shaped C API** (`libay_ffi`), analogous to the
Java binding that ships with Z3 (`com.microsoft.z3`). It is **purely additive**:
new files under `bindings/java/`, no change to the solver or the C ABI.

It is a second-language binding over the same C ABI that
[`ayz3`](../python) (the Python binding) targets.

## Design: pure-Java FFM

The binding uses the **Java FFM API** (`java.lang.foreign`: `Linker`,
`SymbolLookup`, `FunctionDescriptor`, `MethodHandle`, `MemorySegment`, `Arena`) —
pure Java, **no JNI C stubs**. FFM is stable in Java 22+ (this repo uses
openjdk 26), mirroring how `ayz3` uses Python `ctypes`.

The Java layer builds AST handles and marshals calls across the FFI; AY performs
the solving. Correctness still depends on the wrapper's term encoding, FFI
signatures, handle conversions, status mapping, and ABI assumptions. A binding
bug can therefore change either the request or the reported result.

### ABI note

AY's C ABI is **not** libz3-ABI-compatible: `Z3_ast` is a `uint64_t` *handle*
(not a `void*`). It therefore maps to `JAVA_LONG` (carried as a Java `long`),
**not** `ADDRESS`. Every other opaque handle (`Z3_context`, `Z3_sort`,
`Z3_solver`, `Z3_model`, `Z3_symbol`, `Z3_func_decl`, `Z3_config`) is a real
pointer and maps to `ADDRESS`.

## Files

| File | Purpose |
|------|---------|
| `src/ay/z3/Native.java` | Low-level layer: loads the dylib, binds a CORE set of 76 `Z3_*` functions to `MethodHandle`s, string marshalling helpers. |
| `src/ay/z3/Context.java` | OO wrapper: owns the native ctx + `Arena`; sort/const/numeral factories and `mkAnd`/`mkAdd`/`mkLt`/… operator methods. |
| `src/ay/z3/Sort.java` | Wraps a `Z3_sort`. |
| `src/ay/z3/Expr.java` | Wraps a `Z3_ast`; `toString()` (`ast_to_string`), `asLong()` (`get_numeral_int64`). |
| `src/ay/z3/BoolExpr.java`, `ArithExpr.java`, `BitVecExpr.java` | Sort-typed `Expr` subtypes (ArithExpr covers Int/Real). |
| `src/ay/z3/Solver.java` | `add`/`push`/`pop`/`check`/`getModel`/`reset`/`toString`. |
| `src/ay/z3/Model.java` | `eval`, `toString`. |
| `src/ay/z3/Status.java` | `SATISFIABLE`/`UNSATISFIABLE`/`UNKNOWN` enum. |
| `src/ay/z3/AyZ3Exception.java` | Unchecked exception (mirrors z3py `Z3Exception`). |
| `src/ay/z3/Test.java` | End-to-end test: LIA SAT/UNSAT, Bool, BitVector SAT/UNSAT, push/pop. |
| `run.sh` | Sets the JDK on PATH, compiles with `javac`, runs the test against `libay_ffi`. |

No external Java dependencies (no JNI, no build tool) — only a JDK 22+.

## Bound function coverage (76)

Config/context lifecycle, symbols, sorts (Bool/Int/Real/BV), consts & numerals,
Boolean ops (`and`/`or`/`not`/`eq`/`implies`/`iff`/`xor`/`ite`/`distinct`),
arithmetic (`add`/`sub`/`mul`/`unary_minus`/`div`/`mod`/`lt`/`le`/`gt`/`ge`),
bitvector core (`bvadd`/`bvsub`/`bvmul`/`bvudiv`/`bvurem`/`bvand`/`bvor`/`bvxor`/
`bvshl`/`bvlshr`/`bvnot`/`bvneg` plus all unsigned/signed comparisons), solver,
model (`model_eval`/`model_to_string`), stringify (`ast_to_string`), numeral read
(`get_numeral_string`/`get_numeral_int64`), and error code.

Adding a function is mechanical: translate its C prototype to a
`FunctionDescriptor` and add one `h("Z3_name", descriptor)` field in
`Native.java`, then a thin `mk*` method on `Context`.

## Build & run

```sh
# 1. Build the AY FFI library (produces target/debug/libay_ffi.dylib).
cargo build -p ay-ffi

# 2. Build and run the Java test (auto-points AYZ3_LIB at target/debug).
bash bindings/java/run.sh            # or: bash bindings/java/run.sh --release
```

`run.sh` prepends the Homebrew openjdk (26) to `PATH`, sets `AYZ3_LIB` to the
freshly built library, and runs with `--enable-native-access=ALL-UNNAMED` (FFM's
downcalls are "restricted" methods).

Expected output for these named smoke cases:

```
AY Java (FFM) binding test
  bound Z3_* functions: 76
  PASS: lia_sat:check -> SATISFIABLE
  PASS: lia_sat:model_x_in_{4,5} (got 4)
  PASS: lia_unsat:check -> UNSATISFIABLE
  PASS: bool_sat:check -> SATISFIABLE
  PASS: bool_unsat:check -> UNSATISFIABLE
  PASS: bv_sat:check -> SATISFIABLE
  PASS: bv_sat:model_x==255 -> 255
  PASS: bv_unsat:check -> UNSATISFIABLE
  PASS: push_pop:base_sat -> SATISFIABLE
  PASS: push_pop:scoped_unsat -> UNSATISFIABLE
  PASS: push_pop:after_pop_sat -> SATISFIABLE
All Java binding tests passed.
```

## Example

```java
import ay.z3.*;

try (Context ctx = new Context()) {
    ArithExpr x = ctx.mkIntConst("x");
    Solver s = ctx.mkSolver();
    s.add(ctx.mkGt(x, ctx.mkInt(3)));
    s.add(ctx.mkLt(x, ctx.mkInt(6)));
    if (s.check() == Status.SATISFIABLE) {
        Model m = s.getModel();
        System.out.println("x = " + m.eval(x, true).asLong());  // 4 or 5
    }
}
```
