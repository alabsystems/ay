# AY C++ bindings (`ay.hpp`)

A **header-only**, [`z3++.h`](https://github.com/Z3Prover/z3/blob/master/src/api/c++/z3%2B%2B.h)-style
C++ wrapper over AY's Z3-shaped C API
(`crates/ay-ffi/include/ay_z3_compat.h`). It lets C++ consumers build and solve
SMT problems with RAII handles and operator overloads, the same way libz3's C++
API is used.

## Usage

```cpp
#include "ay.hpp"          // also pulls in ay.h + ay_z3_compat.h
using namespace ay;

context c;
expr x = c.int_const("x");
expr y = c.int_const("y");

solver s(c);
s.add(x > c.int_val(0));
s.add((x + y == c.int_val(10)) && (x - y == c.int_val(4)));

if (s.check() == sat) {
    model m = s.get_model();
    int64_t vx = 0;
    m.eval(x).as_int64(&vx);   // vx == 7
}
```

Compile and link against the ay-ffi static (or dynamic) library:

```sh
# macOS
clang++ -std=c++17 \
  -I /path/to/ay/crates/ay-ffi/include \
  -I /path/to/ay/bindings/cpp \
  my_consumer.cpp \
  /path/to/ay/target/debug/libay_ffi.a \
  -framework Security -framework CoreFoundation -lresolv \
  -lpthread -lm -o my_consumer
```

## What the wrapper covers

RAII classes over the C handles:

| C++ class    | Wraps          | Notes                                            |
|--------------|----------------|--------------------------------------------------|
| `config`     | `Z3_config`    | owns / frees the config                          |
| `context`    | `Z3_context`   | owns / frees everything derived from it          |
| `sort`       | `Z3_sort`      | `bool/int/real/bv/array/uninterpreted`           |
| `expr`       | `Z3_ast`       | terms; operator overloads                        |
| `func_decl`  | `Z3_func_decl` | `operator()` for applications                    |
| `model`      | `Z3_model`     | `eval`, `to_string`, `num_consts`                |
| `solver`     | `Z3_solver`    | `add/check/get_model/push/pop`, assumptions      |

Operator overloads on `expr`:

* arithmetic: `+ - * /`, unary `-`
* comparison: `< <= > >=`
* boolean: `&& || !`
* bitvector: `& | ^`
* free functions: `operator==`, `operator!=`, `implies`, `ite`, `distinct`,
  `mk_and`, `mk_or`, `select`, `store`

Sorts/constants/literals via `context`: `bool/int/real/bv/array/uninterpreted`
sorts; `bool/int/real/bv` consts; `bool_val/int_val/real_val/bv_val` literals;
`function(...)` for uninterpreted functions.

## Adapter and correctness boundary

This is a thin adapter over the `Z3_*` C entry points. It adds no independent
solving logic or term-rewriting pass: after the wrapper has encoded a request,
AY's core computes the verdict and model. Correctness still depends on the
wrapper selecting the right entry points, preserving sorts and handles, and
honoring the C ABI and lifetime rules. A bug at that boundary can mis-encode a
problem even though the wrapper does not solve it itself.

* **Memory:** a `context` owns its `Z3_context` and frees it in its destructor,
  which frees every sort/ast/solver/model derived from it (AY arena ownership).
  `Z3_ast` handles are arena-interned and never individually freed, so
  `expr`/`sort`/`func_decl`/`model` are trivially-copyable value handles — no
  per-AST reference counting.
* **Lifetime:** handles borrow their `context` and must not outlive it (same
  contract as z3++).
* **Errors:** fallible builders that the C API would surface as a null handle +
  error code instead throw `ay::exception` carrying the C error message, so a
  consumer never silently builds on a null term.

## Tests

`cpp_consumer.cpp` is a smoke test for that boundary. It builds tiny QF_LIA /
QF_UF / QF_BV / array / boolean problems through the wrapper, checks
satisfiability, and asserts the expected verdicts. It is wired into the cargo
test harness:

```sh
cargo test -p ay-ffi --test group_ffi cpp_consumer
```

The test compiles `cpp_consumer.cpp` with the system C++ compiler, links it
against `libay_ffi.a`, runs it, and verifies the covered operations. If the
static library is absent it falls back to a compile-only header check, which
checks declarations but not runtime encoding or ABI behavior.
