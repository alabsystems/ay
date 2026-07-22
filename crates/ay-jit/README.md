# ay-jit

Native-code and solver-program compilation infrastructure for the ay SMT
solver. It emits machine code for selected helper paths: SAT conflict
processing and inprocessing helpers, theory bound propagation, guarded simplex
update paths, DPLL(T) theory dispatch, and CHC expression evaluation.

## What lives here today

### SAT native-code support

| Module | Role |
|--------|------|
| `conflict_jit` | Production native 1UIP conflict literal processing in `ay-sat` |
| `minimize_jit` | Native conflict-clause minimization helper |
| `simd_inprocess` | SIMD batch literal scanning for inprocessing helpers |
| `batch` | BV bit-blasting batch clause conversion helpers |
| `code_cache` | Executable-memory arena + eviction |
| `executable` | `mmap` + `MAP_JIT` wrapper |
| `aarch64`, `x86_64` | Platform assemblers |

The old SAT propagation compiler (`CompiledFormula`, per-variable propagation
functions, detached compiled watches, full-propagation native code, and related
PGO policy) was removed from the `ay-sat` production path in #8517, and the
retired propagation prototypes have been deleted from this crate. The
active SAT propagation path is standard 2-watched-literal BCP; native-code work
that affects SAT-COMP must be measured as a non-BCP optimization unless and
until a new production integration lands.

### Theory Native-Code Support (production, used by `ay-theories` and `ay-dpll`)

| Module | Role |
|--------|------|
| `theory_prop`, `theory_prop_native` | LRA/LIA bound propagation |
| `theory_dispatch` | O(1) theory-atom dispatch for DPLL(T) |
| `simplex_jit` | Guarded simplex pivot/update kernels with checked fallbacks |
| `expr_eval` | Compiled CHC expression evaluation |

## Learned-clause profiling (profile-only, #8791 / #8268)

The current learned-clause surface is a deterministic profiling and descriptor
contract for offline evaluation. It is not a SAT propagation dispatch
surface.

### Current crate surface

`learned_clause_emit` extracts proof-safe, profile-hot learned-clause
descriptors and records scalar fallbacks/rejections for clauses that cannot be
studied safely. All descriptors are profile-only and never executed, and
`LEARNED_CLAUSE_NATIVE_DISPATCH_ENABLED` is `false`.

```rust
use ay_jit::{
    emit_learned_clause, LearnedClauseCodegenContext, LearnedLiteral, LearnedTrail,
    LearnedLitValue, PropagatorResult,
};

let mut cx = LearnedClauseCodegenContext::new();
let clause = [LearnedLiteral::new(0, true), LearnedLiteral::new(1, false)];
let prop = emit_learned_clause(&clause, &mut cx);

let mut trail = LearnedTrail::new(2);
trail.assign(0, LearnedLitValue::False);
assert_eq!(prop.check(&trail), PropagatorResult::Unit(LearnedLiteral::new(1, false)));
```

- Module: [`learned_clause_emit`] — `emit_learned_clause`,
  `LearnedClausePropagator`, `PropagatorResult { Unit, Falsified, NoOp }`.
- Module: [`batch_recompile`] — `RecompileScheduler`, `BatchRecompileBudget`,
  `LearnedClauseMeta`. Decides *when* to fire batches and *which* clauses to
  profile (top-K by activity, shorter-first as tiebreaker).

**Not wired to `ay-sat` dispatch.** The scalar watched-literal solver remains
the only propagation/proof authority.

### Required gates before any native learned-clause dispatch

- A maintained native lowering with a scalar fallback.
- Differential tests against `learned_clause_emit::interpret_clause`.
- Proof/witness preservation and scalar fallback on any unsupported state.
- Clause deletion/mutation invalidation before a descriptor can execute.
- Telemetry that reports profile candidates separately from native applies.
- A fail-closed competition gate that disables native dispatch when any required
  evidence is missing.

### Future profile work

- Feed real solver snapshots into the descriptor extractor without installing
  code.
- Export candidate/fallback/rejection counters to stats JSON.
- Build offline reducers that compare native candidates against the interpreted oracle.

## Integration map

- `ay-sat` uses `conflict_jit` for non-BCP conflict-analysis work.
- `ay-dpll` uses `TheoryDispatchTable` for O(1) theory-atom dispatch during
  BCP when the `jit` feature is enabled.
- `ay-theories` (LRA) uses `TheoryPropJit`, `NativeVarPropagator`, guarded
  `PivotRowCache` paths with checked fallbacks.
- `ay-chc` uses `expr_eval::compile_expr` for JIT-compiled expression
  evaluation in the implication cache.

## Testing

```bash
cargo test -p ay-jit --lib learned_clause_emit   # profile descriptor + oracle API
cargo test -p ay-jit --lib batch_recompile       # profile batch scheduler
cargo test -p ay-jit                             # full suite
```
