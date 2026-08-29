<!--
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0
Author: Andrew Yates
-->

# ay-encode

**The one shared AY-interface crate.** This is the single, minimal foundation
that downstream model checkers consume to talk to the [AY](https://github.com/alabsystems/ay)
solver. Its consumers are released siblings in the same constellation:

- **model-checker-consumer** — bit-precise software model checker for Rust (MIR → AY),
  development-only integration, and
- **ty** — TLA+ model checker (TLA⁺ → AY), development-only integration.

Before this crate, each project carried its own copy of the AY-facing glue
(sort/term construction, portfolio invocation, result normalization, proof
handling). `ay-encode` is the *approved minimal-sharing design*: exactly one
copy of that glue lives here, and the two frontends depend on it instead of on
`ay-bindings` / `ay-chc` directly for the common path.

## What this crate owns (shared)

| Module             | Role |
|--------------------|------|
| [`sorts`]          | Sort builders over `ay_bindings::Sort`: Bool/Int/Real/BV/Array/Datatype, native `Seq`/`String`, **plus** first-class `set_of` / `map_of` constructors (AY has no native Set/Map sort — these name the Array encoding once). |
| [`terms`]          | Term builders. Scalar/BV/array ops stay on `ay_bindings::Expr`; this adds the four theory wrappers ty currently hand-rolls — `seq`, `set`, `map`, `string` — so both frontends share one encoding. |
| [`invoke`]         | One `EncodeConfig { engine = Auto, timeout, proof_mode }` and a `solve()` that drives `ay_chc::AdaptivePortfolio` (auto/portfolio) or `ay_chc::engines::solve_pdr_proof` (strict proof). |
| [`verdict`]        | `AyVerdict { Proved(Option<Certificate>), Violated(Model), Unknown(reason) }` — the frontend-neutral normalization of AY's sealed `Safe`/`Unsafe`/`Unknown`. |
| [`proof`]          | `Certificate` + `ProofRun`: the hook that captures AY's CHC proof transcript (model + replay transcript, content-addressed) and, under the `alethe` feature, a SAT-level Alethe export for re-checking. |

## What stays per-project (NOT here)

`ay-encode` has **no** knowledge of MIR or TLA⁺. The boundary is:

> **frontend IR → obligations** is per-project; **obligations → AY** is shared here.

So each consumer keeps:

- **model-checker-consumer** keeps `MIR → BmcVc / ChcVc` lowering (`codegen_ay`), its
  `ay_violation_<label>_<N>` BMC naming, the BMC `assert` + OR-of-violations +
  `check-sat` / `get-value` shape, and result → `kani` reporting. It calls into
  `ay-encode` to build the `AYProgram` / `ChcProblem` and to invoke + normalize.
- **ty** keeps `TLA⁺ → TlaSort / TlaExpr` translation, its BMC / k-induction
  driver state (`BmcRunResult`, `KInductionResult`, `PdrRunResult`), and the
  genuinely TLA-specific encoders (`record_encoder`, `powerset_encoder`,
  `nested_powerset`). It calls into `ay-encode`'s term builders to replace its
  four hand-rolled theory encoders (`sequence_encoder`, `finite_set`,
  `function_encoder`, `string_intern`), and into `invoke` / `verdict` / `proof`
  for the portfolio, PDR, and proof boundary.

## Dependencies

A leaf crate over three workspace members:

- `ay-bindings` — typed builder surface (`Sort` / `Expr` / `AYProgram`, Horn +
  BMC presets). Re-exports `ay_core::{Sort, quote_symbol, panic_payload_to_string}`.
- `ay-chc` — CHC problem model, `AdaptivePortfolio`, `solve_pdr_proof`, the
  sealed `VerifiedChcResult`, and the proof-transcript types.
- `ay-core` — core sorts + symbol quoting.

Optional feature `alethe` pulls in `ay-proof` for SAT-level Alethe certificate
export. Off by default to keep the foundation minimal.

## Status

This is the **foundation skeleton**. Public types and signatures are real and
compile; bodies that depend on the full port are `todo!()` and flagged in their
doc comments (e.g. native `seq.++` / `str.len` wrappers awaiting the primitive
on `ay_bindings::Expr`, and the proof-run → verdict wiring). No frontend code is
migrated here yet — model-checker-consumer and ty are untouched.

## License

Apache-2.0 OR MIT, © 2026 Andrew Yates.
