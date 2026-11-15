<!--
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0
Author: Andrew Yates
-->

# ay-encode

**The shared AY-interface crate.** This is the minimal foundation a
downstream model checker consumes to talk to the [AY](https://github.com/alabsystems/ay)
solver. Its consumer is a released sibling in the same constellation:

- **model-checker-consumer** — bit-precise software model checker for Rust (MIR → AY),
  development-only integration. Its native CHC/PDR lane calls
  `invoke`, `verdict` and `proof`.

**ty** — TLA+ model checker (TLA⁺ → AY), development-only integration —
was the second intended consumer. It keeps its own AY-facing encoders and does
not depend on this crate.

`ay-encode` holds one copy of the AY-facing glue (sort/term construction,
portfolio invocation, result normalization, proof handling), so a frontend
depends on it instead of on `ay-bindings` / `ay-chc` directly for the common
path.

## What this crate owns (shared)

| Module             | Role |
|--------------------|------|
| [`sorts`]          | Sort builders over `ay_bindings::Sort`: Bool/Int/Real/BV/Array/Datatype, native `Seq`/`String`, **plus** first-class `set_of` / `map_of` constructors (AY has no native Set/Map sort — these name the Array encoding once). |
| [`terms`]          | Term builders. Scalar/BV/array ops stay on `ay_bindings::Expr`; this adds the four theory wrappers `seq`, `set`, `map`, `string`, so a frontend need not hand-roll them. |
| [`invoke`]         | One `EncodeConfig { engine = Auto, timeout, proof_mode }` and a `solve()` that drives `ay_chc::AdaptivePortfolio` (auto/portfolio) or `ay_chc::engines::solve_pdr_proof` (strict proof). |
| [`verdict`]        | `AyVerdict { Proved(Option<Certificate>), Violated(Model), Unknown(reason) }` — the frontend-neutral normalization of AY's sealed `Safe`/`Unsafe`/`Unknown`. |
| [`proof`]          | `Certificate` + `ProofRun`: the hook that captures AY's CHC proof transcript (model + replay transcript, content-addressed) and, under the `alethe` feature, a SAT-level Alethe export (not implemented yet; see Status). |

## What stays per-project (NOT here)

`ay-encode` has **no** knowledge of MIR or TLA⁺. The boundary is:

> **frontend IR → obligations** is per-project; **obligations → AY** is shared here.

So a consumer keeps its own lowering:

- **model-checker-consumer** keeps `MIR → BmcVc / ChcVc` lowering (`codegen_ay`), its
  `ay_violation_<label>_<N>` BMC naming, the BMC `assert` + OR-of-violations +
  `check-sat` / `get-value` shape, and result → `kani` reporting. It calls into
  `ay-encode` to build the `AYProgram` / `ChcProblem` and to invoke + normalize.

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

`invoke`, `verdict`, `proof`, `quantified` and the query-obligation proof
reports are implemented and tested in this crate. Two surfaces still return
`EncodeError::Unimplemented`: `terms::set::{union, intersect, difference}`,
which need an array-map/lambda primitive on `ay_bindings::Expr`, and
`Certificate::to_alethe` (feature `alethe`), which needs an `ay-chc` bridge to
the PDR run's SAT proof.

## License

Apache-2.0, © 2026 Andrew Yates.
