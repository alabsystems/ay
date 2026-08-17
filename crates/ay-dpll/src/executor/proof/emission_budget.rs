// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Rendering-work cap for the SYNTHESIZED-DEFAULT Alethe certificate's
/// emission phase (#A2b), in abstract printer work units (roughly bytes
/// touched by term formatting and surface-tautology re-derivation).
///
/// Sibling of `DEFAULT_PROOF_RECONSTRUCTION_STEP_BUDGET` in `ay::run`: the
/// by-default `<input>.alethe` is best-effort, so after a fast UNSAT verdict
/// the emission must terminate in bounded time — a certificate within the
/// budget, or the honest "no proof certificate emitted" warning (QF_ALIA
/// pp-family: 2s solves whose emission ground for 300s+ without completing).
/// Deterministic (work units, not wall time). Ordinary explicit `--proof`,
/// `--strict-proofs`, `--self-check`, and `(get-proof)` paths remain uncapped;
/// the query-sealed finite-enum exception deliberately uses the same 64 MiB
/// ceiling on every export path because its bounded authority contract must
/// hold independently of which API requests the diagnostic text.
///
/// Calibration (#A2b-recal): store-chain (dis)equality UNSAT proofs render the
/// array-extensionality witness (`__ay_arr2lia_k` choice term inside a nested
/// read-over-write `ite`) as a tree, not a DAG, so a handful of proof steps
/// balloon to hundreds of MB of surface — measured 821 MB / ~1 GB on the
/// QF_ALIA `ios_t1_*` family, at which point the whole best-effort document is
/// discarded anyway (whole-document rejection on exhaustion). At 2 GB the
/// "bounded time" contract failed: `ios_*00004` ground out a full 821 MB proof
/// (~2.8s) and `ios_*00005` rendered ~1 GB before giving up (~5.9s), both AFTER
/// a sub-0.2s UNSAT verdict. A best-effort text certificate over tens of MB is
/// impractical for any downstream checker, so bound rendering to 64 MiB of
/// surface: normal proofs (KB–single-digit MB — every carcara-checked test
/// proof included) are untouched and still fully emitted; only the pathological
/// tree-expansions truncate early to the honest "no proof certificate emitted"
/// warning. The verdict is already out and unchanged either way.
pub(super) const DEFAULT_ALETHE_EMISSION_WORK_BUDGET: u64 = 64 * 1024 * 1024;
