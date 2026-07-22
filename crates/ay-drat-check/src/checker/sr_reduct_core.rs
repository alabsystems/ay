// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Shared, trust-checkable CORE of the native PR/SR reduct decision.
//
// This file holds the single soundness-critical CLASSIFICATION the PR/SR kernel
// runs: `classify_reduct`. It is compiled by `cargo` — the real
// `reduce_clause_under_subst` in `sr.rs` calls it, so the SHIPPED checker runs
// THIS decision — AND it is verified by `offline deductive checker check` against the exact
// same source bytes: the development proof harness pulls this file in
// with `include!`, so the proof is over the real code, NO TWIN. Plain `//`
// comments only, so it stays valid when `include!`d into the proof harness.
//
// A reduct CLASS is a `u8` CODE mirroring `enum Reduce` in `sr.rs`:
//   0 = Satisfied, 1 = NotReduced, 2 = Reduced, 3 = Contradiction.

// THE soundness-critical CLASSIFICATION of a clause under the substitution sigma.
//
// Given the per-literal tally of the clause's images under sigma — whether any
// literal mapped to the constant True (`any_true`), how many mapped to the
// constant False (`falsified`), how many are sigma-fixed (`identity`), and the
// clause `size` — decide the reduct class. THE skip/reject decision of the PR/SR
// kernel routes through here, so a wrong answer here is the false-accept hole:
//
//   * True present   -> Satisfied (0): the reduct is valid; the clause is SKIPPED.
//   * else all-False -> Contradiction (3): the reduct is the empty clause.
//   * else all-fixed -> NotReduced (1): D|sigma == D; SKIPPED (D is in F already).
//   * else           -> Reduced (2): a real RUP check is required.
//
// The True / all-False / all-fixed priority is byte-identical to the original
// short-circuit order of `reduce_clause_under_subst`. The two SKIP outcomes
// (Satisfied, NotReduced) are exactly the no-false-accept-critical cases; their
// model-theoretic soundness is the obligation discharged in
// the development proof harness.
#[inline]
#[must_use]
pub(crate) fn classify_reduct(
    any_true: bool,
    falsified: usize,
    identity: usize,
    size: usize,
) -> u8 {
    if any_true {
        0 // Satisfied
    } else if falsified == size {
        3 // Contradiction
    } else if identity == size {
        1 // NotReduced
    } else {
        2 // Reduced
    }
}
