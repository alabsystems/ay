// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Shared, trust-checkable CORE of the IC3 / PDR inductive-invariant ACCEPTANCE
// decision.
//
// This file holds the single soundness-critical CONJUNCTION the IC3 validator
// runs to admit a candidate safety lemma into the inductive model. A lemma is
// accepted as inductive iff its per-obligation checks ALL hold:
//
//   * self_ind   — Inv(s) /\ T(s,s') => Inv(s')  (consecution: the candidate is
//                                                  closed under the transition)
//   * init_valid — Init(s) => Inv(s)             (the candidate covers every
//                                                  initial state)
//   * entry_ind  — multi-predicate entry inductiveness (trivially true for the
//                                                  single-predicate case)
//
// It is compiled by `cargo` — the real `check_invariants_prove_safety` in
// `safety_proof_inductive.rs` calls it at the admit decision, so the SHIPPED
// validator runs THIS decision — AND it is verified by `offline deductive checker check`
// against the exact same source bytes: the harness
// the development proof harness pulls this file in with
// `include!`, so the proof is over the real code, NO TWIN. Plain `//` comments
// only, so it stays valid when `include!`d into the proof harness.
//
// THE false-accept hole the obligation closes: admitting a candidate where one
// of the conjuncts does NOT hold — most dangerously `self_ind` (consecution). A
// candidate that is NOT closed under T can still cover Init and exclude Bad yet
// permit a transition INTO a bad state, so accepting it without the consecution
// conjunct is a false-SAFE. The bounded model bridge in the proof discharges,
// over a COMPLETE finite transition system, that ANDing exactly these per-
// obligation checks and accepting only on all-true never false-accepts (accept
// => the bad state is genuinely unreachable). Dropping any conjunct here yields
// a falsifying transition system and breaks `offline deductive checker check`.

/// THE soundness-critical per-lemma ACCEPTANCE conjunction of the IC3 validator.
///
/// A candidate safety lemma is admitted into the inductive model iff EVERY
/// per-obligation check holds: `self_ind` (consecution, Inv /\ T => Inv'),
/// `init_valid` (Init => Inv), and `entry_ind` (multi-predicate entry
/// inductiveness). Dropping any conjunct is the false-accept hole; its model-
/// theoretic soundness (accept => bad unreachable) is the obligation discharged
/// in the development proof harness.
///
/// Non-short-circuiting `&` — the inputs are already-evaluated, side-effect-free
/// booleans, so `&` is semantically identical to the `&&` it replaced AND keeps
/// the body straight-line so the bounded-MC exhaustive-finite route can ground
/// the obligation when this function is called from the proof's bridge.
#[inline]
#[must_use]
pub(crate) fn lemma_admitted_inductive(self_ind: bool, init_valid: bool, entry_ind: bool) -> bool {
    self_ind & init_valid & entry_ind
}
