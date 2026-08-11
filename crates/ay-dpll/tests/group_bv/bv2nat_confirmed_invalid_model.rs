// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression guard: a `bv2nat` bridge `sat` must publish a model that actually
//! satisfies the authored assertions.
//!
//! Red before the one-line `model/output.rs` fix that ships with this file,
//! green after. The verdict was right and the witness was a lie.
//!
//! ```smt2
//! (set-logic ALL)
//! (declare-const k (_ BitVec 8))
//! (declare-const L Int)
//! (assert (= L (bv2nat k)))
//! (assert (= L 5))
//! (assert (= k #x05))     ; <- literally pins k
//! (check-sat) (get-model)
//! ```
//!
//! AY answers `sat` — which is CORRECT, `bv2nat(#x05) = 5` — but prints
//! `k = #x00`, contradicting the explicit assertion `(= k #x05)`, and
//! `(= L (bv2nat k))` reads `5 = 0`. Under `--stats` the gate reports
//! `:model_check_gate.result "confirmed-sat"`: this is a FALSE CONFIRM, not a
//! coverage gap. Reproduced 3/3.
//!
//! What makes it narrow — and what any fix must preserve — is that the
//! two-assertion subsets are handled correctly:
//!
//! ```text
//! L = bv2nat(k) /\ k = #x05           -> soundness gate CATCHES it -> unknown
//! L = bv2nat(k) /\ L = 5              -> unknown (incomplete)
//! L = bv2nat(k) /\ L = 5 /\ k = #x05  -> sat + INVALID model, gate confirms
//! ```
//!
//! So adding the third (redundant, consistent) assertion flips the gate from
//! catching to confirming. `:model-validation-skips 4` and
//! `:model_completion.recovered 1` on the failing run point at the model
//! completion/recovery path rather than at BV evaluation itself.
//!
//! This is not a wrong SAT — the verdict is right — but a published `sat` whose
//! `get-model` output falsifies an authored assertion is a false witness, and
//! any consumer that trusts `get-model` is misled by it.
//!
//! ## The fix
//!
//! `get-model` was reading the BitVec value out of the EUF model. In this query
//! `k` has no BV assignment (it occurs only inside `bv2nat(k)` plus the pin), so
//! the EUF lookup produced the default `#x00` and printed it as though it were a
//! witness. `model/output.rs` already skipped that EUF-first lookup for
//! `Int | Real | Seq(_)`, for the same reason — the comment there records that
//! consulting EUF first "leaked bare `@ay-seq!N` identifiers and made get-model
//! disagree with get-value". BitVec belongs in that list:
//!
//! ```text
//! -   if !matches!(info.sort, Sort::Int | Sort::Real | Sort::Seq(_)) {
//! +   if !matches!(info.sort, Sort::Int | Sort::Real | Sort::Seq(_) | Sort::BitVec(_)) {
//! ```
//!
//! This is display-only: it changes which source `get-model` prints from, never
//! a verdict. Note the gate is NOT exonerated by the fix — it still reported
//! `confirmed-sat` for a model it had not fully checked. Repairing the printed
//! witness removes the false witness; making the gate refuse to confirm while
//! skipping an authored assertion is separate, still-open work.

/// A published model must satisfy every authored assertion. Here it does not.
///
/// Deliberately asserts on the MODEL, not the verdict: `sat` is the right
/// verdict, so a test that demanded `unsat`/`unknown` would be wrong and would
/// block the correct answer. `unknown` is acceptable (fail-closed); `sat` with a
/// model that contradicts `(= k #x05)` is not.
#[test]
fn bv2nat_bridge_sat_model_must_satisfy_the_pinned_bitvector() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (= L 5))
        (assert (= k #x05))
        (check-sat)
        (get-model)
    "#;
    let output = crate::common::solve(smt);

    // Fail-closed is fine. Only a `sat` obliges the model to be a real witness.
    if !output.contains("sat") || output.contains("unsat") || output.contains("unknown") {
        return;
    }

    assert!(
        !output.contains("(define-fun k () (_ BitVec 8) #x00)"),
        "published `sat` with a model that FALSIFIES the authored assertion \
         `(= k #x05)`: the model binds k = #x00, and `(= L (bv2nat k))` then \
         reads 5 = 0. The independent model-check gate reports \
         `:model_check_gate.result \"confirmed-sat\"` for this, so it is a false \
         confirm, not a coverage gap.\n\nfull output:\n{output}"
    );

    // Positive form of the same requirement, so a differently-wrong binding
    // (e.g. #x01) is caught too rather than sliding past the negative check.
    assert!(
        output.contains("(define-fun k () (_ BitVec 8) #x05)"),
        "published `sat` but the model does not bind k to the only value the \
         assertions permit (#x05).\n\nfull output:\n{output}"
    );
}

/// CONTROL: the two-assertion subset is already handled correctly today.
///
/// Pins the behaviour a fix must not break — the soundness gate catches the
/// invalid model here and fails closed to `unknown`.
#[test]
fn bv2nat_bridge_two_assertion_subset_is_not_wrongly_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (= k #x05))
        (check-sat)
        (get-model)
    "#;
    let output = crate::common::solve(smt);
    assert!(
        !output.contains("(define-fun k () (_ BitVec 8) #x00)"),
        "the two-assertion subset must not publish a model binding k = #x00 \
         while `(= k #x05)` is asserted\n\nfull output:\n{output}"
    );
}

/// CONTROL: plain QF_BV, no `bv2nat` bridge, must keep answering correctly.
///
/// Isolates the defect to the bridge: without `bv2nat` the same pin is modelled
/// correctly, so a fix that degrades this has overreached.
#[test]
fn plain_bitvector_pin_still_models_correctly() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const k (_ BitVec 8))
        (assert (= k #x05))
        (check-sat)
        (get-model)
    "#;
    let output = crate::common::solve(smt);
    assert!(
        output.contains("sat") && !output.contains("unsat"),
        "plain QF_BV pin must be sat\n\nfull output:\n{output}"
    );
    assert!(
        output.contains("(define-fun k () (_ BitVec 8) #x05)"),
        "plain QF_BV pin must model k = #x05\n\nfull output:\n{output}"
    );
}
