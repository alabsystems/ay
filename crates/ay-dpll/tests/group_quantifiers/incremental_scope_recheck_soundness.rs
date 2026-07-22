// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Incremental re-check soundness under push scopes with quantifier-lane
//! nested probes (#qmg-incr-bv-scope-leak).
//!
//! REGRESSION (wrong UNSAT, found 2026-07-18 via deductive-checks's broadcast-vacuity
//! consistency probes): inside a push scope, a satisfiable set containing an
//! exhaustively-provable BV8 guarded square lemma answered `sat` on the first
//! `(check-sat)` and **`unsat`** on an immediate re-check of the SAME scope —
//! popping the scope flipped it back to `sat`. Root cause: quantifier-lane
//! nested probe solves (the closed-universal validity precheck, the
//! quantified-model fail-closed gate's universal confirm, and the
//! result-mapping disambiguation re-solves) swap `ctx.assertions` to a probe
//! set and save/restore `incr_theory_state`, but not the persistent BV
//! incremental state (`incr_bv_state`). The probe (a skolemized NEGATED
//! matrix, unsatisfiable by itself for a valid forall) was encoded into the
//! OUTER persistent BV SAT solver as a scope-level activation, which the next
//! `(check-sat)` in the same scope replayed as an assumption — deriving a
//! bogus theory lemma `(not ground) ∨ (not forall)` and a wrong `unsat`.
//!
//! The converse direction is equally unsound: with a SHARED persistent BV
//! state, a nested probe is solved UNDER the outer scope's activations, so a
//! probe expected to be independently decided (e.g. a CE-lemma refutation
//! that flips a verdict to Sat) can be spuriously UNSAT — a wrong-SAT channel.
//!
//! FIX: every nested isolated solve that takes `incr_theory_state` now also
//! takes/restores `incr_bv_state`, and the quantified clean-window
//! save/restore in `check_sat_internal` includes it.

use ntest::timeout;

/// The guarded BV8 square lemma: |x| <= 11 ==> x*x >=s 0. Valid under
/// wrapping 8-bit semantics (11^2 = 121 <= 127; 12^2 wraps negative), and
/// exhaustively provable by BV-MBQI (width 8 <= BV_EXHAUSTIVE_MAX_WIDTH).
const GUARDED_SQ_FORALL: &str = "(assert (forall ((gx (_ BitVec 8))) (or (bvsle #x00 (bvmul gx gx)) (not (bvsle #xf5 gx)) (not (bvsle gx #x0b)))))";

fn assert_results(smt: &str, expected: &[&str], label: &str) {
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results, expected,
        "{label}: expected {expected:?}, got {results:?}"
    );
}

/// The minimized wrong-UNSAT exhibit: push, check (sat), re-check must stay
/// sat — no assertions were added between the checks.
#[test]
#[timeout(60000)]
fn bv8_guarded_forall_recheck_in_scope_stays_sat() {
    let smt = format!("(set-logic ALL)\n{GUARDED_SQ_FORALL}\n(push 1)\n(check-sat)\n(check-sat)\n");
    assert_results(
        &smt,
        &["sat", "sat"],
        "re-check of an unchanged pushed scope",
    );
}

/// The deductive-checks revalidation shape: ground facts + the lemma, then entailed
/// (here literally `true`) instances asserted between the checks. The
/// re-check must stay sat, and popping the scope must too.
#[test]
#[timeout(60000)]
fn bv8_guarded_forall_recheck_after_entailed_instances_stays_sat() {
    let smt = format!(
        "(set-logic ALL)\n\
         (declare-const v (_ BitVec 32))\n\
         (assert (= v #x00000005))\n\
         {GUARDED_SQ_FORALL}\n\
         (push 1)\n\
         (assert true)\n\
         (check-sat)\n\
         (assert true)\n\
         (assert true)\n\
         (assert true)\n\
         (check-sat)\n\
         (pop 1)\n\
         (check-sat)\n"
    );
    assert_results(
        &smt,
        &["sat", "sat", "sat"],
        "revalidation-shaped re-check inside a pushed scope",
    );
}

/// Control: the genuinely UNSAT variant (unguarded BV8 square lemma is
/// falsified at 12) must still be refuted on both checks — the fix must not
/// weaken the refutation direction.
#[test]
#[timeout(60000)]
fn bv8_unguarded_false_forall_still_unsat_on_recheck() {
    let smt = "(set-logic ALL)\n\
               (assert (forall ((gx (_ BitVec 8))) (bvsle #x00 (bvmul gx gx))))\n\
               (push 1)\n\
               (check-sat)\n\
               (check-sat)\n";
    assert_results(
        smt,
        &["unsat", "unsat"],
        "false BV8 forall must stay unsat across re-checks",
    );
}
