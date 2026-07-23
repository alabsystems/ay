// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: nested array-of-array read-over-write wrong-SAT (QF_AUFNIA).
//!
//! Minimized from the SV-COMP `s3_srvr.blast.07/10` UltimateAutomizer scripts
//! (`benchmarks/smtlib-all/QF_AUFNIA/...`) which AY certified `sat` — in DEFAULT
//! mode AND under `ay solve --self-check` — while z3 4.16 and each file's own
//! `(set-info :status unsat)` say UNSAT. THE CARDINAL FAILURE: a wrong `sat`
//! passing AY's own fail-closed self-check gate.
//!
//! Mechanism: the model evaluator's `evaluate_select` could not reduce a
//! NESTED array-valued select — `(select (select m b) o)` over a two-level
//! memory `(Array Int (Array Int Int))`. It treated the inner `(select m b)`
//! as an opaque base, returned `Unknown`, and the caller's LIA-model fallback
//! (mod.rs, "in AUFLIA the LIA solver treats select terms as opaque variables")
//! then laundered the arithmetic solver's UNCONSTRAINED value for a read that
//! the store structure actually FORCES. The strict oracle never observed the
//! contradiction, so the internally-inconsistent model escaped as a wrong SAT.
//!
//! Fix: `evaluate_select` now resolves an array-valued nested select to the
//! concrete inner-array term it denotes (exact ROW1/ROW2 peeling through
//! store chains and array-variable definitions), so the forced value is
//! recomputed and the inconsistent candidate model is rejected (verdict
//! degrades to a sound `unknown`).
//!
//! These must NEVER return `sat` again.

fn assert_not_sat(label: &str, smt: &str) {
    let output = crate::common::solve(smt);
    let verdict = crate::common::sat_result(&output).unwrap_or("<none>");
    assert_ne!(
        verdict, "sat",
        "{label}: nested array-of-array read-over-write is UNSAT (z3) — AY must \
         never certify sat here (a wrong SAT); got {verdict:?}\n{output}"
    );
    assert!(
        matches!(verdict, "unsat" | "unknown"),
        "{label}: expected unsat or unknown, got {verdict:?}\n{output}"
    );
}

/// The smallest fragment that still wrong-SATs: one nested store, one nested
/// read. `m1[b][o] = 8448`, then `x <= m1[b][o]` with `x >= 8640` is UNSAT
/// because the read is forced to 8448 < 8640.
#[test]
fn nested_array_row_single_store_is_not_sat() {
    let smt = r#"
        (set-logic QF_AUFNIA)
        (declare-fun m0 () (Array Int (Array Int Int)))
        (declare-fun m1 () (Array Int (Array Int Int)))
        (declare-fun b () Int)
        (declare-fun o () Int)
        (declare-fun x () Int)
        (assert (= m1 (store m0 b (store (select m0 b) o 8448))))
        (assert (<= x (select (select m1 b) o)))
        (assert (>= x 8640))
        (check-sat)
    "#;
    assert_not_sat("single-store nested ROW", smt);
}

/// Two nested stores at the same base with a shadowing overwrite at a
/// DIFFERENT inner index — the read at the original index still resolves
/// through the chain to 8448 (< 8640), so UNSAT.
#[test]
fn nested_array_row_two_store_shadow_is_not_sat() {
    let smt = r#"
        (set-logic QF_AUFNIA)
        (declare-fun m0 () (Array Int (Array Int Int)))
        (declare-fun m1 () (Array Int (Array Int Int)))
        (declare-fun m2 () (Array Int (Array Int Int)))
        (declare-fun b () Int)
        (declare-fun o () Int)
        (declare-fun s_state () Int)
        (declare-fun s_init () Int)
        (declare-fun x () Int)
        (assert (= m1 (store m0 b (store (select m0 b) (+ o s_state) 8448))))
        (assert (= m2 (store m1 b (store (select m1 b) (+ o s_init) 0))))
        (assert (<= x (select (select m2 b) (+ o s_state))))
        (assert (>= x 8640))
        (check-sat)
    "#;
    assert_not_sat("two-store shadow nested ROW", smt);
}

/// Faithful shape of the original CIL benchmark: three nested stores across
/// two distinct bases, offsets built from symbolic struct-field constants.
/// The read `m3[base][off+STATE]` resolves to one of {0, 3, 8448}, all < 8640.
#[test]
fn nested_array_row_three_store_two_base_is_not_sat() {
    let smt = r#"
        (set-logic QF_AUFNIA)
        (declare-fun m0 () (Array Int (Array Int Int)))
        (declare-fun m1 () (Array Int (Array Int Int)))
        (declare-fun m2 () (Array Int (Array Int Int)))
        (declare-fun m3 () (Array Int (Array Int Int)))
        (declare-fun b () Int)
        (declare-fun o () Int)
        (declare-fun b2 () Int)
        (declare-fun o2 () Int)
        (declare-fun s_state () Int)
        (declare-fun s_next () Int)
        (declare-fun s_init () Int)
        (declare-fun x () Int)
        (assert (= m1 (store m0 b (store (select m0 b) (+ o s_state) 8448))))
        (assert (= m2 (store m1 b2 (store (select m1 b2) (+ o2 s_next) 3))))
        (assert (= m3 (store m2 b (store (select m2 b) (+ o s_init) 0))))
        (assert (<= x (select (select m3 b) (+ o s_state))))
        (assert (>= x 8640))
        (check-sat)
    "#;
    assert_not_sat("three-store two-base nested ROW", smt);
}

/// Soundness guard in the SAT direction: the SAME nested-array shape but
/// GENUINELY SATISFIABLE (`x = m1[b][o] = 8448`, z3: sat). The fix resolves
/// the nested read to its forced value (8448) during model validation. The
/// only WRONG answer here is `unsat` — the fix must never manufacture a
/// refutation of a satisfiable instance. `sat` is ideal; `unknown` is the
/// current sound-but-incomplete result (the core UF/NIA model leaves the
/// opaque select value unpinned, so the honest gate degrades to `unknown`
/// rather than emitting the internally-inconsistent model the base build
/// certified as `sat`). Both are accepted; only `unsat` fails.
#[test]
fn nested_array_row_consistent_read_is_never_unsat() {
    let smt = r#"
        (set-logic QF_AUFNIA)
        (declare-fun m0 () (Array Int (Array Int Int)))
        (declare-fun m1 () (Array Int (Array Int Int)))
        (declare-fun b () Int)
        (declare-fun o () Int)
        (declare-fun x () Int)
        (assert (= m1 (store m0 b (store (select m0 b) o 8448))))
        (assert (= x (select (select m1 b) o)))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let verdict = crate::common::sat_result(&output).unwrap_or("<none>");
    assert_ne!(
        verdict, "unsat",
        "a satisfiable nested-array read (x = m1[b][o] = 8448) must NEVER be \
         refuted — the read-resolution fix must not manufacture a wrong unsat; \
         got {verdict:?}\n{output}"
    );
}

/// Precision + consistency guard: the fix makes NESTED arrays behave exactly
/// like FLAT arrays already did. The base build was fail-CLOSED (`unknown`) on
/// this flat pinned read-over-write (`x = a1[o]`) — it cannot verify a read
/// pinned to a variable through the opaque arithmetic value — yet was
/// fail-OPEN (`sat`) on the structurally-identical NESTED read. The new arm is
/// gated on an array-sorted select head, so it cannot change this flat case at
/// all; it only closes the nested fail-open to match. A genuinely-SAT flat
/// read must never be wrongly refuted.
#[test]
fn flat_array_read_over_write_is_never_unsat() {
    let smt = r#"
        (set-logic QF_AUFNIA)
        (declare-fun a0 () (Array Int Int))
        (declare-fun a1 () (Array Int Int))
        (declare-fun o () Int)
        (declare-fun x () Int)
        (assert (= a1 (store a0 o 8448)))
        (assert (= x (select a1 o)))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let verdict = crate::common::sat_result(&output).unwrap_or("<none>");
    assert_ne!(
        verdict, "unsat",
        "flat single-level array read-over-write is satisfiable — must never \
         be refuted; got {verdict:?}\n{output}"
    );
}
