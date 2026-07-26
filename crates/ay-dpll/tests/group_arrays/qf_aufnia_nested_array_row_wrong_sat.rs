// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression + capability: nested array-of-array read-over-write (QF_AUFNIA).
//!
//! Minimized from the SV-COMP `s3_srvr.blast.07/10` UltimateAutomizer scripts
//! (`benchmarks/smtlib-all/QF_AUFNIA/...`) which AY once certified `sat` — in
//! DEFAULT mode AND under `ay solve --self-check` — while z3 4.16 and each
//! file's own `(set-info :status unsat)` say UNSAT (the original wrong-SAT).
//!
//! Two layers protect this family, exercised here:
//!
//!  1. SOUNDNESS FLOOR (unchanged, commit 0fd51aa7dd + the
//!     `quarantine_unverified_nested_array_unsat` boundary): the lazy array +
//!     arithmetic combination cannot be trusted on `(Array Int (Array Int Int))`,
//!     so a nested read must NEVER be certified `sat` when the store structure
//!     forces a contradicting value, and an UNVERIFIED nested-array UNSAT is
//!     fail-closed to `unknown`.
//!
//!  2. CAPABILITY (this change, `try_ufnia_store_flat_row_refutation` in
//!     `combined/mod.rs`): `solve_uf_nia` (QF_AUFNIA) has no dedicated array
//!     theory, so read-over-write through a NAMED array variable
//!     (`(= M1 (store M0 …))`) was never propagated and a determined UNSAT came
//!     back `unknown`. The rescue inlines each single-definition `var = store(…)`
//!     (equisatisfiable) and lets exact `select(store(a,i,v),i)=v` rewriting fold
//!     the nested read-over-write chains to their forced values. When EVERY array
//!     term folds away, the sound NIA solver refutes the pure-arithmetic residue
//!     — an authoritative, array-combination-free UNSAT that is exempt from the
//!     quarantine. Shapes whose reads collapse only under a case split on
//!     symbolic index equalities stay a sound `unknown`.
//!
//! DEFAULT-mode `unsat` is the bar for the fully-collapsing shapes; `--self-check`
//! may still report `unknown` until the proof lane certifies the residue.
//!
//! No shape here may EVER return `sat` (soundness), and no SAT-direction shape
//! may EVER return `unsat` (no over-refutation).

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

/// The fully-collapsing shapes MUST now be refuted: the read-over-write chain
/// folds to a concrete value (no case split needed), so `unknown` is no longer
/// acceptable — DEFAULT-mode `unsat` is required.
fn assert_unsat(label: &str, smt: &str) {
    let output = crate::common::solve(smt);
    let verdict = crate::common::sat_result(&output).unwrap_or("<none>");
    assert_eq!(
        verdict, "unsat",
        "{label}: read-over-write forces the nested read to a value the bound \
         rules out — AY must derive unsat via the store-flat ROW reduction; \
         got {verdict:?}\n{output}"
    );
}

/// THE minimized wrong-SAT reproducer, verbatim (`.claude/wrongsat_min.smt2`):
/// constant outer/inner keys `0`, so `select(select(M1,0),0)` folds by exact
/// ROW1 to `8448`, contradicting `>= 8640`. This is the shape that MUST become
/// `unsat` in default mode.
#[test]
fn nested_array_row_minimized_repro_is_unsat() {
    let smt = r#"
        (set-logic QF_AUFNIA)
        (declare-fun M0 () (Array Int (Array Int Int)))
        (declare-fun M1 () (Array Int (Array Int Int)))
        (assert (= M1 (store M0 0 (store (select M0 0) 0 8448))))
        (assert (>= (select (select M1 0) 0) 8640))
        (check-sat)
    "#;
    assert_unsat("minimized nested ROW repro", smt);
}

/// The smallest symbolic fragment: one nested store, one nested read at the
/// SAME (symbolic) keys. `m1[b][o] = 8448`, then `x <= m1[b][o]` with
/// `x >= 8640` is UNSAT because the read folds (ROW1, key-identical) to 8448.
#[test]
fn nested_array_row_single_store_is_unsat() {
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
    assert_unsat("single-store nested ROW", smt);
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
