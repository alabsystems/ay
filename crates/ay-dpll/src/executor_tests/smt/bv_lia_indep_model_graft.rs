// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `_BV_LIA_INDEP` assumption-route model graft
//! (#bv-lia-indep-model-graft, `restore_indep_bv_model_with_arith_graft`).
//!
//! With `:produce-unsat-cores` on, named assertions solve through the
//! assumption-tracked route. In the independent BV+LIA category the BV lane's
//! model carries NO Int assignment, and the old blind model restore after a
//! SAT AUFLIA cross-check made the final validation evaluate an
//! arithmetically-pinned Int constant from the 0-defaulted completion — a
//! genuine SAT then fail-closed to Unknown (`(= len 3)` "evaluates to
//! false"). This is the deductive-checks mut-slice/collection VC shape (R1
//! 2026-07-18): a `len == N` frame fact alongside pure-BV element
//! constraints. The graft fills the arithmetic components from the AUFLIA
//! model (fill-only, re-validated fail-closed).

use super::*;

/// Int pin + BV pin under the assumption-tracked route: trivially SAT, and
/// the emitted witness must survive validation (len from the AUFLIA lane, the
/// BV leaf from the BV lane).
#[test]
fn named_cores_int_pin_plus_bv_pin_is_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-const seed (_ BitVec 64))
        (declare-const len Int)
        (assert (! (= len 3) :named a0))
        (assert (! (= seed #x0000000000000005) :named a1))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["sat"],
        "independent Int + BV pins must not fail-close on the assumption route (R1)"
    );
}

/// The deductive-checks mut-slice VC shape: slice length frame fact (Int) + ground
/// seed read over an `Array (BV64) (BV64)`.
#[test]
fn named_cores_slice_len_frame_with_array_read_is_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-const __ground_seed_x (_ BitVec 64))
        (declare-const x (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-const __deductive_checks_len_x Int)
        (assert (! (<= 0 __deductive_checks_len_x) :named dn0))
        (assert (! (= __deductive_checks_len_x 3) :named dn1))
        (assert (! (= (select x #x0000000000000000) __ground_seed_x) :named dn2))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["sat"],
        "slice len-frame + array seed read must stay SAT on the assumption route (R1)"
    );
}

/// UNSAT twins on the same route: the graft must not weaken either lane's
/// refutations (Int-side and BV-side conflicts).
#[test]
fn named_cores_conflicting_pins_stay_unsat() {
    for (label, input) in [
        (
            "int-side",
            r#"
                (set-option :produce-unsat-cores true)
                (set-logic ALL)
                (declare-const seed (_ BitVec 64))
                (declare-const len Int)
                (assert (! (= len 3) :named a0))
                (assert (! (= len 4) :named a1))
                (assert (! (= seed #x0000000000000005) :named a2))
                (check-sat)
            "#,
        ),
        (
            "bv-side",
            r#"
                (set-option :produce-unsat-cores true)
                (set-logic ALL)
                (declare-const seed (_ BitVec 64))
                (declare-const len Int)
                (assert (! (= len 3) :named a0))
                (assert (! (= seed #x0000000000000005) :named a1))
                (assert (! (= seed #x0000000000000006) :named a2))
                (check-sat)
            "#,
        ),
    ] {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["unsat"], "{label} conflict must stay unsat");
    }
}
