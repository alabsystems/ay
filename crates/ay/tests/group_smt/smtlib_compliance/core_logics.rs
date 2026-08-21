// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `smtlib_compliance.rs` to preserve test FQNs.

// ===========================================================================
// Part 1: Per-logic SAT/UNSAT compliance tests
// ===========================================================================

// ---- QF_UF ---------------------------------------------------------------

#[test]
fn test_compliance_qf_uf_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (= a b))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_UF sat");
}

#[test]
fn test_compliance_qf_uf_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (= a b))
(assert (= b c))
(assert (distinct a c))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_UF unsat");
}

// ---- QF_LIA --------------------------------------------------------------

#[test]
fn test_compliance_qf_lia_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 10))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_LIA sat");
}

#[test]
fn test_compliance_qf_lia_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_LIA unsat");
}

// ---- QF_LRA --------------------------------------------------------------

#[test]
fn test_compliance_qf_lra_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (> x 0.0))
(assert (< x 1.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_LRA sat");
}

#[test]
fn test_compliance_qf_lra_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (> x 5.0))
(assert (< x 3.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_LRA unsat");
}

// ---- QF_LIRA (mixed int/real) --------------------------------------------

#[test]
fn test_compliance_qf_lira_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIRA)
(declare-const x Int)
(declare-const y Real)
(assert (> (to_real x) y))
(assert (> y 0.0))
(check-sat)
(exit)
",
    );
    // QF_LIRA support is documented as incomplete; accept unknown.
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_LIRA sat");
}

#[test]
fn test_compliance_qf_lira_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIRA)
(declare-const x Int)
(assert (> (to_real x) 1.0))
(assert (< (to_real x) 0.0))
(check-sat)
(exit)
",
    );
    // to_real(x) > 1 and to_real(x) < 0 is contradictory.
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_LIRA unsat");
}

// ---- QF_BV ---------------------------------------------------------------

#[test]
fn test_compliance_qf_bv_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x42))
(assert (not (= x #xFF)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_BV sat");
}

#[test]
fn test_compliance_qf_bv_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x00))
(assert (= x #xFF))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_BV unsat");
}

// ---- QF_ABV (arrays indexed by bitvectors) -------------------------------

#[test]
fn test_compliance_qf_abv_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const i (_ BitVec 8))
(assert (= (select a i) #xFF))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_ABV sat");
}

#[test]
fn test_compliance_qf_abv_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const i (_ BitVec 8))
(assert (= (select (store a i #x01) i) #x02))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_ABV unsat");
}

// ---- QF_AUFBV ------------------------------------------------------------

#[test]
fn test_compliance_qf_aufbv_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #xFF))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_AUFBV sat");
}

#[test]
fn test_compliance_qf_aufbv_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_AUFBV unsat");
}

// ---- QF_UFBV -------------------------------------------------------------

#[test]
fn test_compliance_qf_ufbv_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) x))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_UFBV sat");
}

#[test]
fn test_compliance_qf_ufbv_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_UFBV unsat");
}

// ---- QF_UFLIA ------------------------------------------------------------

#[test]
fn test_compliance_qf_uflia_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= (f x) 42))
(assert (> x 0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_UFLIA sat");
}

#[test]
fn test_compliance_qf_uflia_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_UFLIA unsat");
}

// ---- QF_UFLRA ------------------------------------------------------------

#[test]
fn test_compliance_qf_uflra_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(assert (= (f x) 1.0))
(assert (> x 0.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_UFLRA sat");
}

#[test]
fn test_compliance_qf_uflra_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_UFLRA unsat");
}

// ---- QF_AUFLRA -----------------------------------------------------------

#[test]
fn test_compliance_qf_auflra_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_AUFLRA)
(declare-const a (Array Real Real))
(declare-const x Real)
(assert (> (select a x) 0.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_AUFLRA sat");
}

#[test]
fn test_compliance_qf_auflra_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_AUFLRA)
(declare-const a (Array Real Real))
(declare-const x Real)
(assert (= (select (store a x 1.0) x) 2.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_AUFLRA unsat");
}

// ---- QF_AUFLIA -----------------------------------------------------------

#[test]
fn test_compliance_qf_auflia_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select a i) 42))
(assert (> i 0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_AUFLIA sat");
}

#[test]
fn test_compliance_qf_auflia_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select (store a i 5) i) 10))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_AUFLIA unsat");
}
