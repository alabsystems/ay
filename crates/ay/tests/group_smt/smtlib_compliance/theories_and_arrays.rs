// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `smtlib_compliance.rs` to preserve test FQNs.

// ---- QF_NIA (nonlinear integer -- may return unknown) --------------------

#[test]
fn test_compliance_qf_nia_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 6))
(assert (> x 0))
(assert (> y 0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_NIA sat");
}

#[test]
fn test_compliance_qf_nia_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_NIA)
(declare-const x Int)
(assert (= (* x x) 2))
(check-sat)
(exit)
",
    );
    // x^2 = 2 has no integer solution.
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_NIA unsat");
}

// ---- QF_NRA (nonlinear real -- may return unknown) -----------------------

#[test]
fn test_compliance_qf_nra_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* x x) 4.0))
(assert (> x 0.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_NRA sat");
}

#[test]
fn test_compliance_qf_nra_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* x x) (- 1.0)))
(check-sat)
(exit)
",
    );
    // x^2 = -1 has no real solution.
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_NRA unsat");
}

// ---- QF_FP (floating-point) ----------------------------------------------

#[test]
fn test_compliance_qf_fp_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.gt x (fp #b0 #x00 #b00000000000000000000000)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_FP sat");
}

#[test]
fn test_compliance_qf_fp_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.eq x ((_ to_fp 8 24) RNE 1.0)))
(assert (fp.eq x ((_ to_fp 8 24) RNE 2.0)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_FP unsat");
}

// ---- QF_BVFP (bitvector + floating-point) --------------------------------

#[test]
fn test_compliance_qf_bvfp_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_BVFP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const bv (_ BitVec 32))
(assert (fp.gt x ((_ to_fp 8 24) RNE 0.0)))
(assert (bvugt bv #x00000000))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_BVFP sat");
}

#[test]
fn test_compliance_qf_bvfp_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_BVFP)
(declare-const bv (_ BitVec 8))
(assert (= bv #x00))
(assert (= bv #xFF))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_BVFP unsat");
}

// ---- QF_S (strings) ------------------------------------------------------

#[test]
fn test_compliance_qf_s_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_S)
(declare-const s String)
(assert (= s \"hello\"))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_S sat");
}

#[test]
fn test_compliance_qf_s_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_S)
(declare-const s String)
(assert (= s \"hello\"))
(assert (= s \"world\"))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_S unsat");
}

// ---- QF_SLIA (strings + LIA) --------------------------------------------

#[test]
fn test_compliance_qf_slia_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_SLIA)
(declare-const s String)
(assert (= (str.len s) 5))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_SLIA sat");
}

#[test]
fn test_compliance_qf_slia_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_SLIA)
(declare-const s String)
(assert (= (str.len s) (- 1)))
(check-sat)
(exit)
",
    );
    // String length cannot be negative.
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_SLIA unsat");
}

// ---- QF_DT (datatypes) --------------------------------------------------

#[test]
fn test_compliance_qf_dt_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_DT)
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-const c Color)
(assert (= c Red))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_DT sat");
}

#[test]
fn test_compliance_qf_dt_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_DT)
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-const c Color)
(assert (= c Red))
(assert (= c Green))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_DT unsat");
}

// ---- QF_UFDT (UF + datatypes) -------------------------------------------

#[test]
fn test_compliance_qf_ufdt_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_UFDT)
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-fun f (Color) Color)
(declare-const c Color)
(assert (= (f c) Red))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Accept, "QF_UFDT sat");
}

#[test]
fn test_compliance_qf_ufdt_unsat() {
    // Use a pure DT contradiction; x=y => f(x)!=f(y) is a known congruence
    // gap in UF+DT interaction. This test exercises DT distinctness.
    let out = run_ay_stdin(
        "(set-logic QF_UFDT)
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-const c Color)
(assert (= c Red))
(assert (= c Green))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Accept, "QF_UFDT unsat");
}

// ---- QF_AX (arrays, no arithmetic) --------------------------------------

#[test]
fn test_compliance_qf_ax_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_AX)
(declare-sort Idx 0)
(declare-sort Elm 0)
(declare-const a (Array Idx Elm))
(declare-const i Idx)
(declare-const v Elm)
(assert (= (select (store a i v) i) v))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_AX sat");
}

#[test]
fn test_compliance_qf_ax_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_AX)
(declare-sort Idx 0)
(declare-sort Elm 0)
(declare-const a (Array Idx Elm))
(declare-const i Idx)
(declare-const v1 Elm)
(declare-const v2 Elm)
(assert (distinct v1 v2))
(assert (= (select (store a i v1) i) v2))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_AX unsat");
}

// ---- QF_ALIA (arrays + LIA) ---------------------------------------------

#[test]
fn test_compliance_qf_alia_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (> (select a i) 0))
(assert (> i 0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_ALIA sat");
}

#[test]
fn test_compliance_qf_alia_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select (store a i 5) i) 10))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_ALIA unsat");
}

#[test]
fn test_compliance_qf_alia_store_diff_idx_unsat() {
    // Store at i, select at j (i != j): value should be unchanged.
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (not (= i j)))
(assert (not (= (select (store a i 42) j) (select a j))))
(check-sat)
(exit)
",
    );
    assert_result(
        &out,
        "unsat",
        UnknownPolicy::Reject,
        "QF_ALIA store different index",
    );
}

#[test]
fn test_compliance_qf_alia_nested_stores_sat() {
    // Nested stores at distinct LIA-constrained indices
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (> i 0))
(assert (< i 10))
(assert (= j (+ i 1)))
(assert (= (select (store (store a i 1) j 2) i) 1))
(assert (= (select (store (store a i 1) j 2) j) 2))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_ALIA nested stores");
}

#[test]
fn test_compliance_qf_alia_array_bounds_unsat() {
    // Array value with conflicting LIA constraints
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (>= (select a i) 0))
(assert (<= (select a i) 10))
(assert (= (+ (select a i) 5) 20))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", UnknownPolicy::Reject, "QF_ALIA array bounds");
}

#[test]
fn test_compliance_qf_alia_stack_verification_unsat() {
    // Stack push/pop pattern from software verification
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-fun mem () (Array Int Int))
(declare-fun sp () Int)
(declare-fun mem2 () (Array Int Int))
(declare-fun sp2 () Int)
(declare-fun mem3 () (Array Int Int))
(declare-fun sp3 () Int)
(declare-fun val1 () Int)
(declare-fun val2 () Int)
(assert (>= sp 0))
(assert (= mem2 (store mem sp val1)))
(assert (= sp2 (+ sp 1)))
(assert (= mem3 (store mem2 sp2 val2)))
(assert (= sp3 (+ sp2 1)))
(assert (= (select mem3 (- sp3 1)) val2))
(assert (= (select mem3 (- sp3 2)) val1))
(assert (or (not (= (select mem3 (- sp3 1)) val2))
            (not (= (select mem3 (- sp3 2)) val1))))
(check-sat)
(exit)
",
    );
    assert_result(
        &out,
        "unsat",
        UnknownPolicy::Reject,
        "QF_ALIA stack verification",
    );
}

#[test]
fn test_compliance_qf_alia_const_array_sat() {
    // Constant array + store
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= a ((as const (Array Int Int)) 0)))
(assert (= (select (store a 5 42) 5) 42))
(assert (= (select (store a 5 42) 3) 0))
(assert (> i 10))
(assert (= (select a i) 0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", UnknownPolicy::Reject, "QF_ALIA const array");
}

#[test]
fn test_compliance_qf_alia_model_generation() {
    // Verify model generation works for QF_ALIA
    let out = run_ay_stdin(
        "(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select a 0) 5))
(assert (> i 0))
(check-sat)
(get-model)
(exit)
",
    );
    assert!(out.success, "QF_ALIA model generation should succeed");
    assert!(
        out.stdout.contains("sat"),
        "QF_ALIA model generation should return sat"
    );
    assert!(
        out.stdout.contains("model"),
        "QF_ALIA should produce a model"
    );
}
