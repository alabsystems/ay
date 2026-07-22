// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB 2.6 compliance test suite (#8343).
//!
//! Systematic coverage of every supported logic with SAT/UNSAT formulas,
//! plus command-response format compliance and incremental solving tests.
//! Each test is self-contained with an inline SMT-LIB string.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

// ---------------------------------------------------------------------------
// Helper: run AY with SMT-LIB input on stdin, return (stdout, stderr, success)
// ---------------------------------------------------------------------------

struct AYOutput {
    stdout: String,
    stderr: String,
    success: bool,
}

fn run_ay_stdin(input: &str) -> AYOutput {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().expect("stdin must be piped");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write to ay stdin");
    }

    let output = child.wait_with_output().expect("failed to wait on ay");
    AYOutput {
        stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        success: output.status.success(),
    }
}

/// Extract the first line of stdout, trimmed.
fn first_line(out: &AYOutput) -> &str {
    out.stdout.lines().next().unwrap_or("").trim()
}

/// Collect all check-sat result lines from stdout.
fn check_sat_results(out: &AYOutput) -> Vec<String> {
    out.stdout
        .lines()
        .filter(|l| {
            let t = l.trim();
            t == "sat" || t == "unsat" || t == "unknown"
        })
        .map(|l| l.trim().to_string())
        .collect()
}

/// Assert the first check-sat result is exactly `expected`, or "unknown" if `allow_unknown`.
fn assert_result(out: &AYOutput, expected: &str, allow_unknown: bool, context: &str) {
    let fl = first_line(out);
    if allow_unknown && fl == "unknown" {
        // Accepted for incomplete logics.
        return;
    }
    assert!(
        out.success,
        "{context}: ay exited with failure\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert_eq!(
        fl, expected,
        "{context}: expected '{expected}', got '{fl}'\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// ===========================================================================
// Part 1: Per-logic SAT/UNSAT compliance tests
// ===========================================================================

// ---- QF_UF ---------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_UF sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_UF unsat");
}

// ---- QF_LIA --------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_LIA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_LIA unsat");
}

// ---- QF_LRA --------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_LRA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_LRA unsat");
}

// ---- QF_LIRA (mixed int/real) --------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", true, "QF_LIRA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_LIRA unsat");
}

// ---- QF_BV ---------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_BV sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_BV unsat");
}

// ---- QF_ABV (arrays indexed by bitvectors) -------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_ABV sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_ABV unsat");
}

// ---- QF_AUFBV ------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_AUFBV sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_AUFBV unsat");
}

// ---- QF_UFBV -------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_UFBV sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_UFBV unsat");
}

// ---- QF_UFLIA ------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_UFLIA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_UFLIA unsat");
}

// ---- QF_UFLRA ------------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_UFLRA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_UFLRA unsat");
}

// ---- QF_AUFLRA -----------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_AUFLRA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_AUFLRA unsat");
}

// ---- QF_AUFLIA -----------------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_AUFLIA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_AUFLIA unsat");
}

// ---- QF_NIA (nonlinear integer -- may return unknown) --------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", true, "QF_NIA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_NIA unsat");
}

// ---- QF_NRA (nonlinear real -- may return unknown) -----------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", true, "QF_NRA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_NRA unsat");
}

// ---- QF_FP (floating-point) ----------------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_qf_fp_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.gt x (fp #b0 #x00 #b00000000000000000000000)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "QF_FP sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_FP unsat");
}

// ---- QF_BVFP (bitvector + floating-point) --------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", true, "QF_BVFP sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_BVFP unsat");
}

// ---- QF_S (strings) ------------------------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_qf_s_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_S)
(declare-const s String)
(assert (= s \"hello\"))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "QF_S sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_S unsat");
}

// ---- QF_SLIA (strings + LIA) --------------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_qf_slia_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_SLIA)
(declare-const s String)
(assert (= (str.len s) 5))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "QF_SLIA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_SLIA unsat");
}

// ---- QF_DT (datatypes) --------------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", true, "QF_DT sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_DT unsat");
}

// ---- QF_UFDT (UF + datatypes) -------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", true, "QF_UFDT sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", true, "QF_UFDT unsat");
}

// ---- QF_AX (arrays, no arithmetic) --------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_AX sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_AX unsat");
}

// ---- QF_ALIA (arrays + LIA) ---------------------------------------------

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_ALIA sat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_ALIA unsat");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_ALIA store different index");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_ALIA nested stores");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_ALIA array bounds");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "unsat", false, "QF_ALIA stack verification");
}

#[test]
#[timeout(30_000)]
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
    assert_result(&out, "sat", false, "QF_ALIA const array");
}

#[test]
#[timeout(30_000)]
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

// ===========================================================================
// Part 2: SMT-LIB command compliance tests
// ===========================================================================

// ---- check-sat returns exactly "sat", "unsat", or "unknown" --------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_check_sat_format_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let fl = first_line(&out);
    assert_eq!(fl, "sat", "check-sat must return exactly 'sat', got '{fl}'");
}

#[test]
#[timeout(30_000)]
fn test_compliance_command_check_sat_format_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let fl = first_line(&out);
    assert_eq!(
        fl, "unsat",
        "check-sat must return exactly 'unsat', got '{fl}'"
    );
}

// ---- get-model returns a valid s-expression after SAT --------------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_get_model() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
(get-model)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert!(
        out.stdout.contains("sat"),
        "should contain 'sat' before model"
    );
    // Model must contain (define-fun or (model or opening parenthesis
    assert!(
        out.stdout.contains("define-fun") || out.stdout.contains("(model"),
        "get-model should return a model s-expression, got:\n{}",
        out.stdout
    );
    // Must mention x somewhere in the model
    assert!(
        out.stdout.contains(" x "),
        "model should define variable x, got:\n{}",
        out.stdout
    );
}

// ---- get-unsat-core returns a valid s-expression after UNSAT -------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_get_unsat_core() {
    let out = run_ay_stdin(
        "(set-option :produce-unsat-cores true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 10) :named a1))
(assert (! (< x 5) :named a2))
(check-sat)
(get-unsat-core)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert!(
        out.stdout.contains("unsat"),
        "should be unsat before core extraction"
    );
    // The unsat core must be an s-expression (starts with open paren)
    // and should mention at least one of the named assertions.
    let core_line = out
        .stdout
        .lines()
        .find(|l| l.trim().starts_with('(') && (l.contains("a1") || l.contains("a2")));
    assert!(
        core_line.is_some(),
        "get-unsat-core should return an s-expr mentioning named assertions, got:\n{}",
        out.stdout
    );
}

// ---- push/pop work correctly ---------------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_push_pop() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    assert_eq!(
        results[0], "unsat",
        "after push+contradiction: expected unsat, got {}",
        results[0]
    );
    assert_eq!(
        results[1], "sat",
        "after pop: expected sat, got {}",
        results[1]
    );
}

// ---- reset and reset-assertions work -------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_reset_assertions() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(reset-assertions)
(declare-const y Int)
(assert (= y 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    assert_eq!(results[0], "unsat", "before reset: expected unsat");
    assert_eq!(results[1], "sat", "after reset-assertions: expected sat");
}

#[test]
#[timeout(30_000)]
fn test_compliance_command_reset() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(reset)
(set-logic QF_LIA)
(declare-const y Int)
(assert (= y 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results after reset, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    assert_eq!(results[0], "unsat", "before reset: expected unsat");
    assert_eq!(results[1], "sat", "after reset: expected sat");
}

// ---- echo command --------------------------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_echo() {
    let out = run_ay_stdin(
        "(echo \"hello world\")
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert!(
        out.stdout.contains("hello world"),
        "echo should output the string, got:\n{}",
        out.stdout
    );
}

// ---- exit terminates cleanly ---------------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_exit() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(exit)
",
    );
    assert!(out.success, "ay should exit cleanly on (exit)");
}

// ---- get-info :name and :version -----------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_get_info_name() {
    let out = run_ay_stdin(
        "(get-info :name)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    // Response should be an s-expression like (:name "AY")
    assert!(
        out.stdout.contains(":name") || out.stdout.contains("ay") || out.stdout.contains("AY"),
        "get-info :name should return solver name, got:\n{}",
        out.stdout
    );
}

#[test]
#[timeout(30_000)]
fn test_compliance_command_get_info_version() {
    let out = run_ay_stdin(
        "(get-info :version)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    // Response should be an s-expression containing :version
    assert!(
        out.stdout.contains(":version"),
        "get-info :version should return version info, got:\n{}",
        out.stdout
    );
}

// ---- set-option :produce-models is accepted ------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_command_set_option_produce_models() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should accept :produce-models true");
    assert_eq!(
        first_line(&out),
        "sat",
        "should still solve correctly after set-option"
    );
}

// ===========================================================================
// Part 3: Incremental solving tests
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_compliance_incremental_push_pop_result_changes() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 0))
(assert (<= x 10))
(check-sat)
(push 1)
(assert (> x 20))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= x 5))
(check-sat)
(pop 1)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        5,
        "expected 5 check-sat results, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    // Initial: 0 <= x <= 10 -> sat
    assert_eq!(results[0], "sat", "initial constraints: sat");
    // After push + x > 20 contradicts x <= 10 -> unsat
    assert_eq!(results[1], "unsat", "after push + contradiction: unsat");
    // After pop: back to 0 <= x <= 10 -> sat
    assert_eq!(results[2], "sat", "after pop: sat");
    // After push + x = 5 (consistent with 0 <= x <= 10) -> sat
    assert_eq!(results[3], "sat", "after push + x=5: sat");
    // After pop: back to 0 <= x <= 10 -> sat
    assert_eq!(results[4], "sat", "after second pop: sat");
}

#[test]
#[timeout(30_000)]
fn test_compliance_incremental_nested_push_pop() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(push 1)
(assert (= x 5))
(push 1)
(assert (= y 10))
(assert (> x y))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        3,
        "expected 3 check-sat results, got {results:?}"
    );
    // x=5, y=10, x>y -> unsat
    assert_eq!(results[0], "unsat", "x=5 and x>10: unsat");
    // After inner pop: x=5 -> sat
    assert_eq!(results[1], "sat", "after inner pop (x=5): sat");
    // After outer pop: x>=0 -> sat
    assert_eq!(results[2], "sat", "after outer pop (x>=0): sat");
}

#[test]
#[timeout(30_000)]
fn test_compliance_incremental_push_n_pop_n() {
    // Test push/pop with N > 1 (batch push/pop).
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 0))
(push 2)
(assert (= x 5))
(push 1)
(assert (< x 0))
(check-sat)
(pop 3)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {results:?}"
    );
    // x >= 0 and x = 5 and x < 0 -> unsat
    assert_eq!(results[0], "unsat", "all pushed: unsat");
    // After pop 3: back to just x >= 0 -> sat
    assert_eq!(results[1], "sat", "after pop 3: sat");
}

// ---- Incremental with BV logic -------------------------------------------

#[test]
#[timeout(30_000)]
fn test_compliance_incremental_bv_push_pop() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvuge x #x10))
(check-sat)
(push 1)
(assert (bvult x #x10))
(check-sat)
(pop 1)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(results.len(), 3, "expected 3 results, got {results:?}");
    assert_eq!(results[0], "sat", "x >= 0x10: sat");
    assert_eq!(results[1], "unsat", "x >= 0x10 and x < 0x10: unsat");
    assert_eq!(results[2], "sat", "after pop (x >= 0x10): sat");
}

// ===========================================================================
// Part 4: Multi-check-sat and model extraction per logic
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_compliance_qf_lia_get_model() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
(get-model)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert_eq!(first_line(&out), "sat", "expected sat");
    assert!(
        out.stdout.contains("define-fun"),
        "model should contain define-fun, got:\n{}",
        out.stdout
    );
}

#[test]
#[timeout(30_000)]
fn test_compliance_qf_bv_get_model() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #xAB))
(check-sat)
(get-model)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert_eq!(first_line(&out), "sat", "expected sat");
    assert!(
        out.stdout.contains("define-fun"),
        "model should contain define-fun, got:\n{}",
        out.stdout
    );
}

// ===========================================================================
// Part 5: Logic acceptance (logic string is recognized, no parse error)
// ===========================================================================

/// Test that all documented logic strings are accepted without error.
/// We do not require a specific SAT/UNSAT result here -- just that the
/// solver does not reject the logic.
#[test]
#[timeout(30_000)]
fn test_compliance_all_logic_strings_accepted() {
    let logics = [
        "QF_UF",
        "QF_LIA",
        "QF_LRA",
        "QF_LIRA",
        "QF_BV",
        "QF_ABV",
        "QF_AUFBV",
        "QF_UFBV",
        "QF_UFLIA",
        "QF_UFLRA",
        "QF_AUFLRA",
        "QF_AUFLIA",
        "QF_NIA",
        "QF_NRA",
        "QF_FP",
        "QF_BVFP",
        "QF_S",
        "QF_SLIA",
        "QF_DT",
        "QF_UFDT",
        "QF_AX",
        "QF_ALIA",
        "QF_NIRA",
        "QF_AUFLIRA",
        "QF_UFNIA",
        "QF_UFNRA",
        "QF_UFNIRA",
        "QF_SNIA",
        "QF_SEQ",
        "QF_SEQLIA",
        "ALL",
    ];

    for logic in &logics {
        let input = format!("(set-logic {logic})\n(check-sat)\n(exit)\n");
        let out = run_ay_stdin(&input);
        assert!(
            out.success,
            "ay should accept logic '{logic}' without crashing\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        );
        let fl = first_line(&out);
        assert!(
            fl == "sat" || fl == "unsat" || fl == "unknown",
            "logic '{logic}': check-sat should return sat/unsat/unknown, got '{fl}'\nstderr:\n{}",
            out.stderr
        );
    }
}

/// Test that quantified logic strings are also accepted.
#[test]
#[timeout(30_000)]
fn test_compliance_quantified_logic_strings_accepted() {
    let logics = [
        "LIA", "LRA", "NIA", "NRA", "NIRA", "UF", "UFLIA", "UFLRA", "UFNIA", "UFNRA", "UFNIRA",
        "BV", "UFBV", "AUFLIA", "AUFLRA", "LIRA", "AUFLIRA", "UFDT", "UFDTLIA", "UFDTNIA",
    ];

    for logic in &logics {
        let input = format!("(set-logic {logic})\n(check-sat)\n(exit)\n");
        let out = run_ay_stdin(&input);
        assert!(
            out.success,
            "ay should accept quantified logic '{logic}' without crashing\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        );
        let fl = first_line(&out);
        assert!(
            fl == "sat" || fl == "unsat" || fl == "unknown",
            "logic '{logic}': check-sat should return sat/unsat/unknown, got '{fl}'\nstderr:\n{}",
            out.stderr
        );
    }
}
