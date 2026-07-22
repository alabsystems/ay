// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI integration tests for `--minimize-model` flag (#8297).
//!
//! Verifies that the `--minimize-model` flag produces SAT results with
//! minimized BV variable values (pinned to 0/1 where observable).

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_counterexample_minimize_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    std::fs::write(&path, contents).expect("write temp input");
    (path.clone(), CleanupGuard(path))
}

/// --minimize-model flag is accepted and produces SAT for a satisfiable BV formula.
#[test]
#[timeout(60_000)]
fn test_minimize_model_flag_accepted_bv() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // x has two satisfying values; minimization should pick #x00.
    let smt = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (or (= x #x00) (= x #x01)))
(check-sat)
(get-value (x))
(exit)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = Command::new(ay_path)
        .arg("--minimize-model")
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "ay --minimize-model failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("sat"), "expected sat, got: {stdout}");
    assert!(
        stdout.contains("#x00"),
        "expected minimized BV value #x00, got: {stdout}"
    );
}

/// --minimize-model produces a valid model for a constrained BV formula.
#[test]
#[timeout(60_000)]
fn test_minimize_model_constrained_bv() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // x != y with 8-bit BVs. Minimization should produce x=0, y=1 (or similar minimal).
    let smt = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (not (= x y)))
(check-sat)
(get-model)
(exit)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = Command::new(ay_path)
        .arg("--minimize-model")
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "ay --minimize-model failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("sat"), "expected sat, got: {stdout}");
    assert!(
        stdout.contains("model"),
        "expected model output, got: {stdout}"
    );
}

/// --minimize-model works for LIA formulas (not just BV).
#[test]
#[timeout(60_000)]
fn test_minimize_model_lia() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // x >= 5: minimization should try to minimize x to 5 or a small value.
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 5))
(check-sat)
(get-model)
(exit)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = Command::new(ay_path)
        .arg("--minimize-model")
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "ay --minimize-model failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("sat"), "expected sat, got: {stdout}");
    assert!(
        stdout.contains("model"),
        "expected model output, got: {stdout}"
    );
}

/// --minimize-model does not break UNSAT results.
#[test]
#[timeout(60_000)]
fn test_minimize_model_unsat_unchanged() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
(exit)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = Command::new(ay_path)
        .arg("--minimize-model")
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "ay --minimize-model failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("unsat"), "expected unsat, got: {stdout}");
}

/// API-level test: Solver::try_minimize_model() is accessible through ay facade.
#[test]
fn test_solver_api_minimize_model() {
    use ay::prelude::*;

    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);
    let zero = solver.bv_const(0, 8);
    let ge = solver.bvuge(x, zero);
    solver.assert_term(ge);

    assert!(solver.check_sat().is_sat());

    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    // Minimized unconstrained BV should be 0.
    if let Some(ModelValue::BitVec { value, width }) = solver.value(x) {
        assert_eq!(width, 8);
        assert_eq!(value, BigInt::from(0u8), "should minimize to 0");
    } else {
        panic!("expected BitVec model value");
    }

    solver.try_pop().expect("pop should succeed");
}

/// API-level test: Solver::project_model() filters variables correctly.
#[test]
fn test_solver_api_project_model() {
    use ay::prelude::*;

    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8.clone());
    let _y = solver.declare_const("y", bv8);

    let zero = solver.bv_const(0, 8);
    let eq = solver.eq(x, zero);
    solver.assert_term(eq);

    assert!(solver.check_sat().is_sat());

    let projected = solver.project_model(&["x"]);
    assert!(projected.contains_key("x"), "projection should include x");
    assert!(!projected.contains_key("y"), "projection should exclude y");
}
