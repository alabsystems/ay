// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay <query>` on scripts whose user symbols are spelled like a name AY mints
//! internally. Each test names the script it runs and asserts what `ay`
//! prints for it or writes to its Alethe proof.

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const FIELD_BEFORE_ROOT: &str = "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
    (declare-const p!x Int)\n\
    (declare-const p P)\n\
    (assert (= p!x 1))\n\
    (assert (= (x p) 2))\n\
    (check-sat)\n";

const FIELD_AFTER_ROOT: &str = "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
    (declare-const p P)\n\
    (declare-const p!x Int)\n\
    (assert (= p!x 1))\n\
    (assert (= (x p) 2))\n\
    (check-sat)\n";

const EMPTY_SELECTOR: &str = "(declare-datatypes ((P 0)) (((mk (|| Int)))))\n\
    (declare-const p! Int)\n\
    (declare-const p P)\n\
    (assert (= p! 1))\n\
    (assert (= (|| p) 2))\n\
    (check-sat)\n";

const NAN_WITNESS_SPELLING: &str = "(set-logic QF_FPLRA)\n\
    (declare-const x (_ FloatingPoint 8 24))\n\
    (declare-const |__fp_undef_(__NaN_8_24)| Real)\n\
    (assert (fp.isNaN x))\n\
    (assert (= |__fp_undef_(__NaN_8_24)| 5.0))\n\
    (assert (= (fp.to_real x) 7.0))\n\
    (check-sat)\n";

/// `ay query.smt2 <args>` run in a fresh directory: stdout, stderr, and that
/// directory (kept alive for the proof file).
fn run(query: &str, args: &[&str]) -> (String, String, tempfile::TempDir) {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("query.smt2");
    std::fs::write(&input, query).expect("write the query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&input)
        .args(args)
        .current_dir(dir.path())
        .output_timeout(Duration::from_secs(60))
        .expect("ay finishes within the child deadline");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        dir,
    )
}

fn first_line(stdout: &str) -> &str {
    stdout.lines().next().unwrap_or_default().trim()
}

#[test]
fn field_spelled_constants_are_sat_in_the_default_posture_and_with_proofs() {
    for (label, query) in [
        ("before", FIELD_BEFORE_ROOT),
        ("after", FIELD_AFTER_ROOT),
        ("empty", EMPTY_SELECTOR),
    ] {
        let (stdout, stderr, _dir) = run(query, &[]);
        assert_eq!(stdout.trim(), "sat", "{label}: stderr={stderr}");
        let (stdout, stderr, _dir) = run(query, &["--proof", "query.alethe"]);
        assert_eq!(stdout.trim(), "sat", "{label} --proof: stderr={stderr}");
    }
}

#[test]
fn get_value_reports_the_user_constant_and_the_field_separately() {
    let query = format!(
        "(set-option :produce-models true)\n{FIELD_BEFORE_ROOT}(get-value (p!x (x p) p))\n"
    );
    let (stdout, stderr, _dir) = run(&query, &[]);
    assert_eq!(first_line(&stdout), "sat", "stderr={stderr}");
    let values = stdout
        .lines()
        .skip(1)
        .collect::<Vec<_>>()
        .join(" ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(values, "((p!x 1) ((x p) 2) (p (mk 2)))", "stdout={stdout}");
}

#[test]
fn the_unsat_proof_assumes_the_user_constant_and_the_selector_as_written() {
    let query = "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
        (declare-const p!x Int)\n\
        (declare-const p P)\n\
        (assert (= p!x 1))\n\
        (assert (= (x p) 2))\n\
        (assert (= p!x (x p)))\n\
        (check-sat)\n";
    let (stdout, stderr, dir) = run(query, &["--proof", "query.alethe"]);
    assert_eq!(stdout.trim(), "unsat", "stderr={stderr}");
    let proof = std::fs::read_to_string(Path::new(dir.path()).join("query.alethe"))
        .expect("the proof file is written");
    let assumes: Vec<&str> = proof
        .lines()
        .filter(|line| line.starts_with("(assume "))
        .collect();
    assert!(
        assumes.iter().all(|line| !line.contains("(= (x p) 1)")),
        "the user's `(= p!x 1)` must not print as the field: {proof}"
    );
    for authored in ["(= p!x 1)", "(= (x p) 2)", "(= p!x (x p))"] {
        assert!(
            assumes.iter().any(|line| line.contains(authored)),
            "missing assume {authored}: {proof}"
        );
    }
}

#[test]
fn a_real_spelled_like_the_old_nan_witness_is_not_fp_to_real_of_nan() {
    let (stdout, stderr, _dir) = run(NAN_WITNESS_SPELLING, &[]);
    assert_eq!(stdout.trim(), "sat", "stderr={stderr}");
}

/// Hunt probe `binder-n/qs8`; z3 answers `unsat`.
const BINDER_THEN_CONSTANT: &str = "(set-logic LIA)\n\
    (assert (forall ((x Int)) (or (< x 1) (> x 1) (forall ((y Int)) (=> (> y x) (> y 0))))))\n\
    (declare-const x_0 Int)\n\
    (assert (forall ((w Int)) (=> (> w x_0) (> w 0))))\n\
    (assert (= x_0 (- 1)))\n\
    (check-sat)\n";

/// Hunt probe `binder-names/vdef`; z3 answers `unsat`.
const FORMAL_THEN_CONSTANT: &str =
    "(define-fun h ((x Int)) Bool (forall ((z Int)) (>= (+ z x) z)))\n\
    (declare-const x Int)\n\
    (assert (forall ((w Int)) (>= (+ w x) w)))\n\
    (assert (< x 0))\n\
    (check-sat)\n";

/// Hunt probe `powneg/wsat_alpha0`; z3 answers `unsat`.
const NEGATIVE_POWER_WITNESS_SPELLING: &str = "(declare-const x Real)\n\
    (assert (= x 0.0))\n\
    (assert (forall ((b Bool)) (or b (= (^ x (- 1)) 0.0))))\n\
    (declare-const |pow_neg_at_zero_2| Real)\n\
    (assert (forall ((c Bool)) (or c (= (ite (= x 0.0) |pow_neg_at_zero_2| (/ 1.0 x)) 0.0))))\n\
    (assert (= |pow_neg_at_zero_2| 5.0))\n\
    (check-sat)\n";

/// Hunt probe `powneg/wunsat_alpha0`; z3 answers `sat`.
const NEGATIVE_POWER_WITNESS_SPELLING_NEGATED: &str = "(declare-const x Real)\n\
    (assert (= x 0.0))\n\
    (assert (forall ((b Bool)) (or b (= (^ x (- 1)) 0.0))))\n\
    (declare-const |pow_neg_at_zero_2| Real)\n\
    (assert (not (forall ((c Bool)) (or c (= (ite (= x 0.0) |pow_neg_at_zero_2| (/ 1.0 x)) 0.0)))))\n\
    (check-sat)\n";

/// Hunt probe `divmod-aux/h6_d2`; z3 answers `unsat`.
const HORN_MOD_AUXILIARY_SPELLING: &str = "(set-logic HORN)\n\
    (declare-fun inv (Int) Bool)\n\
    (assert (forall ((x Int)) (=> (= x 0) (inv x))))\n\
    (assert (forall ((x Int) (x1 Int)) (=> (and (inv x) (< x 2) (= x1 (+ x 1))) (inv x1))))\n\
    (assert (forall ((x Int) (_mod_r_1 Int)) (=> (and (inv x) (>= x 2) (not (= (mod x 3) _mod_r_1)) (= _mod_r_1 1000)) (inv _mod_r_1))))\n\
    (assert (forall ((x Int)) (=> (and (inv x) (>= x 1000)) false)))\n\
    (check-sat)\n";

/// Hunt probe `chc-mint/c02_cata_fact`; z3 answers `unsat`.
const HORN_CATAMORPHISM_SPELLING: &str = "(set-logic HORN)\n\
    (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
    (declare-fun P (Lst Int) Bool)\n\
    (assert (forall ((l Lst) (n Int) (__cata0_size Int)) (=> (and (= l nil) (= n 0) (or (< __cata0_size 1) (> __cata0_size 1000000))) (P l n))))\n\
    (assert (forall ((l Lst) (n Int) (x Int)) (=> (P l n) (P (cons x l) (+ n 1)))))\n\
    (assert (forall ((l Lst) (n Int)) (=> (and (P l n) (>= n 10)) false)))\n\
    (check-sat)\n";

/// Hunt probe `dtkey/ws/min2`; z3 answers `unsat`.
const SELECTOR_SPELLING_ANOTHER_APPLICATION: &str = "(declare-datatypes ((D 0) (L 0)) (((C (v (_ BitVec 8))) (E)) ((nil) (c (h Bool) (t L)) (w (|c K:Bool(true)| L)))))\n\
    (declare-const l L)\n\
    (declare-const a (Array (_ BitVec 8) D))\n\
    (declare-const b (Array (_ BitVec 8) D))\n\
    (declare-const i (_ BitVec 8))\n\
    (declare-const y (_ BitVec 8))\n\
    (assert (= l (w nil)))\n\
    (assert (or (= (store a i E) (store b i (C y))) (= (c true l) (|c K:Bool(true)| l))))\n\
    (check-sat)\n";

fn verdict_lines(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

#[test]
fn a_constant_spelled_like_a_binder_or_a_formal_is_unsat_as_authored() {
    for (label, query) in [
        ("binder", BINDER_THEN_CONSTANT),
        ("formal", FORMAL_THEN_CONSTANT),
    ] {
        for args in [&[][..], &["--rigor", "certified"][..]] {
            let (stdout, stderr, _dir) = run(query, args);
            assert_eq!(
                verdict_lines(&stdout),
                ["unsat"],
                "{label} {args:?}: stderr={stderr}"
            );
        }
    }
}

#[test]
fn the_proof_of_the_binder_script_assumes_the_users_constant_as_written() {
    let (stdout, stderr, dir) = run(BINDER_THEN_CONSTANT, &["--proof", "query.alethe"]);
    assert_eq!(verdict_lines(&stdout), ["unsat"], "stderr={stderr}");
    let proof = std::fs::read_to_string(Path::new(dir.path()).join("query.alethe"))
        .expect("the proof file is written");
    let assumes: Vec<&str> = proof
        .lines()
        .filter(|line| line.starts_with("(assume "))
        .collect();
    for authored in ["(forall ((w Int)) (=> (> w x_0) (> w 0)))", "(= x_0 (- 1))"] {
        assert!(
            assumes.iter().any(|line| line.contains(authored)),
            "missing assume {authored}: {proof}"
        );
    }
    assert!(!proof.contains("__ay_"), "{proof}");
}

#[test]
fn a_real_spelled_like_the_old_negative_power_witness_is_not_the_witness() {
    let (stdout, stderr, _dir) = run(NEGATIVE_POWER_WITNESS_SPELLING, &[]);
    assert_eq!(verdict_lines(&stdout), ["unsat"], "stderr={stderr}");
    let (stdout, stderr, _dir) = run(
        NEGATIVE_POWER_WITNESS_SPELLING,
        &["--proof", "query.alethe"],
    );
    assert_ne!(verdict_lines(&stdout), ["sat"], "--proof: stderr={stderr}");
    let (stdout, stderr, _dir) = run(NEGATIVE_POWER_WITNESS_SPELLING_NEGATED, &[]);
    assert_ne!(
        verdict_lines(&stdout),
        ["unsat"],
        "negated: stderr={stderr}"
    );
}

#[test]
fn get_value_of_a_negative_power_reports_the_asserted_value() {
    let query = "(set-option :produce-models true)\n\
        (declare-const x Real)\n\
        (assert (= x 0.0))\n\
        (assert (= (^ x (- 1)) 0.0))\n\
        (check-sat)\n\
        (get-value ((^ x (- 1))))\n";
    let (stdout, stderr, _dir) = run(query, &[]);
    assert_eq!(verdict_lines(&stdout), ["sat"], "stderr={stderr}");
    assert!(stdout.contains("(((^ x (- 1)) 0.0))"), "stdout={stdout}");
}

#[test]
fn horn_variables_spelled_like_engine_variables_do_not_make_an_unsafe_system_safe() {
    let (stdout, stderr, _dir) = run(HORN_MOD_AUXILIARY_SPELLING, &[]);
    assert_eq!(verdict_lines(&stdout), ["unsat"], "mod: stderr={stderr}");
    let (stdout, stderr, _dir) = run(HORN_CATAMORPHISM_SPELLING, &[]);
    assert_ne!(verdict_lines(&stdout), ["sat"], "cata: stderr={stderr}");
}

#[test]
fn a_selector_whose_name_spells_another_application_does_not_excuse_an_assertion() {
    let (stdout, stderr, _dir) = run(SELECTOR_SPELLING_ANOTHER_APPLICATION, &[]);
    assert_eq!(verdict_lines(&stdout), ["unsat"], "stderr={stderr}");
}

#[test]
fn ctx_solver_simplify_does_not_merge_a_constant_with_the_power_witness() {
    // Hunt probe `embedder-capi/e1_css_graft_merge`: the goal is satisfiable.
    let query = "(declare-const x Real)\n\
        (declare-const y Real)\n\
        (assert (= x 0.0))\n\
        (assert (= y (^ x (- 1))))\n\
        (declare-const |pow_neg_at_zero_2| Real)\n\
        (assert (= |pow_neg_at_zero_2| (+ y 1.0)))\n\
        (apply ctx-solver-simplify)\n\
        (check-sat)\n";
    let (stdout, stderr, _dir) = run(query, &[]);
    assert_eq!(verdict_lines(&stdout), ["sat"], "stderr={stderr}");
    let goal: String = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(!goal.contains("(goal false"), "stdout={stdout}");
    assert!(
        goal.contains("(= pow_neg_at_zero_2 (+ y 1.0))"),
        "stdout={stdout}"
    );
}

#[test]
fn ctx_solver_simplify_accepts_a_constant_redeclared_after_pop() {
    // Hunt probe `embedder-capi/p5_pushpop_only`.
    let query = "(push)\n\
        (declare-const c Int)\n\
        (pop)\n\
        (declare-const c Int)\n\
        (assert (= c 2))\n\
        (apply ctx-solver-simplify)\n";
    let (stdout, stderr, _dir) = run(query, &[]);
    assert!(
        !stdout.contains("(error"),
        "stdout={stdout} stderr={stderr}"
    );
    let goal: String = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(goal.contains("(goal (= c 2)"), "stdout={stdout}");
}

#[test]
fn a_model_parameter_is_not_spelled_like_a_function_the_body_applies() {
    // Hunt probe `fresh-consts/mdl/min_param`.
    let query = "(set-logic UFLIA)\n\
        (set-option :produce-models true)\n\
        (declare-fun |y_0| (Int) Int)\n\
        (declare-fun f (Int) Int)\n\
        (assert (forall ((y Int)) (= (f y) (+ (|y_0| y) 1))))\n\
        (check-sat)\n\
        (get-model)\n";
    let (stdout, stderr, _dir) = run(query, &[]);
    assert_eq!(verdict_lines(&stdout), ["sat"], "stderr={stderr}");
    let model: String = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        !model.contains("(define-fun f ((y_0 Int))"),
        "stdout={stdout}"
    );
    assert!(!model.contains("(y_0 y_0)"), "stdout={stdout}");
}
