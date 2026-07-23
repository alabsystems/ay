// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Optimization (OMT) executor tests — single and multi-objective.

use crate::Executor;
use ay_frontend::parse;
use ay_frontend::sexp::parse_sexp;

#[test]
fn test_executor_optimize_maximize_qf_lia() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize (+ (* 2 x) y))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    assert_eq!(pair[1].as_numeral(), Some("20"));
}

#[test]
fn test_executor_optimize_maximize_qf_lia_equality_pinned_objective() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 20))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).expect("SMT-LIB input should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("optimizer should execute equality-pinned objective");

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).expect("objective output should parse");
    let items = sexp.as_list().expect("objective output should be a list");
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1]
        .as_list()
        .expect("objective entry should be a pair");
    assert_eq!(pair.len(), 2);
    assert_eq!(pair[1].as_numeral(), Some("20"));
}

#[test]
fn test_executor_optimize_maximize_qf_lra() {
    // Maximize x subject to 0 <= x <= 10.5. Optimal: x = 10.5 = 21/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 0.0))
        (assert (<= x (/ 21 2)))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 21/2 = 10.5
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str.contains("21") && val_str.contains("2"),
        "expected 21/2 (10.5), got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_minimize_qf_lra() {
    // Minimize x subject to x >= 3.5. Optimal: x = 3.5 = 7/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x (/ 7 2)))
        (assert (<= x 100.0))
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 7/2 = 3.5
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str.contains("7") && val_str.contains("2"),
        "expected 7/2 (3.5), got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_real_linear_combination() {
    // Maximize (+ (* (/ 3 1) x) (* (/ 2 1) y)) subject to x + y <= 10, x >= 0, y >= 0.
    // Optimal at vertex (10, 0): objective = 30.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x (/ 0 1)))
        (assert (>= y (/ 0 1)))
        (assert (<= (+ x y) (/ 10 1)))
        (maximize (+ (* (/ 3 1) x) (* (/ 2 1) y)))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str == "30" || val_str.contains("30"),
        "expected 30, got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_real_unsat() {
    // Infeasible constraints: x >= 5 and x <= 3.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 5.0))
        (assert (<= x 3.0))
        (maximize x)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}

// --- Multi-objective (lexicographic) tests (#4128 Phase 2) ---

#[test]
fn test_executor_optimize_lex_two_objectives_qf_lia() {
    // Lexicographic: maximize x first, then maximize y.
    // Constraints: x + y <= 10, x >= 0, y >= 0.
    // Optimal: x = 10 (maximized first), then y = 0 (constrained by x = 10).
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 3);

    let pair_x = items[1].as_list().unwrap();
    assert_eq!(pair_x[1].as_numeral(), Some("10"));

    let pair_y = items[2].as_list().unwrap();
    assert_eq!(pair_y[1].as_numeral(), Some("0"));
}

#[test]
fn test_executor_optimize_lex_min_then_max_qf_lia() {
    // Lexicographic: minimize x first, then maximize y.
    // Constraints: x + y <= 10, x >= 0, y >= 0.
    // Optimal: x = 0 (minimized first), then y = 10 (x pinned to 0).
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (minimize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 3);

    let pair_x = items[1].as_list().unwrap();
    assert_eq!(pair_x[1].as_numeral(), Some("0"));

    let pair_y = items[2].as_list().unwrap();
    assert_eq!(pair_y[1].as_numeral(), Some("10"));
}

#[test]
fn test_executor_optimize_lex_real_two_objectives() {
    // Lexicographic Real: maximize x first, then maximize y.
    // Use separate bounds (not x+y combined) so simplex converges exactly.
    // x in [0, 21/2], y in [0, 7/2].
    // Optimal: x = 21/2 (maximized first), then y = 7/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x (/ 0 1)))
        (assert (<= x (/ 21 2)))
        (assert (>= y (/ 0 1)))
        (assert (<= y (/ 7 2)))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 3);

    let pair_x = items[1].as_list().unwrap();
    let val_x = format!("{}", pair_x[1]);
    assert!(
        val_x.contains("21") && val_x.contains("2"),
        "expected 21/2 for x, got: {val_x}"
    );

    let pair_y = items[2].as_list().unwrap();
    let val_y = format!("{}", pair_y[1]);
    assert!(
        val_y.contains("7") && val_y.contains("2"),
        "expected 7/2 for y, got: {val_y}"
    );
}

// --- Optimization blocking constraint model extraction regression (#8515) ---

/// Regression test for #8515: optimization blocking constraints introduce new
/// SAT variables that are not present in the persistent solver's variable
/// arrays. Model extraction and provenance must not panic on out-of-bounds
/// access when iterating over term_to_var entries from those extra variables.
///
/// The trigger path: (1) check-sat with optimization (maximize/minimize)
/// calls check_sat_assuming repeatedly with new bound constraints, (2) each
/// call creates new terms (>= x bound), which get new Tseitin SAT variables,
/// (3) the model's term_to_var mapping includes these new variables, (4)
/// capture_trail_provenance or blocking clause construction indexes into the
/// persistent solver's arrays with these out-of-range indices.
#[test]
fn test_executor_optimize_blocking_constraint_no_overflow_8515() {
    // Use incremental mode (push/pop) + optimization to maximize the chance
    // of hitting the code path where blocking constraints are added.
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (>= x 0))
        (assert (<= x 100))
        (assert (>= y 0))
        (assert (<= y 100))
        (assert (>= z 0))
        (assert (<= z 100))
        (assert (<= (+ x y z) 50))
        (maximize (+ x y z))
        (check-sat)
        (get-model)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should not panic during model extraction or provenance.
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "optimization should return sat"
    );
    // Model output should be well-formed (at least starts with '(').
    assert!(
        outputs[1].starts_with('('),
        "model output should start with '('"
    );
}

/// Regression test for #8515: multi-objective optimization with get-model
/// exercises the full model extraction path after multiple rounds of
/// check-sat-assuming with blocking constraints.
#[test]
fn test_executor_optimize_multi_objective_model_no_overflow_8515() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (assert (>= a 0))
        (assert (<= a 20))
        (assert (>= b 0))
        (assert (<= b 20))
        (assert (<= (+ a b) 30))
        (maximize a)
        (minimize b)
        (check-sat)
        (get-model)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // The key assertion: no panic during model extraction.
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "multi-objective optimization should return sat"
    );
}

// --- Multi-variable objective regression tests (#8278) ---

#[test]
fn test_executor_optimize_minimize_multi_var_sum_qf_lra() {
    // Regression test for #8278: minimize (+ x0 x1) with x0, x1 in [-1, 1].
    // Expected optimal: x0 = -1, x1 = -1, objective = -2.
    // The iterative approach incorrectly converged to approximately -1 because
    // the SAT solver only adjusted one variable per iteration.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x0 Real)
        (declare-const x1 Real)
        (assert (>= x0 (- 1.0)))
        (assert (<= x0 1.0))
        (assert (>= x1 (- 1.0)))
        (assert (<= x1 1.0))
        (minimize (+ x0 x1))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value should be -2 (or -(2/1) etc.)
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str.contains("-2") || val_str.contains("(- 2"),
        "expected -2 for minimize (+ x0 x1) with bounds [-1,1], got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_maximize_multi_var_sum_qf_lra() {
    // Maximize (+ x0 x1) with x0, x1 in [-1, 1].
    // Expected optimal: x0 = 1, x1 = 1, objective = 2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x0 Real)
        (declare-const x1 Real)
        (assert (>= x0 (- 1.0)))
        (assert (<= x0 1.0))
        (assert (>= x1 (- 1.0)))
        (assert (<= x1 1.0))
        (maximize (+ x0 x1))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str == "2.0",
        "expected 2.0 for maximize (+ x0 x1) with bounds [-1,1], got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_minimize_constrained_sum_qf_lra() {
    // Minimize (+ x y) subject to x + y >= 5, x >= 0, y >= 0.
    // Optimal: x + y = 5 (the lower bound of the sum constraint).
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0.0))
        (assert (>= y 0.0))
        (assert (>= (+ x y) 5.0))
        (minimize (+ x y))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str == "5.0",
        "expected 5.0 for minimize (+ x y) subject to x+y>=5, got: {val_str}"
    );
}

/// #8694: Unbounded minimize still produces correct sat result
/// (warnings go to stderr but optimization completes).
#[test]
fn test_optimize_unbounded_minimize_still_solves() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ x y) 37))
        (minimize (+ x y))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should still return sat even with unbounded variables
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    // The objective value should be 37 (pinned by equality)
    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);
    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    assert_eq!(pair[1].as_numeral(), Some("37"));
}

/// #8694: Unbounded maximize still produces correct sat result.
#[test]
fn test_optimize_unbounded_maximize_still_solves() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 42))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    let pair = items[1].as_list().unwrap();
    assert_eq!(pair[1].as_numeral(), Some("42"));
}

/// Genuinely-unbounded Real maximize must report `oo`, not a finite value.
///
/// Regression for the wrong-optimization-result bug: `x` is unbounded above
/// (only constrained by `x - y <= 5` with `y >= 0`), so the LRA simplex reports
/// Unbounded. The executor must surface this as `oo` in `get-objectives` instead
/// of falling into the iterative strict-improvement loop, which would print an
/// arbitrary finite value (~5).
#[test]
fn test_optimize_unbounded_maximize_real_reports_oo() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0.0))
        (assert (>= y 0.0))
        (assert (<= (- x y) 5.0))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(
        outputs[1].contains("oo") && !outputs[1].contains("(* (- 1) oo)"),
        "expected unbounded maximize to report `oo`, got: {}",
        outputs[1]
    );
}

/// Genuinely-unbounded Real minimize must report `(* (- 1) oo)` (the exact
/// z3 shape; z3 5.0.0, unchanged from 4.15.4), not a finite value.
///
/// Regression: `x <= 10` leaves `x` unbounded below, so the simplex reports
/// Unbounded; `get-objectives` must print `(* (- 1) oo)` rather than an
/// arbitrary finite value (e.g. -64 from the iterative fallback).
#[test]
fn test_optimize_unbounded_minimize_real_reports_neg_oo() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 10.0))
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(
        outputs[1].contains("(* (- 1) oo)"),
        "expected unbounded minimize to report `(* (- 1) oo)`, got: {}",
        outputs[1]
    );
}

/// #8694: Bounded variables should not produce warnings.
/// This test verifies optimization works on fully bounded variables.
#[test]
fn test_optimize_bounded_no_warnings() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= x 50))
        (assert (<= y 50))
        (assert (<= (+ x y) 37))
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    let pair = items[1].as_list().unwrap();
    assert_eq!(pair[1].as_numeral(), Some("0"));
}

/// #8708: Regression guard for index-out-of-bounds panic in minimize over
/// QF_LIA with a pre-existing upper bound on the objective variable.
///
/// The bug: `(minimize total)` over an integer variable that already has an
/// asserted upper bound (`<= total 100`) plus a linear equality definition
/// (`total = c10 + c9 + c1`) exercised the optimization-blocking-constraint
/// path in `check_sat_assuming`. That path captured trail provenance for
/// variables whose index exceeded the persistent SAT solver's variable count,
/// panicking at `crates/ay-sat/src/solver/incremental.rs:241`
/// (`val_at(vals, var_idx * 2)`) with "index out of bounds: len=8 index=16".
///
/// Root-cause fix: `capture_trail_provenance` now skips `term_to_var` entries
/// whose `var_idx >= sat.total_num_vars()` (see
/// `crates/ay-dpll/src/executor.rs`, guard added for #8515 and validated here
/// for #8708).
///
/// This coin-change encoding exercises the original failure shape. It must
/// return `sat` with an integer objective value and must not panic.
#[test]
fn test_optimize_minimize_coin_change_no_panic_8708() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const c10 Int)
        (declare-const c9 Int)
        (declare-const c1 Int)
        (declare-const total Int)
        (assert (>= c10 0))
        (assert (>= c9 0))
        (assert (>= c1 0))
        (assert (= (+ (* 10 c10) (* 9 c9) (* 1 c1)) 37))
        (assert (= total (+ c10 c9 c1)))
        (assert (<= total 100))
        (minimize total)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    // The pre-fix binary panicked here. Executing must succeed.
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    let pair = items[1].as_list().unwrap();
    assert_eq!(pair[0].as_symbol(), Some("total"));
    // Optimal coin count for amount 37 with denominations {10, 9, 1} is 4
    // (e.g., 1*10 + 3*9 = 37 via 4 coins). The exact witness may vary; the
    // essential property is that the objective matches the encoding.
    let got = pair[1]
        .as_numeral()
        .expect("objective must be a numeral")
        .parse::<i64>()
        .expect("objective must parse as integer");
    assert_eq!(got, 4, "optimal coin count for 37 with {{10,9,1}} is 4");
}

/// #8708: Minimize with explicit objective-variable upper bound but no lower
/// bound on contributors. Exercises the optimization blocking-constraint path
/// with fewer auxiliary variables than the coin-change encoding, narrowing the
/// regression surface.
#[test]
fn test_optimize_minimize_with_upper_bound_no_panic_8708() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const total Int)
        (assert (>= a 0))
        (assert (>= b 0))
        (assert (= total (+ a b)))
        (assert (<= total 1000))
        (assert (>= (+ (* 3 a) (* 5 b)) 17))
        (minimize total)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    let pair = items[1].as_list().unwrap();
    // Optimal: 3a + 5b >= 17 with a,b >= 0 minimizing a+b.
    // Candidates: b=4,a=0 -> total=4, sum 20. b=3,a=1 -> total=4, sum 14 (fails).
    // b=4,a=0 satisfies with total=4. b=3,a=1 -> 3+5=8 (fails). a=0,b=4 -> 20>=17 ok.
    // a=4,b=1 -> 17>=17 ok, total=5. a=0,b=4 -> total=4 is better.
    let got = pair[1]
        .as_numeral()
        .expect("objective must be a numeral")
        .parse::<i64>()
        .expect("objective must parse as integer");
    assert_eq!(got, 4, "optimal a+b subject to 3a+5b>=17 is 4 (a=0,b=4)");
}

/// Contract: a `set_timeout` deadline bounds the whole `(check-sat)` with
/// objectives, and an expired deadline yields `unknown`, never `sat`.
///
/// Background: `optimize_check_sat` enters through `check_sat_internal()`
/// and used to bypass `install_timeout_deadline_for_call()` (which only
/// `check_sat()`/`check_sat_assuming()` run), so the BASE objective solve at
/// the top of the optimization driver carried no deadline and deadline-aware
/// theory probes (the IntSat fixpoint, `propagate_with_deadline` with
/// `deadline: None`) ran unbounded — surfaced as a multi-minute hang of
/// `prop_minimize_never_panics_8708` once Fix B1 made eager solves (and
/// their IntSat probes) the default for the blocking-constraint re-solves.
/// `optimize_check_sat` now installs the deadline around the entire run.
#[test]
fn optimize_check_sat_honors_set_timeout_deadline() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize (+ (* 2 x) y))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::ZERO));
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unknown"),
        "zero-timeout optimization must observe the installed deadline"
    );
}

#[test]
fn nested_array_false_unsat_with_objective_is_quarantined() {
    let repro = include_str!("../../../../repros/cs_stateful-1.i_2.MINIMIZED.smt2");
    let input = repro.replacen("(check-sat)", "(minimize 0)\n(check-sat)", 1);
    let commands = parse(&input).expect("nested-array optimization repro parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("nested-array optimization repro executes");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unknown"),
        "optimization must not bypass the nested-array UNSAT quarantine"
    );
}

// --- BOX multi-objective tests (Z3 `(set-option :opt.priority box)`) ---

/// Helper: run an SMT-LIB string and return the `(check-sat)` verdict followed
/// by the `(get-objectives)` output. Asserts both commands are present.
fn run_two(input: &str) -> (String, String) {
    let commands = parse(input).expect("input should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should succeed");
    (outputs[0].clone(), outputs[1].clone())
}

/// Helper: extract the numeral value of the i-th objective (1-based for the
/// objective pairs; index 0 is the `objectives` head) from a `(get-objectives)`
/// output string.
fn objective_numeral(get_objectives: &str, pair_index: usize) -> String {
    let sexp = parse_sexp(get_objectives).expect("objectives output should parse");
    let items = sexp.as_list().expect("objectives output should be a list");
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    let pair = items[pair_index]
        .as_list()
        .expect("objective entry should be a pair");
    pair[1]
        .as_numeral()
        .expect("objective value should be a numeral")
        .to_string()
}

/// ORACLE (the core correctness gate): each BOX optimum must equal optimizing
/// that objective ALONE against the same hard constraints.
///
/// Constraints: x + y <= 10, x, y >= 0. Maximize x AND maximize y in box mode.
/// Box optimum of x is 10 (optimizing x alone), box optimum of y is 10
/// (optimizing y alone) — neither constrains the other. We assert each box
/// optimum equals the value from a SEPARATE single-objective run.
#[test]
fn test_box_oracle_matches_single_objective_runs() {
    let box_input = r#"
        (set-option :opt.priority box)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(box_input);
    assert_eq!(verdict, "sat");
    let box_x = objective_numeral(&objs, 1);
    let box_y = objective_numeral(&objs, 2);

    // Oracle: optimize x ALONE.
    let only_x = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;
    let (vx, ox) = run_two(only_x);
    assert_eq!(vx, "sat");
    let oracle_x = objective_numeral(&ox, 1);

    // Oracle: optimize y ALONE.
    let only_y = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (vy, oy) = run_two(only_y);
    assert_eq!(vy, "sat");
    let oracle_y = objective_numeral(&oy, 1);

    assert_eq!(
        box_x, oracle_x,
        "box optimum of x ({box_x}) must equal optimizing x alone ({oracle_x})"
    );
    assert_eq!(
        box_y, oracle_y,
        "box optimum of y ({box_y}) must equal optimizing y alone ({oracle_y})"
    );
    // Concretely: both independent optima are 10.
    assert_eq!(box_x, "10");
    assert_eq!(box_y, "10");
}

/// Regression for objective-identity aliasing: declaration index, not `TermId`,
/// identifies an objective. Z3 reports `(x 10)` then `(x 0)` for this exact
/// script; both SMT-LIB rows must remain distinct even though they print the
/// same expression.
#[test]
fn test_box_duplicate_term_objectives_keep_distinct_values() {
    let input = r#"
        (set-option :opt.priority box)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 10))
        (maximize x)
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objectives) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objectives, 1), "10", "{objectives}");
    assert_eq!(objective_numeral(&objectives, 2), "0", "{objectives}");
}

/// Same identity regression for unbounded outcomes: two declarations over the
/// same Real term have opposite infinities in box mode and must not overwrite
/// each other in the renderer's outcome cache.
#[test]
fn test_box_duplicate_term_objectives_keep_distinct_infinities() {
    let input = r#"
        (set-option :opt.priority box)
        (set-logic QF_LRA)
        (declare-const x Real)
        (maximize x)
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objectives) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(objectives, "(objectives\n (x oo)\n (x (* (- 1) oo))\n)\n");
}

/// Lex differs from box after an unbounded prefix. There is no model attaining
/// the first objective's `+oo`, so the later objective has no scalar lex optimum
/// (Z3 reports an interval). AY's SMT-LIB surface fails honestly rather than
/// printing the independently optimized `-oo` value that box mode would have.
#[test]
fn test_lex_unbounded_prefix_makes_suffix_unavailable() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (maximize x)
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objectives) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(
        objectives,
        "(error \"objective 1 is unavailable after a lexicographic predecessor with no attainable optimum\")"
    );
}

/// BOX vs LEX DIFFER where expected.
///
/// Constraints: x + y <= 10, x, y >= 0. Objectives: maximize x, then maximize y.
/// - LEX: x is pinned to 10 first, so y's optimum is constrained to 0.
/// - BOX: y is optimized independently, so its optimum is the freer value 10.
///
/// This proves box does NOT commit objective-1's optimum onto objective-2.
#[test]
fn test_box_vs_lex_differ_second_objective_is_freer() {
    let common = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;

    // LEX (default, no option): y constrained to 0 by x = 10.
    let (lex_verdict, lex_objs) = run_two(common);
    assert_eq!(lex_verdict, "sat");
    let lex_x = objective_numeral(&lex_objs, 1);
    let lex_y = objective_numeral(&lex_objs, 2);
    assert_eq!(lex_x, "10");
    assert_eq!(lex_y, "0", "lex must pin y to 0 once x=10 is committed");

    // BOX: y free to reach 10.
    let box_input = format!("(set-option :opt.priority box){common}");
    let (box_verdict, box_objs) = run_two(&box_input);
    assert_eq!(box_verdict, "sat");
    let box_x = objective_numeral(&box_objs, 1);
    let box_y = objective_numeral(&box_objs, 2);
    assert_eq!(box_x, "10");
    assert_eq!(
        box_y, "10",
        "box must report y's INDEPENDENT optimum 10, unconstrained by x"
    );

    // The whole point: box and lex disagree on objective 2.
    assert_ne!(
        box_y, lex_y,
        "box and lex objective-2 optima must differ on this instance"
    );
}

/// `(set-option :opt.priority box)` is parsed and routes to box mode.
/// (Behavioral proof: it produces the box optimum, which differs from lex.)
#[test]
fn test_box_option_parsing_routes_to_box() {
    let input = r#"
        (set-option :opt.priority box)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    // Box-specific outcome: both independent optima are 10.
    assert_eq!(objective_numeral(&objs, 1), "10");
    assert_eq!(objective_numeral(&objs, 2), "10");
}

/// Explicit `(set-option :opt.priority lex)` keeps lexicographic behavior,
/// identical to the no-option default.
#[test]
fn test_lex_option_explicit_matches_default() {
    let body = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (_, default_objs) = run_two(body);
    let explicit = format!("(set-option :opt.priority lex){body}");
    let (_, explicit_objs) = run_two(&explicit);
    assert_eq!(
        objective_numeral(&default_objs, 1),
        objective_numeral(&explicit_objs, 1)
    );
    assert_eq!(
        objective_numeral(&default_objs, 2),
        objective_numeral(&explicit_objs, 2)
    );
    // Sanity: lex pins y to 0.
    assert_eq!(objective_numeral(&explicit_objs, 2), "0");
}

/// An unbounded objective in BOX mode must still report unbounded (`oo`).
///
/// Maximize x (unbounded above: only x - y <= 5 with y >= 0) AND minimize y
/// (bounded below by 0) in box mode. The unbounded objective reports `oo`; the
/// bounded one reports its independent optimum (0).
#[test]
fn test_box_unbounded_objective_reports_oo() {
    let input = r#"
        (set-option :opt.priority box)
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= y 0.0))
        (assert (<= (- x y) 5.0))
        (maximize x)
        (minimize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    // First objective (maximize x) unbounded above.
    assert!(
        objs.contains("oo") && !objs.contains("(* (- 1) oo)"),
        "box unbounded maximize must report `oo`, got: {objs}"
    );
    // Second objective (minimize y) has independent optimum 0.
    let sexp = parse_sexp(&objs).expect("objectives output should parse");
    let items = sexp.as_list().expect("objectives output should be a list");
    let pair_y = items[2].as_list().expect("y objective should be a pair");
    let y_val = format!("{}", pair_y[1]);
    assert!(
        y_val == "0" || y_val.contains("0"),
        "box minimize y independent optimum should be 0, got: {y_val}"
    );
}

/// `opt.priority=pareto` is handled HONESTLY: it does not error and falls back
/// to lexicographic (a sound per-objective optimum), since Pareto enumeration is
/// out of scope. We assert it produces the LEX outcome (y pinned to 0), proving
/// we did not silently treat it as box or crash.
#[test]
fn test_box_pareto_falls_back_to_lex_honestly() {
    let input = r#"
        (set-option :opt.priority pareto)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objs, 1), "10");
    assert_eq!(
        objective_numeral(&objs, 2),
        "0",
        "pareto must fall back to lex (y pinned to 0), not box"
    );
}

/// BOX min-then-max oracle on Real, mixing directions.
///
/// x in [0, 21/2], y in [0, 7/2], independent. Box: minimize x (optimum 0) and
/// maximize y (optimum 7/2). Each must match its single-objective run.
#[test]
fn test_box_oracle_real_mixed_directions() {
    let box_input = r#"
        (set-option :opt.priority box)
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x (/ 0 1)))
        (assert (<= x (/ 21 2)))
        (assert (>= y (/ 0 1)))
        (assert (<= y (/ 7 2)))
        (minimize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(box_input);
    assert_eq!(verdict, "sat");
    let sexp = parse_sexp(&objs).unwrap();
    let items = sexp.as_list().unwrap();
    let box_x = format!("{}", items[1].as_list().unwrap()[1]);
    let box_y = format!("{}", items[2].as_list().unwrap()[1]);

    // Oracle: minimize x alone -> 0.
    let only_x = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x (/ 0 1)))
        (assert (<= x (/ 21 2)))
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;
    let (_, ox) = run_two(only_x);
    let oracle_x = format!(
        "{}",
        parse_sexp(&ox).unwrap().as_list().unwrap()[1]
            .as_list()
            .unwrap()[1]
    );

    // Oracle: maximize y alone -> 7/2.
    let only_y = r#"
        (set-logic QF_LRA)
        (declare-const y Real)
        (assert (>= y (/ 0 1)))
        (assert (<= y (/ 7 2)))
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (_, oy) = run_two(only_y);
    let oracle_y = format!(
        "{}",
        parse_sexp(&oy).unwrap().as_list().unwrap()[1]
            .as_list()
            .unwrap()[1]
    );

    assert_eq!(box_x, oracle_x, "box min x must match minimize-x-alone");
    assert_eq!(box_y, oracle_y, "box max y must match maximize-y-alone");
    assert_eq!(box_x, "0.0");
    assert_eq!(box_y, "(/ 7.0 2.0)", "box max y should be 7/2");
}

// --- BitVector OPTIMIZATION objectives (Phase 2 "wider unsilo") -------------
//
// Z3 SEMANTICS (verified empirically against Z3 4.x, 2026-06-15):
//   * Z3 optimizes the UNSIGNED integer value of a BV objective (NOT signed).
//     Decisive `(_ BitVec 4)` test with x in {#x7 (=7), #xf (=15 / -1 signed)}:
//       (minimize x) -> (objectives (x 7))    => picks 7  => UNSIGNED
//       (maximize x) -> (objectives (x 15))   => picks 15 => UNSIGNED
//   * `(get-objectives)` reports the optimum as a DECIMAL numeral (`(x 7)`);
//     `(get-value (x))` reports the bitvector literal (`((x #x7))`).

/// Brute-force every value of a small-width unsigned BV domain to find the TRUE
/// optimum under a constraint, used as the soundness oracle for AY's BV
/// optimizer. `feasible(v)` reports whether the value `v` is allowed by the hard
/// constraints (here, a simple inclusive interval).
fn bv_brute_optimum(width: u32, maximize: bool, feasible: impl Fn(u64) -> bool) -> Option<u64> {
    let domain = 1u64 << width;
    let mut best: Option<u64> = None;
    for v in 0..domain {
        if !feasible(v) {
            continue;
        }
        best = Some(match best {
            None => v,
            Some(b) if maximize => b.max(v),
            Some(b) => b.min(v),
        });
    }
    best
}

/// Width-`w` SMT-LIB bitvector literal (hex when divisible by 4, else binary)
/// matching AY/Z3 output conventions.
fn bv_lit(value: u64, width: u32) -> String {
    if width.is_multiple_of(4) {
        format!("#x{:0width$x}", value, width = (width / 4) as usize)
    } else {
        format!("#b{:0width$b}", value, width = width as usize)
    }
}

/// BRUTE-FORCE ORACLE (the core soundness gate): for widths 1..=4, every
/// inclusive interval `[lo, hi]`, and both directions, AY's BV optimum must equal
/// the value found by enumerating the entire finite domain. This is the
/// independent check that AY never reports a wrong BV optimum.
#[test]
fn test_bv_optimize_brute_force_oracle_width_le_4() {
    for width in 1u32..=4 {
        let max = (1u64 << width) - 1;
        for lo in 0..=max {
            for hi in lo..=max {
                for &maximize in &[false, true] {
                    let dir = if maximize { "maximize" } else { "minimize" };
                    let input = format!(
                        "(declare-const x (_ BitVec {width}))\n\
                         (assert (bvuge x {}))\n\
                         (assert (bvule x {}))\n\
                         ({dir} x)\n\
                         (check-sat)\n\
                         (get-objectives)\n",
                        bv_lit(lo, width),
                        bv_lit(hi, width),
                    );
                    let (verdict, objs) = run_two(&input);
                    assert_eq!(
                        verdict, "sat",
                        "width {width} [{lo},{hi}] {dir}: expected sat"
                    );
                    let ay = objective_numeral(&objs, 1);
                    let truth = bv_brute_optimum(width, maximize, |v| v >= lo && v <= hi)
                        .expect("interval is non-empty");
                    assert_eq!(
                        ay,
                        truth.to_string(),
                        "width {width} [{lo},{hi}] {dir}: AY optimum {ay} != brute-force {truth}"
                    );
                }
            }
        }
    }
}

/// Z3 CROSS-CHECK (hardcoded values captured from Z3 4.x in Step 0): the
/// distinguishing signed-vs-unsigned case proves AY matches Z3's UNSIGNED
/// semantics and decimal `(get-objectives)` shape exactly. x ranges over
/// {#x7 (=7), #xf (=15 unsigned / -1 signed)}.
#[test]
fn test_bv_optimize_unsigned_matches_z3_signed_distinguishing() {
    // minimize: Z3 picks 7 (unsigned), NOT -1 (signed). Captured: (objectives (x 7)).
    let (verdict, objs) = run_two(
        "(declare-const x (_ BitVec 4))\n\
         (assert (or (= x #x7) (= x #xf)))\n\
         (minimize x)\n(check-sat)\n(get-objectives)\n",
    );
    assert_eq!(verdict, "sat");
    assert_eq!(
        objective_numeral(&objs, 1),
        "7",
        "unsigned minimize must pick 7, not -1 (signed)"
    );

    // maximize: Z3 picks 15 (unsigned), NOT 7. Captured: (objectives (x 15)).
    let (verdict, objs) = run_two(
        "(declare-const x (_ BitVec 4))\n\
         (assert (or (= x #x7) (= x #xf)))\n\
         (maximize x)\n(check-sat)\n(get-objectives)\n",
    );
    assert_eq!(verdict, "sat");
    assert_eq!(
        objective_numeral(&objs, 1),
        "15",
        "unsigned maximize must pick 15"
    );
}

/// `(get-value)` reports the BV optimum as a BITVECTOR literal (Z3 shape),
/// while `(get-objectives)` reports the decimal. Captured from Z3:
/// `(get-objectives) -> (x 12)`, `(get-value (x)) -> ((x #xc))`.
#[test]
fn test_bv_optimize_get_value_reports_bitvector_literal() {
    let input = "(declare-const x (_ BitVec 4))\n\
         (assert (bvule x #xC))\n\
         (maximize x)\n(check-sat)\n(get-objectives)\n(get-value (x))\n";
    let commands = parse(input).expect("input should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should succeed");
    assert_eq!(outputs[0], "sat");
    // get-objectives: decimal 12.
    assert_eq!(objective_numeral(&outputs[1], 1), "12");
    // get-value: bitvector literal #xc (parses as a Hexadecimal sexp node, so
    // compare its serialized form rather than `as_symbol`).
    let sexp = parse_sexp(&outputs[2]).expect("get-value output should parse");
    let items = sexp.as_list().expect("get-value is a list");
    let pair = items[0].as_list().expect("first pair is a list");
    assert_eq!(pair[1].to_string(), "#xc");
}

/// An UNCONSTRAINED BV objective is finite-domain bounded: maximize yields the
/// domain max, minimize yields 0 (matches Z3). This exercises the warm-start
/// fallback for an objective the base model may leave unassigned.
#[test]
fn test_bv_optimize_unconstrained_uses_full_domain() {
    let (v, objs) =
        run_two("(declare-const x (_ BitVec 8))\n(maximize x)\n(check-sat)\n(get-objectives)\n");
    assert_eq!(v, "sat");
    assert_eq!(objective_numeral(&objs, 1), "255", "8-bit max is 255");

    let (v, objs) =
        run_two("(declare-const x (_ BitVec 8))\n(minimize x)\n(check-sat)\n(get-objectives)\n");
    assert_eq!(v, "sat");
    assert_eq!(objective_numeral(&objs, 1), "0", "8-bit min is 0");
}

/// BOX composition (the previously-erroring path now SUCCEEDS): two BV
/// objectives under `(set-option :opt.priority box)` are each optimized
/// INDEPENDENTLY against the hard constraints. Cross-checked against single-
/// objective runs (the box oracle) and against the brute-force domain optimum.
#[test]
fn test_bv_optimize_box_two_objectives_compose() {
    let box_input = "(set-option :opt.priority box)\n\
         (declare-const x (_ BitVec 4))\n\
         (declare-const y (_ BitVec 4))\n\
         (assert (bvuge x #x2))\n\
         (assert (bvule y #xC))\n\
         (minimize x)\n(maximize y)\n(check-sat)\n(get-objectives)\n";
    let (verdict, objs) = run_two(box_input);
    assert_eq!(verdict, "sat");
    let box_x = objective_numeral(&objs, 1);
    let box_y = objective_numeral(&objs, 2);

    // Box optimum of x (minimize, x >= 2) is 2; of y (maximize, y <= 12) is 12.
    assert_eq!(box_x, "2");
    assert_eq!(box_y, "12");

    // Oracle: each box optimum equals optimizing that objective ALONE.
    let (_, only_x) = run_two(
        "(declare-const x (_ BitVec 4))\n(assert (bvuge x #x2))\n\
         (minimize x)\n(check-sat)\n(get-objectives)\n",
    );
    let (_, only_y) = run_two(
        "(declare-const y (_ BitVec 4))\n(assert (bvule y #xC))\n\
         (maximize y)\n(check-sat)\n(get-objectives)\n",
    );
    assert_eq!(
        box_x,
        objective_numeral(&only_x, 1),
        "box x == minimize-x-alone"
    );
    assert_eq!(
        box_y,
        objective_numeral(&only_y, 1),
        "box y == maximize-y-alone"
    );

    // Brute-force the same independent optima.
    assert_eq!(
        box_x,
        bv_brute_optimum(4, false, |v| v >= 2).unwrap().to_string()
    );
    assert_eq!(
        box_y,
        bv_brute_optimum(4, true, |v| v <= 12).unwrap().to_string()
    );
}

/// LEX composition: minimize x then maximize y under `x + y == 10` (mod 16).
/// Lex commits x's optimum (0) before maximizing y, so y -> 10. Confirms the
/// `mk_commit_le`/`mk_commit_ge` BV arms pin the first objective correctly.
#[test]
fn test_bv_optimize_lex_two_objectives_commit() {
    let input = "(declare-const x (_ BitVec 4))\n\
         (declare-const y (_ BitVec 4))\n\
         (assert (= (bvadd x y) #xA))\n\
         (minimize x)\n(maximize y)\n(check-sat)\n(get-objectives)\n";
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    // x minimized to 0; with x=0, y=10 is forced and is also the max.
    assert_eq!(objective_numeral(&objs, 1), "0");
    assert_eq!(objective_numeral(&objs, 2), "10");
}

/// REGRESSION: the case that previously returned
/// `unsupported optimization: unsupported objective sort: BitVec(...)` now
/// succeeds and reports the correct optimum.
#[test]
fn test_bv_optimize_previously_erroring_case_now_succeeds() {
    let input = "(declare-const x (_ BitVec 4))\n\
         (assert (bvuge x #x3))\n\
         (minimize x)\n(check-sat)\n(get-objectives)\n";
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat", "BV objective must no longer error");
    assert_eq!(objective_numeral(&objs, 1), "3", "min of x>=3 is 3");
}

// --- PARETO multi-objective tests (Z3 `(set-option :opt.priority pareto)`) ---
//
// Z3 protocol (verified empirically, Z3 4.15.4, 2026-06-15): pareto mode is
// STATEFUL. Each `(check-sat)` returns `sat` and emits the NEXT Pareto-optimal
// point (reported by `(get-objectives)`); once the front is exhausted
// `(check-sat)` returns `unsat` and a FURTHER `(check-sat)` RESTARTS the front.
// AY matches the SET of Pareto points and the sat/unsat/cyclic protocol; AY's
// emission ORDER is its own deterministic GIA discovery order (Z3's order is
// algorithm-specific, so we assert the SET, not the sequence).

/// Run a script and return every output line (one per command output).
fn run_all(input: &str) -> Vec<String> {
    let commands = parse(input).expect("input should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("execution should succeed")
}

/// Extract the SET of pareto points emitted by a script of alternating
/// `(check-sat)`/`(get-objectives)` pairs. Each point is the sorted-by-objective
/// vector of numerals from a `sat` get-objectives output; `unsat` verdicts (and
/// the get-objectives that follow them) are skipped. The objective COUNT per
/// point is `n_obj`.
fn collect_pareto_points(outputs: &[String], n_obj: usize) -> std::collections::BTreeSet<Vec<i64>> {
    let mut set = std::collections::BTreeSet::new();
    let mut i = 0;
    while i + 1 < outputs.len() {
        let verdict = &outputs[i];
        let objs = &outputs[i + 1];
        if verdict == "sat" {
            let mut point = Vec::with_capacity(n_obj);
            for k in 1..=n_obj {
                let v: i64 = objective_numeral(objs, k)
                    .parse()
                    .expect("objective numeral should parse as i64");
                point.push(v);
            }
            set.insert(point);
        }
        i += 2;
    }
    set
}

/// Brute-force the TRUE Pareto front of a small 2-var Int instance:
/// `x,y in [0,xy_max]`, `x+y <= sum_max`, maximize both. Returns the
/// non-dominated set of `(x,y)` points.
fn brute_force_pareto_max_max(xy_max: i64, sum_max: i64) -> std::collections::BTreeSet<Vec<i64>> {
    let mut feasible: Vec<(i64, i64)> = Vec::new();
    for x in 0..=xy_max {
        for y in 0..=xy_max {
            if x + y <= sum_max {
                feasible.push((x, y));
            }
        }
    }
    // p dominates q iff p>=q on both AND strictly > on at least one (both max).
    let dominates = |p: (i64, i64), q: (i64, i64)| -> bool {
        p.0 >= q.0 && p.1 >= q.1 && (p.0 > q.0 || p.1 > q.1)
    };
    let mut front = std::collections::BTreeSet::new();
    for &p in &feasible {
        if !feasible.iter().any(|&q| dominates(q, p)) {
            front.insert(vec![p.0, p.1]);
        }
    }
    front
}

/// ORACLE (the core correctness gate): AY's enumerated Pareto set must EXACTLY
/// equal the true Pareto front computed by brute force — no missing point, no
/// extra point, no dominated point.
#[test]
fn test_pareto_brute_force_oracle_2obj_int() {
    // x,y in [0,4], x+y <= 4, maximize both. True front: x+y == 4.
    let input = r#"
        (set-option :opt.priority pareto)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= x 4))
        (assert (<= y 4))
        (assert (<= (+ x y) 4))
        (maximize x)
        (maximize y)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
    "#;
    let outputs = run_all(input);
    let ay_set = collect_pareto_points(&outputs, 2);
    let true_front = brute_force_pareto_max_max(4, 4);
    assert_eq!(
        ay_set, true_front,
        "AY pareto front must equal the brute-force true front exactly"
    );
    // Concretely: {(0,4),(1,3),(2,2),(3,1),(4,0)}.
    assert_eq!(ay_set.len(), 5);
}

/// Z3 CROSS-CHECK: the SET captured from Z3 (Step 0) must equal AY's set.
///
/// Z3's pareto sequence for `x+y<=4` (maximize x, maximize y) is the 5 points
/// where x+y=4: (3,1),(2,2),(1,3),(4,0),(0,4) — captured verbatim. AY's emission
/// order differs but the SET must match (documented ordering choice).
#[test]
fn test_pareto_z3_cross_check_set() {
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 0) (>= y 0) (<= (+ x y) 4)))
        (maximize x)
        (maximize y)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
    "#;
    let ay_set = collect_pareto_points(&run_all(input), 2);
    // Captured from `z3 -in` on the identical Step-0 script.
    let z3_set: std::collections::BTreeSet<Vec<i64>> =
        [vec![3, 1], vec![2, 2], vec![1, 3], vec![4, 0], vec![0, 4]]
            .into_iter()
            .collect();
    assert_eq!(ay_set, z3_set, "AY pareto SET must match Z3's captured SET");
}

/// The terminal `(check-sat)` returns `unsat` once the front is exhausted, and
/// `(get-objectives)` then reports the LAST emitted point (matching Z3).
#[test]
fn test_pareto_terminal_check_sat_is_unsat() {
    // 3-point front (x+y<=2): (2,0),(1,1),(0,2).
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 0) (>= y 0) (<= (+ x y) 2)))
        (maximize x)
        (maximize y)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
    "#;
    let outputs = run_all(input);
    // outputs: [v0,o0, v1,o1, v2,o2, v3,o3]; three sats then the terminal unsat.
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[2], "sat");
    assert_eq!(outputs[4], "sat");
    assert_eq!(
        outputs[6], "unsat",
        "4th check-sat must be unsat (front exhausted)"
    );
    // The full SET is correct.
    let ay_set = collect_pareto_points(&outputs, 2);
    assert_eq!(ay_set, brute_force_pareto_max_max(2, 2));
    // get-objectives after the terminal unsat still reports a valid last point.
    let last = &outputs[7];
    assert!(
        last.contains("objectives") && last.contains("(x ") && last.contains("(y "),
        "get-objectives after terminal unsat must report the last point, got: {last}"
    );
}

/// Z3 CYCLIC RESTART: after the terminal `unsat`, a further `(check-sat)`
/// restarts the front from the first point. A 3-point front over 8 check-sats
/// must yield `sat sat sat unsat sat sat sat unsat`.
#[test]
fn test_pareto_cyclic_restart_matches_z3() {
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 0) (>= y 0) (<= (+ x y) 2)))
        (maximize x)
        (maximize y)
        (check-sat)(check-sat)(check-sat)(check-sat)
        (check-sat)(check-sat)(check-sat)(check-sat)
    "#;
    let outputs = run_all(input);
    let verdicts: Vec<&str> = outputs.iter().map(String::as_str).collect();
    assert_eq!(
        verdicts,
        vec!["sat", "sat", "sat", "unsat", "sat", "sat", "sat", "unsat"],
        "pareto must restart the front after the terminal unsat (Z3 cyclic behavior)"
    );
}

/// MIXED min/max: maximize x AND minimize y, 2 <= x+y <= 4. (x=4,y=0) dominates
/// every other feasible point (max x, min y simultaneously), so the front is the
/// single point {(4,0)} — exactly Z3's answer.
#[test]
fn test_pareto_mixed_min_max_single_point() {
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 0) (>= y 0) (<= (+ x y) 4) (>= (+ x y) 2)))
        (maximize x)
        (minimize y)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
    "#;
    let outputs = run_all(input);
    assert_eq!(outputs[0], "sat");
    assert_eq!(objective_numeral(&outputs[1], 1), "4");
    assert_eq!(objective_numeral(&outputs[1], 2), "0");
    assert_eq!(outputs[2], "unsat", "front is the single dominating point");
}

/// A 3-OBJECTIVE Pareto front (x+y+z <= 2, maximize all). The true front is every
/// (a,b,c) with a+b+c == 2 and a,b,c >= 0 — 6 points. AY must emit exactly that
/// set, then unsat. (Z3 returns the same 6-point set.)
#[test]
fn test_pareto_three_objectives() {
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (and (>= x 0) (>= y 0) (>= z 0) (<= (+ x y z) 2)))
        (maximize x)
        (maximize y)
        (maximize z)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
    "#;
    let outputs = run_all(input);
    let ay_set = collect_pareto_points(&outputs, 3);
    // Brute-force true 3-objective front: all (a,b,c) with a+b+c == 2.
    let mut true_front = std::collections::BTreeSet::new();
    for a in 0..=2 {
        for b in 0..=2 {
            for c in 0..=2 {
                if a + b + c == 2 {
                    true_front.insert(vec![a, b, c]);
                }
            }
        }
    }
    assert_eq!(ay_set, true_front, "3-objective pareto front must be exact");
    assert_eq!(ay_set.len(), 6);
    // The 7th check-sat (after all 6 points) is unsat.
    assert_eq!(outputs[12], "unsat");
}

/// BV pareto: 3-bit x,y with `bvule (bvadd x y) #b100` (== 4). The unsigned
/// front (note bvadd wraps mod 8) is {(7,5),(6,6),(5,7)} — matches Z3's SET.
#[test]
fn test_pareto_bitvec_objectives() {
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x (_ BitVec 3))
        (declare-const y (_ BitVec 3))
        (assert (bvule (bvadd x y) (_ bv4 3)))
        (maximize x)
        (maximize y)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
    "#;
    let outputs = run_all(input);
    let ay_set = collect_pareto_points(&outputs, 2);
    let z3_set: std::collections::BTreeSet<Vec<i64>> =
        [vec![7, 5], vec![6, 6], vec![5, 7]].into_iter().collect();
    assert_eq!(ay_set, z3_set, "BV pareto SET must match Z3");
    assert_eq!(
        outputs[6], "unsat",
        "4th check-sat exhausts the 3-point BV front"
    );
}

/// STATE RESET: after a partial pareto enumeration, a new `(assert ...)`
/// invalidates the pareto state and switching to `lex` produces the correct lex
/// answer (no leaked front). Proves pareto state is hooked into the same
/// invalidation as `last_check_result`.
#[test]
fn test_pareto_state_resets_on_assert_then_lex() {
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 0) (>= y 0) (<= (+ x y) 4)))
        (maximize x)
        (maximize y)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (assert (= x 2))
        (set-option :opt.priority lex)
        (check-sat)(get-objectives)
    "#;
    let outputs = run_all(input);
    // Two pareto points first.
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[2], "sat");
    // Then lex with x pinned to 2: x=2 (its only value), y maximized to 2.
    let lex_verdict = &outputs[4];
    let lex_objs = &outputs[5];
    assert_eq!(lex_verdict, "sat");
    assert_eq!(objective_numeral(lex_objs, 1), "2", "x pinned to 2");
    assert_eq!(
        objective_numeral(lex_objs, 2),
        "2",
        "lex must maximize y under x=2 (=> y<=2): the pareto front must NOT leak"
    );
}

/// A FRESH pareto query after an exhausted one (with reset in between via a new
/// objective set) re-enumerates from scratch — no stale state.
#[test]
fn test_pareto_fresh_query_after_reset() {
    // First a full small enumeration to exhaustion, then `(reset)`, then a new
    // pareto problem. The second front must be computed cleanly.
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const a Int)
        (declare-const b Int)
        (assert (and (>= a 0) (>= b 0) (<= (+ a b) 1)))
        (maximize a)
        (maximize b)
        (check-sat)(check-sat)(check-sat)
        (reset)
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 0) (>= y 0) (<= (+ x y) 2)))
        (maximize x)
        (maximize y)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
        (check-sat)(get-objectives)
    "#;
    let outputs = run_all(input);
    // First problem: 2-point front (a+b<=1): (1,0),(0,1), so sat sat unsat.
    assert_eq!(&outputs[0..3], &["sat", "sat", "unsat"]);
    // Second problem (after reset): the 3-point front for x+y<=2.
    let second = &outputs[3..];
    let ay_set = collect_pareto_points(second, 2);
    assert_eq!(ay_set, brute_force_pareto_max_max(2, 2));
}

/// A Real objective under `pareto` is NOT supported (AY's LRA multi-objective
/// optimizer is itself incomplete); it falls back to lex SOUNDLY rather than
/// risk emitting a non-Pareto point. The result must be a sound verdict, never a
/// panic or a wrong point. (We assert only the sound `sat` verdict and that the
/// pareto enumeration was NOT engaged — the exact Real optimum is governed by
/// AY's pre-existing LRA epsilon arithmetic, not by this increment.)
#[test]
fn test_pareto_real_objective_falls_back_to_lex_soundly() {
    let input = r#"
        (set-option :opt.priority pareto)
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0.0))
        (assert (>= y 0.0))
        (assert (<= x 5.0))
        (assert (<= y 5.0))
        (assert (<= (+ x y) 4.0))
        (maximize x)
        (maximize y)
        (check-sat)(get-objectives)
    "#;
    let commands = parse(input).expect("input should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("Real pareto must fall back to lex soundly, never erroring");
    // Sound verdict; the front fell back to lex so pareto_state must stay empty.
    assert_eq!(outputs[0], "sat");
    assert!(
        exec.pareto_state.is_none(),
        "Real pareto must not engage the pareto enumerator"
    );
    // get-objectives produces a well-formed objectives list (no error/panic).
    assert!(
        outputs[1].contains("objectives"),
        "get-objectives must be well-formed after the lex fallback, got: {}",
        outputs[1]
    );
}

/// #8708 (acceptance criterion): Fuzz test for `(minimize ...)` with random
/// objectives.
///
/// Generates small random QF_LIA formulae with 2–3 integer variables, random
/// linear equality constraints, directional objective bounds, and a random
/// linear objective (either `minimize` or `maximize`). The property under test
/// is that the optimizer never panics — regardless of satisfiability or
/// whether the objective variable has a pre-asserted bound that previously
/// triggered the `incremental.rs:241` index-out-of-bounds crash.
///
/// The generated objectives are bounded in the optimization direction so the
/// test stays within normal CI budgets while still exploring the encodings that
/// exercise the optimization blocking-constraint path in `check_sat_assuming`.
#[cfg(test)]
mod minimize_fuzz_8708 {
    use super::*;
    use proptest::prelude::*;
    use std::time::Duration;

    /// Build a random QF_LIA `(minimize ...)` / `(maximize ...)` formula.
    ///
    /// Returns `(smt_source, objective_name)`. The generator is intentionally
    /// biased toward the shapes that historically panicked:
    /// - objective variable defined by a linear equality, and
    /// - an asserted upper/lower bound on the objective variable.
    fn gen_minimize_smt() -> impl Strategy<Value = (String, &'static str)> {
        // 2..=3 contributor variables (small, to keep per-case cost low).
        let n_contribs = 2usize..=3usize;
        // Objective direction.
        let direction = prop_oneof![Just("minimize"), Just("maximize")];
        // Bound magnitude on the objective variable. Each generated objective
        // receives both a regression-shape pre-bound and a directional bound,
        // so optimization terminates quickly instead of spending the full
        // search budget on unbounded cases.
        let obj_bound = 1i64..=50i64;
        // Target sum for the linear equality constraint.
        let target = 1i64..=20i64;
        // Coefficients for the linear equality (keep small to avoid blowups).
        let coeffs = prop::collection::vec(1i64..=5i64, 2..=3);
        // Whether to add a per-contributor non-negativity lower bound.
        let nonneg = any::<bool>();

        (n_contribs, direction, obj_bound, target, coeffs, nonneg).prop_map(
            |(n, dir, bound, tgt, mut cs, nn)| {
                cs.truncate(n);
                while cs.len() < n {
                    cs.push(1);
                }
                let mut smt = String::new();
                smt.push_str("(set-logic QF_LIA)\n");
                for i in 0..n {
                    smt.push_str(&format!("(declare-const x{i} Int)\n"));
                }
                smt.push_str("(declare-const total Int)\n");
                if nn {
                    for i in 0..n {
                        smt.push_str(&format!("(assert (>= x{i} 0))\n"));
                    }
                }
                // Linear equality: sum(c_i * x_i) = target
                smt.push_str("(assert (= (+");
                for (i, c) in cs.iter().enumerate() {
                    smt.push_str(&format!(" (* {c} x{i})"));
                }
                smt.push_str(&format!(") {tgt}))\n"));
                // Linear definition: total = sum(x_i)
                smt.push_str("(assert (= total (+");
                for i in 0..n {
                    smt.push_str(&format!(" x{i}"));
                }
                smt.push_str(")))\n");
                // Asserted bounds on the objective variable. The first bound
                // in each branch is the shape that exercised the blocking-
                // constraint path in #8708; the second keeps the objective
                // bounded in the optimization direction for test reliability.
                match dir {
                    "minimize" => {
                        smt.push_str(&format!("(assert (<= total {bound}))\n"));
                        smt.push_str(&format!("(assert (>= total (- {bound})))\n"));
                    }
                    _ => {
                        smt.push_str(&format!("(assert (>= total (- {bound})))\n"));
                        smt.push_str(&format!("(assert (<= total {bound}))\n"));
                    }
                }
                smt.push_str(&format!("({dir} total)\n"));
                smt.push_str("(check-sat)\n");
                smt.push_str("(get-objectives)\n");
                (smt, "total")
            },
        )
    }

    proptest! {
        // Keep cases modest: the assertion budget is "does not panic", so we
        // prioritize coverage of shapes over large case counts. 16 cases keeps
        // this well within the default per-test budget even in debug builds,
        // while still exercising the blocking-constraint path on diverse
        // encodings (different direction, variable counts, coefficients, and
        // bound configurations).
        #![proptest_config(ProptestConfig { cases: 16, .. ProptestConfig::default() })]

        /// Property: for any random small QF_LIA formula with `(minimize total)`
        /// or `(maximize total)`, the optimizer terminates without panicking
        /// (result must be sat, unsat, or unknown — never a panic and never an
        /// unexpected error variant).
        #[test]
        fn prop_minimize_never_panics_8708((smt, _obj) in gen_minimize_smt()) {
            let commands = match parse(&smt) {
                Ok(c) => c,
                // Parser rejection is fine; we only care that the optimizer
                // cannot panic on anything that parses.
                Err(_) => return Ok(()),
            };
            let mut exec = Executor::new();
            exec.set_timeout(Some(Duration::from_millis(250)));
            // The core property: execute_all must return a Result rather than
            // panicking. Both Ok and Err are acceptable; only an index-out-of-
            // bounds panic would fail this test.
            let res = exec.execute_all(&commands);
            match res {
                Ok(outputs) => {
                    // First output is the check-sat verdict.
                    if let Some(first) = outputs.first() {
                        prop_assert!(
                            matches!(first.as_str(), "sat" | "unsat" | "unknown"),
                            "unexpected verdict for minimize fuzz input: {first:?}\n{smt}"
                        );
                    }
                }
                Err(_e) => {
                    // Errors are acceptable (e.g., unsupported encodings);
                    // only panics fail this property.
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Unbounded-objective detection (#unbounded-oo): Int objectives reach the
// audited LP-relaxation probe; the faithfulness audits keep every relaxation
// (Boolean structure, opaque sub-terms) fail-closed. z3 shapes verified live
// (z3 5.0.0, unchanged from 4.15.4): maximize -> `oo`, minimize -> `(* (- 1) oo)`.
// ---------------------------------------------------------------------------

/// Unbounded Int maximize: `sat` + `(x oo)` (z3 shape), like the Real path.
/// Previously: 128-round exponential search exhausted -> `unknown` +
/// `(error "objectives are not available")`.
#[test]
fn test_optimize_unbounded_maximize_int_reports_oo() {
    let input = r#"
        (declare-const x Int)
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert!(
        objs.contains("oo") && !objs.contains("(* (- 1) oo)"),
        "unbounded Int maximize must report `oo`, got: {objs}"
    );
}

/// Unbounded Int minimize: `sat` + `(x (* (- 1) oo))` — z3's exact spelling
/// (z3 5.0.0, unchanged from 4.15.4; NOT `(- oo)`).
#[test]
fn test_optimize_unbounded_minimize_int_reports_neg_oo() {
    let input = r#"
        (declare-const x Int)
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert!(
        objs.contains("(* (- 1) oo)"),
        "unbounded Int minimize must report `(* (- 1) oo)`, got: {objs}"
    );
}

/// A one-sided (non-strict) bound leaves the Int objective unbounded in the
/// optimize direction: still `oo`.
#[test]
fn test_optimize_unbounded_int_with_lower_bound_reports_oo() {
    let input = r#"
        (declare-const x Int)
        (assert (>= x 100))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert!(objs.contains("oo"), "expected `oo`, got: {objs}");
}

/// A composite LINEAR Int objective parses faithfully, so unboundedness is
/// still provable: `(+ x (* 2 y))` free -> `oo`.
#[test]
fn test_optimize_unbounded_composite_int_objective_reports_oo() {
    let input = r#"
        (declare-const x Int)
        (declare-const y Int)
        (maximize (+ x (* 2 y)))
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert!(objs.contains("oo"), "expected `oo`, got: {objs}");
}

/// `(get-model)` after a sat-with-unbounded-objective run must produce a
/// valid model of the hard constraints (z3 does the same).
#[test]
fn test_get_model_after_unbounded_int_maximize() {
    let input = r#"
        (declare-const x Int)
        (assert (>= x 3))
        (maximize x)
        (check-sat)
        (get-objectives)
        (get-model)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(
        outputs[1].contains("oo"),
        "expected `oo`, got: {}",
        outputs[1]
    );
    assert!(
        outputs[2].contains("define-fun x"),
        "get-model after sat+oo must return a model, got: {}",
        outputs[2]
    );
    assert!(
        !outputs[2].contains("error"),
        "get-model after sat+oo must not error, got: {}",
        outputs[2]
    );
}

/// Bounded Int objectives are UNCHANGED by the probe (fail-safe direction):
/// non-strict and strict upper bounds still produce the exact optimum.
#[test]
fn test_optimize_bounded_int_unchanged_by_unbounded_probe() {
    let (verdict, objs) = run_two(
        r#"
        (declare-const x Int)
        (assert (<= x 5))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#,
    );
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objs, 1), "5");
    assert!(
        !objs.contains("oo"),
        "bounded maximize must not report oo: {objs}"
    );

    // Strict bound: the LP probe fails closed (strict-bound gate) and the
    // exact search still answers 4.
    let (verdict, objs) = run_two(
        r#"
        (declare-const x Int)
        (assert (< x 5))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#,
    );
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objs, 1), "4");
    assert!(
        !objs.contains("oo"),
        "bounded maximize must not report oo: {objs}"
    );
}

/// WRONG-oo regression (Real): `(or (<= x 5) (<= x 3))` bounds x, but the
/// standalone LRA skips the or-term, so pre-fix simplex concluded Unbounded
/// over a RELAXATION and printed `sat (x oo)` (z3: 5). The faithfulness audit
/// must reject the verdict: `unknown` or the true optimum 5 are both
/// acceptable — `oo` never is.
#[test]
fn test_optimize_or_bounded_real_must_not_report_oo() {
    let input = r#"
        (declare-const x Real)
        (assert (or (<= x 5.0) (<= x 3.0)))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert!(
        !objs.contains("oo"),
        "or-bounded Real maximize must not report oo (verdict {verdict}), got: {objs}"
    );
    assert!(
        verdict == "unknown" || objs.contains('5'),
        "expected unknown or optimum 5, got verdict {verdict}, objectives {objs}"
    );
}

/// WRONG-oo regression (Int twin): the or-bounded Int objective must keep its
/// exact optimum 5 (the audit forces the probe to NotApplicable and the
/// exponential+binary search answers via the full solver).
#[test]
fn test_optimize_or_bounded_int_stays_exact() {
    let input = r#"
        (declare-const x Int)
        (assert (or (<= x 5) (<= x 3)))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objs, 1), "5");
}

/// REFUTATION CASE (ite atom, Real): `(= y (ite c 1.0 2.0))` parses with
/// `has_unsupported == false` (link-lemma protocol), so pre-fix the standalone
/// simplex concluded `sat (y oo)` over a relaxation (z3: 2). Only the
/// backing-term audit catches it. The true optimum 2 or unknown are
/// acceptable; `oo` never is.
#[test]
fn test_optimize_ite_atom_real_must_not_report_oo() {
    let input = r#"
        (declare-const c Bool)
        (declare-const y Real)
        (assert (= y (ite c 1.0 2.0)))
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert!(
        !objs.contains("oo"),
        "ite-bounded Real maximize must not report oo (verdict {verdict}), got: {objs}"
    );
    assert!(
        verdict == "unknown" || objs.contains('2'),
        "expected unknown or optimum 2, got verdict {verdict}, objectives {objs}"
    );
}

/// REFUTATION CASE (ite atom, Int): must stay exactly 2 — the design's
/// original probe-first Int arm without the backing-term audit regressed this
/// to `oo`.
#[test]
fn test_optimize_ite_atom_int_stays_exact() {
    let input = r#"
        (declare-const c Bool)
        (declare-const y Int)
        (assert (= y (ite c 1 2)))
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objs, 1), "2");
}

/// REFUTATION CASE (opaque objective, nonlinear): bounded `maximize (* x x)`
/// must stay 25 — the objective parse interns `(* x x)` as a fresh FREE
/// variable, so without the backing-term audit the LP probe reads it as
/// unbounded.
#[test]
fn test_optimize_bounded_nonlinear_int_objective_stays_exact() {
    let input = r#"
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 5))
        (maximize (* x x))
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objs, 1), "25");
}

/// REFUTATION CASE (opaque objective, div): bounded `maximize (div x 2)` must
/// stay 5 for the same reason.
#[test]
fn test_optimize_bounded_div_int_objective_stays_exact() {
    let input = r#"
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 10))
        (maximize (div x 2))
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(objective_numeral(&objs, 1), "5");
}

/// GATED unbounded Int objective stays fail-closed (`unknown`, never `oo`):
/// the Bool-var assertion fails the faithfulness audit, so the LP probe is
/// NotApplicable and the exhaustive exponential search (128 cheap probes
/// here) exhausts without an infeasible bound — today's honest unknown.
/// This is the Int twin of `test_optimize_bool_var_assertion_fails_closed`
/// and the executor-level pin of the fail-safe direction; the NONLINEAR
/// gated shapes (`(= y (* x x))`, opaque objectives) are pinned at the LRA
/// level in `tests::faithfulness_audit` and by
/// `test_optimize_bounded_nonlinear_int_objective_stays_exact` (their
/// unbounded twins spend minutes in the pre-existing NIA search lane, which
/// does not poll the executor deadline — too slow for a unit test).
#[test]
fn test_optimize_gated_unbounded_int_falls_closed_to_unknown() {
    let input = r#"
        (declare-const p Bool)
        (declare-const x Int)
        (assert p)
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(
        verdict, "unknown",
        "expected fail-closed unknown, got {verdict}: {objs}"
    );
    assert!(
        !objs.contains("oo"),
        "gated unbounded Int must not report oo: {objs}"
    );
}

/// Boolean structure that does NOT constrain the objective still fails
/// closed: `(assert p)(maximize x)` was `oo` pre-fix (and that answer happened
/// to be right), but the audit cannot distinguish irrelevant Boolean structure
/// from load-bearing structure, so it flips to `unknown` — the review accepted
/// this completeness regression. Pin "unknown, not wrong": a finite value or
/// `oo` printed alongside `sat` would both be acceptable improvements later,
/// but today's contract is unknown.
#[test]
fn test_optimize_bool_var_assertion_fails_closed() {
    let input = r#"
        (declare-const p Bool)
        (declare-const x Real)
        (assert p)
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(
        verdict, "unknown",
        "expected fail-closed unknown, got {verdict}: {objs}"
    );
    assert!(
        !objs.contains("oo"),
        "unknown run must not report oo: {objs}"
    );
}

/// BOX mode with one unbounded and one bounded INT objective: the unbounded
/// one reports `oo`, the bounded one its independent optimum (matches z3).
#[test]
fn test_box_mixed_int_unbounded_and_bounded() {
    let input = r#"
        (set-option :opt.priority box)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= y 0))
        (maximize x)
        (minimize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert!(
        objs.contains("oo"),
        "box unbounded Int maximize must report oo: {objs}"
    );
    assert_eq!(objective_numeral(&objs, 2), "0");
}

/// LEX with an unbounded FIRST Int objective: the first supremum is not
/// attained, so there is no model at which the later objective has a scalar
/// lexicographic optimum. Match the Real-valued contract above and fail
/// honestly instead of reporting an independently optimized suffix value.
#[test]
fn test_optimize_lex_unbounded_then_bounded_int() {
    let input = r#"
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= y 3))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(verdict, "sat");
    assert_eq!(
        objs,
        "(error \"objective 1 is unavailable after a lexicographic predecessor with no attainable optimum\")"
    );
}

/// PARETO with an unbounded objective: no Pareto-optimal point exists, so
/// enumeration must fail CLOSED (`unknown`, objectives unavailable) — never
/// emit a fake "Pareto-optimal" point. (z3 does not terminate on this input.)
#[test]
fn test_optimize_pareto_with_unbounded_objective_fails_closed() {
    let input = r#"
        (set-option :opt.priority pareto)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= y 0))
        (assert (<= y 5))
        (maximize x)
        (maximize y)
        (check-sat)
        (get-objectives)
    "#;
    let (verdict, objs) = run_two(input);
    assert_eq!(
        verdict, "unknown",
        "pareto with unbounded axis must be unknown: {objs}"
    );
    assert!(
        objs.contains("error"),
        "objectives must be unavailable after fail-closed pareto, got: {objs}"
    );
}
