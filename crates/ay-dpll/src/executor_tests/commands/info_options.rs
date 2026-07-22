// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========== Get-Info Tests ==========

#[test]
fn test_get_info_name() {
    let input = r#"
        (get-info :name)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("ay"),
        "Expected solver name: {}",
        outputs[0]
    );
}

#[test]
fn test_get_info_version() {
    let input = r#"
        (get-info :version)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].starts_with("(:version \""),
        "Expected SMT-LIB string-valued version info: {}",
        outputs[0]
    );
    assert!(
        outputs[0].ends_with("\")"),
        "Expected SMT-LIB string-valued version info: {}",
        outputs[0]
    );
    for field in [
        "build.version=",
        "build.increment=",
        "build.commit=",
        "build.datetime_utc=",
        "build.stamp=",
    ] {
        assert!(
            outputs[0].contains(field),
            "Expected structured build provenance field {field}: {}",
            outputs[0]
        );
    }
}

#[test]
fn test_get_info_assertion_stack_levels() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (get-info :assertion-stack-levels)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("assertion-stack-levels"),
        "Expected assertion-stack-levels: {}",
        outputs[0]
    );
}

#[test]
fn test_get_info_all_statistics() {
    // Test Z3-compatible :all-statistics format (#647)
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should have check-sat result and statistics
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");

    // Statistics should use Z3-compatible format (keyword-value pairs, sorted)
    let stats = &outputs[1];
    assert!(
        stats.starts_with("(:"),
        "Expected s-expression starting with (:, got: {stats}"
    );
    assert!(
        stats.contains(":conflicts"),
        "Expected :conflicts stat: {stats}"
    );
    assert!(
        stats.contains(":decisions"),
        "Expected :decisions stat: {stats}"
    );
    assert!(
        stats.contains(":propagations"),
        "Expected :propagations stat: {stats}"
    );
    // Should NOT have the old :all-statistics wrapper
    assert!(
        !stats.contains(":all-statistics"),
        "Should not wrap in :all-statistics: {stats}"
    );
}

#[test]
fn test_get_info_all_statistics_theory_path() {
    // Test that statistics are populated on theory solve paths (#648)
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");

    // Statistics should be populated (not all zeros from default)
    let stats = &outputs[1];
    // After solving, at least some activity should have occurred
    // The stats should have real values, but we don't assert specific numbers
    // since they depend on the solver's internal behavior
    assert!(
        stats.contains(":conflicts"),
        "Expected :conflicts stat: {stats}"
    );
    assert!(
        stats.contains(":propagations"),
        "Expected :propagations stat: {stats}"
    );
    assert!(
        stats.contains(":theory-conflicts"),
        "Expected :theory-conflicts stat: {stats}"
    );

    let theory_conflicts = get_numeral_stat(stats, ":theory-conflicts")
        .expect("expected :theory-conflicts numeral value");
    assert!(
        theory_conflicts > 0,
        "Expected non-zero theory conflicts, got {theory_conflicts}: {stats}"
    );
}

#[test]
fn test_get_info_dpll_round_trips_nonzero_4802() {
    // Test that DPLL(T) phase timing appears in statistics for QF_LRA.
    // QF_LRA defaults to the incremental split-loop pipeline, which emits
    // dpll.round-trips and timing stats but not dpll.eager.* counters while
    // the #6586 TheoryExtension packet remains disabled.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (< y 10.0))
        (assert (= (+ x y) 7.0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");

    let stats = &outputs[1];
    // dpll.round-trips must be present and non-zero for theory formulas
    // (underscores are converted to hyphens in SMT-LIB output)
    assert!(
        stats.contains(":dpll.round-trips"),
        "Expected :dpll.round-trips in stats: {stats}"
    );
    // Verify non-zero round trip count
    assert!(
        !stats.contains(":dpll.round-trips       0"),
        "Expected non-zero dpll.round-trips: {stats}"
    );
    // Stats emitted by the incremental split-loop pipeline
    assert_stats_contains_all(
        stats,
        &[
            ":time.dpll.sat-solve",
            ":time.dpll.theory-check",
            ":time.dpll.theory-sync",
            ":time.construct.preprocess",
        ],
    );
}

fn assert_stats_contains_all(stats: &str, keys: &[&str]) {
    for key in keys {
        assert!(stats.contains(key), "Expected {key} in stats: {stats}");
    }
}

#[test]
fn test_get_info_unsupported() {
    let input = r#"
        (get-info :nonexistent-keyword)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("error"),
        "Expected error for unsupported keyword: {}",
        outputs[0]
    );
}

// ========== get-option tests ==========

#[test]
fn test_get_option_produce_models() {
    let input = r#"
        (get-option :produce-models)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("produce-models"),
        "Expected produce-models: {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains("true"),
        "Expected true value: {}",
        outputs[0]
    );
}

#[test]
fn test_get_option_print_success() {
    let input = r#"
        (get-option :print-success)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("print-success"),
        "Expected print-success: {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains("false"),
        "Expected false value (default): {}",
        outputs[0]
    );
}

#[test]
fn test_get_option_random_seed() {
    let input = r#"
        (get-option :random-seed)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("random-seed"),
        "Expected random-seed: {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains('0'),
        "Expected 0 (default): {}",
        outputs[0]
    );
}

#[test]
fn test_set_and_get_option() {
    let input = r#"
        (set-option :random-seed 42)
        (get-option :random-seed)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("42"),
        "Expected 42 after set-option: {}",
        outputs[0]
    );
}

#[test]
fn test_set_option_random_seed_applies_to_sat_solver() {
    let input = r#"
        (set-option :random-seed 42)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let mut solver = SatSolver::new(0);
    exec.apply_random_seed_to_sat(&mut solver);

    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn test_set_and_get_option_bool() {
    let input = r#"
        (set-option :print-success true)
        (get-option :print-success)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("true"),
        "Expected true after set-option: {}",
        outputs[0]
    );
}

#[test]
fn test_set_and_get_option_string_escapes() {
    // SMT-LIB 2.6: `""` is the escape for an embedded quote (a backslash is a
    // literal character, so the old `\"` form is no longer a quote escape — see
    // ay-core::unescape_string_contents, commit 204a245f). The set value
    // `say ""hi""` denotes `say "hi"`; get-option must re-emit it canonically
    // (doubled quotes) so the printed option s-expression round-trips.
    let input = r#"
        (set-option :diagnostic-output-channel "say ""hi""")
        (get-option :diagnostic-output-channel)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);

    let sexp = parse_sexp(&outputs[0]).unwrap();
    let SExpr::List(ref items) = sexp else {
        panic!("Expected option s-expression list, got: {sexp:?}");
    };
    assert_eq!(items.len(), 2, "Option sexp: {items:?}");
    assert!(matches!(&items[0], SExpr::Keyword(k) if k == ":diagnostic-output-channel"));
    assert!(matches!(&items[1], SExpr::String(s) if s == r#"say "hi""#));
}

#[test]
fn test_get_option_unknown() {
    let input = r#"
        (get-option :nonexistent-option)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("error"),
        "Expected error for unknown option: {}",
        outputs[0]
    );
}

// ========== echo tests ==========

#[test]
fn test_echo_basic() {
    let input = r#"
        (echo "hello")
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["hello"]);
}

#[test]
fn test_echo_with_escape_sequences() {
    // SMT-LIB strings: only \\ and \" are interpreted as escape sequences.
    // \n is NOT a newline - it's a literal backslash followed by 'n'.
    // See the development design notes
    let input = r#"
        (echo "hello\nworld")
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Output is literal backslash-n, not a newline character
    assert_eq!(outputs, vec![r"hello\nworld"]);
}
