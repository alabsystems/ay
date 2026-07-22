// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `Solver::unsat_core_with_farkas()` and the
//! `(get-unsat-core :farkas)` SMT-LIB command extension.
//!
//! Covers the public API surface introduced for #8769. Downstream
//! consumers (model-checker-consumer, VerifierConsumer, deductive-checks, proof-emission pipelines) use this
//! entry point to obtain structured Farkas coefficients alongside the
//! names of the core assertions.

#![allow(deprecated)]

use ay::executor::Executor;
use ay::{Logic, Solver, Sort, TheoryAttribution};

/// Construct a QF_LIA UNSAT instance with two named, contradictory
/// bounds on an integer variable and return the solver after
/// `check_sat()` returns UNSAT.
fn solve_contradiction_lia() -> Solver {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let three = solver.int_const(3);

    // x > 5 AND x < 3 -> UNSAT
    let gt = solver.gt(x, five);
    let lt = solver.lt(x, three);
    solver
        .try_assert_named(gt, "x_gt_5")
        .expect("assert_named succeeds in fresh solver");
    solver
        .try_assert_named(lt, "x_lt_3")
        .expect("assert_named succeeds in fresh solver");

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "expected UNSAT for x > 5 /\\ x < 3, got {result:?}"
    );
    solver
}

#[test]
fn test_unsat_core_with_farkas_returns_annotated_core() {
    let solver = solve_contradiction_lia();

    let core = solver
        .unsat_core_with_farkas()
        .expect("unsat_core_with_farkas should be Some after UNSAT with proofs+cores enabled");

    assert!(
        !core.is_empty(),
        "core should contain at least one named assertion"
    );

    // Core should reference at least one of the named assertions we filed.
    let names: Vec<&str> = core.entries().iter().map(|e| e.name.as_str()).collect();
    assert!(
        names.contains(&"x_gt_5") || names.contains(&"x_lt_3"),
        "core names should include at least one of x_gt_5/x_lt_3: {names:?}"
    );
}

#[test]
fn test_unsat_core_with_farkas_matches_annotated_unsat_core() {
    // The new accessor is documented as a thin alias for
    // `annotated_unsat_core()`; check that the two surfaces agree so
    // model-checker-consumer/VerifierConsumer can rely on either spelling.
    let solver = solve_contradiction_lia();

    let via_alias = solver
        .unsat_core_with_farkas()
        .expect("alias returns Some after UNSAT");
    let via_direct = solver
        .annotated_unsat_core()
        .expect("direct accessor returns Some after UNSAT");

    assert_eq!(
        via_alias.entries().len(),
        via_direct.entries().len(),
        "both accessors must return the same number of core entries"
    );
    assert_eq!(
        via_alias.theories_involved(),
        via_direct.theories_involved(),
        "both accessors must report the same theories_involved list"
    );
}

#[test]
fn test_unsat_core_with_farkas_carries_coefficients_when_present() {
    let solver = solve_contradiction_lia();
    let core = solver
        .unsat_core_with_farkas()
        .expect("unsat_core_with_farkas should be Some after UNSAT");

    // We do not assert specific coefficient values -- only that *when* a
    // Farkas or LiaGeneric attribution is attached, its coefficients
    // vector is non-empty and structurally usable by downstream consumers.
    // LIA conflicts may surface either Farkas directly or wrapped inside
    // LiaGeneric.
    for entry in core.entries() {
        for attr in &entry.attributions {
            match attr {
                TheoryAttribution::Farkas { coefficients } => {
                    assert!(
                        !coefficients.is_empty(),
                        "Farkas attribution on {} must have non-empty coefficients",
                        entry.name
                    );
                }
                TheoryAttribution::LiaGeneric {
                    coefficients: Some(coeffs),
                    ..
                } => {
                    assert!(
                        !coeffs.is_empty(),
                        "LiaGeneric attribution on {} carries a Some(coeffs) with empty vec",
                        entry.name
                    );
                }
                // Other attribution variants carry no Farkas data -- fine.
                _ => {}
            }
        }
    }
}

#[test]
fn test_get_unsat_core_farkas_smtlib_command() {
    // Drive the SMT-LIB textual front-end end-to-end to confirm the
    // `(get-unsat-core :farkas)` extension parses and produces a
    // well-formed s-expression. Consumers that speak SMT-LIB text
    // (model-checker-consumer's existing proxy, Alethe pipelines) rely on this path.
    let input = r#"
(set-logic QF_LIA)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(declare-const x Int)
(assert (! (> x 5) :named x_gt_5))
(assert (! (< x 3) :named x_lt_3))
(check-sat)
(get-unsat-core :farkas)
"#;

    let commands = ay::parse(input).expect("SMT-LIB input parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("executor runs the extended get-unsat-core command");

    // Expect at least two output lines: one `unsat` line from check-sat
    // and one s-expression line from (get-unsat-core :farkas).
    assert!(
        outputs.len() >= 2,
        "expected at least check-sat + get-unsat-core outputs, got {outputs:?}"
    );

    let check_sat_line = outputs
        .iter()
        .find(|s| s.trim() == "unsat")
        .unwrap_or_else(|| panic!("expected 'unsat' in outputs: {outputs:?}"));
    assert_eq!(check_sat_line.trim(), "unsat");

    // The last output is the core. It must be a parenthesized list and
    // reference at least one named assertion. It must NOT be an error
    // message claiming the extension is unsupported (#8769 regression
    // guard).
    let core_line = outputs
        .last()
        .expect("outputs has at least one element (we asserted >= 2)");
    assert!(
        core_line.starts_with('('),
        "get-unsat-core :farkas should emit an s-expression, got: {core_line:?}"
    );
    assert!(
        !core_line.contains("unsupported"),
        "get-unsat-core :farkas must be a supported AY extension, got: {core_line:?}"
    );
    assert!(
        core_line.contains("x_gt_5") || core_line.contains("x_lt_3"),
        "core output should reference at least one named assertion: {core_line:?}"
    );
}

#[test]
fn test_unsat_core_with_farkas_none_when_not_unsat() {
    // Pre-condition: no call to check_sat -> no core yet.
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    assert!(
        solver.unsat_core_with_farkas().is_none(),
        "no check_sat yet -> None"
    );

    // SAT result also yields None (the core is only meaningful on UNSAT).
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);
    let result = solver.check_sat();
    assert!(result.is_sat(), "expected SAT");
    assert!(
        solver.unsat_core_with_farkas().is_none(),
        "SAT result -> unsat_core_with_farkas is None"
    );
}
