// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The eager-persistent LRA split loop's model-validation recovery
//! (`lra_recover_assignment_verdict`, #split-loop-false-unsat) re-solves the
//! failing assignment and publishes the re-solve's model as the query's model.
//! It must keep the assignment's Bool-sorted constants: re-solving the theory
//! atoms alone left them at a completion default, so the recovered model
//! failed validation against the original assertions and the solve ended
//! `unknown` (om1_with_relays_agreement_two_faults BMC depth 3, about one fresh
//! run in three under load; DPLL_LRA_perf_2026-09-23 §1).

use super::run_script;
use crate::executor::theories::lra::force_loop_model_reject;

#[test]
fn recovered_lra_model_keeps_the_assignment_bool_constants() {
    // b1 must be true and b2 false (x < 3 rules out x > 5), so a completion
    // default of either polarity breaks one of the first two assertions.
    let script = "(set-logic QF_LRA)
(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const x Real)
(assert (or b1 (> x 5.0)))
(assert (or (not b2) (> x 5.0)))
(assert (< x 3.0))
(check-sat)
(get-value (b1 b2))
";
    // Reject the loop's first model publication as if validation had failed:
    // the assignment is theory-SAT, so the guard takes the recovery path.
    force_loop_model_reject(1);
    let out = run_script(script);
    force_loop_model_reject(0);
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}");
    let values = out.get(1).cloned().unwrap_or_default();
    assert!(
        values.contains("(b1 true)") && values.contains("(b2 false)"),
        "recovered model must keep the assignment's Bool constants: {out:?}"
    );
}

#[test]
fn unforced_solve_is_unchanged() {
    let out = run_script(
        "(set-logic QF_LRA)
(declare-const b1 Bool)
(declare-const x Real)
(assert (or b1 (> x 5.0)))
(assert (< x 3.0))
(check-sat)
(get-value (b1))
",
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}");
    assert!(
        out.get(1).is_some_and(|v| v.contains("(b1 true)")),
        "{out:?}"
    );
}
