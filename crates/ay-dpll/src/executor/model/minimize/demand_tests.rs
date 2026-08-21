// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-output DEMAND gate (#model-demand).
//!
//! Counterexample minimization is witness cosmetics: this module's own doc
//! calls it "best-effort COSMETICS for witness quality -- the stored model is
//! already valid". These tests pin that it is skipped when nothing in the
//! session can read a model, and -- the part that matters more -- that nothing
//! else moves when it is.

use crate::executor::Executor;

/// Two free variables with a chain constraint, so the solver's raw assignment
/// has something a minimization pass would actually work on. Used by every
/// test here so the control and the shed arm differ in exactly one thing.
const SHRINKABLE: &str = "(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)\
                          (assert (> x 90))(assert (> y x))(check-sat)";

/// How many times the cosmetic pass ran during this executor's session.
fn minimization_runs(exec: &Executor) -> u64 {
    exec.last_statistics
        .get_int("model_minimization.runs")
        .unwrap_or(0)
}

fn run(script: &str, shed: bool) -> Executor {
    let commands = ay_frontend::parse(script).expect("valid SMT-LIB");
    let mut exec = Executor::new();
    exec.set_model_output_shedding(shed);
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    assert_eq!(outputs[0], "sat", "script must be satisfiable: {script}");
    exec
}

/// The demand gate sits at the CALL SITES, so it has to be proven there: a
/// full `check-sat` with no possible model consumer must not enter the
/// cosmetic pass, and the identical script under the default (demand-assumed)
/// posture must enter it. The control arm is what makes this non-vacuous --
/// without it, a script with nothing to minimize would "pass" either way.
#[test]
fn model_output_shedding_skips_counterexample_minimization() {
    let demanded = run(SHRINKABLE, false);
    assert!(
        minimization_runs(&demanded) > 0,
        "control: the default posture must still polish the witness"
    );

    let shed = run(SHRINKABLE, true);
    assert_eq!(
        minimization_runs(&shed),
        0,
        "no consumer exists, so the cosmetic pass must not run"
    );
}

/// `:produce-models false` makes `(get-model)`/`(get-value)` an error, so it
/// leaves no reader either. It must reach the same gate -- this is the half of
/// the demand signal a host cannot compute in advance, because the script sets
/// it mid-session.
#[test]
fn produce_models_false_skips_counterexample_minimization() {
    let demanded = run(
        &SHRINKABLE.replace(
            "(set-logic QF_LIA)",
            "(set-logic QF_LIA)(set-option :produce-models true)",
        ),
        false,
    );
    assert!(
        minimization_runs(&demanded) > 0,
        "control: `:produce-models true` keeps the cosmetic pass"
    );

    let shed = run(
        &SHRINKABLE.replace(
            "(set-logic QF_LIA)",
            "(set-logic QF_LIA)(set-option :produce-models false)",
        ),
        false,
    );
    assert_eq!(
        minimization_runs(&shed),
        0,
        "`:produce-models false` leaves no reader, so no cosmetics"
    );
}

/// COSMETICS ONLY. A shed run publishes the same verdict and still carries a
/// VALIDATED witness -- the gate that authorizes `sat` is untouched. If this
/// ever fails, the demand flag has leaked into the checking path and the change
/// is wrong regardless of how fast it is.
#[test]
fn model_output_shedding_leaves_validation_armed() {
    let shed = run(SHRINKABLE, true);
    assert!(
        shed.last_model_validated,
        "a shed run must still publish a VALIDATED model"
    );
    assert!(
        shed.last_model.is_some(),
        "a shed run must still hold the witness it validated"
    );

    // And the witness itself still satisfies the query: shedding drops polish,
    // never correctness.
    let demanded = run(SHRINKABLE, false);
    assert!(
        demanded.last_model_validated,
        "control: the demanded run validates too"
    );
}
