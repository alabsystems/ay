// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact integer-existential theorem lane must name its confirming
//! authority in the SAT-evidence signal.
//!
//! Like the checked-projection lane, this chokepoint decides the authored query
//! outright and never reaches `apply_independent_model_gate`, so it used to mint
//! `sat` while writing no `model_check_gate.result` at all. Its confirmation is
//! real — `executor::exact_exists_bounds` reparses the authored root from
//! scratch and proves it true for every valuation of its free integer constants
//! — but an evidence census reading only that key could not see it.
//!
//! No corpus file currently takes this lane, so these tests are the whole
//! regression surface for it.

/// `(exists ((x Int)) (and (> x 5) (< x 10)))`: `U - L = 5 >= 2`, so integer
/// discreteness makes the formula a theorem and the canonical default model a
/// witness by that theorem.
const EXACT_EXISTS_QUERY: &str = r#"
(set-logic LIA)
(assert (exists ((x Int)) (and (> x 5) (< x 10))))
(check-sat)
"#;

/// The `model_check_gate.result` value the ordinary funnel's independent gate
/// writes, and the shared prefix of every confirmed-SAT authority value.
const CONFIRMED_SAT_INDEPENDENT_GATE: &str = "confirmed-sat";

/// The value this lane must publish.
const CONFIRMED_SAT_CHECKED_EXACT_EXISTS: &str = "confirmed-sat-checked-exact-exists";

#[test]
fn exact_exists_sat_names_its_confirming_authority() {
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(EXACT_EXISTS_QUERY);
    assert_eq!(output, ["sat"]);
    assert_eq!(
        gate.as_deref(),
        Some(CONFIRMED_SAT_CHECKED_EXACT_EXISTS),
        "the exact-exists theorem lane must publish its own confirming authority"
    );
}

/// The value must stay distinguishable from the compositional gate's.
///
/// This lane proves a theorem; it does not evaluate a witness compositionally.
/// Reporting the bare `confirmed-sat` would claim an evaluation that never ran,
/// while dropping the shared prefix would hide the verdict from a census that
/// counts confirmed SAT.
#[test]
fn exact_exists_authority_is_distinguishable_from_the_compositional_gate() {
    let (_, gate) = crate::common::solve_authored_vec_with_gate_result(EXACT_EXISTS_QUERY);
    let gate = gate.expect("the exact-exists lane publishes a SAT-evidence signal");
    assert_ne!(
        gate, CONFIRMED_SAT_INDEPENDENT_GATE,
        "a theorem lane must not be reported as the compositional gate's verdict"
    );
    assert!(
        gate.starts_with(CONFIRMED_SAT_INDEPENDENT_GATE),
        "a confirmed-SAT authority value must carry the shared census prefix: {gate}"
    );
}

/// The refuting case never acquires the lane's confirmation value.
///
/// `U - L = 1 < 2` leaves no integer strictly between the bounds, so the same
/// checker decides UNSAT. A SAT-confirmation value here would be a green signal
/// on a verdict that is not `sat` at all.
#[test]
fn refuted_exact_exists_gets_no_sat_confirmation_value() {
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(
        "(set-logic LIA)\n(assert (exists ((x Int)) (and (> x 5) (< x 6))))\n(check-sat)\n",
    );
    assert_eq!(output, ["unsat"]);
    assert_ne!(
        gate.as_deref(),
        Some(CONFIRMED_SAT_CHECKED_EXACT_EXISTS),
        "an UNSAT verdict must never carry a SAT-confirmation authority"
    );
}
