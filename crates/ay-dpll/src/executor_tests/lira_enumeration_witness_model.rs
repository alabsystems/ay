// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LIRA: a model the LIA side answered with a direct-enumeration witness is
//! published as that witness.
//!
//! Measured (2026-10-01, CLI and Z3 C API alike): `(and (< b a) (= y x) p)`
//! with Int `a b`, Real `x y` and Bool `p` answered `unknown` ("strict
//! model-validation oracle arithmetic rejected assertion 1"). After a theory
//! conflict the split loop asserted `(= a b)` false, the LIA finite-domain
//! search found a verified witness without moving the simplex tableau, and
//! model reconciliation overwrote the witness with the Real side's
//! unconstrained integral `a = 0, b = 0`, which falsifies `b < a`.

use ay_frontend::parse;

use crate::Executor;

fn check_and_values(script: &str, names: &str) -> Vec<String> {
    let commands = parse(script).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .unwrap_or_else(|e| panic!("execute failed for {names}: {e}"))
}

#[test]
fn mixed_int_real_conjunction_with_a_bool_is_sat_with_a_valid_model() {
    for goal in [
        "(assert (and (< b a) (= y x) p))",
        "(assert (and (< b a) (< y x) p))",
        "(assert (< b a)) (assert (= y x)) (assert p)",
    ] {
        let script = format!(
            "(declare-fun a () Int) (declare-fun b () Int) (declare-fun x () Real) \
             (declare-fun y () Real) (declare-fun p () Bool) {goal} (check-sat) \
             (get-value ((< b a) (= y x) (< y x) p))"
        );
        let outputs = check_and_values(&script, goal);
        assert_eq!(outputs[0], "sat", "{goal}");
        let values = &outputs[1];
        assert!(values.contains("((< b a) true)"), "{goal}: {values}");
        assert!(values.contains("(p true)"), "{goal}: {values}");
    }
}

/// A witness answers LIA's own literals only. The mixed atom `(<= x i)` is
/// the Real side's, so its integral value of a witness term stands when it
/// falsifies no LIA literal (measured: the witness's `i = 0` overwrote the
/// Real side's `i = 2` under `x = 2.0`, the model gate refused `(<= x i)`,
/// and opt_epsilon's m15/adv3 objectives answered `unknown`).
#[test]
fn a_mixed_atom_keeps_the_real_sides_value_of_a_witness_term() {
    let script = "(set-logic QF_LIRA) (declare-fun x () Real) (declare-fun i () Int) \
                  (assert (<= x i)) (assert (< i 3)) (assert (>= x 2.0)) (check-sat) \
                  (get-value (x i))";
    let outputs = check_and_values(script, "mixed atom");
    assert_eq!(outputs[0], "sat", "{outputs:?}");
    assert!(outputs[1].contains("(i 2)"), "{outputs:?}");
}
