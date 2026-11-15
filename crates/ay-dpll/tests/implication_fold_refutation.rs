// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Trust cttz-at-zero query must keep its proof across conjunct ordering.

#![allow(clippy::panic)]

mod common;

const PREFIX: &str = "(set-option :produce-proofs true)\n(set-logic QF_LIA)\n\
    (declare-fun __trust_u__0 () Int)\n(declare-fun __trust_u_x () Int)\n";

// Exact failing assertion recorded by TRUST_AY_SMT_TRACE on 2026-10-29.
const TRUST_ASSERTION: &str = "(and (>= __trust_u__0 0) (<= __trust_u__0 32) (=> (= __trust_u__0 32) (= __trust_u_x 0)) (=> (= __trust_u_x 0) (= __trust_u__0 32)) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (<= 0 __trust_u__0) (<= __trust_u__0 4294967295) (= __trust_u_x 0) (>= __trust_u_x 0) (<= __trust_u_x 4294967295) (=> (= __trust_u_x 0) (= __trust_u__0 32)) (=> (= __trust_u__0 32) (= __trust_u_x 0)) (<= __trust_u__0 32) (>= __trust_u__0 0) (not (= __trust_u__0 32)))";

#[test]
fn exact_trust_intrinsic_query_exports_a_complete_refutation() {
    // Preserve the actual reconstruction refusal in a failing test's output.
    // These existing channels affect diagnostics only, not proof acceptance.
    ay_core::set_global_misc_cli_flags_with(|flags| {
        flags.trace_cegqi_attr = true;
        flags.probe_cert_reject = true;
    });
    let script = format!("{PREFIX}(assert {TRUST_ASSERTION})\n(check-sat)\n(get-proof)\n");
    let output = common::solve_authored_vec(&script);
    let [verdict, proof] = output.as_slice() else {
        panic!("expected verdict and proof: {output:?}");
    };
    assert_eq!(verdict, "unsat");
    assert!(
        proof.contains(TRUST_ASSERTION),
        "the original premise was renamed: {proof}"
    );
    assert!(proof.contains("(cl)"), "no empty clause: {proof}");
    assert!(!proof.contains(":rule hole"), "incomplete proof: {proof}");
    assert!(!proof.contains(":rule trust"), "trusted proof: {proof}");
    assert_eq!(
        common::solve_authored_selfcheck_vec(&format!(
            "{PREFIX}(assert {TRUST_ASSERTION})\n(check-sat)\n"
        )),
        ["unsat"]
    );
}

#[test]
fn implication_order_and_satisfiable_controls_preserve_verdicts() {
    for assertion in [
        "(and (= __trust_u_x 0) (=> (= __trust_u_x 0) (= __trust_u__0 32)) (not (= __trust_u__0 32)))",
        "(and (not (= __trust_u__0 32)) (=> (= __trust_u_x 0) (= __trust_u__0 32)) (= __trust_u_x 0))",
        "(and (and (= __trust_u_x 0) (not (= __trust_u__0 32))) (=> (= __trust_u_x 0) (= __trust_u__0 32)))",
    ] {
        assert_eq!(
            common::solve_authored_selfcheck_vec(&format!(
                "{PREFIX}(assert {assertion})\n(check-sat)\n"
            )),
            ["unsat"],
            "{assertion}"
        );
    }
    // Removing the zero precondition makes the original query satisfiable:
    // x=1, result=1 witnesses it. A solver repair must not prove that row.
    let control = TRUST_ASSERTION.replace(
        "(= __trust_u_x 0) (>= __trust_u_x 0)",
        "(= __trust_u_x 1) (>= __trust_u_x 0)",
    );
    assert_ne!(control, TRUST_ASSERTION);
    assert_eq!(
        common::solve_authored_vec(&format!("{PREFIX}(assert {control})\n(check-sat)\n")),
        ["sat"]
    );
    // The other exact query from the same Trust test asks whether the result
    // can exceed 31 without a zero-input precondition. It is satisfiable at
    // x=0, result=32; the repair must preserve that intrinsic counterexample.
    let original_negative = TRUST_ASSERTION
        .replace("(= __trust_u_x 0) (>= __trust_u_x 0)", "(>= __trust_u_x 0)")
        .replace("(not (= __trust_u__0 32))", "(not (<= __trust_u__0 31))");
    assert_eq!(
        common::solve_authored_vec(&format!(
            "{PREFIX}(assert {original_negative})\n(check-sat)\n"
        )),
        ["sat"]
    );
}
