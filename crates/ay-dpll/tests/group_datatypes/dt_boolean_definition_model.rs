// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean definitions must preserve nested datatype model reconstruction.

use ntest::timeout;

const PREFIX: &str = "(set-logic ALL)
(set-option :timeout 5000)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-datatype L ((MkL (size (_ BitVec 8)) (align (_ BitVec 8)))))
(declare-datatype R ((Ok (value L)) (Err (error Bool))))
(declare-const r R)
(assert (= r (ite (= y #x08) (Ok (MkL x y)) (Err false))))
(declare-const flag Bool)
";

const BODY: &str = "(and (= x #x03) (= y #x08) ((_ is Ok) r))";

fn script(definition: &str, assertion: &str) -> String {
    format!("{PREFIX}{definition}\n{assertion}\n(check-sat)\n")
}

#[test]
#[timeout(60_000)]
fn asserted_boolean_equality_reconstructs_nested_model() {
    let smt = script(&format!("(assert (= flag {BODY}))"), "(assert flag)");
    assert_eq!(crate::common::solve(&smt), "sat");
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(&smt);
    assert_eq!(output, ["sat"]);
    assert_eq!(gate.as_deref(), Some("confirmed-sat"));
}

#[test]
#[timeout(60_000)]
fn nested_fields_and_boolean_queries_match_the_recovered_model() {
    let smt = format!(
        "{}(get-value (flag x y (size (value r)) (align (value r))))\n",
        script(&format!("(assert (= flag {BODY}))"), "(assert flag)")
    );
    let expected = [
        "sat",
        "((flag true) (x #x03) (y #x08) ((size (value r)) #x03) ((align (value r)) #x08))",
    ];
    assert_eq!(crate::common::solve_vec(&smt), expected);
    assert_eq!(crate::common::solve_authored_vec(&smt), expected);
}

#[test]
#[timeout(60_000)]
fn boolean_equality_with_reversed_operands_remains_sat() {
    let smt = script(&format!("(assert (= {BODY} flag))"), "(assert flag)");
    assert_eq!(crate::common::solve(&smt), "sat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["sat"]);
}

#[test]
#[timeout(60_000)]
fn false_boolean_definition_can_select_the_error_branch() {
    let smt = format!(
        "{}(get-value (flag r))\n",
        script(
            &format!("(assert (= flag {BODY}))"),
            "(assert (not flag))\n(assert (= y #x09))",
        )
    );
    let expected = ["sat", "((flag false) (r (Err false)))"];
    assert_eq!(crate::common::solve_vec(&smt), expected);
    assert_eq!(crate::common::solve_authored_vec(&smt), expected);
}

#[test]
#[timeout(60_000)]
fn reduced_error_definition_has_confirmed_field_model() {
    let smt = format!(
        "{}(get-value (r (error r)))\n",
        script(
            &format!("(assert (= flag {BODY}))"),
            "(assert (not flag))\n(assert (= y #x09))\n(assert (not (error r)))",
        )
    );
    let expected = ["sat", "((r (Err false)) ((error r) false))"];
    assert_eq!(crate::common::solve_vec(&smt), expected);
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(&smt);
    assert_eq!(output, expected);
    assert_eq!(gate.as_deref(), Some("confirmed-sat"));
}

#[test]
#[timeout(60_000)]
fn reduced_error_definition_cannot_make_its_field_true() {
    let smt = script(
        &format!("(assert (= flag {BODY}))"),
        "(assert (not flag))\n(assert (= y #x09))\n(assert (error r))",
    );
    assert_eq!(crate::common::solve(&smt), "unsat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["unsat"]);
}

#[test]
#[timeout(60_000)]
fn computed_error_field_definition_has_confirmed_model() {
    let smt = format!(
        "{}(get-value (r (error r)))\n",
        script(
            &format!("(assert (= flag {BODY}))"),
            "(assert (not flag))\n(assert (= y #x09))\n(assert (error r))",
        )
    )
    .replace("(Err false)", "(Err (bvult x #x05))");
    let expected = ["sat", "((r (Err true)) ((error r) true))"];
    assert_eq!(crate::common::solve_vec(&smt), expected);
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(&smt);
    assert_eq!(output, expected);
    assert_eq!(gate.as_deref(), Some("confirmed-sat"));
}

#[test]
#[timeout(60_000)]
fn computed_error_field_cannot_contradict_its_definition() {
    let smt = script(
        &format!("(assert (= flag {BODY}))"),
        "(assert (not flag))\n(assert (= y #x09))\n(assert (error r))\n(assert (= x #x07))",
    )
    .replace("(Err false)", "(Err (bvult x #x05))");
    assert_eq!(crate::common::solve(&smt), "unsat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["unsat"]);
}

#[test]
#[timeout(60_000)]
fn true_body_cannot_make_its_boolean_definition_false() {
    let smt = script(
        &format!("(assert (= flag {BODY}))"),
        &format!("(assert {BODY})\n(assert (not flag))"),
    );
    assert_eq!(crate::common::solve(&smt), "unsat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["unsat"]);
}

#[test]
#[timeout(60_000)]
fn scoped_definition_recovery_does_not_keep_the_previous_branch() {
    let smt = format!(
        "{PREFIX}(assert (= flag {BODY}))\n\
         (push 1)\n(assert flag)\n(check-sat)\n(pop 1)\n\
         (assert (not flag))\n(assert (= y #x09))\n(check-sat)\n\
         (get-value (flag r))\n"
    );
    let expected = ["sat", "sat", "((flag false) (r (Err false)))"];
    assert_eq!(crate::common::solve_vec(&smt), expected);
    assert_eq!(crate::common::solve_authored_vec(&smt), expected);
}

#[test]
#[timeout(60_000)]
fn original_layout_boolean_definition_has_confirmed_model() {
    let smt = format!(
        "(set-option :timeout 5000)\n{}",
        include_str!("fixtures/layout_boolean_definition.smt2")
    );
    let expected = ["sat", "((ay_violation_checked_layout true))"];
    assert_eq!(crate::common::solve_vec(&smt), expected);
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(&smt);
    assert_eq!(output, expected);
    assert_eq!(gate.as_deref(), Some("confirmed-sat"));
}

#[test]
#[timeout(60_000)]
fn equivalent_implication_definition_remains_sat() {
    let smt = script(
        &format!("(assert (=> flag {BODY}))\n(assert (=> {BODY} flag))"),
        "(assert flag)",
    );
    assert_eq!(crate::common::solve(&smt), "sat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["sat"]);
}

#[test]
#[timeout(60_000)]
fn boolean_definition_cannot_hide_wrong_constructor() {
    let smt = script(
        &format!("(assert (= flag {BODY}))"),
        "(assert flag)\n(assert ((_ is Err) r))",
    );
    assert_eq!(crate::common::solve(&smt), "unsat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["unsat"]);
}

#[test]
#[timeout(60_000)]
fn boolean_definition_cannot_hide_wrong_nested_field() {
    let smt = script(
        &format!("(assert (= flag {BODY}))"),
        "(assert flag)\n(assert (not (= (size (value r)) #x03)))",
    );
    assert_eq!(crate::common::solve(&smt), "unsat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["unsat"]);
}

#[test]
#[timeout(60_000)]
fn false_guard_cannot_force_ok_constructor() {
    let smt = script(
        "(assert (= flag (and (= y #x09) ((_ is Ok) r))))",
        "(assert flag)",
    );
    assert_eq!(crate::common::solve(&smt), "unsat");
    assert_eq!(crate::common::solve_authored_vec(&smt), ["unsat"]);
}
