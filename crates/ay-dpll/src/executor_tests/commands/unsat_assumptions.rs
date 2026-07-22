// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========== get-unsat-assumptions Tests ==========

#[test]
fn test_get_unsat_assumptions_after_check_sat_assuming() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (check-sat-assuming ((not a) b))
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Should return assumptions that caused unsat
    // (not a) is the conflicting assumption since a is asserted
    assert!(
        outputs[1].contains("not") || outputs[1].contains('a') || outputs[1].contains('b'),
        "Expected assumptions in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_assumptions_no_check_sat_assuming() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Should error because regular check-sat was used, not check-sat-assuming
    assert!(
        outputs[1].contains("error") && outputs[1].contains("check-sat-assuming"),
        "Expected error about no check-sat-assuming: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_assumptions_after_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (check-sat-assuming (a))
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Should error because last result was SAT
    assert!(
        outputs[1].contains("error") && outputs[1].contains("sat"),
        "Expected error about sat result: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_assumptions_empty() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat-assuming ())
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Empty assumptions list should return empty
    assert_eq!(outputs[1], "()");
}

#[test]
fn test_get_unsat_assumptions_contradictory() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (check-sat-assuming (a (not a)))
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Should return the assumptions (a and (not a))
    assert!(
        outputs[1].contains('a'),
        "Expected 'a' in assumptions: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("not"),
        "Expected '(not a)' in assumptions: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_assumptions_no_check_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should error because no check-sat has been performed
    assert!(
        outputs[0].contains("error") && outputs[0].contains("no check-sat"),
        "Expected error about no check-sat: {}",
        outputs[0]
    );
}

#[test]
fn test_get_unsat_assumptions_minimal_core() {
    // Test that we get a MINIMAL core, not all assumptions
    // (assert a) means (not a) causes UNSAT - b, c, d are irrelevant
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (declare-const d Bool)
        (assert a)
        (check-sat-assuming ((not a) b c d))
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // The minimal core should be just (not a), not b, c, d
    // The core should contain "not" and "a"
    assert!(
        outputs[1].contains("not") && outputs[1].contains('a'),
        "Expected (not a) in minimal core: {}",
        outputs[1]
    );
    // The core should NOT contain b, c, or d (they're irrelevant)
    assert!(
        !outputs[1].contains(" b") && !outputs[1].contains(" c") && !outputs[1].contains(" d"),
        "Minimal core should not contain b, c, d: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_assumptions_minimal_core_multiple_needed() {
    // Test where multiple assumptions are needed in the core
    // (assert (or a b)) with assumptions (not a) (not b) c should give core (not a) (not b)
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (or a b))
        (check-sat-assuming ((not a) (not b) c))
        (get-unsat-assumptions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // The core should contain (not a) and (not b) but not c
    // Count occurrences of "not" - should be exactly 2
    let not_count = outputs[1].matches("not").count();
    assert!(
        not_count >= 2,
        "Expected at least 2 negated assumptions in core: {}",
        outputs[1]
    );
    // c should not be in the core
    assert!(
        !outputs[1].contains(" c)") && !outputs[1].contains(" c "),
        "Minimal core should not contain c: {}",
        outputs[1]
    );
}

#[test]
fn test_get_proof_not_enabled() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("error") && outputs[1].contains("produce-proofs"),
        "Expected error about produce-proofs: {}",
        outputs[1]
    );
}

#[test]
fn test_get_proof_after_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("error") && outputs[1].contains("sat"),
        "Expected error about result being sat: {}",
        outputs[1]
    );
}

#[test]
fn test_get_proof_after_unsat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Proof should be in Alethe format with assume and step commands
    let proof = &outputs[1];
    assert!(
        proof.contains("assume"),
        "Expected proof to contain assume steps: {proof}"
    );
    assert!(
        proof.contains("step"),
        "Expected proof to contain step: {proof}"
    );
    assert!(
        proof.contains("(cl)"),
        "Expected proof to derive empty clause: {proof}"
    );
}

#[test]
fn test_get_proof_after_theory_unsat_includes_assertion_assumes() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");

    let proof = &outputs[1];
    let assume_count = count_assumes(proof);
    assert!(
        assume_count == 3,
        "Expected exactly three assertion assume steps, got {assume_count}: {proof}"
    );
    assert!(
        count_assumes_for_term(proof, "(= a b)") == 1,
        "Expected exactly one assume for (= a b): {proof}"
    );
    assert!(
        count_assumes_for_term(proof, "(= b c)") == 1,
        "Expected exactly one assume for (= b c): {proof}"
    );
    assert!(
        count_assumes_for_term(proof, "(not (= a c))") == 1,
        "Expected exactly one assume for (not (= a c)): {proof}"
    );
    assert!(
        proof.contains("(cl)"),
        "Expected proof to derive empty clause: {proof}"
    );
}

#[test]
fn test_get_proof_after_named_unsat_core_redirect() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named h0))
        (assert (! (not a) :named h1))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    let proof = &outputs[1];
    assert!(
        !proof.contains("error") && proof.contains("(cl)"),
        "Expected named-unsat-core route to materialize a proof: {proof}"
    );
}

#[test]
fn test_get_proof_no_check_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("error") && outputs[0].contains("no check-sat"),
        "Expected error about no check-sat: {}",
        outputs[0]
    );
}

#[test]
fn test_named_terms_cleared_on_pop() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named outer_a))
        (push 1)
        (assert (! (not a) :named inner_not_a))
        (check-sat)
        (get-unsat-core)
        (pop 1)
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat is unsat (a and not a)
    // First get-unsat-core should include both outer_a and inner_not_a
    // After pop, inner_not_a should be removed
    // Second check-sat is sat (only a is asserted)
    // Second get-unsat-core should error because sat

    assert_eq!(outputs.len(), 4);
    assert_eq!(outputs[0], "unsat");
    // First unsat-core should have both names
    assert!(
        outputs[1].contains("outer_a") && outputs[1].contains("inner_not_a"),
        "Expected both named terms in core: {}",
        outputs[1]
    );
    assert_eq!(outputs[2], "sat");
    // After pop and sat, get-unsat-core should error
    assert!(
        outputs[3].contains("error"),
        "Expected error after sat: {}",
        outputs[3]
    );
}

#[test]
fn test_named_terms_scope_independent() {
    // Named terms defined outside any scope should remain after pop
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (! a :named assert_a))
        (push 1)
        (assert (! b :named assert_b))
        (pop 1)
        (push 1)
        (assert (! (not a) :named assert_not_a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Should have assert_a (outer scope) and assert_not_a (current scope)
    // Should NOT have assert_b (was popped)
    assert!(
        outputs[1].contains("assert_a"),
        "Expected outer named term: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("assert_not_a"),
        "Expected inner named term: {}",
        outputs[1]
    );
    assert!(
        !outputs[1].contains("assert_b"),
        "Should not contain popped named term: {}",
        outputs[1]
    );
}
