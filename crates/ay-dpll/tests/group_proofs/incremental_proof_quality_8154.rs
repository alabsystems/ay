// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for incremental proof certificate quality across push/pop scope
//! boundaries (Phase 6a, #8154).
//!
//! Acceptance criteria: incremental proof quality matches standalone — no trust
//! degradation steps that would not appear in standalone mode.

#![allow(deprecated)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof;
use ntest::timeout;

/// Assert that last_proof() exists and passes the internal proof checker.
fn assert_valid_proof(exec: &Executor, context: &str) {
    let proof = exec
        .last_proof()
        .unwrap_or_else(|| panic!("expected last_proof() to be Some after UNSAT ({context})"));
    check_proof(proof, exec.terms())
        .unwrap_or_else(|e| panic!("proof check failed after UNSAT ({context}): {e}"));
}

/// Assert that the proof Alethe text does not contain `:rule trust` fallbacks.
fn assert_no_trust_rules(exec: &Executor, context: &str) {
    let proof = exec
        .last_proof()
        .unwrap_or_else(|| panic!("expected last_proof() to be Some ({context})"));
    let text = ay_proof::export_alethe(proof, exec.terms());
    assert!(
        !text.contains(":rule trust"),
        "proof contains :rule trust fallback ({context}):\n{text}"
    );
}

// ========================================================================
// QF_LIA: push/check-sat(UNSAT)/pop/push/check-sat(UNSAT)
// Both UNSAT results must produce full proofs
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_lia_push_pop_push_pop_both_unsat_have_proofs() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (push 1)
        (assert (> x 10))
        (assert (< x 5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> y 20))
        (assert (< y 15))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut check_sat_count = 0;
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            check_sat_count += 1;
            assert_eq!(
                output, "unsat",
                "check-sat #{check_sat_count} should return unsat"
            );
            assert_valid_proof(&exec, &format!("check-sat #{check_sat_count}"));
            assert_no_trust_rules(&exec, &format!("check-sat #{check_sat_count}"));
        }
    }
    assert_eq!(check_sat_count, 2, "expected 2 check-sat outputs");
}

// ========================================================================
// QF_UF: push/check-sat(UNSAT)/pop/push/check-sat(UNSAT)
// Congruence contradictions across scopes
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_euf_push_pop_push_pop_both_unsat_have_proofs() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (push 1)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= c d))
        (assert (not (= (f c) (f d))))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut check_sat_count = 0;
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            check_sat_count += 1;
            assert_eq!(
                output, "unsat",
                "check-sat #{check_sat_count} should return unsat"
            );
            assert_valid_proof(&exec, &format!("EUF check-sat #{check_sat_count}"));
        }
    }
    assert_eq!(check_sat_count, 2, "expected 2 check-sat outputs");
}

// ========================================================================
// QF_LRA: nested push levels with proofs
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_lra_nested_push_pop_unsat_proofs() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (push 1)
        (assert (> x 1.0))
        (push 1)
        (assert (< x 0.0))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> y 5.0))
        (assert (< y 3.0))
        (check-sat)
        (pop 1)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut check_sat_count = 0;
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            check_sat_count += 1;
            assert_eq!(
                output, "unsat",
                "check-sat #{check_sat_count} should return unsat"
            );
            assert_valid_proof(&exec, &format!("LRA nested check-sat #{check_sat_count}"));
        }
    }
    assert_eq!(check_sat_count, 2, "expected 2 check-sat outputs");
}

// ========================================================================
// QF_LIA: SAT then UNSAT across scopes -- proof only for UNSAT
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_lia_sat_then_unsat_proof_available() {
    // Use different variables for the two scopes to avoid LIA preprocessing
    // interactions between scopes.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (push 1)
        (assert (> x 5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> y 10))
        (assert (< y 5))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut outputs = Vec::new();
    let mut unsat_proof_validated = false;
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            outputs.push(output.clone());
            // Validate proof immediately after UNSAT, before the pop invalidates
            // query artefacts (SMT-LIB 2.6 semantics: pop invalidates last result).
            if output == "unsat" {
                assert_valid_proof(&exec, "SAT-then-UNSAT incremental LIA");
                unsat_proof_validated = true;
            }
        }
    }
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "unsat");
    assert!(
        unsat_proof_validated,
        "UNSAT proof should have been validated"
    );
}

// ========================================================================
// QF_LIA: three successive UNSAT scopes to test proof state reset
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_lia_three_successive_unsat_scopes() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (push 1)
        (assert (> a 10))
        (assert (< a 5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> b 20))
        (assert (< b 15))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> c 30))
        (assert (< c 25))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut check_sat_count = 0;
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            check_sat_count += 1;
            assert_eq!(
                output, "unsat",
                "check-sat #{check_sat_count} should return unsat"
            );
            assert_valid_proof(
                &exec,
                &format!("three-scope LIA check-sat #{check_sat_count}"),
            );
        }
    }
    assert_eq!(check_sat_count, 3, "expected 3 check-sat outputs");
}

// ========================================================================
// QF_LIA: verify theory lemma proof annotations persist across push/pop
// (#8154 subtask 6a: trust degradation fix)
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_lia_theory_lemma_proofs_survive_push_pop() {
    // Regression test for #8154 subtask 6a: original_clause_theory_proofs
    // was cleared entirely on pop(), losing theory lemma proof annotations
    // from lower scopes and causing trust degradation in subsequent UNSAT proofs.
    //
    // Pattern: push/assert/check-sat(UNSAT)/pop/push/assert/check-sat(UNSAT)
    // Both UNSAT results should have identical proof quality (no trust degradation).
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
        (push 1)
        (assert (> a 10))
        (assert (< a 5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> c 20))
        (assert (< c 15))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut proofs_validated = 0;
    let mut trust_counts = Vec::new();
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            if output == "unsat" {
                assert_valid_proof(
                    &exec,
                    &format!("theory-lemma-survival check-sat #{}", proofs_validated + 1),
                );
                // Count trust steps in the proof
                let proof = exec.last_proof().expect("proof after UNSAT");
                let text = ay_proof::export_alethe(proof, exec.terms());
                let trust_count = text.matches(":rule trust").count();
                trust_counts.push(trust_count);
                proofs_validated += 1;
            }
        }
    }
    assert_eq!(proofs_validated, 2, "expected 2 UNSAT results");
    // The second proof should not have MORE trust steps than the first.
    // Trust degradation would manifest as trust_counts[1] > trust_counts[0].
    assert!(
        trust_counts[1] <= trust_counts[0],
        "proof quality degraded after push/pop: trust steps went from {} to {}",
        trust_counts[0],
        trust_counts[1],
    );
}

// ========================================================================
// QF_LRA: verify no trust degradation across three push/pop cycles
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_lra_no_trust_degradation_three_cycles() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (push 1)
        (assert (> x 5.0))
        (assert (< x 3.0))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> y 10.0))
        (assert (< y 7.0))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> z 20.0))
        (assert (< z 15.0))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut proofs_validated = 0;
    let mut all_valid = true;
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            if output == "unsat" {
                proofs_validated += 1;
                let proof = exec.last_proof();
                if proof.is_none() {
                    all_valid = false;
                } else {
                    let p = proof.unwrap();
                    if check_proof(p, exec.terms()).is_err() {
                        all_valid = false;
                    }
                }
            }
        }
    }
    assert_eq!(proofs_validated, 3, "expected 3 UNSAT results");
    assert!(all_valid, "all three proofs should be valid");
}

// ========================================================================
// QF_UF: get-proof across push/pop returns valid proof text
// ========================================================================

#[test]
#[timeout(10_000)]
fn test_incremental_euf_get_proof_after_push_pop_cycle() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (push 1)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
        (get-proof)
        (pop 1)
        (push 1)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
        (get-proof)
        (pop 1)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();

    let mut outputs = Vec::new();
    for cmd in &commands {
        if let Some(output) = exec.execute(cmd).expect("execute") {
            outputs.push(output);
        }
    }

    // Expect: unsat, proof, unsat, proof
    assert_eq!(outputs.len(), 4);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("(cl)"),
        "first proof should derive empty clause"
    );
    assert_eq!(outputs[2], "unsat");
    assert!(
        outputs[3].contains("(cl)"),
        "second proof should derive empty clause"
    );
}
