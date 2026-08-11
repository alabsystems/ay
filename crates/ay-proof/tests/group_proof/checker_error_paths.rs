// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for ProofCheckError variants that were previously uncovered.
// Covers: EmptyProof, NoClauseProducingSteps, FinalClauseNotEmpty,
// MissingPremise, PremiseHasNoClause, UnsupportedResolutionArity,
// InvalidDrup, and the NonPriorPremise dead-code finding.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermStore};
use ay_proof::{check_proof, ProofCheckError};

#[test]
fn test_rejects_empty_proof() {
    let terms = TermStore::new();
    let proof = Proof::new();

    let err = check_proof(&proof, &terms).expect_err("empty proof must be rejected");
    assert_eq!(err, ProofCheckError::EmptyProof);
}

#[test]
fn test_rejects_no_clause_producing_steps() {
    let terms = TermStore::new();
    let mut proof = Proof::new();
    // An anchor produces None in derived_clauses, so the proof has steps
    // but no clause-producing steps.
    proof.add_step(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![],
    });

    let err = check_proof(&proof, &terms).expect_err("proof with only anchors must be rejected");
    assert_eq!(err, ProofCheckError::NoClauseProducingSteps);
}

#[test]
fn test_rejects_final_clause_not_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);

    let err = check_proof(&proof, &terms)
        .expect_err("proof ending with non-empty clause must be rejected");
    assert_eq!(
        err,
        ProofCheckError::FinalClauseNotEmpty { step: ProofId(0) }
    );
}

#[test]
fn test_rejects_missing_premise() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    // Reference premise ProofId(99) which doesn't exist.
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![ProofId(0), ProofId(99)],
        vec![],
    );

    let err = check_proof(&proof, &terms).expect_err("referencing nonexistent premise must fail");
    assert_eq!(
        err,
        ProofCheckError::MissingPremise {
            step: ProofId(1),
            premise: ProofId(99),
        }
    );
}

#[test]
fn test_self_referencing_premise_caught_as_missing() {
    // NonPriorPremise is unreachable under sequential processing:
    // at step idx, derived_clauses.len() == idx, so
    // premise_idx >= derived_clauses.len() (MissingPremise) fires
    // before premise_idx >= step_idx (NonPriorPremise) can be checked.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![ProofId(0), ProofId(1)],
        vec![],
    );

    let err = check_proof(&proof, &terms).expect_err("self-referencing premise must fail");
    assert_eq!(
        err,
        ProofCheckError::MissingPremise {
            step: ProofId(1),
            premise: ProofId(1),
        },
        "self-reference caught by MissingPremise (NonPriorPremise is unreachable dead code)"
    );
}

#[test]
fn test_rejects_premise_pointing_to_anchor() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![],
    });
    proof.add_assume(x, None);
    proof.add_assume(not_x, None);
    // Step 3 references anchor step 0 as premise (no clause).
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![ProofId(0), ProofId(1)],
        vec![],
    );

    let err = check_proof(&proof, &terms).expect_err("premise pointing to anchor must fail");
    assert_eq!(
        err,
        ProofCheckError::PremiseHasNoClause {
            step: ProofId(3),
            premise: ProofId(0),
        }
    );
}

// SHAPE CHANGED (#dt-premise-binding): arity != 2 is no longer a blanket
// rejection. Alethe resolution is n-ary, and rejecting it forced emitters to
// spell chains out as one binary step per premise — each printing its whole
// remaining clause, i.e. TRIANGULAR text. Measured on
// QF_DT/20210312-Bouvier/vlsat3_b14.smt2 (2,986 premises) that shape rendered a
// 105.6 MB .alethe, which blew the 64 MiB emission work budget, so the default
// path emitted NO PROOF AT ALL. The same refutation as one n-ary step is
// 193 KB. `UnsupportedResolutionArity` now means only 0 or 1 premises.
#[test]
fn test_rejects_resolution_arity_below_two() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    // One premise cannot denote a resolution at any arity.
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![p0], vec![]);

    let err = check_proof(&proof, &terms).expect_err("unary resolution must be rejected");
    assert_eq!(
        err,
        ProofCheckError::UnsupportedResolutionArity {
            step: ProofId(1),
            rule: "resolution".to_string(),
            premise_count: 1,
        }
    );
}

// AY's chain fold is deliberately STRICTER than carcara 1.1.0: carcara absorbs
// premises once the accumulator is empty (it accepts this very proof), but the
// true resolvent of {x}, {¬x}, {y} is {y}, not ⊥. Absorbing surplus premises
// would let a step claim more than it derives, so AY rejects it.
#[test]
fn test_rejects_chain_resolution_with_absorbed_premise() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    let y = terms.mk_var("y", Sort::Bool);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    let p2 = proof.add_assume(y, None);
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![p0, p1, p2], vec![]);

    let err = check_proof(&proof, &terms).expect_err("non-resolving premise must be rejected");
    assert_eq!(
        err,
        ProofCheckError::InvalidResolution {
            step: ProofId(3),
            rule: "resolution".to_string(),
        }
    );
}

// The shape the premise-binding rebuild now emits: one wide clause, then one
// n-ary step consuming every unit at once.
#[test]
fn test_accepts_nary_chain_resolution() {
    let mut terms = TermStore::new();
    let vars: Vec<_> = ["a", "b", "c", "d"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Bool))
        .collect();
    let negated: Vec<_> = vars.iter().map(|&v| terms.mk_not(v)).collect();

    let mut proof = Proof::new();
    let units: Vec<ProofId> = vars.iter().map(|&v| proof.add_assume(v, None)).collect();
    let wide = proof.add_rule_step(AletheRule::Trust, negated, vec![], vec![]);

    let mut premises = vec![wide];
    premises.extend(units);
    proof.add_rule_step(AletheRule::ThResolution, vec![], premises, vec![]);

    check_proof(&proof, &terms).expect("n-ary chain resolution to the empty clause must check");
}

// A chain that stops short of the clause it declares must fail: the fold's
// result is compared to the declared clause as a set.
#[test]
fn test_rejects_chain_resolution_with_wrong_conclusion() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);

    let mut proof = Proof::new();
    let ua = proof.add_assume(a, None);
    let ub = proof.add_assume(b, None);
    // (cl (not a) (not b) c) resolved with a and b leaves {c}, not {}.
    let wide = proof.add_rule_step(AletheRule::Trust, vec![not_a, not_b, c], vec![], vec![]);
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![wide, ua, ub], vec![]);

    let err = check_proof(&proof, &terms).expect_err("under-resolved chain must be rejected");
    assert_eq!(
        err,
        ProofCheckError::InvalidResolution {
            step: ProofId(3),
            rule: "th_resolution".to_string(),
        }
    );
}

#[test]
fn test_rejects_invalid_drup() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    // Clause (y) is NOT RUP-derivable from just {(x)}.
    proof.add_rule_step(AletheRule::Drup, vec![y], vec![], vec![]);

    let err = check_proof(&proof, &terms).expect_err("non-derivable DRUP clause must be rejected");
    assert_eq!(err, ProofCheckError::InvalidDrup { step: ProofId(1) });
}
