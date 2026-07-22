// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::check_proof_partial;
use ay_core::Sort;
use resolution::is_valid_rup_step;

#[test]
fn test_check_proof_accepts_valid_resolution_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![], x, p0, p1);

    check_proof(&proof, &terms).expect("valid resolution proof should pass");
}

#[test]
fn test_check_proof_rejects_invalid_resolution_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(y, None);
    proof.add_resolution(vec![], x, p0, p1);

    let err = check_proof(&proof, &terms).expect_err("invalid resolution must fail");
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { .. }),
        "unexpected error variant: {err:?}"
    );
}

#[test]
fn test_check_proof_accepts_valid_drup_empty_clause() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let not_a = terms.mk_not(a);

    let mut proof = Proof::new();
    proof.add_assume(a, None);
    proof.add_assume(not_a, None);
    proof.add_rule_step(AletheRule::Drup, vec![], vec![], vec![]);

    check_proof(&proof, &terms).expect("DRUP empty-clause derivation should pass");
}

#[test]
fn test_check_proof_rejects_hole_step() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    proof.add_rule_step(AletheRule::Hole, vec![], vec![], vec![]);

    let err = check_proof(&proof, &terms).expect_err("hole steps must be rejected");
    assert!(
        matches!(err, ProofCheckError::HoleStep { .. }),
        "unexpected error variant: {err:?}"
    );
}

#[test]
fn test_validate_step_allows_trust_in_non_strict_mode() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    let trust_step = ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    };
    let mut derived = Vec::new();

    validate_step(&terms, &mut derived, ProofId(0), &trust_step, false, None)
        .expect("non-strict mode should accept trust steps");

    assert_eq!(derived, vec![Some(vec![not_x])]);
}

#[test]
fn test_validate_step_rejects_trust_in_strict_mode() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    let trust_step = ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    };
    let mut derived = Vec::new();

    let err = validate_step(&terms, &mut derived, ProofId(0), &trust_step, true, None)
        .expect_err("strict mode must reject trust steps");
    assert_eq!(err, ProofCheckError::TrustStep { step: ProofId(0) });
    assert!(
        derived.is_empty(),
        "rejected steps must not mutate derived clauses"
    );
}

#[test]
fn test_validate_step_strict_mode_rejects_unvalidated_generic_rule() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    // Use AllSimplify — a rule that remains unvalidated in strict mode.
    let generic_step = ProofStep::Step {
        rule: AletheRule::AllSimplify,
        clause: vec![x, not_x],
        premises: vec![],
        args: vec![],
    };
    let mut derived = Vec::new();

    let err = validate_step(&terms, &mut derived, ProofId(0), &generic_step, true, None)
        .expect_err("strict mode must reject unvalidated generic rules");
    assert_eq!(
        err,
        ProofCheckError::UnvalidatedRule {
            step: ProofId(0),
            rule: "all_simplify".to_string(),
        }
    );
    assert!(
        derived.is_empty(),
        "rejected steps must not mutate derived clauses"
    );
}

#[test]
fn test_validate_step_strict_rejects_invalid_or_pos() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    // Invalid OrPos: clause [x, not_x] doesn't match (cl (not (or ...)) ...)
    let step = ProofStep::Step {
        rule: AletheRule::OrPos(0),
        clause: vec![x, not_x],
        premises: vec![],
        args: vec![],
    };
    let mut derived = Vec::new();

    let err = validate_step(&terms, &mut derived, ProofId(0), &step, true, None)
        .expect_err("strict mode must reject invalid or_pos clause");
    assert!(
        matches!(err, ProofCheckError::InvalidBooleanRule { .. }),
        "expected InvalidBooleanRule, got {err:?}"
    );
}

#[test]
fn test_validate_step_non_strict_mode_accepts_unvalidated_generic_rule() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    let generic_step = ProofStep::Step {
        rule: AletheRule::OrPos(0),
        clause: vec![x, not_x],
        premises: vec![],
        args: vec![],
    };
    let mut derived = Vec::new();

    validate_step(&terms, &mut derived, ProofId(0), &generic_step, false, None)
        .expect("non-strict mode should accept unvalidated generic rules");

    assert_eq!(derived, vec![Some(vec![x, not_x])]);
}

#[test]
fn test_premise_clause_rejects_non_prior_premise() {
    let derived: Vec<Option<Vec<TermId>>> = vec![Some(vec![]), Some(vec![]), Some(vec![])];
    let err = premise_clause(&derived, ProofId(1), ProofId(2))
        .expect_err("future premise must be rejected");
    assert!(
        matches!(
            err,
            ProofCheckError::NonPriorPremise {
                step: ProofId(1),
                premise: ProofId(2)
            }
        ),
        "expected NonPriorPremise, got {err:?}"
    );
}

#[test]
fn test_rup_multi_round_propagation_terminates() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let not_c = terms.mk_not(c);

    let prior: Vec<Option<Vec<TermId>>> = vec![
        Some(vec![a, b]),
        Some(vec![not_a, c]),
        Some(vec![not_b, c]),
        Some(vec![not_c, d]),
    ];

    assert!(
        is_valid_rup_step(&terms, &[d], &prior),
        "multi-round BCP: (d) should be RUP valid"
    );
}

#[test]
fn test_rup_rejects_non_implied_clause() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);

    let prior: Vec<Option<Vec<TermId>>> = vec![Some(vec![a, b])];

    assert!(
        !is_valid_rup_step(&terms, &[c], &prior),
        "(c) is not implied by (a ∨ b)"
    );
}

#[test]
fn test_rup_empty_clause_from_contradictory_units() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let not_a = terms.mk_not(a);

    let prior: Vec<Option<Vec<TermId>>> = vec![Some(vec![a]), Some(vec![not_a])];

    assert!(
        is_valid_rup_step(&terms, &[], &prior),
        "empty clause should be RUP valid when formula is contradictory"
    );
}

#[test]
fn test_check_proof_partial_accepts_mixed_hole_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let hole = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, hole, h0);

    let (summary, err) = check_proof_partial(&proof, &terms);
    assert!(
        err.is_none(),
        "partial checker should validate mixed hole/non-hole proofs: {err:?}"
    );
    assert_eq!(summary.total_steps, 3);
    assert_eq!(summary.skipped_hole_steps, 1);
    assert_eq!(summary.checked_steps, 2);
}

#[test]
fn test_check_proof_partial_rejects_invalid_non_hole_step() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let h1 = proof.add_assume(not_x, None);
    proof.add_step(ProofStep::Resolution {
        clause: vec![y],
        pivot: x,
        clause1: h0,
        clause2: h1,
    });

    let (_partial, some_err) = check_proof_partial(&proof, &terms);
    let err = some_err.expect("partial checker must reject invalid non-hole steps");
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { .. }),
        "unexpected error variant: {err:?}"
    );
}

// ============================================================================
// Boolean tautology rule validation tests (strict mode)
// ============================================================================

/// Helper: create `(and a b)` without simplification.
fn mk_and_raw(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("and"), args, Sort::Bool)
}

/// Helper: create `(or a b)` without simplification.
fn mk_or_raw(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("or"), args, Sort::Bool)
}

/// Helper: create `(= a b)` without simplification.
fn mk_eq_raw(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// Helper: create `(xor a b)` without simplification.
fn mk_xor_raw(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("xor"), vec![lhs, rhs], Sort::Bool)
}

/// Helper: validate a step in strict mode.
fn validate_strict(
    terms: &TermStore,
    rule: AletheRule,
    clause: Vec<TermId>,
    premises: Vec<ProofId>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule,
        clause,
        premises,
        args: vec![],
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

/// Helper: validate a step in strict mode with prior derived clauses.
fn validate_strict_with_derived(
    terms: &TermStore,
    rule: AletheRule,
    clause: Vec<TermId>,
    premises: Vec<ProofId>,
    prior_derived: Vec<Option<Vec<TermId>>>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule,
        clause,
        premises,
        args: vec![],
    };
    let mut derived = prior_derived;
    let step_id = ProofId(derived.len() as u32);
    validate_step(terms, &mut derived, step_id, &step, true, None)
}

fn la_disequality_term(
    terms: &mut TermStore,
    lhs: TermId,
    rhs: TermId,
) -> (TermId, TermId, TermId, TermId) {
    let eq = terms.mk_app(ay_core::Symbol::named("="), [lhs, rhs], Sort::Bool);
    let le_lhs_rhs = terms.mk_app(ay_core::Symbol::named("<="), [lhs, rhs], Sort::Bool);
    let le_rhs_lhs = terms.mk_app(ay_core::Symbol::named("<="), [rhs, lhs], Sort::Bool);
    let not_le_lhs_rhs = terms.mk_not_raw(le_lhs_rhs);
    let not_le_rhs_lhs = terms.mk_not_raw(le_rhs_lhs);
    let split = terms.mk_app(
        ay_core::Symbol::named("or"),
        [eq, not_le_lhs_rhs, not_le_rhs_lhs],
        Sort::Bool,
    );
    (split, eq, not_le_lhs_rhs, not_le_rhs_lhs)
}

// --- la_disequality ---

#[test]
fn test_strict_la_disequality_accepts_exact_antisymmetry_split() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (split, _, _, _) = la_disequality_term(&mut terms, x, y);
    validate_strict(&terms, AletheRule::LaDisequality, vec![split], vec![])
        .expect("the exact arithmetic antisymmetry split must validate");
}

#[test]
fn test_strict_la_disequality_rejects_wrong_opposite_operand() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let (_, eq, not_le_xy, _) = la_disequality_term(&mut terms, x, y);
    let le_zx = terms.mk_app(ay_core::Symbol::named("<="), [z, x], Sort::Bool);
    let not_le_zx = terms.mk_not_raw(le_zx);
    let forged = terms.mk_app(
        ay_core::Symbol::named("or"),
        [eq, not_le_xy, not_le_zx],
        Sort::Bool,
    );
    validate_strict(&terms, AletheRule::LaDisequality, vec![forged], vec![])
        .expect_err("an unrelated reverse bound must not certify antisymmetry");
}

#[test]
fn test_strict_la_disequality_rejects_non_arithmetic_sort() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let (forged, _, _, _) = la_disequality_term(&mut terms, p, q);
    validate_strict(&terms, AletheRule::LaDisequality, vec![forged], vec![])
        .expect_err("la_disequality must reject non-arithmetic operands");
}

#[test]
fn test_strict_la_disequality_rejects_premises_arguments_and_malformed_order() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (split, eq, not_le_xy, not_le_yx) = la_disequality_term(&mut terms, x, y);

    validate_strict_with_derived(
        &terms,
        AletheRule::LaDisequality,
        vec![split],
        vec![ProofId(0)],
        vec![Some(vec![eq])],
    )
    .expect_err("la_disequality must be premiseless");

    let step_with_arg = ProofStep::Step {
        rule: AletheRule::LaDisequality,
        clause: vec![split],
        premises: vec![],
        args: vec![x],
    };
    validate_step(
        &terms,
        &mut Vec::new(),
        ProofId(0),
        &step_with_arg,
        true,
        None,
    )
    .expect_err("la_disequality must not carry arguments");

    let malformed = terms.mk_app(
        ay_core::Symbol::named("or"),
        [not_le_xy, eq, not_le_yx],
        Sort::Bool,
    );
    validate_strict(&terms, AletheRule::LaDisequality, vec![malformed], vec![])
        .expect_err("la_disequality equality must occupy the rule's specified position");

    let swapped_bounds = terms.mk_app(
        ay_core::Symbol::named("or"),
        [eq, not_le_yx, not_le_xy],
        Sort::Bool,
    );
    validate_strict(
        &terms,
        AletheRule::LaDisequality,
        vec![swapped_bounds],
        vec![],
    )
    .expect_err("la_disequality bound operands must follow Alethe's rigid order");
}

// --- and_pos ---

#[test]
fn test_strict_and_pos_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let and_abc = mk_and_raw(&mut terms, vec![a, b, c]);
    let not_and = terms.mk_not_raw(and_abc);
    // and_pos(1): (cl (not (and a b c)) b)
    validate_strict(&terms, AletheRule::AndPos(1), vec![not_and, b], vec![])
        .expect("valid and_pos(1) should pass");
}

#[test]
fn test_strict_and_pos_wrong_conjunct() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let and_abc = mk_and_raw(&mut terms, vec![a, b, c]);
    let not_and = terms.mk_not_raw(and_abc);
    // Wrong: and_pos(1) but clause has 'a' instead of 'b'
    let err = validate_strict(&terms, AletheRule::AndPos(1), vec![not_and, a], vec![])
        .expect_err("wrong conjunct must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- and_neg ---

#[test]
fn test_strict_and_neg_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // and_neg: (cl (and a b) (not a) (not b))
    validate_strict(
        &terms,
        AletheRule::AndNeg,
        vec![and_ab, not_a, not_b],
        vec![],
    )
    .expect("valid and_neg should pass");
}

#[test]
fn test_strict_and_neg_accepts_emitted_clause_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    validate_strict(
        &terms,
        AletheRule::AndNeg,
        vec![not_a, not_b, and_ab],
        vec![],
    )
    .expect("emitted and_neg clause order should pass");
}

#[test]
fn test_strict_and_neg_missing_negation() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    let not_a = terms.mk_not_raw(a);
    // Wrong: second literal is 'b' not '(not b)'
    let err = validate_strict(&terms, AletheRule::AndNeg, vec![and_ab, not_a, b], vec![])
        .expect_err("missing negation must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_and_neg_rejects_extra_literal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // Invalid: clause has an extra literal 'c' beyond the spec shape
    let err = validate_strict(
        &terms,
        AletheRule::AndNeg,
        vec![and_ab, not_a, not_b, c],
        vec![],
    )
    .expect_err("extra literal in and_neg clause must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_and_neg_rejects_duplicate_negation() {
    // META-FALSE-PROVE regression: and_neg is the tautology (and a b) ∨ ¬a ∨ ¬b.
    // The old validator only COUNTED literals negating some conjunct, so a
    // duplicated ¬a stood in for the missing ¬b. Forged clause
    // [(and a b), ¬a, ¬a] is NOT a tautology (false at a=true, b=false) yet was
    // accepted, letting it resolve to the empty clause and certify UNSAT on a
    // satisfiable formula. Strict mode must REJECT it.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    let not_a = terms.mk_not_raw(a);
    let err = validate_strict(
        &terms,
        AletheRule::AndNeg,
        vec![and_ab, not_a, not_a],
        vec![],
    )
    .expect_err("duplicate negation hiding a missing conjunct must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- or_pos ---

#[test]
fn test_strict_or_pos_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let or_abc = mk_or_raw(&mut terms, vec![a, b, c]);
    let not_or = terms.mk_not_raw(or_abc);
    // or_pos: (cl (not (or a b c)) a b c)
    validate_strict(&terms, AletheRule::OrPos(0), vec![not_or, a, b, c], vec![])
        .expect("valid or_pos should pass");
}

#[test]
fn test_strict_or_pos_wrong_disjunct() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let or_ab = mk_or_raw(&mut terms, vec![a, b]);
    let not_or = terms.mk_not_raw(or_ab);
    // Wrong: clause has 'd' instead of 'b'
    let err = validate_strict(&terms, AletheRule::OrPos(0), vec![not_or, a, d], vec![])
        .expect_err("wrong disjunct must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- or_neg ---

#[test]
fn test_strict_or_neg_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let or_ab = mk_or_raw(&mut terms, vec![a, b]);
    let not_a = terms.mk_not_raw(a);
    // or_neg: (cl (or a b) (not a))
    validate_strict(&terms, AletheRule::OrNeg, vec![or_ab, not_a], vec![])
        .expect("valid or_neg should pass");
}

#[test]
fn test_strict_or_neg_accepts_emitted_clause_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let or_ab = mk_or_raw(&mut terms, vec![a, b]);
    let not_a = terms.mk_not_raw(a);
    validate_strict(&terms, AletheRule::OrNeg, vec![not_a, or_ab], vec![])
        .expect("emitted or_neg clause order should pass");
}

#[test]
fn test_strict_or_neg_accepts_compact_complement_of_negated_disjunct() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let or_term = mk_or_raw(&mut terms, vec![b, not_a]);

    // Internally AY normalizes the complement of `(not a)` to `a`; the
    // printer restores the explicit double negation and a `not_not` bridge.
    validate_strict(&terms, AletheRule::OrNeg, vec![or_term, a], vec![])
        .expect("the exact compact complement must pass");
}

#[test]
fn test_strict_or_neg_rejects_wrong_positive_literal_for_negated_disjunct() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let or_term = mk_or_raw(&mut terms, vec![b, not_a]);

    let err = validate_strict(&terms, AletheRule::OrNeg, vec![or_term, c], vec![])
        .expect_err("an unrelated positive literal must not pass as a complement");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_or_neg_literal_not_disjunct() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let or_ab = mk_or_raw(&mut terms, vec![a, b]);
    let not_c = terms.mk_not_raw(c);
    // Wrong: (not c) but c is not a disjunct of (or a b)
    let err = validate_strict(&terms, AletheRule::OrNeg, vec![or_ab, not_c], vec![])
        .expect_err("non-disjunct must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- equiv_pos1 ---

#[test]
fn test_strict_equiv_pos1_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq = terms.mk_not_raw(eq_ab);
    let not_b = terms.mk_not_raw(b);
    // equiv_pos1: (cl (not (= a b)) a (not b))
    validate_strict(
        &terms,
        AletheRule::EquivPos1,
        vec![not_eq, a, not_b],
        vec![],
    )
    .expect("valid equiv_pos1 should pass");
}

// --- equiv_pos2 ---

#[test]
fn test_strict_equiv_pos2_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq = terms.mk_not_raw(eq_ab);
    let not_a = terms.mk_not_raw(a);
    // equiv_pos2: (cl (not (= a b)) (not a) b)
    validate_strict(
        &terms,
        AletheRule::EquivPos2,
        vec![not_eq, not_a, b],
        vec![],
    )
    .expect("valid equiv_pos2 should pass");
}

// --- equiv_neg1 ---

#[test]
fn test_strict_equiv_neg1_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // equiv_neg1: (cl (= a b) (not a) (not b))
    validate_strict(
        &terms,
        AletheRule::EquivNeg1,
        vec![eq_ab, not_a, not_b],
        vec![],
    )
    .expect("valid equiv_neg1 should pass");
}

// --- equiv_neg2 ---

#[test]
fn test_strict_equiv_neg2_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    // equiv_neg2: (cl (= a b) a b)
    validate_strict(&terms, AletheRule::EquivNeg2, vec![eq_ab, a, b], vec![])
        .expect("valid equiv_neg2 should pass");
}

#[test]
fn test_strict_equiv_neg2_accepts_emitted_clause_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    validate_strict(&terms, AletheRule::EquivNeg2, vec![a, b, eq_ab], vec![])
        .expect("emitted equiv_neg2 clause order should pass");
}

// --- ite_pos1 ---

#[test]
fn test_strict_ite_pos1_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    // ite_pos1: (cl (not (ite c t e)) c e)
    validate_strict(&terms, AletheRule::ItePos1, vec![not_ite, c, e], vec![])
        .expect("valid ite_pos1 should pass");
}

// --- ite_pos2 ---

#[test]
fn test_strict_ite_pos2_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    let not_c = terms.mk_not_raw(c);
    // ite_pos2: (cl (not (ite c t e)) (not c) t)
    validate_strict(&terms, AletheRule::ItePos2, vec![not_ite, not_c, t], vec![])
        .expect("valid ite_pos2 should pass");
}

// --- ite_neg1 ---

#[test]
fn test_strict_ite_neg1_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_e = terms.mk_not_raw(e);
    // ite_neg1: (cl (ite c t e) c (not e))
    validate_strict(&terms, AletheRule::IteNeg1, vec![ite, c, not_e], vec![])
        .expect("valid ite_neg1 should pass");
}

#[test]
fn test_strict_ite_neg1_accepts_emitted_clause_order() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_e = terms.mk_not_raw(e);
    validate_strict(&terms, AletheRule::IteNeg1, vec![c, not_e, ite], vec![])
        .expect("emitted ite_neg1 clause order should pass");
}

// --- ite_neg2 ---

#[test]
fn test_strict_ite_neg2_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_c = terms.mk_not_raw(c);
    let not_t = terms.mk_not_raw(t);
    // ite_neg2: (cl (ite c t e) (not c) (not t))
    validate_strict(&terms, AletheRule::IteNeg2, vec![ite, not_c, not_t], vec![])
        .expect("valid ite_neg2 should pass");
}

// --- ite1 / ite2 (premise-consuming boolean ite elimination) ---

#[test]
fn test_strict_ite1_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let _ = t;
    // premise (cl (ite c t e)) \u22a2 (cl c e)
    validate_strict_with_derived(
        &terms,
        AletheRule::Ite1,
        vec![c, e],
        vec![ProofId(0)],
        vec![Some(vec![ite])],
    )
    .expect("valid ite1 should pass");
}

#[test]
fn test_strict_ite1_rejects_then_branch() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let _ = e;
    validate_strict_with_derived(
        &terms,
        AletheRule::Ite1,
        vec![c, t],
        vec![ProofId(0)],
        vec![Some(vec![ite])],
    )
    .expect_err("ite1 concluding the then-branch must be rejected");
}

#[test]
fn test_strict_ite2_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_c = terms.mk_not_raw(c);
    let _ = e;
    // premise (cl (ite c t e)) \u22a2 (cl (not c) t)
    validate_strict_with_derived(
        &terms,
        AletheRule::Ite2,
        vec![not_c, t],
        vec![ProofId(0)],
        vec![Some(vec![ite])],
    )
    .expect("valid ite2 should pass");
}

#[test]
fn test_strict_ite2_rejects_else_branch() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_c = terms.mk_not_raw(c);
    let _ = t;
    validate_strict_with_derived(
        &terms,
        AletheRule::Ite2,
        vec![not_c, e],
        vec![ProofId(0)],
        vec![Some(vec![ite])],
    )
    .expect_err("ite2 concluding the else-branch must be rejected");
}

// --- ite_intro (self-naming term-ite definition) ---

#[test]
fn test_strict_ite_intro_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let s = terms.mk_ite(c, x, y);
    let k = terms.mk_int(2.into());
    let p = terms.mk_app(ay_core::Symbol::named("<"), vec![s, k], Sort::Bool);
    let eq_sx = terms.mk_app(ay_core::Symbol::named("="), vec![s, x], Sort::Bool);
    let eq_sy = terms.mk_app(ay_core::Symbol::named("="), vec![s, y], Sort::Bool);
    let def = terms.mk_ite(c, eq_sx, eq_sy);
    let and_term = terms.mk_app(ay_core::Symbol::named("and"), vec![p, def], Sort::Bool);
    let intro_eq = terms.mk_app(ay_core::Symbol::named("="), vec![p, and_term], Sort::Bool);
    validate_strict(&terms, AletheRule::IteIntro, vec![intro_eq], vec![])
        .expect("valid ite_intro should pass");
}

#[test]
fn test_strict_ite_intro_rejects_foreign_ite() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let s = terms.mk_ite(c, x, y);
    let k = terms.mk_int(2.into());
    let eq_sx = terms.mk_app(ay_core::Symbol::named("="), vec![s, x], Sort::Bool);
    let eq_sy = terms.mk_app(ay_core::Symbol::named("="), vec![s, y], Sort::Bool);
    let def = terms.mk_ite(c, eq_sx, eq_sy);
    // A left side that does NOT contain the defined ite term.
    let z = terms.mk_var("z", Sort::Int);
    let q = terms.mk_app(ay_core::Symbol::named("<"), vec![z, k], Sort::Bool);
    let and_term = terms.mk_app(ay_core::Symbol::named("and"), vec![q, def], Sort::Bool);
    let intro_eq = terms.mk_app(ay_core::Symbol::named("="), vec![q, and_term], Sort::Bool);
    validate_strict(&terms, AletheRule::IteIntro, vec![intro_eq], vec![])
        .expect_err("ite_intro over a formula not containing the ite must be rejected");
}

#[test]
fn test_strict_ite_intro_rejects_swapped_branches() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let s = terms.mk_ite(c, x, y);
    let k = terms.mk_int(2.into());
    let p = terms.mk_app(ay_core::Symbol::named("<"), vec![s, k], Sort::Bool);
    let eq_sx = terms.mk_app(ay_core::Symbol::named("="), vec![s, x], Sort::Bool);
    let eq_sy = terms.mk_app(ay_core::Symbol::named("="), vec![s, y], Sort::Bool);
    // Swapped: then-branch equates the ELSE branch.
    let def = terms.mk_ite(c, eq_sy, eq_sx);
    let and_term = terms.mk_app(ay_core::Symbol::named("and"), vec![p, def], Sort::Bool);
    let intro_eq = terms.mk_app(ay_core::Symbol::named("="), vec![p, and_term], Sort::Bool);
    validate_strict(&terms, AletheRule::IteIntro, vec![intro_eq], vec![])
        .expect_err("ite_intro with swapped branch equalities must be rejected");
}

// --- xor_pos1 ---

#[test]
fn test_strict_xor_pos1_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_xor = terms.mk_not_raw(xor_ab);
    // xor_pos1: (cl (not (xor a b)) a b)
    validate_strict(&terms, AletheRule::XorPos1, vec![not_xor, a, b], vec![])
        .expect("valid xor_pos1 should pass");
}

// --- xor_neg1 ---

#[test]
fn test_strict_xor_neg1_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_b = terms.mk_not_raw(b);
    // xor_neg1: (cl (xor a b) a (not b))
    validate_strict(&terms, AletheRule::XorNeg1, vec![xor_ab, a, not_b], vec![])
        .expect("valid xor_neg1 should pass");
}

#[test]
fn test_strict_xor_neg1_accepts_emitted_clause_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_b = terms.mk_not_raw(b);
    validate_strict(&terms, AletheRule::XorNeg1, vec![a, not_b, xor_ab], vec![])
        .expect("emitted xor_neg1 clause order should pass");
}

// --- eq_reflexive ---

#[test]
fn test_strict_eq_reflexive_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let eq_aa = mk_eq_raw(&mut terms, a, a);
    // eq_reflexive: (cl (= a a))
    validate_strict(&terms, AletheRule::EqReflexive, vec![eq_aa], vec![])
        .expect("valid eq_reflexive should pass");
}

#[test]
fn test_strict_eq_reflexive_rejects_non_reflexive() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    // Wrong: (= a b) where a != b
    let err = validate_strict(&terms, AletheRule::EqReflexive, vec![eq_ab], vec![])
        .expect_err("non-reflexive must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- eq_symmetric ---

#[test]
fn test_strict_eq_symmetric_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_ba = mk_eq_raw(&mut terms, b, a);
    let equiv = mk_eq_raw(&mut terms, eq_ab, eq_ba);
    // eq_symmetric: (cl (= (= a b) (= b a)))
    validate_strict(&terms, AletheRule::EqSymmetric, vec![equiv], vec![])
        .expect("valid eq_symmetric should pass");
}

#[test]
fn test_strict_eq_symmetric_rejects_unswapped() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_bc = mk_eq_raw(&mut terms, b, c);
    // Wrong: (= (= a b) (= b c)) is not an orientation swap
    let equiv = mk_eq_raw(&mut terms, eq_ab, eq_bc);
    validate_strict(&terms, AletheRule::EqSymmetric, vec![equiv], vec![])
        .expect_err("non-swapped eq_symmetric must fail");
}

#[test]
fn test_strict_eq_symmetric_rejects_extra_literals() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_ba = mk_eq_raw(&mut terms, b, a);
    let equiv = mk_eq_raw(&mut terms, eq_ab, eq_ba);
    validate_strict(&terms, AletheRule::EqSymmetric, vec![equiv, eq_ab], vec![])
        .expect_err("multi-literal eq_symmetric must fail");
}

// --- implies_pos ---

#[test]
fn test_strict_implies_pos_valid_desugared() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    // Desugared (=> a b) = (or (not a) b)
    let imp = mk_or_raw(&mut terms, vec![not_a, b]);
    let not_imp = terms.mk_not_raw(imp);
    // implies_pos: (cl (not (=> a b)) (not a) b) = (cl (not (or (not a) b)) (not a) b)
    validate_strict(
        &terms,
        AletheRule::ImpliesPos,
        vec![not_imp, not_a, b],
        vec![],
    )
    .expect("valid implies_pos (desugared) should pass");
}

// --- contraction ---

#[test]
fn test_strict_contraction_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    // Premise clause: [a, b, a] (has duplicate 'a')
    let prior = vec![Some(vec![a, b, a])];
    // Result: [a, b] (duplicates removed)
    validate_strict_with_derived(
        &terms,
        AletheRule::Contraction,
        vec![a, b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid contraction should pass");
}

#[test]
fn test_strict_contraction_rejects_extra_literal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    // Premise clause: [a, b]
    let prior = vec![Some(vec![a, b])];
    // Wrong: result has 'c' which is not in premise
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Contraction,
        vec![a, c],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("extra literal must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_contraction_many_literals_correctness() {
    // Verify contraction correctness at larger scale: 200 unique literals,
    // premise has each literal duplicated 3x (600 total).
    // This exercises the O(n^2) .contains() paths in validate_contraction.
    let mut terms = TermStore::new();
    let n = 200;
    let vars: Vec<TermId> = (0..n)
        .map(|i| terms.mk_var(format!("v{i}"), Sort::Bool))
        .collect();

    // Premise: each variable appears 3 times
    let mut premise_lits = Vec::with_capacity(n * 3);
    for &v in &vars {
        premise_lits.push(v);
        premise_lits.push(v);
        premise_lits.push(v);
    }
    let prior = vec![Some(premise_lits)];

    // Result: deduplicated — each variable once
    validate_strict_with_derived(
        &terms,
        AletheRule::Contraction,
        vars,
        vec![ProofId(0)],
        prior,
    )
    .expect("200-literal contraction should pass");
}

#[test]
fn test_contraction_rejects_dropped_premise_literal() {
    // Premise has [a, b, c, d], result drops 'c' → must fail
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let prior = vec![Some(vec![a, b, c, d])];
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Contraction,
        vec![a, b, d],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("dropping a premise literal must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- weakening ---

#[test]
fn test_strict_weakening_valid_prefix() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    // Premise [a, b]; conclusion [a, b, c] (premise is a leading prefix).
    let prior = vec![Some(vec![a, b])];
    validate_strict_with_derived(
        &terms,
        AletheRule::Weakening,
        vec![a, b, c],
        vec![ProofId(0)],
        prior,
    )
    .expect("prefix weakening should pass");
}

#[test]
fn test_strict_weakening_rejects_non_prefix() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    // Premise [a, b]; conclusion [a, c, b]: the premise is NOT a leading
    // prefix (carcara's positional check would fail too).
    let prior = vec![Some(vec![a, b])];
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Weakening,
        vec![a, c, b],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("non-prefix weakening must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_weakening_rejects_dropped_literal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    // Premise [a, b]; conclusion [a]: weakening can only ADD literals.
    let prior = vec![Some(vec![a, b])];
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Weakening,
        vec![a],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("shorter conclusion must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- distinct_elim ---

#[test]
fn test_strict_distinct_elim_binary() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".into());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let dist = terms.mk_app(ay_core::Symbol::named("distinct"), [a, b], Sort::Bool);
    let eq = terms.mk_app(ay_core::Symbol::named("="), [a, b], Sort::Bool);
    let not_eq = terms.mk_not_raw(eq);
    let equiv = terms.mk_app(ay_core::Symbol::named("="), [dist, not_eq], Sort::Bool);
    validate_strict_with_derived(
        &terms,
        AletheRule::DistinctElim,
        vec![equiv],
        vec![],
        vec![],
    )
    .expect("binary distinct_elim should pass");
}

#[test]
fn test_strict_distinct_elim_ternary() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".into());
    let xs: Vec<TermId> = ["a", "b", "c"]
        .iter()
        .map(|n| terms.mk_var(*n, u.clone()))
        .collect();
    let dist = terms.mk_app(ay_core::Symbol::named("distinct"), xs.clone(), Sort::Bool);
    let mut conjs = Vec::new();
    for i in 0..3 {
        for j in (i + 1)..3 {
            let eq = terms.mk_app(ay_core::Symbol::named("="), [xs[i], xs[j]], Sort::Bool);
            conjs.push(terms.mk_not_raw(eq));
        }
    }
    let and = terms.mk_app(ay_core::Symbol::named("and"), conjs, Sort::Bool);
    let equiv = terms.mk_app(ay_core::Symbol::named("="), [dist, and], Sort::Bool);
    validate_strict_with_derived(
        &terms,
        AletheRule::DistinctElim,
        vec![equiv],
        vec![],
        vec![],
    )
    .expect("ternary distinct_elim should pass");
}

#[test]
fn test_strict_distinct_elim_rejects_wrong_pair_order() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".into());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let dist = terms.mk_app(ay_core::Symbol::named("distinct"), [a, b], Sort::Bool);
    // Flipped pair: (not (= b a)) instead of (not (= a b)).
    let eq = terms.mk_app(ay_core::Symbol::named("="), [b, a], Sort::Bool);
    let not_eq = terms.mk_not_raw(eq);
    let equiv = terms.mk_app(ay_core::Symbol::named("="), [dist, not_eq], Sort::Bool);
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::DistinctElim,
        vec![equiv],
        vec![],
        vec![],
    )
    .expect_err("flipped pair order must fail");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

#[test]
fn test_contraction_rejects_duplicate_in_result() {
    // Premise has [a, b, a], result has [a, a, b] — duplicates in result must fail
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let prior = vec![Some(vec![a, b, a])];
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Contraction,
        vec![a, a, b],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("duplicate in result must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- not_and (premise-based) ---

#[test]
fn test_strict_not_and_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    let not_and = terms.mk_not_raw(and_ab);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // Premise: (not (and a b))
    let prior = vec![Some(vec![not_and])];
    // not_and: (cl (not a) (not b))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotAnd,
        vec![not_a, not_b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_and should pass");
}

// --- not_or (premise-based) ---

#[test]
fn test_strict_not_or_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let or_ab = mk_or_raw(&mut terms, vec![a, b]);
    let not_or = terms.mk_not_raw(or_ab);
    let not_a = terms.mk_not_raw(a);
    // Premise: (not (or a b))
    let prior = vec![Some(vec![not_or])];
    // not_or: (cl (not a))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotOr,
        vec![not_a],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_or should pass");
}

// --- not_equiv1 (premise-based) ---

#[test]
fn test_strict_not_equiv1_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq = terms.mk_not_raw(eq_ab);
    // Premise: (not (= a b))
    let prior = vec![Some(vec![not_eq])];
    // not_equiv1: (cl a b)
    validate_strict_with_derived(
        &terms,
        AletheRule::NotEquiv1,
        vec![a, b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_equiv1 should pass");
}

// --- not_equiv2 (premise-based) ---

#[test]
fn test_strict_not_equiv2_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq = terms.mk_not_raw(eq_ab);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // Premise: (not (= a b))
    let prior = vec![Some(vec![not_eq])];
    // not_equiv2: (cl (not a) (not b))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotEquiv2,
        vec![not_a, not_b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_equiv2 should pass");
}

// --- not_ite1 (premise-based) ---

#[test]
fn test_strict_not_ite1_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    let not_e = terms.mk_not_raw(e);
    // Premise: (not (ite c t e))
    let prior = vec![Some(vec![not_ite])];
    // not_ite1: (cl c (not e))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotIte1,
        vec![c, not_e],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_ite1 should pass");
}

// --- not_ite2 (premise-based) ---

#[test]
fn test_strict_not_ite2_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    let not_c = terms.mk_not_raw(c);
    let not_t = terms.mk_not_raw(t);
    // Premise: (not (ite c t e))
    let prior = vec![Some(vec![not_ite])];
    // not_ite2: (cl (not c) (not t))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotIte2,
        vec![not_c, not_t],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_ite2 should pass");
}

mod array_chain_axiom_tests;
mod boolean_coverage_tests;
mod boolean_negation_coverage_tests;
mod datatype_axiom_tests;
mod euf_coverage_tests;
mod lra_farkas_coverage_tests;
mod or_coverage_tests;
mod theory_forgery_tests;
