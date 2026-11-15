// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the authored boolean-skeleton refutation.
//!
//! Every positive test asserts the built candidate is accepted by the STRICT
//! checker over the exact authored scope — the same gate the installation
//! boundary applies — so a test can never pass on a document the publisher
//! would refuse. Every negative test asserts the lane recognizes nothing, which
//! is the fail-closed direction.

use super::*;

/// Mirror the lane's own `#authored-scope-premise-grant` step: a bare
/// `Executor` has no installed problem obligation, so without the grant the
/// strict checker refuses every `assume` as unauthorized — exactly the
/// production failure the grant exists to fix.
fn grant_authored_premises(exec: &mut Executor, authored: &[TermId]) {
    for &root in authored {
        exec.record_rebuilt_authored_proof_premise(root);
    }
}

/// `(and G E)` plus `(not E)` where `E` is a quantifier: the shape the
/// ground-core leg drops because neither root is quantifier-free.
fn complementary_quantifier_fixture() -> (Executor, Vec<TermId>) {
    let mut exec = Executor::new();
    let n = exec.ctx.terms.mk_var("n", Sort::Int);
    let m = exec.ctx.terms.mk_var("m", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![x, n], Sort::Bool);
    let exists = exec
        .ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let ground = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![m, n], Sort::Bool);
    let conjunction = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![ground, exists], Sort::Bool);
    let negated = exec.ctx.terms.mk_not_raw(exists);
    (exec, vec![conjunction, negated])
}

#[test]
fn complementary_units_build_a_strict_authored_refutation() {
    let (mut exec, authored) = complementary_quantifier_fixture();
    let plan = exec
        .plan_authored_skeleton_closure(&authored)
        .expect("complementary units must be recognized");
    assert!(matches!(plan, SkeletonClosure::ComplementaryUnits { .. }));
    let candidate = exec
        .build_authored_skeleton_candidate(&authored, &plan)
        .expect("candidate must build");
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok(),
        "every assume must be an authored root"
    );
    assert!(Executor::proof_derives_empty_clause(&candidate));
    grant_authored_premises(&mut exec, &authored);
    let quality = exec
        .check_proof_strict_with_datatypes(&candidate)
        .expect("strict check must accept");
    assert!(quality.is_complete(), "candidate must be a complete proof");
}

#[test]
fn the_built_certificate_carries_no_hole_and_no_trust_step() {
    let (mut exec, authored) = complementary_quantifier_fixture();
    let plan = exec.plan_authored_skeleton_closure(&authored).unwrap();
    let candidate = exec
        .build_authored_skeleton_candidate(&authored, &plan)
        .unwrap();
    for step in &candidate.steps {
        match step {
            ProofStep::Step { rule, .. } => assert!(
                matches!(
                    rule,
                    AletheRule::AndPos(_) | AletheRule::NotAnd | AletheRule::Or
                ),
                "unexpected rule in a skeleton certificate: {rule:?}"
            ),
            ProofStep::Assume(_) | ProofStep::Resolution { .. } => {}
            other => panic!("unexpected step kind in a skeleton certificate: {other:?}"),
        }
    }
}

/// A NEGATIVE control with the same term inventory: the second root negates a
/// DIFFERENT quantifier, so nothing closes.
#[test]
fn a_different_quantifier_on_the_negative_side_is_not_recognized() {
    let mut exec = Executor::new();
    let n = exec.ctx.terms.mk_var("n", Sort::Int);
    let m = exec.ctx.terms.mk_var("m", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![x, n], Sort::Bool);
    let other_body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![x, m], Sort::Bool);
    let exists = exec
        .ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let other = exec
        .ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], other_body);
    let ground = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![m, n], Sort::Bool);
    let conjunction = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![ground, exists], Sort::Bool);
    let negated = exec.ctx.terms.mk_not_raw(other);
    let authored = vec![conjunction, negated];
    assert!(
        exec.plan_authored_skeleton_closure(&authored).is_none(),
        "a different quantifier must not close the skeleton"
    );
}

#[test]
fn a_falsified_negated_conjunction_builds_a_strict_refutation() {
    let mut exec = Executor::new();
    let n = exec.ctx.terms.mk_var("n", Sort::Int);
    let m = exec.ctx.terms.mk_var("m", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![x, n], Sort::Bool);
    let exists = exec
        .ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let g1 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![m, n], Sort::Bool);
    let g2 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![n, m], Sort::Bool);
    let assumed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![g1, g2, exists], Sort::Bool);
    // The GOAL negates a sub-conjunction of what is assumed.
    let goal_inner = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![g1, exists], Sort::Bool);
    let goal = exec.ctx.terms.mk_not_raw(goal_inner);
    let authored = vec![assumed, goal];
    let plan = exec
        .plan_authored_skeleton_closure(&authored)
        .expect("falsified negated conjunction must be recognized");
    assert!(matches!(plan, SkeletonClosure::FalsifiedNegatedAnd { .. }));
    let candidate = exec
        .build_authored_skeleton_candidate(&authored, &plan)
        .expect("candidate must build");
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok());
    assert!(Executor::proof_derives_empty_clause(&candidate));
    grant_authored_premises(&mut exec, &authored);
    assert!(exec
        .check_proof_strict_with_datatypes(&candidate)
        .is_ok_and(|quality| quality.is_complete()));
}

/// A NEGATIVE control for the conjunction shape: one conjunct of the negated
/// goal is NOT assumed, so the clause does not close and the lane declines.
#[test]
fn an_unassumed_goal_conjunct_declines() {
    let mut exec = Executor::new();
    let n = exec.ctx.terms.mk_var("n", Sort::Int);
    let m = exec.ctx.terms.mk_var("m", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![x, n], Sort::Bool);
    let exists = exec
        .ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let g1 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![m, n], Sort::Bool);
    let unassumed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), vec![n, m], Sort::Bool);
    let assumed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![g1, exists], Sort::Bool);
    let goal_inner =
        exec.ctx
            .terms
            .mk_app(Symbol::named("and"), vec![unassumed, exists], Sort::Bool);
    let goal = exec.ctx.terms.mk_not_raw(goal_inner);
    let authored = vec![assumed, goal];
    assert!(
        exec.plan_authored_skeleton_closure(&authored).is_none(),
        "a goal conjunct the problem does not assert must not close the skeleton"
    );
}

/// A satisfiable disjunction with only one refuted alternative must leave the
/// term inventory untouched when recognition declines. In particular, `not p`
/// has never been constructed and must not be interned by the scan.
#[test]
fn a_declined_disjunction_does_not_create_terms() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let q = exec.ctx.terms.mk_var("q", Sort::Bool);
    let disjunction = exec
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![p, q], Sort::Bool);
    let not_q = exec.ctx.terms.mk_not_raw(q);
    let authored = [disjunction, not_q];
    let len = exec.ctx.terms.len();
    let stamp = exec.ctx.terms.snapshot_stamp();

    assert!(exec.plan_authored_skeleton_closure(&authored).is_none());
    assert_eq!(exec.ctx.terms.len(), len);
    assert_eq!(exec.ctx.terms.snapshot_stamp(), stamp);
}

#[test]
fn existing_negative_units_refute_a_disjunction_strictly() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let q = exec.ctx.terms.mk_var("q", Sort::Bool);
    let disjunction = exec
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![p, q], Sort::Bool);
    let not_p = exec.ctx.terms.mk_not_raw(p);
    let not_q = exec.ctx.terms.mk_not_raw(q);
    let authored = [disjunction, not_p, not_q];
    let plan = exec.plan_authored_skeleton_closure(&authored).unwrap();
    assert!(matches!(plan, SkeletonClosure::FalsifiedOr { .. }));
    let candidate = exec
        .build_authored_skeleton_candidate(&authored, &plan)
        .unwrap();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok());
    assert!(Executor::proof_derives_empty_clause(&candidate));
    grant_authored_premises(&mut exec, &authored);
    assert!(exec
        .check_proof_strict_with_datatypes(&candidate)
        .is_ok_and(|quality| quality.is_complete()));
}

/// For a raw `not (not p)` disjunct the complement is the existing `not p`
/// term. That member is indexed under `p`, so the negative branch must retain
/// its one-layer complement rather than looking up the disjunct's atom.
#[test]
fn a_nested_raw_negation_in_a_disjunction_is_refuted_strictly() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let q = exec.ctx.terms.mk_var("q", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not_raw(p);
    let not_not_p = exec.ctx.terms.mk_not_raw(not_p);
    let not_q = exec.ctx.terms.mk_not_raw(q);
    let disjunction = exec
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![not_not_p, q], Sort::Bool);
    let authored = [disjunction, not_p, not_q];
    let plan = exec.plan_authored_skeleton_closure(&authored).unwrap();
    assert!(matches!(plan, SkeletonClosure::FalsifiedOr { .. }));
    let candidate = exec
        .build_authored_skeleton_candidate(&authored, &plan)
        .unwrap();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok());
    assert!(Executor::proof_derives_empty_clause(&candidate));
    grant_authored_premises(&mut exec, &authored);
    assert!(exec
        .check_proof_strict_with_datatypes(&candidate)
        .is_ok_and(|quality| quality.is_complete()));
}

/// The lane must consume at most one attempt per check-sat, so a repeated
/// consultation cannot re-pay the scan.
#[test]
fn the_lane_budget_is_consumed_once() {
    let (mut exec, authored) = complementary_quantifier_fixture();
    let _ = authored;
    assert_eq!(exec.authored_skeleton_refutation_attempts.get(), 0);
    exec.authored_skeleton_refutation_attempts
        .set(MAX_LANE_ATTEMPTS);
    assert!(
        !exec.try_translate_authored_skeleton_refutation_unsat(),
        "an exhausted budget must decline"
    );
}

/// The grant is LOAD-BEARING, not decoration: without it the same candidate is
/// refused as an unauthorized assumption. A change that silently dropped the
/// grant would fail here rather than quietly publish nothing.
#[test]
fn without_the_authored_premise_grant_the_strict_check_refuses() {
    let (mut exec, authored) = complementary_quantifier_fixture();
    let plan = exec.plan_authored_skeleton_closure(&authored).unwrap();
    let candidate = exec
        .build_authored_skeleton_candidate(&authored, &plan)
        .unwrap();
    assert!(
        matches!(
            exec.check_proof_strict_with_datatypes(&candidate),
            Err(ay_proof::ProofCheckError::UnauthorizedAssumption { .. })
        ),
        "an ungranted authored root must be refused, not accepted"
    );
}
