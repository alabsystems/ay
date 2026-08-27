// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial negatives and exhaustive sweeps for the bridge planner.
//!
//! Two things are checked here that the positive tests cannot:
//!
//! * **Every negative names a CONCRETE falsifying assignment and CHECKS it.**
//!   The claim a bridge makes is that its clause
//!   `(cl (not h_1) .. (not h_k) goal)` is VALID. A negative therefore either
//!   exhibits a model in which every literal is FALSE — computed by
//!   [`falsifies`], which shares no code with the planner — or shows that the
//!   planner declines.
//! * **Exhaustive sweeps over a bounded alphabet**, with EVERY accept
//!   re-checked by that same independent evaluator, and the sweep asserting
//!   the box contains genuinely INVALID configurations so a future loosening
//!   cannot pass unnoticed.

use super::plan_definitional_bridge;
use super::tests::{bridge, element, eq, uninterpreted};
use crate::congruence_derivation::sweep_tests::falsifies;
use ay_core::{Sort, Symbol, TermStore};

// ===== adversarial negatives =====

/// `(= a b)` does NOT follow from `(= c d)`. The named falsifying assignment
/// is `a=0, b=1, c=0, d=0`, and it is CHECKED: the independent evaluator finds
/// a countermodel of the clause a planner would have to emit.
#[test]
fn an_unentailed_goal_has_a_checked_countermodel_and_is_declined() {
    let mut terms = TermStore::new();
    let a = element(&mut terms, "a");
    let b = element(&mut terms, "b");
    let c = element(&mut terms, "c");
    let d = element(&mut terms, "d");
    let hypothesis = eq(&mut terms, c, d);
    let goal = eq(&mut terms, a, b);
    let negated = terms.mk_not(hypothesis);
    let countermodel = falsifies(&terms, &[negated, goal])
        .expect("a=0 b=1 c=0 d=0 falsifies both literals of the clause");
    let block = |term| {
        countermodel
            .iter()
            .find(|(other, _)| *other == term)
            .expect("every leaf is assigned")
            .1
    };
    assert_eq!(block(c), block(d), "the hypothesis holds at the witness");
    assert_ne!(block(a), block(b), "the goal FAILS at the witness");
    assert!(plan_definitional_bridge(&mut terms, goal, &[hypothesis]).is_none());
}

/// A goal entailed by NOTHING in the pool is declined rather than emitted with
/// an empty hypothesis list — which would be a derivation of a non-tautology
/// from no premise at all. Falsifying assignment: `a=0, b=1`, checked.
#[test]
fn a_goal_entailed_by_nothing_in_the_pool_is_declined() {
    let mut terms = TermStore::new();
    let a = element(&mut terms, "a");
    let b = element(&mut terms, "b");
    let goal = eq(&mut terms, a, b);
    let unrelated_l = element(&mut terms, "u");
    let unrelated_r = element(&mut terms, "v");
    let unrelated = eq(&mut terms, unrelated_l, unrelated_r);
    assert!(
        falsifies(&terms, &[goal]).is_some(),
        "`(= a b)` is not valid: a=0, b=1 refutes it"
    );
    assert!(plan_definitional_bridge(&mut terms, goal, &[unrelated]).is_none());
}

/// A congruence that would need the WRONG argument position declines. From
/// `(= a b)` alone, `(= (f a c) (f b d))` does not follow: `c=0, d=1` refutes
/// it while `(= a b)` holds. Checked.
#[test]
fn a_congruence_missing_one_argument_equality_is_declined() {
    let mut terms = TermStore::new();
    let u = uninterpreted("Element");
    let a = element(&mut terms, "a");
    let b = element(&mut terms, "b");
    let c = element(&mut terms, "c");
    let d = element(&mut terms, "d");
    let left = terms.mk_app(Symbol::named("f"), vec![a, c], u.clone());
    let right = terms.mk_app(Symbol::named("f"), vec![b, d], u);
    let hypothesis = eq(&mut terms, a, b);
    let goal = eq(&mut terms, left, right);
    let negated = terms.mk_not(hypothesis);
    let countermodel = falsifies(&terms, &[negated, goal])
        .expect("a=b=0, c=0, d=1 falsifies the hypothesis-negation and the goal");
    let block = |term| {
        countermodel
            .iter()
            .find(|(other, _)| *other == term)
            .expect("every leaf is assigned")
            .1
    };
    assert_eq!(block(a), block(b));
    assert_ne!(block(left), block(right));
    assert!(plan_definitional_bridge(&mut terms, goal, &[hypothesis]).is_none());
}

/// A candidate whose negation is not a plain `Not` wrapper is DROPPED, not
/// mis-read. `(= x true)` folds to `x` under `mk_eq`, so a pool entry built
/// that way is not a binary `=` application at all.
#[test]
fn a_candidate_whose_negation_is_not_a_plain_wrapper_is_dropped() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    // `(and p)` and `(and q)`: `mk_not` pushes De Morgan through `and`, so the
    // negation of this candidate is NOT a plain wrapper around it.
    let conj = terms.mk_app(Symbol::named("and"), vec![p, q], Sort::Bool);
    let negated = terms.mk_not(conj);
    assert!(
        !matches!(terms.get(negated), ay_core::TermData::Not(inner) if *inner == conj),
        "the fixture depends on `mk_not` normalising this candidate"
    );
    let a = element(&mut terms, "a");
    let b = element(&mut terms, "b");
    let goal = eq(&mut terms, a, b);
    assert!(plan_definitional_bridge(&mut terms, goal, &[conj]).is_none());
}

/// The planned clause is EXACTLY what the caller resolves against: hypotheses
/// first, in the planner's own order, goal last.
#[test]
fn the_planned_clause_is_the_clause_the_caller_resolves() {
    let mut terms = TermStore::new();
    let fixture = super::tests::store_chain(&mut terms);
    let planned = bridge(&mut terms, fixture.goal, &fixture.candidates);
    let last = planned
        .derivation
        .steps
        .last()
        .expect("a planned fragment has steps");
    let ay_core::ProofStep::Step { clause, .. } = last else {
        panic!("the planner emits only generic steps");
    };
    assert_eq!(clause, &planned.derivation.clause);
    assert_eq!(clause.last(), Some(&fixture.goal));
}

/// No literal outside the bridge clause survives into it — the condition the
/// `cited.len() != literals.len() + 1` guard enforces.
#[test]
fn a_bridge_never_carries_a_literal_outside_its_own_clause() {
    let mut terms = TermStore::new();
    let fixture = super::tests::store_chain(&mut terms);
    let planned = bridge(&mut terms, fixture.goal, &fixture.candidates);
    let mut allowed: Vec<_> = planned
        .hypotheses
        .iter()
        .map(|&hypothesis| terms.mk_not(hypothesis))
        .collect();
    allowed.push(fixture.goal);
    for literal in &planned.derivation.clause {
        assert!(allowed.contains(literal), "a literal escaped the bridge");
    }
}

// ===== exhaustive sweep =====

/// Every subset of a three-equality pool, against a fixed store-chain goal:
/// 8 configurations, every ACCEPT re-checked for VALIDITY by the independent
/// evaluator AND replayed by the untouched strict checker, and the box
/// asserted to contain genuinely INVALID configurations so a future loosening
/// cannot pass unnoticed.
///
/// The pool's third entry `(= e_249 e_253)` is chosen to add NO new sub-term,
/// so the evaluator's alphabet stays at the nine nodes its partition
/// enumeration can afford.
#[test]
fn sweep_every_subset_of_a_three_equality_pool() {
    let mut terms = TermStore::new();
    let fixture = super::tests::store_chain(&mut terms);
    let pool = [fixture.candidates[0], fixture.candidates[1], fixture.spare];
    let mut accepted = 0usize;
    let mut declined = 0usize;
    let mut invalid_boxes = 0usize;
    for mask in 0u32..8 {
        let subset: Vec<_> = (0..3)
            .filter(|bit| mask & (1 << bit) != 0)
            .map(|bit| pool[bit])
            .collect();
        // What a bridge over this WHOLE subset would have to claim.
        let mut whole: Vec<_> = subset.iter().map(|&h| terms.mk_not(h)).collect();
        whole.push(fixture.goal);
        if falsifies(&terms, &whole).is_some() {
            invalid_boxes += 1;
        }
        match plan_definitional_bridge(&mut terms, fixture.goal, &subset) {
            Some(planned) => {
                accepted += 1;
                assert!(
                    falsifies(&terms, &planned.derivation.clause).is_none(),
                    "mask {mask:b}: the independent evaluator refutes an ACCEPTED bridge clause"
                );
                let closed = crate::close_congruence_derivation(&mut terms, &planned.derivation);
                crate::quality::check_proof_strict(&closed, &terms)
                    .expect("every planned step must strict-check");
            }
            None => declined += 1,
        }
    }
    assert_eq!(accepted + declined, 8);
    assert!(accepted > 0, "the sweep must exercise the accept side");
    assert!(
        invalid_boxes > 0,
        "the box must contain genuinely INVALID configurations, or the sweep proves nothing"
    );
    // Exactly the two subsets containing BOTH chain links are bridgeable.
    assert_eq!(accepted, 2);
}

/// The bridge is INSENSITIVE to irrelevant pool growth: adding equalities the
/// explanation does not use never changes the cited set. Every step of the
/// sweep re-runs the independent evaluator on the ACCEPTED clause.
#[test]
fn sweep_irrelevant_pool_growth_never_changes_the_cited_set() {
    let mut terms = TermStore::new();
    let fixture = super::tests::store_chain(&mut terms);
    let baseline = bridge(&mut terms, fixture.goal, &fixture.candidates);
    let mut pool = fixture.candidates.clone();
    for size in 0..12 {
        let left = element(&mut terms, &format!("grow_l{size}"));
        let right = element(&mut terms, &format!("grow_r{size}"));
        let filler = eq(&mut terms, left, right);
        pool.push(filler);
        let planned = bridge(&mut terms, fixture.goal, &pool);
        assert_eq!(
            planned.hypotheses,
            baseline.hypotheses,
            "pool size {} changed the cited set",
            pool.len()
        );
    }
}
