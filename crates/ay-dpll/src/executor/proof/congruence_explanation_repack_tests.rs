// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The RE-PACK arm's own scope guard and the property it rests on — section 4
//! of `congruence_explanation_tests.rs`, split out only to keep each file
//! inside the repository's 500-line ceiling.

use super::super::*;
use super::{explanation_lemma, or_term};

use ay_core::{Sort, Symbol, TermId};

/// The RE-PACK arm's own fail-closed guard, RE-AIMED.
///
/// The first version of this test padded a two-literal congruence with eight
/// irrelevant disjuncts and came back GREEN under its own mutation — the
/// planner declines an unentailed pad for a reason that has nothing to do with
/// the cap, so raising the cap changed nothing. This version uses a
/// transitivity CHAIN of exactly `MAX_REPACK_DISJUNCTS + 1` literals, which
/// the planner derives happily, and ASSERTS that precondition first: with the
/// cap raised the lane fires, and the only thing stopping it here is the cap.
///
/// The cap is SCOPE, not soundness — each disjunct costs an `or_neg` step
/// whose clause carries the WHOLE disjunction — and a decline is fail-closed.
#[test]
fn a_packed_leaf_wider_than_the_repack_cap_is_left_alone() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("EufSort".to_string());
    // NINE literals, pinned as a LITERAL and deliberately NOT computed from
    // `MAX_REPACK_DISJUNCTS`. Measured: the first version derived the width
    // from the constant, so raising the cap widened the fixture with it and
    // the guard test defeated its own mutation.
    let width = 8usize;
    let chain: Vec<TermId> = (0..=width)
        .map(|index| {
            executor
                .ctx
                .terms
                .mk_var(format!("wide_x{index}"), sort.clone())
        })
        .collect();
    let mut equalities = Vec::new();
    let mut flat = Vec::new();
    for window in chain.windows(2) {
        let equality = executor.ctx.terms.mk_eq(window[0], window[1]);
        equalities.push(equality);
        flat.push(executor.ctx.terms.mk_not_raw(equality));
    }
    let goal = executor.ctx.terms.mk_eq(chain[0], chain[width]);
    flat.push(goal);
    assert_eq!(flat.len(), 9, "nine literals, one over the shipped cap");
    // PRECONDITION: the planner derives this clause. Without it the test
    // passes vacuously under its own mutation.
    assert!(
        ay_proof::plan_euf_congruence_derivation(&mut executor.ctx.terms, &flat).is_some(),
        "the fixture must be derivable, or the cap is not what declines it"
    );
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    for &equality in &equalities {
        proof.add_step(ProofStep::Assume(equality));
    }
    let not_goal = executor.ctx.terms.mk_not_raw(goal);
    proof.add_step(ProofStep::Assume(not_goal));
    let leaf = proof.add_step(explanation_lemma(vec![packed]));
    // A CONTRACTION consumer, so the FLAT arm declines too and the cap is the
    // only thing left.
    let mut current = proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: flat.clone(),
        premises: vec![leaf],
        args: Vec::new(),
    });
    let mut remaining = flat.clone();
    for (index, &equality) in equalities.iter().enumerate() {
        let _ = remaining.remove(0);
        current = proof.add_step(ProofStep::Resolution {
            clause: remaining.clone(),
            pivot: equality,
            clause1: current,
            clause2: ProofId(u32::try_from(index).expect("small")),
        });
    }
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: goal,
        clause1: current,
        clause2: ProofId(u32::try_from(width).expect("small")),
    });
    let before = format!("{:?}", proof.steps);
    assert_eq!(executor.derive_congruence_explanations(&mut proof), 0);
    assert_eq!(
        format!("{:?}", proof.steps),
        before,
        "a leaf over the cap must be left byte-identical"
    );
}

/// The property the RE-PACK arm's complement check rests on, pinned directly
/// because deleting the check fails no test: `mk_not` is the exact resolution
/// complement for a plain literal and for a negated one, and is NOT one for a
/// literal that is itself a conjunction or a disjunction.
#[test]
fn mk_not_is_a_resolution_complement_only_for_plain_literals() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("cmp_a", sort.clone());
    let b = executor.ctx.terms.mk_var("cmp_b", sort);
    let equality = executor.ctx.terms.mk_eq(a, b);
    let negated = executor.ctx.terms.mk_not_raw(equality);
    let complement = executor.ctx.terms.mk_not(equality);
    assert!(
        matches!(executor.ctx.terms.get(complement),
            ay_core::TermData::Not(inner) if *inner == equality),
        "a plain literal negates under one Not"
    );
    let cancelled = executor.ctx.terms.mk_not(negated);
    assert_eq!(cancelled, equality, "a negated literal cancels");
    for connective in ["and", "or"] {
        let compound = executor.ctx.terms.mk_app(
            Symbol::named(connective),
            vec![equality, negated],
            Sort::Bool,
        );
        let dual = executor.ctx.terms.mk_not(compound);
        assert!(
            !matches!(executor.ctx.terms.get(dual),
                ay_core::TermData::Not(inner) if *inner == compound),
            "mk_not pushes through `{connective}`, so it is not a complement"
        );
    }
}
