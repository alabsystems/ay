// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The planning-run memo returns what the recomputation returns, follows the
//! authored set, the store snapshot and the checker-visible metadata, and
//! evaluates each term (and scans for each term's candidates) once.

use super::*;

/// The candidate list exactly as it was computed before the memo: scan the
/// authored set, keep the sides of `x`'s sort other than `x`, and evaluate
/// them in order until `MAX_CANDIDATES` are found.
fn recomputed_candidates(exec: &mut Executor, x: TermId, original_terms: &[TermId]) -> Vec<TermId> {
    let sort = exec.ctx.terms.sort(x).clone();
    let mut sides: Vec<TermId> = Vec::new();
    for &original in original_terms {
        let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(original) else {
            continue;
        };
        if name != "=" || args.len() != 2 {
            continue;
        }
        for side in [args[0], args[1]] {
            if side != x && *exec.ctx.terms.sort(side) == sort && !sides.contains(&side) {
                sides.push(side);
            }
        }
    }
    let mut candidates = Vec::new();
    for side in sides {
        if candidates.len() >= 64 {
            break;
        }
        if exec.term_is_ground_evaluable_uncached(side) {
            candidates.push(side);
        }
    }
    candidates
}

fn int(exec: &mut Executor, value: i64) -> TermId {
    exec.ctx.terms.mk_int(BigInt::from(value))
}

fn eq(exec: &mut Executor, lhs: TermId, rhs: TermId) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool)
}

#[test]
fn memoized_candidates_follow_the_authored_set() {
    let mut exec = Executor::new();
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let w = exec.ctx.terms.mk_var("w", Sort::Int);
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let (zero, one, two) = (int(&mut exec, 0), int(&mut exec, 1), int(&mut exec, 2));
    let one_plus_one = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [one, one], Sort::Int);
    let v_plus_one = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [v, one], Sort::Int);
    let truth = exec.ctx.terms.mk_bool(true);
    let pin_zero = eq(&mut exec, v, zero);
    let pin_one = eq(&mut exec, one, v);
    let pin_sum = eq(&mut exec, w, one_plus_one);
    let pin_step = eq(&mut exec, w, v_plus_one);
    let pin_bool = eq(&mut exec, p, truth);
    let pin_two = eq(&mut exec, two, w);
    let sets: [&[TermId]; 6] = [
        &[pin_zero, pin_one, pin_sum, pin_step, pin_bool, pin_zero],
        &[pin_two],
        &[],
        &[pin_step, pin_one, pin_two],
        &[pin_zero, pin_one, pin_sum, pin_step, pin_bool, pin_zero],
        &[pin_bool],
    ];
    // Interleaved with the memo's own runs, so every set switch and every
    // warm entry is exercised: the first ask per set computes the list, the
    // second answers from the memo. `zero` and `one` also ask with `x` itself
    // an authored side, `p` with a Boolean sort.
    for set in sets {
        for round in ["cold", "warm"] {
            for x in [v, w, zero, one, p] {
                let memoized = exec.authored_ground_candidates(x, set);
                assert_eq!(
                    memoized,
                    recomputed_candidates(&mut exec, x, set),
                    "{round} memoized candidates for {x:?} over {set:?} must equal the recomputation"
                );
            }
        }
    }
    assert_eq!(exec.authored_ground_candidates(v, &[pin_two]), vec![two]);
    assert!(exec.authored_ground_candidates(v, &[]).is_empty());
}

#[test]
fn a_store_rollback_retires_memoized_evaluability() {
    let mut exec = Executor::new();
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let (one, two) = (int(&mut exec, 1), int(&mut exec, 2));
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let ground = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [one, two], Sort::Int);
    assert!(exec.term_is_ground_evaluable(ground));
    exec.ctx.terms.rollback_to(checkpoint);
    // The rollback freed `ground`'s id, and the next term takes it over.
    let symbolic = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [v, two], Sort::Int);
    assert_eq!(symbolic, ground, "the test needs the id to be re-minted");
    assert!(
        !exec.term_is_ground_evaluable(symbolic),
        "an entry recorded before the rollback must not answer for the re-minted id"
    );
}

/// The strict evaluator reads the `to_real` shadow latch, which flips
/// WITHOUT retiring the snapshot stamp (#checker-visible-metadata-generation):
/// both the evaluability entry and the candidate list built on it must go.
#[test]
fn a_shadowed_to_real_retires_memoized_evaluability() {
    let mut exec = Executor::new();
    let r = exec.ctx.terms.mk_var("r", Sort::Real);
    let one = int(&mut exec, 1);
    let lifted = exec
        .ctx
        .terms
        .mk_app(Symbol::named("to_real"), [one], Sort::Real);
    let pin = eq(&mut exec, r, lifted);
    assert!(exec.term_is_ground_evaluable_uncached(lifted));
    assert!(exec.term_is_ground_evaluable(lifted));
    assert_eq!(exec.authored_ground_candidates(r, &[pin]), vec![lifted]);
    exec.ctx.terms.mark_to_real_shadowed();
    assert!(
        !exec.term_is_ground_evaluable_uncached(lifted),
        "the recomputation must refuse a shadowed to_real"
    );
    assert!(
        !exec.term_is_ground_evaluable(lifted),
        "an entry recorded before the latch flip must not answer after it"
    );
    assert!(
        exec.authored_ground_candidates(r, &[pin]).is_empty(),
        "a candidate list recorded before the latch flip must not answer after it"
    );
}

/// The shape of `group_lia::lia_incremental_bmc_stress`'s `mod` script: a
/// counter pinned at 0 and stepped by `+ 1`, and a substituted leaf the
/// planner can never close, so the bridge spends its whole node budget
/// asking for the same authored candidates at node after node.
#[test]
fn a_spent_bridge_budget_evaluates_each_term_once() {
    const LINKS: i64 = 64;
    let mut exec = Executor::new();
    let (zero, one, three) = (int(&mut exec, 0), int(&mut exec, 1), int(&mut exec, 3));
    let mut counter = exec.ctx.terms.mk_var("x_0", Sort::Int);
    let mut originals = vec![eq(&mut exec, counter, zero)];
    for link in 1..=LINKS {
        let next = exec.ctx.terms.mk_var(format!("x_{link}"), Sort::Int);
        let step = exec
            .ctx
            .terms
            .mk_app(Symbol::named("+"), [counter, one], Sort::Int);
        originals.push(eq(&mut exec, next, step));
        counter = next;
    }
    let q = exec.ctx.terms.mk_var("q", Sort::Int);
    let multiple = exec
        .ctx
        .terms
        .mk_app(Symbol::named("*"), [q, three], Sort::Int);
    originals.push(eq(&mut exec, counter, multiple));
    let substituted = int(&mut exec, LINKS);
    let goal = eq(&mut exec, substituted, multiple);

    let mut budget = EQ_PLAN_BUDGET;
    assert!(exec
        .plan_substitution_bridge_with_budget(goal, &originals, &mut budget)
        .is_none());
    assert_eq!(
        budget, 0,
        "the bridge must spend its whole budget, as on the BMC script"
    );
    // Recomputed per node this was millions of evaluations (5.1 million per
    // bridge on the BMC script); memoized, each term is evaluated, and has
    // its candidate list computed, at most once. Both counters survive state
    // resets, so a memo that kept discarding its entries would fail here too.
    let terms = exec.ctx.terms.len();
    let evaluations = exec.ground_candidate_memo.evaluations;
    assert!(
        evaluations <= terms,
        "{evaluations} strict ground evaluations for a store of {terms} terms"
    );
    let scans = exec.ground_candidate_memo.scans;
    assert!(
        scans <= terms,
        "{scans} candidate scans for a store of {terms} terms"
    );
}
