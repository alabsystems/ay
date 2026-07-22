// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the substitution bridge's `trans`-through-a-definition leg
//! (`proof_original_rebuild.rs`).
//!
//! These exercise the PLANNER directly, which is where the authority argument
//! lives: the planner may only build a derivation out of assertions the
//! problem authored, so a definition the problem does not contain must make
//! planning fail rather than produce a step. The end-to-end shape (a real
//! store-flat UNSAT self-certifying) is covered in `executor/proof/tests.rs`.

use super::*;

/// Build the store-flat fixture:
///
/// ```text
///   b1 = (store a1 i1 e1)      b2 = (store b1 i2 e2)
/// ```
///
/// and return `(b2, expanded)` where `expanded` is the fully substituted
/// `(store (store a1 i1 e1) i2 e2)` — exactly what
/// `substitute_store_flat_equalities` leaves in the assertion the proof
/// assumes — plus the two authored defining equalities.
struct StoreChain {
    b2: TermId,
    expanded: TermId,
    def_b1: TermId,
    def_b2: TermId,
}

fn store_chain(exec: &mut Executor) -> StoreChain {
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Element".to_string());
    let array = Sort::array(index.clone(), element.clone());
    let terms = &mut exec.ctx.terms;

    let a1 = terms.mk_var("a1", array.clone());
    let b1 = terms.mk_var("b1", array.clone());
    let b2 = terms.mk_var("b2", array.clone());
    let i1 = terms.mk_var("i1", index.clone());
    let i2 = terms.mk_var("i2", index);
    let e1 = terms.mk_var("e1", element.clone());
    let e2 = terms.mk_var("e2", element);

    let store_a1 = terms.mk_app(Symbol::named("store"), [a1, i1, e1], array.clone());
    let store_b1 = terms.mk_app(Symbol::named("store"), [b1, i2, e2], array.clone());
    let expanded = terms.mk_app(Symbol::named("store"), [store_a1, i2, e2], array);

    let def_b1 = terms.mk_app(Symbol::named("="), [b1, store_a1], Sort::Bool);
    let def_b2 = terms.mk_app(Symbol::named("="), [b2, store_b1], Sort::Bool);

    StoreChain {
        b2,
        expanded,
        def_b1,
        def_b2,
    }
}

/// POSITIVE: with BOTH authored defining equalities present, the planner walks
/// the chain — `trans` through `b2`'s definition, then congruence on the
/// store's array argument, then `trans` through `b1`'s definition — and every
/// premise it needs is one of the authored assertions.
#[test]
fn plan_eq_bridges_a_store_chain_through_authored_definitions() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    let originals = vec![chain.def_b1, chain.def_b2];

    let mut budget = EQ_PLAN_BUDGET;
    let plan = exec
        .plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget)
        .expect("the store chain must be derivable from its authored definitions");

    assert!(
        matches!(plan.kind, EqPlanKind::Trans { .. }),
        "the top of the chain must be a `trans` through b2's definition"
    );

    // Every premise the plan needs is an AUTHORED assertion — the whole point
    // of the #8821 gate.
    let mut assumed = Vec::new();
    plan.collect_assumed(&mut assumed);
    assert!(
        !assumed.is_empty(),
        "a chain bridge must rest on real premises, not on nothing"
    );
    for term in &assumed {
        assert!(
            originals.contains(term),
            "planner assumed a non-authored term {term:?}"
        );
    }
    assert!(
        assumed.contains(&chain.def_b1) && assumed.contains(&chain.def_b2),
        "both links of the chain must be used"
    );
}

/// NEGATIVE (the load-bearing one): drop `b1`'s defining equality from the
/// authored set. The chain is now unreachable, and the planner must FAIL
/// rather than invent the missing link — a fabricated `(= b1 (store a1 i1 e1))`
/// would be a free axiom laundered into an `assume`.
#[test]
fn plan_eq_refuses_to_fabricate_an_absent_defining_equality() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    // `b2`'s definition is authored; `b1`'s is NOT.
    let originals = vec![chain.def_b2];

    let mut budget = EQ_PLAN_BUDGET;
    let plan = exec.plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget);
    assert!(
        plan.is_none(),
        "with b1's defining equality absent the bridge must fail closed, \
         not manufacture the missing link"
    );
}

/// NEGATIVE: nothing at all is authored. Even the first link must not appear.
#[test]
fn plan_eq_refuses_a_chain_with_no_authored_definitions() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);

    let mut budget = EQ_PLAN_BUDGET;
    assert!(
        exec.plan_eq(chain.b2, chain.expanded, &[], 0, &mut budget)
            .is_none(),
        "an empty authored set can derive nothing"
    );
}

/// NEGATIVE: a leaf bridged from the WRONG authored assertion must be
/// rejected. Here the problem authors a decoy predicate over a DIFFERENT
/// variable (`c2`), whose arguments cannot be connected to the substituted
/// leaf's. `plan_substitution_bridge` must not latch onto the decoy just
/// because it shares the goal's head symbol and arity.
#[test]
fn plan_substitution_bridge_rejects_an_unconnected_authored_source() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Element".to_string());
    let array = Sort::array(index, element);

    // Decoy: `(not (= c2 d2))`, same head (`=`) and arity as the goal, but
    // over variables with no authored definitions at all.
    let (decoy, goal) = {
        let terms = &mut exec.ctx.terms;
        let c2 = terms.mk_var("c2", array.clone());
        let d2 = terms.mk_var("d2", array.clone());
        let other = terms.mk_var("other", array);
        let decoy_eq = terms.mk_app(Symbol::named("="), [c2, d2], Sort::Bool);
        let decoy = terms.mk_not_raw(decoy_eq);
        // The substituted leaf: `(not (= expanded other))`.
        let goal_eq = terms.mk_app(Symbol::named("="), [chain.expanded, other], Sort::Bool);
        let goal = terms.mk_not_raw(goal_eq);
        (decoy, goal)
    };

    // The decoy and both real definitions are authored; the leaf still cannot
    // be derived, because no authored equality connects `other`.
    let originals = vec![chain.def_b1, chain.def_b2, decoy];
    assert!(
        exec.plan_substitution_bridge(goal, &originals).is_none(),
        "the bridge must not source a leaf from an authored assertion whose \
         arguments it cannot actually connect"
    );
}

/// The planner's search is bounded: a budget of zero derives nothing, so a
/// pathological original set can never spin the export.
#[test]
fn plan_eq_respects_its_work_budget() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    let originals = vec![chain.def_b1, chain.def_b2];

    let mut budget = 0;
    assert!(
        exec.plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget)
            .is_none(),
        "an exhausted budget must fail closed"
    );

    // And the same query succeeds once the budget is restored, proving the
    // failure above was the budget and not the fixture.
    let mut budget = EQ_PLAN_BUDGET;
    assert!(exec
        .plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget)
        .is_some());
}

/// `reachable_step_mask` must agree with the #8821 gate's own cone walk: the
/// dead branch is excluded, the live one is not. This is what lets the bridge
/// stop vetoing a whole proof over a leaf that carries no authority claim.
#[test]
fn reachable_step_mask_matches_the_authority_gate_cone() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let dead = terms.mk_var("dead", Sort::Bool);

    let mut proof = Proof::new();
    let live_a = proof.add_assume(p, None); // 0: reachable
    let live_b = proof.add_assume(not_p, None); // 1: reachable
    let _dead_assume = proof.add_assume(dead, None); // 2: NOT reachable
    proof.add_resolution(Vec::new(), p, live_a, live_b); // 3: the empty clause

    let mask = Executor::reachable_step_mask(&proof);
    assert_eq!(mask, vec![true, true, false, true]);

    // The authority gate agrees: with only `p` and `(not p)` in problem scope,
    // the dead `dead` assume does NOT make the proof unauthorized.
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &[p, not_p]).is_ok(),
        "a dead assume is outside the cone the #8821 gate inspects"
    );
}
