// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failed speculative proof pairs cannot pollute the shared typed term store.

use super::*;

#[test]
fn mismatched_equality_plan_consumes_budget_without_minting_terms() {
    for (left, right) in [
        (
            Sort::Uninterpreted("L".into()),
            Sort::Uninterpreted("U".into()),
        ),
        (Sort::Int, Sort::Real),
        (Sort::bitvec(8), Sort::bitvec(16)),
    ] {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("a", left);
        let b = executor.ctx.terms.mk_var("b", right);
        let before = executor.ctx.terms.len();
        let mut budget = EQ_PLAN_BUDGET;
        assert!(executor.plan_eq(a, b, &[], 0, &mut budget).is_none());
        assert_eq!(budget, EQ_PLAN_BUDGET - 1);
        assert_eq!(executor.ctx.terms.len(), before);
    }
}

#[test]
fn bridge_skips_an_incompatible_carrier_and_strictly_proves_a_later_source() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let list = Sort::Uninterpreted("L".into());
    let item = Sort::Uninterpreted("U".into());
    let nil = terms.mk_var("nil", list.clone());
    let xs = terms.mk_var("xs", list);
    let u0 = terms.mk_var("u0", item.clone());
    let u1 = terms.mk_var("u1", item.clone());
    let u2 = terms.mk_var("u2", item);
    let decoy = terms.mk_app(Symbol::named("="), [nil, xs], Sort::Bool);
    let source = terms.mk_app(Symbol::named("="), [u0, u1], Sort::Bool);
    let pin = terms.mk_app(Symbol::named("="), [u1, u2], Sort::Bool);
    let goal = terms.mk_app(Symbol::named("="), [u0, u2], Sort::Bool);
    let not_goal = terms.mk_not_raw(goal);
    let before = terms.len();
    let originals = [decoy, source, pin];
    let plan = executor.plan_substitution_bridge(goal, &originals).unwrap();
    assert_eq!(plan.source, source);
    for index in before..executor.ctx.terms.len() {
        if let TermData::App(symbol, args) = executor.ctx.terms.get(TermId(index as u32)) {
            if symbol.name() == "=" {
                assert_eq!(
                    executor.ctx.terms.sort(args[0]),
                    executor.ctx.terms.sort(args[1])
                );
            }
        }
    }
    let mut proof = Proof::new();
    let mut assumptions = HashMap::default();
    for original in originals {
        assumptions.insert(original, proof.add_assume(original, None));
    }
    let unit = Executor::emit_substitution_bridge(
        &mut executor.ctx.terms,
        &mut proof,
        &plan,
        &assumptions,
    )
    .unwrap();
    let denial = proof.add_assume(not_goal, None);
    proof.add_resolution(Vec::new(), goal, unit, denial);
    assert!(ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .unwrap()
        .is_complete());
    let authored = [decoy, source, pin, not_goal];
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
    assert!(executor
        .plan_substitution_bridge(goal, &[decoy, source])
        .is_none());
}
