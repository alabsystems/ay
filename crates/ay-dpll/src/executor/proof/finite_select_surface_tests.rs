// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{ArraySort, Proof, ProofStep, Sort, Symbol, TheoryLemmaKind};

use super::Executor;

fn finite_select_fixture() -> (Executor, Proof, ay_core::TermId, ay_core::TermId) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let array_sort = Sort::Array(Box::new(ArraySort::new(Sort::Bool, Sort::Int)));
    let array = terms.mk_var("finite_select_array", array_sort);
    let condition = terms.mk_var("finite_select_condition", Sort::Bool);
    let true_term = terms.true_term();
    let false_term = terms.false_term();
    let selected_condition = terms.mk_app(Symbol::named("select"), [array, condition], Sort::Int);
    let selected_true = terms.mk_app(Symbol::named("select"), [array, true_term], Sort::Int);
    let selected_false = terms.mk_app(Symbol::named("select"), [array, false_term], Sort::Int);
    let then_equality = terms.mk_eq(selected_true, selected_condition);
    let else_equality = terms.mk_eq(selected_false, selected_condition);
    let goal = terms.mk_ite_raw(condition, then_equality, else_equality);
    let not_goal = terms.mk_not_raw(goal);

    let mut proof = Proof::new();
    let finite = proof.add_theory_lemma_with_kind(
        "Array",
        vec![goal],
        TheoryLemmaKind::ArrayFiniteSelectExpansion,
    );
    let assumption = proof.add_assume(not_goal, None);
    proof.add_resolution(Vec::new(), goal, finite, assumption);
    executor.ctx.assertions.push(not_goal);
    (executor, proof, goal, condition)
}

#[test]
fn bool_finite_select_surface_lowers_to_strict_primitives() {
    let (mut executor, mut proof, _, _) = finite_select_fixture();
    executor.promote_bool_finite_select_expansion_surface(&mut proof);
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayFiniteSelectExpansion,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: ay_core::AletheRule::EqCongruent,
            ..
        }
    )));
    ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("lowered Bool finite-select proof must check strictly");
}

#[test]
fn bool_finite_select_surface_rejects_override_in_goal_cone() {
    let (mut executor, mut proof, _, condition) = finite_select_fixture();
    let before = format!("{:?}", proof.steps);
    let mut active = HashMap::default();
    active.insert(condition, "finite_select_surface_alias".to_string());
    executor.last_proof_term_overrides = Some(active);
    executor.promote_bool_finite_select_expansion_surface(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayFiniteSelectExpansion,
            ..
        }
    )));
}

#[test]
fn bool_finite_select_surface_rejects_oversized_override_map() {
    let (mut executor, mut proof, _, _) = finite_select_fixture();
    let before = format!("{:?}", proof.steps);
    let mut active = HashMap::default();
    for index in 0..8_193 {
        let term = executor
            .ctx
            .terms
            .mk_var(format!("finite_select_oversized_{index}"), Sort::Bool);
        active.insert(term, format!("finite_select_surface_{index}"));
    }
    executor.last_proof_term_overrides = Some(active);
    executor.promote_bool_finite_select_expansion_surface(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}
