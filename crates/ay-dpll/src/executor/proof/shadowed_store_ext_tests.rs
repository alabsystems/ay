// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordering regression for shadowed-store and array-extensionality promotion.

use super::*;
use crate::executor::theories::{array_extensionality_witness, ArrayExtWitnessBinding};
use ay_frontend::command::Term as FrontendTerm;

struct ExtensionalityBranch {
    axiom: TermId,
    not_array_equality: TermId,
    value_equality: TermId,
}

struct ExtensionalityTerms {
    branch: ExtensionalityBranch,
    folded_equality: TermId,
    array_equality: TermId,
    not_folded_equality: TermId,
}

fn make_extensionality_terms(exec: &mut Executor) -> ExtensionalityTerms {
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let base = exec
        .ctx
        .terms
        .mk_var("ordered_ext_base", array_sort.clone());
    let index = exec.ctx.terms.mk_var("ordered_ext_index", Sort::Int);
    let left_value = exec.ctx.terms.mk_var("ordered_ext_left", Sort::Int);
    let right_value = exec.ctx.terms.mk_var("ordered_ext_right", Sort::Int);
    let left = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        [base, index, left_value],
        array_sort.clone(),
    );
    let right = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        [base, index, right_value],
        array_sort,
    );
    let witness = array_extensionality_witness(
        &mut exec.ctx.terms,
        &mut exec.array_ext_witness_cache,
        left,
        right,
    )
    .expect("fixture witness");

    let condition = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [witness, index], Sort::Bool);
    let base_read = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [base, witness], Sort::Int);
    let folded_left = exec.ctx.terms.mk_ite_raw(condition, left_value, base_read);
    let folded_right = exec.ctx.terms.mk_ite_raw(condition, right_value, base_read);
    let folded_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [folded_left, folded_right], Sort::Bool);
    let array_equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let not_folded_equality = exec.ctx.terms.mk_not_raw(folded_equality);
    let axiom = exec.ctx.terms.mk_app(
        Symbol::named("or"),
        [array_equality, not_folded_equality],
        Sort::Bool,
    );
    assert!(exec.array_ext_witness_cache.record_generated_clause(
        &exec.ctx.terms,
        axiom,
        vec![ArrayExtWitnessBinding {
            witness,
            array_a: left,
            array_b: right,
        }],
    ));

    let value_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [left_value, right_value], Sort::Bool);
    let not_array_equality = exec.ctx.terms.mk_not_raw(array_equality);
    ExtensionalityTerms {
        branch: ExtensionalityBranch {
            axiom,
            not_array_equality,
            value_equality,
        },
        folded_equality,
        array_equality,
        not_folded_equality,
    }
}

fn add_extensionality_branch(exec: &mut Executor, proof: &mut Proof) -> ExtensionalityBranch {
    let terms = make_extensionality_terms(exec);
    let extensionality = proof.add_theory_lemma("array", vec![terms.branch.axiom]);
    let value_assume = proof.add_assume(terms.branch.value_equality, None);
    let folded_unit = proof.add_rule_step(
        AletheRule::Cong,
        vec![terms.folded_equality],
        vec![value_assume],
        Vec::new(),
    );
    let unpacked = proof.add_rule_step(
        AletheRule::Or,
        vec![terms.array_equality, terms.not_folded_equality],
        vec![extensionality],
        Vec::new(),
    );
    let array_unit = proof.add_resolution(
        vec![terms.array_equality],
        terms.folded_equality,
        unpacked,
        folded_unit,
    );
    let disequality = proof.add_assume(terms.branch.not_array_equality, None);
    proof.add_resolution(Vec::new(), terms.array_equality, array_unit, disequality);
    exec.ctx.add_assertion_with_parsed(
        terms.branch.value_equality,
        FrontendTerm::Symbol("problem".to_string()),
    );
    exec.ctx.add_assertion_with_parsed(
        terms.branch.not_array_equality,
        FrontendTerm::Symbol("problem".to_string()),
    );
    terms.branch
}

fn add_shadowed_store_branch(exec: &mut Executor, proof: &mut Proof) -> (TermId, TermId) {
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let base = exec.ctx.terms.mk_var("ordered_shadow_base", array_sort);
    let inner_index = exec.ctx.terms.mk_var("ordered_shadow_i", Sort::Int);
    let outer_index = exec.ctx.terms.mk_var("ordered_shadow_j", Sort::Int);
    let left_value = exec.ctx.terms.mk_var("ordered_shadow_left", Sort::Int);
    let right_value = exec.ctx.terms.mk_var("ordered_shadow_right", Sort::Int);
    let outer_value = exec.ctx.terms.mk_var("ordered_shadow_outer", Sort::Int);
    let left_inner = exec.ctx.terms.mk_store(base, inner_index, left_value);
    let right_inner = exec.ctx.terms.mk_store(base, inner_index, right_value);
    let left = exec
        .ctx
        .terms
        .mk_store(left_inner, outer_index, outer_value);
    let right = exec
        .ctx
        .terms
        .mk_store(right_inner, outer_index, outer_value);
    let array_equality = exec.ctx.terms.mk_eq(left, right);
    let not_array_equality = exec.ctx.terms.mk_not(array_equality);
    let index_equality = exec.ctx.terms.mk_eq(inner_index, outer_index);
    let value_equality = exec.ctx.terms.mk_eq(left_value, right_value);
    let compact = exec
        .ctx
        .terms
        .mk_or(vec![not_array_equality, index_equality, value_equality]);
    let not_compact = exec.ctx.terms.mk_not_raw(compact);
    let lemma = proof.add_theory_lemma("array", vec![compact]);
    let assumption = proof.add_assume(not_compact, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![lemma, assumption],
        Vec::new(),
    );
    exec.ctx
        .add_assertion_with_parsed(not_compact, FrontendTerm::Symbol("problem".to_string()));
    (compact, not_compact)
}

#[test]
fn shadowed_store_gate_validates_with_deferred_extensionality_on_a_clone() {
    let mut exec = Executor::new();
    let mut proof = Proof::new();
    let extensionality = add_extensionality_branch(&mut exec, &mut proof);
    let (compact, _) = add_shadowed_store_branch(&mut exec, &mut proof);
    exec.ctx.assertions.push(extensionality.axiom);

    exec.split_shadowed_store_equality_lemmas(&mut proof);

    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma { clause, kind, .. }
            if clause == &[extensionality.axiom] && kind.is_trust()
    )));
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::TheoryLemma { clause, kind, .. }
            if clause == &[compact] && kind.is_trust()
    )));
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());

    exec.promote_array_extensionality_axioms(&mut proof);
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("final extensionality promotion completes both load-bearing branches");
    assert!(exec
        .ctx
        .assertions
        .contains(&extensionality.not_array_equality));
    assert!(exec.ctx.assertions.contains(&extensionality.value_equality));
}
