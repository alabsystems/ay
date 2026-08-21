// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{
    AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TheoryLemmaKind,
};

use super::super::EufLemmaPlan;
use crate::executor::Executor;

struct PackedFixture {
    executor: Executor,
    proof: Proof,
    plans: Vec<Option<EufLemmaPlan>>,
    typed: Vec<bool>,
    a: TermId,
    ab: TermId,
    not_ab: TermId,
}

fn swapped_equality(executor: &Executor, equality: TermId) -> String {
    let TermData::App(Symbol::Named(operator), sides) = executor.ctx.terms.get(equality) else {
        panic!("fixture equality lost its application shape")
    };
    assert_eq!(operator, "=");
    assert_eq!(sides.len(), 2);
    format!(
        "(= {} {})",
        ay_proof::format_term_alethe(&executor.ctx.terms, sides[1]),
        ay_proof::format_term_alethe(&executor.ctx.terms, sides[0]),
    )
}

fn packed_transitive_fixture() -> PackedFixture {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("packed_surface_a", Sort::Int);
    let b = executor.ctx.terms.mk_var("packed_surface_b", Sort::Int);
    let c = executor.ctx.terms.mk_var("packed_surface_c", Sort::Int);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let bc = executor.ctx.terms.mk_eq(b, c);
    let ac = executor.ctx.terms.mk_eq(a, c);
    let not_ab = executor.ctx.terms.mk_not_raw(ab);
    let not_bc = executor.ctx.terms.mk_not_raw(bc);
    let disjuncts = vec![not_ab, not_bc, ac];
    let root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), disjuncts.clone(), Sort::Bool);
    let plan = executor
        .plan_euf_lemma(&[root])
        .expect("packed transitivity fixture must plan");
    let mut proof = Proof::new();
    let packed =
        proof.add_theory_lemma_with_kind("EUF", vec![root], TheoryLemmaKind::EufTransitive);
    proof.add_rule_step(AletheRule::Or, disjuncts, vec![packed], Vec::new());
    PackedFixture {
        executor,
        proof,
        plans: vec![Some(plan), None],
        typed: vec![true, false],
        a,
        ab,
        not_ab,
    }
}

fn exact_swap_map(fixture: &PackedFixture) -> HashMap<TermId, String> {
    let swapped = swapped_equality(&fixture.executor, fixture.ab);
    let mut active = HashMap::default();
    active.insert(fixture.ab, swapped.clone());
    active.insert(fixture.not_ab, format!("(not {swapped})"));
    active
}

#[test]
fn packed_transitive_surface_accepts_only_exact_swap_and_negation_composition() {
    let mut fixture = packed_transitive_fixture();
    fixture.executor.last_proof_term_overrides = Some(exact_swap_map(&fixture));
    assert!(fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));

    let mut wrong_equality = exact_swap_map(&fixture);
    wrong_equality.insert(
        fixture.ab,
        "(= packed_surface_a packed_surface_a)".to_string(),
    );
    fixture.executor.last_proof_term_overrides = Some(wrong_equality);
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));

    let mut wrong_negation = exact_swap_map(&fixture);
    wrong_negation.insert(
        fixture.not_ab,
        "(not (= packed_surface_a packed_surface_a))".to_string(),
    );
    fixture.executor.last_proof_term_overrides = Some(wrong_negation);
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));

    let p = fixture
        .executor
        .ctx
        .terms
        .mk_var("packed_surface_p", Sort::Bool);
    let not_p = fixture.executor.ctx.terms.mk_not_raw(p);
    let mut non_equality = exact_swap_map(&fixture);
    non_equality.insert(not_p, "(not packed_surface_q)".to_string());
    fixture.executor.last_proof_term_overrides = Some(non_equality);
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));

    let double_not = fixture.executor.ctx.terms.mk_not_raw(fixture.not_ab);
    let mut nested = exact_swap_map(&fixture);
    let swapped = swapped_equality(&fixture.executor, fixture.ab);
    nested.insert(double_not, format!("(not (not {swapped}))"));
    fixture.executor.last_proof_term_overrides = Some(nested);
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));
}

#[test]
fn packed_transitive_surface_rejects_opaque_and_copied_positional_uses() {
    let mut fixture = packed_transitive_fixture();
    let mut opaque = exact_swap_map(&fixture);
    opaque.insert(fixture.a, "packed_surface_alias".to_string());
    fixture.executor.last_proof_term_overrides = Some(opaque);
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));

    fixture.executor.last_proof_term_overrides = Some(exact_swap_map(&fixture));
    fixture.proof.add_rule_step(
        AletheRule::EqReflexive,
        vec![fixture.ab],
        Vec::new(),
        Vec::new(),
    );
    fixture.plans.push(None);
    fixture.typed.push(false);
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));
}

#[test]
fn packed_transitive_surface_rejects_malformed_or_consumer() {
    let mut fixture = packed_transitive_fixture();
    fixture.executor.last_proof_term_overrides = Some(exact_swap_map(&fixture));
    let ProofStep::Step { clause, .. } = &mut fixture.proof.steps[1] else {
        panic!("fixture OR consumer lost its step shape")
    };
    clause[0] = clause[1];
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));

    let mut fixture = packed_transitive_fixture();
    fixture.executor.last_proof_term_overrides = Some(exact_swap_map(&fixture));
    let ProofStep::Step { premises, .. } = &mut fixture.proof.steps[1] else {
        panic!("fixture OR consumer lost its step shape")
    };
    *premises = vec![ProofId(1)];
    assert!(!fixture
        .executor
        .typed_packed_euf_transitive_surface_is_safe(
            &fixture.proof,
            &fixture.plans,
            &fixture.typed,
        ));
}
