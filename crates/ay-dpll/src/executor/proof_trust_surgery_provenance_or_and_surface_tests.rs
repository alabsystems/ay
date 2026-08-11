// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rendered connective-role tests for conjunctive provenance-OR repair.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, Symbol, TermStore};

use crate::executor::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;

#[test]
fn rendered_connective_roles_allow_exact_permutations_and_reject_shape_drift() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("and_role_a", Sort::Bool);
    let b = terms.mk_var("and_role_b", Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [a, b], Sort::Bool);

    let mut exact = ProvenanceSurfaceAudit::default();
    assert!(exact.require_spelling(&mut terms, root, "(and and_role_a and_role_b)"));
    assert!(exact.protect_and_projection_role(&mut terms, root, 0, a));
    let mut effective = HashMap::default();
    effective.insert(root, "(and and_role_a and_role_b)".to_string());
    assert!(exact.validate_effective(&terms, &effective));

    let mut reordered = ProvenanceSurfaceAudit::default();
    assert!(reordered.require_spelling(&mut terms, root, "(and and_role_b and_role_a)"));
    assert!(reordered.protect_and_projection_role(&mut terms, root, 0, a));
    let mut reordered_effective = HashMap::default();
    reordered_effective.insert(root, "(and and_role_b and_role_a)".to_string());
    assert!(reordered.validate_effective(&terms, &reordered_effective));

    for wrong in [
        "(or and_role_a and_role_b)",
        "(andish and_role_a and_role_b)",
        "(and and_role_a (and_role_b))",
        "(and and_role_a and_role_a)",
    ] {
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(audit.require_spelling(&mut terms, root, wrong));
        assert!(audit.protect_and_projection_role(&mut terms, root, 0, a));
        let mut active = HashMap::default();
        active.insert(root, wrong.to_string());
        assert!(!audit.validate_effective(&terms, &active));
    }

    let int_child = terms.mk_var("and_role_int", Sort::Int);
    let malformed = terms.mk_app(Symbol::named("and"), [a, int_child], Sort::Bool);
    let mut wrong_sort = ProvenanceSurfaceAudit::default();
    assert!(!wrong_sort.protect_and_projection_role(&mut terms, malformed, 0, a));

    let mut wrong_index = ProvenanceSurfaceAudit::default();
    assert!(!wrong_index.protect_and_projection_role(&mut terms, root, 1, a));

    let or_root = terms.mk_app(Symbol::named("or"), [a, b], Sort::Bool);
    let mut permuted_or = ProvenanceSurfaceAudit::default();
    assert!(permuted_or.require_spelling(&mut terms, or_root, "(or and_role_b and_role_a)"));
    assert!(permuted_or.protect_or_decomposition_permutation_role(&mut terms, or_root, &[a, b]));
    let mut reordered_or = HashMap::default();
    reordered_or.insert(or_root, "(or and_role_b and_role_a)".to_string());
    assert!(permuted_or.validate_effective(&terms, &reordered_or));

    for wrong in [
        "(=> and_role_a and_role_b)",
        "(or and_role_a and_role_a)",
        "(or and_role_a (or and_role_b and_role_a))",
    ] {
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(audit.require_spelling(&mut terms, or_root, wrong));
        assert!(audit.protect_or_decomposition_permutation_role(&mut terms, or_root, &[a, b]));
        let mut active = HashMap::default();
        active.insert(or_root, wrong.to_string());
        assert!(!audit.validate_effective(&terms, &active));
    }
}

#[test]
fn generated_and_projection_keeps_unique_selected_operand_contract() {
    let mut terms = TermStore::new();
    let duplicate = terms.mk_var("generated_and_duplicate", Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [duplicate, duplicate], Sort::Bool);
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(!audit.protect_and_projection_role(&mut terms, root, 0, duplicate));
}

#[test]
fn generated_and_introduction_preserves_full_duplicate_multiset() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("and_intro_a", Sort::Bool);
    let b = terms.mk_var("and_intro_b", Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [a, a, b], Sort::Bool);

    let mut exact = ProvenanceSurfaceAudit::default();
    let spelling = "(and and_intro_b and_intro_a and_intro_a)";
    assert!(exact.require_spelling(&mut terms, root, spelling));
    assert!(exact.protect_and_introduction_role(&mut terms, root));
    let mut effective = HashMap::default();
    effective.insert(root, spelling.to_string());
    assert!(exact.validate_effective(&terms, &effective));

    for wrong in [
        "(and and_intro_b and_intro_a)",
        "(and and_intro_b and_intro_b and_intro_a)",
        "(or and_intro_b and_intro_a and_intro_a)",
    ] {
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(audit.require_spelling(&mut terms, root, wrong));
        assert!(audit.protect_and_introduction_role(&mut terms, root));
        let mut active = HashMap::default();
        active.insert(root, wrong.to_string());
        assert!(!audit.validate_effective(&terms, &active));
    }
}

#[test]
fn repeated_generated_connective_uses_share_the_render_budget() {
    let mut terms = TermStore::new();
    let a = terms.mk_var(format!("render_budget_a_{}", "a".repeat(2_048)), Sort::Bool);
    let b = terms.mk_var(format!("render_budget_b_{}", "b".repeat(2_048)), Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [a, b], Sort::Bool);
    let spelling = ay_proof::format_term_alethe(&terms, root);
    let mut effective = HashMap::default();
    effective.insert(root, spelling.clone());

    let mut within = ProvenanceSurfaceAudit::default();
    assert!(within.require_spelling(&mut terms, root, &spelling));
    for _ in 0..64 {
        assert!(within.protect_and_introduction_role(&mut terms, root));
    }
    assert!(within.validate_effective(&terms, &effective));

    let mut exhausted = ProvenanceSurfaceAudit::default();
    assert!(exhausted.require_spelling(&mut terms, root, &spelling));
    for _ in 0..96 {
        assert!(exhausted.protect_and_introduction_role(&mut terms, root));
    }
    assert!(!exhausted.validate_effective(&terms, &effective));
}
