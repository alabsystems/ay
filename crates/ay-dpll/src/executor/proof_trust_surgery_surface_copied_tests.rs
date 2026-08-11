// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Proof, Sort, TermStore};

use super::{copied_structural_roles_are_static, ProvenanceSurfaceAudit};

#[test]
fn copied_ite_rule_rejects_negated_condition_surface_override() {
    let mut terms = TermStore::new();
    let condition = terms.mk_var("copied_ite_condition", Sort::Bool);
    let then_term = terms.mk_var("copied_ite_then", Sort::Int);
    let else_term = terms.mk_var("copied_ite_else", Sort::Int);
    let ite = terms.mk_ite(condition, then_term, else_term);
    let mut proof = Proof::new();
    let premise = proof.add_assume(ite, None);
    proof.add_rule_step(
        AletheRule::Ite1,
        vec![condition, else_term],
        vec![premise],
        Vec::new(),
    );
    let mut effective = HashMap::default();
    effective.insert(
        ite,
        "(ite (not copied_ite_condition) copied_ite_else copied_ite_then)".to_string(),
    );
    assert!(!copied_structural_roles_are_static(
        &proof,
        &[true, true],
        &HashSet::default(),
        &terms,
        &effective,
    ));
}

#[test]
fn copied_or_accepts_flat_reordering_but_rejects_nested_arity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("copied_or_a", Sort::Bool);
    let b = terms.mk_var("copied_or_b", Sort::Bool);
    let c = terms.mk_var("copied_or_c", Sort::Bool);
    let root = terms.mk_or(vec![a, b, c]);
    let mut proof = Proof::new();
    let premise = proof.add_assume(root, None);
    proof.add_rule_step(AletheRule::Or, vec![a, b, c], vec![premise], Vec::new());

    let check = |surface: &str, terms: &mut TermStore| {
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(audit.require_spelling(terms, root, surface));
        assert!(audit.protect_copied_resolution_and_farkas_roles(
            &proof,
            &[true, true],
            &HashSet::default(),
            terms,
        ));
        let mut effective = HashMap::default();
        effective.insert(root, surface.to_string());
        audit.validate_effective(terms, &effective)
    };

    assert!(check(
        "(or copied_or_c copied_or_a copied_or_b)",
        &mut terms
    ));
    assert!(!check(
        "(or copied_or_a (or copied_or_b copied_or_c))",
        &mut terms
    ));
}

#[test]
fn copied_premise_width_is_rejected_before_clause_traversal() {
    let mut terms = TermStore::new();
    let atom = terms.mk_var("copied_wide_premise", Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_assume(atom, None);
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![atom],
        vec![premise; super::MAX_ALIAS_SCAN_TERMS + 1],
        Vec::new(),
    );
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(!audit.protect_copied_resolution_and_farkas_roles(
        &proof,
        &[true, true],
        &HashSet::default(),
        &mut terms,
    ));
}

#[test]
fn repeated_wide_premise_clauses_share_one_scan_budget() {
    let mut terms = TermStore::new();
    let atom = terms.mk_var("copied_repeated_wide_premise", Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_rule_step(
        AletheRule::Weakening,
        vec![atom; 1_000],
        Vec::new(),
        Vec::new(),
    );
    proof.add_rule_step(
        AletheRule::Resolution,
        Vec::new(),
        vec![premise; 101],
        Vec::new(),
    );
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(!audit.protect_copied_resolution_and_farkas_roles(
        &proof,
        &[true, true],
        &HashSet::default(),
        &mut terms,
    ));
}
