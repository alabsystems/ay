// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{FarkasAnnotation, Sort, Symbol, TermId, TermStore};
use ay_frontend::command::{
    Command, Constant as FrontendConstant, Sort as FrontendSort, Term as FrontendTerm,
};

use super::{retained_surface_plan_mix_is_safe, ProvenanceSurfaceAudit, MAX_AUDITED_REQUIREMENTS};
use crate::executor::Executor;

fn declare_bool(executor: &mut Executor, name: &str) -> TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(
            name.to_string(),
            FrontendSort::Simple("Bool".to_string()),
        ))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

#[test]
fn retained_surface_policy_rejects_only_retained_quant_mixes() {
    assert!(retained_surface_plan_mix_is_safe(false, false, false));
    assert!(retained_surface_plan_mix_is_safe(true, false, false));
    assert!(retained_surface_plan_mix_is_safe(false, true, false));
    assert!(!retained_surface_plan_mix_is_safe(true, true, false));
    assert!(retained_surface_plan_mix_is_safe(false, false, true));
    assert!(!retained_surface_plan_mix_is_safe(true, false, true));
    assert!(!retained_surface_plan_mix_is_safe(false, true, true));
}

#[test]
fn retained_surface_base_map_is_bounded_before_clone() {
    let audit = ProvenanceSurfaceAudit::default();
    let mut active = HashMap::default();
    for index in 0..MAX_AUDITED_REQUIREMENTS {
        active.insert(
            TermId(u32::try_from(index).expect("test bound fits u32")),
            String::new(),
        );
    }
    assert!(audit.active_map_is_bounded(&active));
    active.insert(
        TermId(u32::try_from(MAX_AUDITED_REQUIREMENTS).expect("test bound fits u32")),
        String::new(),
    );
    assert!(!audit.active_map_is_bounded(&active));
}

#[test]
fn deep_compatibility_requires_an_exact_value_only_when_active() {
    let mut terms = TermStore::new();
    let term = terms.mk_var("deep_compatibility_term", Sort::Int);
    let expected = "(+ deep_compatibility_term 0)";

    let mut missing = ProvenanceSurfaceAudit::default();
    assert!(missing.require_compatibility_spelling(&mut terms, term, expected));
    missing.protect_operand(&mut terms, term);
    let mut active = HashMap::default();
    assert!(missing.merge_into(&mut active));
    assert!(active.is_empty());
    assert!(missing
        .materialize_protected_requirements()
        .is_some_and(|requirements| requirements.is_empty()));
    assert!(missing.validate_effective(&terms, &active));

    let mut matching = ProvenanceSurfaceAudit::default();
    assert!(matching.require_compatibility_spelling(&mut terms, term, expected));
    matching.protect_operand(&mut terms, term);
    let mut active = HashMap::default();
    active.insert(term, expected.to_string());
    assert!(matching.merge_into(&mut active));
    assert!(matching.validate_effective(&terms, &active));

    let mut mismatching = ProvenanceSurfaceAudit::default();
    assert!(mismatching.require_compatibility_spelling(&mut terms, term, expected));
    mismatching.protect_operand(&mut terms, term);
    let mut active = HashMap::default();
    active.insert(term, "(+ deep_compatibility_term 1)".to_string());
    assert!(!mismatching.merge_into(&mut active));
}

#[test]
fn mandatory_requirement_promotes_deep_compatibility_in_either_order() {
    let mut terms = TermStore::new();
    let term = terms.mk_var("promoted_compatibility_term", Sort::Int);
    let expected = "(+ promoted_compatibility_term 0)";

    for compatibility_first in [true, false] {
        let mut audit = ProvenanceSurfaceAudit::default();
        if compatibility_first {
            assert!(audit.require_compatibility_spelling(&mut terms, term, expected));
            assert!(audit.require_spelling(&mut terms, term, expected));
        } else {
            assert!(audit.require_spelling(&mut terms, term, expected));
            assert!(audit.require_compatibility_spelling(&mut terms, term, expected));
        }
        audit.protect_operand(&mut terms, term);
        assert!(!audit.merge_into(&mut HashMap::default()));
        assert!(audit
            .materialize_protected_requirements()
            .is_some_and(|requirements| requirements.get(&term) == Some(&expected.to_string())));
    }
}

#[test]
fn immediate_noncanonical_ite_child_requirement_stays_mandatory() {
    let mut executor = Executor::new();
    for name in [
        "compat_ite_a",
        "compat_ite_b",
        "compat_ite_t",
        "compat_ite_e",
    ] {
        let _ = declare_bool(&mut executor, name);
    }
    let condition_surface = FrontendTerm::App(
        "=>".to_string(),
        vec![
            FrontendTerm::Symbol("compat_ite_a".to_string()),
            FrontendTerm::Symbol("compat_ite_b".to_string()),
        ],
    );
    let parsed = FrontendTerm::App(
        "ite".to_string(),
        vec![
            condition_surface.clone(),
            FrontendTerm::Symbol("compat_ite_t".to_string()),
            FrontendTerm::Symbol("compat_ite_e".to_string()),
        ],
    );
    let canonical = executor
        .ctx
        .elaborate_surface_subterm(&parsed)
        .expect("ITE source elaborates");
    let condition = executor
        .ctx
        .elaborate_surface_subterm(&condition_surface)
        .expect("ITE condition elaborates");
    let originals = vec![(canonical, parsed)];
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_original(&mut executor.ctx, &originals, canonical));
    audit.protect_operand(&mut executor.ctx.terms, condition);
    assert!(!audit.merge_into(&mut HashMap::default()));

    let mut active = HashMap::default();
    active.insert(condition, "(=> compat_ite_a compat_ite_b)".to_string());
    assert!(audit.merge_into(&mut active));
}

#[test]
fn retained_original_index_is_unique_capped_and_cached() {
    let mut executor = Executor::new();
    let canonical = executor.ctx.terms.mk_bool(true);
    let parsed = FrontendTerm::Const(FrontendConstant::True);
    let originals = vec![(canonical, parsed.clone())];
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_original(&mut executor.ctx, &originals, canonical));
    let first_work = audit.retained_source_work_used();
    assert!(audit.require_original(&mut executor.ctx, &originals, canonical));
    assert_eq!(audit.retained_source_work_used(), first_work);

    let duplicate = vec![(canonical, parsed.clone()), (canonical, parsed.clone())];
    let mut duplicate_audit = ProvenanceSurfaceAudit::default();
    assert!(!duplicate_audit.require_original(&mut executor.ctx, &duplicate, canonical,));

    let over_cap = vec![(canonical, parsed); super::sources::MAX_RETAINED_ORIGINALS + 1];
    let mut capped_audit = ProvenanceSurfaceAudit::default();
    assert!(!capped_audit.require_original(&mut executor.ctx, &over_cap, canonical,));
}

#[test]
fn raw_source_alias_does_not_override_its_derived_canonical_root() {
    let mut executor = Executor::new();
    let canonical = executor.ctx.terms.mk_var("canonical_source", Sort::Bool);
    let alias = executor.ctx.terms.mk_var("raw_source_alias", Sort::Bool);
    let originals = vec![(
        canonical,
        FrontendTerm::Symbol("canonical_source".to_string()),
    )];
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_original_alias_only(&mut executor.ctx, &originals, canonical, alias,));
    audit.protect_rigid_root(&mut executor.ctx.terms, canonical);
    audit.protect_operand(&mut executor.ctx.terms, alias);
    let mut active = HashMap::default();
    active.insert(canonical, "canonical_source".to_string());
    active.insert(alias, "canonical_source".to_string());
    assert!(audit.merge_into(&mut active));
    assert!(!active.contains_key(&canonical));
    assert!(audit.validate_effective(&executor.ctx.terms, &active));
}

#[test]
fn derived_ite_roots_allow_authenticated_child_spellings() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("ite_audit_cond", Sort::Bool);
    let source_then = terms.mk_var("ite_audit_source_then", Sort::Bool);
    let source_else = terms.mk_var("ite_audit_source_else", Sort::Bool);
    let lifted_then = terms.mk_var("ite_audit_lifted_then", Sort::Bool);
    let lifted_else = terms.mk_var("ite_audit_lifted_else", Sort::Bool);
    let def_then = terms.mk_var("ite_audit_def_then", Sort::Bool);
    let def_else = terms.mk_var("ite_audit_def_else", Sort::Bool);
    let orig = terms.mk_ite_raw(cond, source_then, source_else);
    let goal = terms.mk_ite_raw(cond, lifted_then, lifted_else);
    let ite_def = terms.mk_ite_raw(cond, def_then, def_else);
    let and_term = terms.mk_app(Symbol::named("and"), [orig, ite_def], Sort::Bool);
    let intro_eq = terms.mk_app(Symbol::named("="), [orig, and_term], Sort::Bool);
    let cond_surface = "(= ite_audit_cond true)";
    let orig_surface = "(ite (= ite_audit_cond true) ite_audit_source_then ite_audit_source_else)";

    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_spelling(&mut terms, cond, cond_surface));
    assert!(audit.require_spelling(&mut terms, orig, orig_surface));
    audit.protect_operand(&mut terms, orig);
    for derived in [goal, ite_def, and_term, intro_eq] {
        audit.protect_rigid_root(&mut terms, derived);
    }
    let mut active = HashMap::default();
    active.insert(cond, cond_surface.to_string());
    active.insert(orig, orig_surface.to_string());
    assert!(audit.validate_effective(&terms, &active));
}

#[test]
fn root_only_rigidity_allows_children_but_rejects_a_direct_root_override() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("root_only_rigid_cond", Sort::Bool);
    let then_term = terms.mk_var("root_only_rigid_then", Sort::Bool);
    let else_term = terms.mk_var("root_only_rigid_else", Sort::Bool);
    let root = terms.mk_ite_raw(cond, then_term, else_term);
    let cond_surface = "(= root_only_rigid_cond true)";
    let root_surface = ay_proof::format_term_alethe(&terms, root);

    let mut child_only = ProvenanceSurfaceAudit::default();
    assert!(child_only.require_spelling(&mut terms, cond, cond_surface));
    child_only.protect_rigid_root(&mut terms, root);
    let mut child_active = HashMap::default();
    child_active.insert(cond, cond_surface.to_string());
    assert!(child_only.validate_effective(&terms, &child_active));

    let mut masked_child = ProvenanceSurfaceAudit::default();
    assert!(masked_child.require_spelling(&mut terms, cond, cond_surface));
    assert!(masked_child.require_spelling(&mut terms, root, &root_surface));
    masked_child.protect_rigid_root(&mut terms, root);
    let mut masked_active = HashMap::default();
    masked_active.insert(cond, cond_surface.to_string());
    masked_active.insert(root, root_surface);
    assert!(!masked_child.validate_effective(&terms, &masked_active));
}

#[test]
fn recursive_rigidity_upgrades_root_only_and_accepts_only_canonical_identity() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("recursive_rigid_cond", Sort::Bool);
    let then_term = terms.mk_var("recursive_rigid_then", Sort::Bool);
    let else_term = terms.mk_var("recursive_rigid_else", Sort::Bool);
    let root = terms.mk_ite_raw(cond, then_term, else_term);
    let cond_canonical = ay_proof::format_term_alethe(&terms, cond);
    let root_canonical = ay_proof::format_term_alethe(&terms, root);

    let mut canonical = ProvenanceSurfaceAudit::default();
    canonical.protect_rigid_root(&mut terms, root);
    canonical.protect_rigid_operand(&mut terms, root);
    assert!(canonical.recursive_rigid_identity.contains(&cond));
    assert!(canonical.require_spelling(&mut terms, cond, &cond_canonical));
    assert!(canonical.require_spelling(&mut terms, root, &root_canonical));
    let mut canonical_active = HashMap::default();
    canonical_active.insert(cond, cond_canonical);
    canonical_active.insert(root, root_canonical);
    assert!(canonical.validate_effective(&terms, &canonical_active));

    let mut changed_child = ProvenanceSurfaceAudit::default();
    changed_child.protect_rigid_operand(&mut terms, root);
    let changed = "(= recursive_rigid_cond true)";
    assert!(changed_child.require_spelling(&mut terms, cond, changed));
    let mut changed_active = HashMap::default();
    changed_active.insert(cond, changed.to_string());
    assert!(!changed_child.validate_effective(&terms, &changed_active));
}

#[test]
fn ite_intro_role_rejects_swapped_ite_and_reversed_branch_equality() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("ite_role_cond", Sort::Bool);
    let then_term = terms.mk_var("ite_role_then", Sort::Int);
    let else_term = terms.mk_var("ite_role_else", Sort::Int);
    let ite_term = terms.mk_ite_raw(cond, then_term, else_term);
    let eq_then = terms.mk_app(Symbol::named("="), [ite_term, then_term], Sort::Bool);
    let eq_else = terms.mk_app(Symbol::named("="), [ite_term, else_term], Sort::Bool);

    let mut compatible = ProvenanceSurfaceAudit::default();
    assert!(compatible.require_spelling(&mut terms, cond, "(= ite_role_cond true)",));
    compatible.protect_ite_intro_role(&mut terms, ite_term, eq_then, eq_else);
    let mut active = HashMap::default();
    active.insert(cond, "(= ite_role_cond true)".to_string());
    assert!(compatible.validate_effective(&terms, &active));

    let mut swapped = ProvenanceSurfaceAudit::default();
    assert!(swapped.require_spelling(
        &mut terms,
        ite_term,
        "(ite (not ite_role_cond) ite_role_else ite_role_then)",
    ));
    swapped.protect_ite_intro_role(&mut terms, ite_term, eq_then, eq_else);
    let mut active = HashMap::default();
    active.insert(
        ite_term,
        "(ite (not ite_role_cond) ite_role_else ite_role_then)".to_string(),
    );
    assert!(!swapped.validate_effective(&terms, &active));

    let mut reversed = ProvenanceSurfaceAudit::default();
    assert!(reversed.require_spelling(
        &mut terms,
        eq_then,
        "(= ite_role_then (ite ite_role_cond ite_role_then ite_role_else))",
    ));
    reversed.protect_ite_intro_role(&mut terms, ite_term, eq_then, eq_else);
    let mut active = HashMap::default();
    active.insert(
        eq_then,
        "(= ite_role_then (ite ite_role_cond ite_role_then ite_role_else))".to_string(),
    );
    assert!(!reversed.validate_effective(&terms, &active));
}

#[test]
fn duplicate_ite_intro_roles_are_deduplicated_before_rendering() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("duplicate_ite_role_cond", Sort::Bool);
    let then_term = terms.mk_var("duplicate_ite_role_then", Sort::Int);
    let else_term = terms.mk_var("duplicate_ite_role_else", Sort::Int);
    let ite_term = terms.mk_ite_raw(cond, then_term, else_term);
    let eq_then = terms.mk_app(Symbol::named("="), [ite_term, then_term], Sort::Bool);
    let eq_else = terms.mk_app(Symbol::named("="), [ite_term, else_term], Sort::Bool);
    let mut audit = ProvenanceSurfaceAudit::default();
    for _ in 0..super::MAX_AUDITED_FARKAS_LEMMAS {
        audit.protect_ite_intro_role(&mut terms, ite_term, eq_then, eq_else);
    }
    assert_eq!(audit.ite_intro_roles.len(), 1);
    assert!(audit.validate_effective(&terms, &HashMap::default()));
}

#[test]
fn shared_surface_traversal_rejects_high_arity_before_child_clone() {
    let mut terms = TermStore::new();
    let atom = terms.mk_var("surface_high_arity_atom", Sort::Bool);
    let root = terms.mk_app(
        Symbol::named("surface_high_arity"),
        vec![atom; super::MAX_AUDITED_TERMS + 1],
        Sort::Bool,
    );
    let mut audit = ProvenanceSurfaceAudit::default();
    audit.protect_rigid_operand(&mut terms, root);
    assert!(!audit.validate_effective(&terms, &HashMap::default()));
}

#[test]
fn printed_farkas_sign_budget_is_shared_across_lemmas() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let valid = terms.mk_app(Symbol::named("<"), [zero, one], Sort::Bool);
    let farkas = FarkasAnnotation::from_ints(&[1]);
    let mut audit = ProvenanceSurfaceAudit::default();
    audit.protect_farkas_lemma(&mut terms, &[valid], &farkas);
    audit.protect_farkas_lemma(&mut terms, &[valid], &farkas);
    let mut rendered = HashMap::default();
    rendered.insert(valid, ay_proof::format_term_alethe(&terms, valid));

    let mut three_checks = 3;
    let mut unlimited_parse = usize::MAX;
    assert!(!audit.validate_farkas_lemmas_with_budget(
        &terms,
        &rendered,
        &mut three_checks,
        &mut unlimited_parse,
    ));
    assert_eq!(three_checks, 0);

    let mut four_checks = 4;
    let mut unlimited_parse = usize::MAX;
    assert!(audit.validate_farkas_lemmas_with_budget(
        &terms,
        &rendered,
        &mut four_checks,
        &mut unlimited_parse,
    ));
    assert_eq!(four_checks, 0);
}

#[test]
fn printed_farkas_parse_bytes_are_shared_across_repeated_rows() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let valid = terms.mk_app(Symbol::named("<"), [zero, one], Sort::Bool);
    let farkas = FarkasAnnotation::from_ints(&[1]);
    let mut audit = ProvenanceSurfaceAudit::default();
    audit.protect_farkas_lemma(&mut terms, &[valid], &farkas);
    audit.protect_farkas_lemma(&mut terms, &[valid], &farkas);
    let surface = ay_proof::format_term_alethe(&terms, valid);
    let row_bytes = surface.len();
    let mut rendered = HashMap::default();
    rendered.insert(valid, surface);

    let mut checks = 4;
    let mut one_row = row_bytes;
    assert!(!audit.validate_farkas_lemmas_with_budget(
        &terms,
        &rendered,
        &mut checks,
        &mut one_row,
    ));

    let mut checks = 4;
    let mut two_rows = row_bytes * 2;
    assert!(audit.validate_farkas_lemmas_with_budget(
        &terms,
        &rendered,
        &mut checks,
        &mut two_rows,
    ));
    assert_eq!(two_rows, 0);
}
