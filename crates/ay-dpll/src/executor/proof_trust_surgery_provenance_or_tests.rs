// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Policy tests for provenance-authenticated OR repair.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, FarkasAnnotation, Proof, Sort, Symbol};
use ay_frontend::command::{Command, Sort as FrontendSort, Term as FrontendTerm};

use super::proof_trust_surgery_ite::ProvenanceFarkasLemma;
use super::proof_trust_surgery_provenance::{
    retained_original_rows_are_signable, surface_is_direct_arithmetic_literal,
    surface_is_direct_equality, surface_source_work, OriginalSourceIndex, ProvenanceSurfaceAudit,
    SurgeryPlanningBudget, MAX_FARKAS_ATTEMPTS,
};
use super::proof_trust_surgery_provenance_or::{
    ite_refutation_branch_shape, surface_override_policy_allows,
};
use super::proof_trust_surgery_provenance_or_transfer::ite_transfer_branch_shape;
use super::theories::solve_harness::ProofProblemAssertionProvenance;
use super::Executor;

fn declare_fixture_const(
    executor: &mut Executor,
    name: &str,
    sort: FrontendSort,
) -> ay_core::TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(name.to_string(), sort))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

#[test]
fn surface_preserving_or_repair_rejects_normalization_bridge_mix() {
    assert!(surface_override_policy_allows(false, false));
    assert!(surface_override_policy_allows(true, false));
    assert!(surface_override_policy_allows(false, true));
    assert!(!surface_override_policy_allows(true, true));
}

#[test]
fn exact_authored_or_trust_leaf_rebuilds_to_strict_assume() {
    let mut executor = Executor::new();
    let a = declare_fixture_const(&mut executor, "a", FrontendSort::Simple("Bool".to_string()));
    let b = declare_fixture_const(&mut executor, "b", FrontendSort::Simple("Bool".to_string()));
    let authored_or = executor.ctx.terms.mk_or(vec![a, b]);
    let not_authored_or = executor.ctx.terms.mk_not_raw(authored_or);
    let parsed_or = FrontendTerm::App(
        "or".to_string(),
        vec![
            FrontendTerm::Symbol("a".to_string()),
            FrontendTerm::Symbol("b".to_string()),
        ],
    );
    let parsed_not = FrontendTerm::App("not".to_string(), vec![parsed_or.clone()]);
    let originals = vec![(authored_or, parsed_or), (not_authored_or, parsed_not)];
    let mut overrides = HashMap::default();
    for (canonical, parsed) in &originals {
        assert!(
            crate::executor::proof_surface_syntax::collect_surface_term_overrides(
                &mut executor.ctx,
                *canonical,
                parsed,
                &mut overrides,
            )
        );
    }
    executor.last_proof_term_overrides = Some(overrides);
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(authored_or, vec![vec![authored_or]]);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: vec![authored_or, not_authored_or],
        problem_assertions: vec![authored_or, not_authored_or],
        assertion_sources,
    });

    let mut proof = Proof::new();
    let trust = proof.add_rule_step(AletheRule::Trust, vec![authored_or], Vec::new(), Vec::new());
    let complement = proof.add_assume(not_authored_or, None);
    let _ = proof.add_resolution(Vec::new(), authored_or, trust, complement);

    assert!(executor.try_rebuild_with_trust_surgery(&mut proof, &originals));
    let quality = ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("exact authored OR repair must remain strict");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn ite_or_refutation_rejects_guard_support_collision_before_resolution() {
    let mut executor = Executor::new();
    let guard = executor.ctx.terms.mk_var("guard", Sort::Bool);
    let source = executor.ctx.terms.mk_var("source", Sort::Bool);
    let disjunct = executor.ctx.terms.mk_var("disjunct", Sort::Bool);
    let support = executor.ctx.terms.mk_not_raw(guard);
    let source_blocker = executor.ctx.terms.mk_not_raw(source);
    let disjunct_blocker = executor.ctx.terms.mk_not_raw(disjunct);
    let lemma = ProvenanceFarkasLemma {
        clause: vec![source_blocker, disjunct_blocker, guard],
        farkas: FarkasAnnotation::from_ints(&[1, 1, 1]),
        supports: vec![disjunct, support],
    };

    assert!(!ite_refutation_branch_shape(
        &mut executor.ctx.terms,
        guard,
        source,
        disjunct,
        &lemma,
    ));
}

#[test]
fn ite_or_transfer_rejects_guard_support_collision_before_resolution() {
    let mut executor = Executor::new();
    let target = executor.ctx.terms.mk_var("target", Sort::Bool);
    let guard = executor.ctx.terms.mk_var("guard", Sort::Bool);
    let source_branch = executor.ctx.terms.mk_var("source_branch", Sort::Bool);
    let target_branch = executor.ctx.terms.mk_var("target_branch", Sort::Bool);
    let source = executor.ctx.terms.mk_var("source", Sort::Bool);
    let support = executor.ctx.terms.mk_not_raw(guard);
    let source_branch_blocker = executor.ctx.terms.mk_not_raw(source_branch);
    let source_blocker = executor.ctx.terms.mk_not_raw(source);
    let lemma = ProvenanceFarkasLemma {
        clause: vec![source_branch_blocker, source_blocker, guard, target_branch],
        farkas: FarkasAnnotation::from_ints(&[1, 1, 1, 1]),
        supports: vec![source, support],
    };

    assert!(!ite_transfer_branch_shape(
        &mut executor.ctx.terms,
        target,
        guard,
        source_branch,
        target_branch,
        source,
        &lemma,
    ));
}

#[test]
fn provenance_arithmetic_rows_reject_let_hidden_atoms() {
    let mut executor = Executor::new();
    let _x = declare_fixture_const(&mut executor, "x", FrontendSort::Simple("Int".to_string()));
    let _y = declare_fixture_const(&mut executor, "y", FrontendSort::Simple("Int".to_string()));
    let atom = FrontendTerm::App(
        "<".to_string(),
        vec![
            FrontendTerm::Symbol("x".to_string()),
            FrontendTerm::Symbol("y".to_string()),
        ],
    );
    assert!(surface_is_direct_arithmetic_literal(
        &mut executor.ctx,
        &atom
    ));
    let hidden = FrontendTerm::Let(
        vec![("z".to_string(), FrontendTerm::Symbol("x".to_string()))],
        Box::new(atom),
    );
    assert!(!surface_is_direct_arithmetic_literal(
        &mut executor.ctx,
        &hidden
    ));
    let nested_hidden = FrontendTerm::App(
        "=".to_string(),
        vec![
            FrontendTerm::Let(
                vec![("z".to_string(), FrontendTerm::Symbol("y".to_string()))],
                Box::new(FrontendTerm::Symbol("z".to_string())),
            ),
            FrontendTerm::Symbol("x".to_string()),
        ],
    );
    assert!(!surface_is_direct_arithmetic_literal(
        &mut executor.ctx,
        &nested_hidden
    ));
    assert!(!surface_is_direct_equality(&nested_hidden));

    let bool_equality_wrapper = FrontendTerm::App(
        "=".to_string(),
        vec![
            FrontendTerm::App(
                "<".to_string(),
                vec![
                    FrontendTerm::Symbol("x".to_string()),
                    FrontendTerm::Const(ay_frontend::command::Constant::Numeral("0".to_string())),
                ],
            ),
            FrontendTerm::Const(ay_frontend::command::Constant::True),
        ],
    );
    assert!(!surface_is_direct_arithmetic_literal(
        &mut executor.ctx,
        &bool_equality_wrapper,
    ));

    let nonlinear = FrontendTerm::App(
        "<".to_string(),
        vec![
            FrontendTerm::App(
                "*".to_string(),
                vec![
                    FrontendTerm::Const(ay_frontend::command::Constant::Numeral("0".to_string())),
                    FrontendTerm::Symbol("x".to_string()),
                    FrontendTerm::Symbol("x".to_string()),
                ],
            ),
            FrontendTerm::Const(ay_frontend::command::Constant::Numeral("1".to_string())),
        ],
    );
    assert!(!surface_is_direct_arithmetic_literal(
        &mut executor.ctx,
        &nonlinear,
    ));
}

#[test]
fn or_transfer_and_conflict_share_one_attempt_boundary() {
    let mut terms = ay_core::TermStore::new();
    let atom = terms.mk_var("shared_or_budget_atom", Sort::Bool);
    let mut shared = SurgeryPlanningBudget::new();
    let transfer_attempts = MAX_FARKAS_ATTEMPTS / 2;
    for _ in 0..transfer_attempts {
        assert!(shared.spend_farkas_attempt(&terms, &[atom]));
    }
    for _ in transfer_attempts..MAX_FARKAS_ATTEMPTS {
        assert!(shared.spend_farkas_attempt(&terms, &[atom]));
    }
    assert!(
        !shared.spend_farkas_attempt(&terms, &[atom]),
        "fallback must not receive a fresh budget"
    );
}

#[test]
fn retained_row_signability_is_charged_once_and_cached_by_exact_source() {
    let mut executor = Executor::new();
    let _x = declare_fixture_const(
        &mut executor,
        "cached_signable_x",
        FrontendSort::Simple("Int".to_string()),
    );
    let mut sum = vec![FrontendTerm::Symbol("cached_signable_x".to_string())];
    sum.extend(
        (0..4_096)
            .map(|_| FrontendTerm::Const(ay_frontend::command::Constant::Numeral("0".to_string()))),
    );
    let parsed = FrontendTerm::App(
        "=".to_string(),
        vec![
            FrontendTerm::App("+".to_string(), sum),
            FrontendTerm::Const(ay_frontend::command::Constant::Numeral("1".to_string())),
        ],
    );
    let canonical = executor
        .ctx
        .elaborate_surface_subterm(&parsed)
        .expect("large linear row elaborates");
    let other = FrontendTerm::App(
        "=".to_string(),
        vec![
            FrontendTerm::Symbol("cached_signable_x".to_string()),
            FrontendTerm::Const(ay_frontend::command::Constant::Numeral("2".to_string())),
        ],
    );
    let other_canonical = executor
        .ctx
        .elaborate_surface_subterm(&other)
        .expect("second linear row elaborates");
    let originals = vec![(canonical, parsed), (other_canonical, other)];
    let index = OriginalSourceIndex::new(&originals);
    let work = surface_source_work(&originals[0].1).expect("row has bounded work");
    let mut planning = SurgeryPlanningBudget::new();
    planning.set_remaining_work_for_test(work);
    assert!(retained_original_rows_are_signable(
        &mut executor.ctx,
        &[canonical],
        &originals,
        &index,
        &mut planning,
    ));
    assert!(retained_original_rows_are_signable(
        &mut executor.ctx,
        &[canonical],
        &originals,
        &index,
        &mut planning,
    ));
    assert!(!retained_original_rows_are_signable(
        &mut executor.ctx,
        &[other_canonical],
        &originals,
        &index,
        &mut planning,
    ));
}

#[test]
fn provenance_surface_audit_rejects_derived_override_collisions() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let cond = executor.ctx.terms.mk_var("cond", Sort::Bool);
    let target_or = executor.ctx.terms.mk_or(vec![a, b]);
    let target_ite = executor.ctx.terms.mk_ite(cond, a, b);
    let equality = executor.ctx.terms.mk_eq(a, b);
    let nested = executor.ctx.terms.mk_ite(cond, a, b);
    let nested_parent = executor.ctx.terms.mk_or(vec![nested, equality]);
    let mut audit = ProvenanceSurfaceAudit::default();
    audit.protect_rigid_operand(&mut executor.ctx.terms, target_or);
    audit.protect_rigid_operand(&mut executor.ctx.terms, target_ite);
    audit.protect_farkas_operand(&mut executor.ctx.terms, equality);
    let mut active = HashMap::default();
    active.insert(target_or, "(=> a b)".to_string());
    active.insert(target_ite, "(ite (not cond) b a)".to_string());
    active.insert(equality, "(let ((z a)) (= b z))".to_string());
    assert!(!audit.validate_effective(&executor.ctx.terms, &active));

    let mut child_audit = ProvenanceSurfaceAudit::default();
    child_audit.protect_rigid_operand(&mut executor.ctx.terms, nested_parent);
    let mut child_active = HashMap::default();
    child_active.insert(nested, "(ite (not cond) b a)".to_string());
    assert!(!child_audit.validate_effective(&executor.ctx.terms, &child_active));
}

#[test]
fn provenance_surface_audit_rejects_cross_plan_requirements() {
    let mut executor = Executor::new();
    let term = executor.ctx.terms.mk_var("term", Sort::Bool);
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_spelling(&mut executor.ctx.terms, term, "term"));
    assert!(!audit.require_spelling(&mut executor.ctx.terms, term, "(not (not term))"));

    let mut active = HashMap::default();
    active.insert(term, "term".to_string());
    audit.protect_operand(&mut executor.ctx.terms, term);
    assert!(audit.validate_effective(&executor.ctx.terms, &active));
    active.insert(term, "(not (not term))".to_string());
    assert!(!audit.validate_effective(&executor.ctx.terms, &active));

    let other = executor.ctx.terms.mk_var("other", Sort::Bool);
    let derived = executor.ctx.terms.mk_or(vec![term, other]);
    let mut canonical_audit = ProvenanceSurfaceAudit::default();
    canonical_audit.protect_rigid_operand(&mut executor.ctx.terms, derived);
    let canonical_spelling = ay_proof::format_term_alethe(&executor.ctx.terms, derived);
    assert!(canonical_audit.require_spelling(
        &mut executor.ctx.terms,
        derived,
        &canonical_spelling,
    ));
    let mut canonical_active = HashMap::default();
    canonical_active.insert(derived, canonical_spelling);
    assert!(canonical_audit.validate_effective(&executor.ctx.terms, &canonical_active));

    let mut derived_audit = ProvenanceSurfaceAudit::default();
    derived_audit.protect_rigid_operand(&mut executor.ctx.terms, derived);
    assert!(derived_audit.require_spelling(&mut executor.ctx.terms, derived, "(=> term other)"));
    assert!(!derived_audit.validate_effective(&executor.ctx.terms, &HashMap::default()));

    let cond = executor.ctx.terms.mk_var("cond2", Sort::Bool);
    let derived_ite = executor.ctx.terms.mk_ite(cond, term, other);
    let mut ite_audit = ProvenanceSurfaceAudit::default();
    ite_audit.protect_rigid_operand(&mut executor.ctx.terms, derived_ite);
    assert!(ite_audit.require_spelling(
        &mut executor.ctx.terms,
        derived_ite,
        "(ite (not cond2) other term)"
    ));
    assert!(!ite_audit.validate_effective(&executor.ctx.terms, &HashMap::default()));

    let equality = executor.ctx.terms.mk_eq(term, other);
    let mut equality_audit = ProvenanceSurfaceAudit::default();
    equality_audit.protect_farkas_operand(&mut executor.ctx.terms, equality);
    assert!(equality_audit.require_spelling(
        &mut executor.ctx.terms,
        equality,
        "(let ((z term)) (= other z))"
    ));
    assert!(!equality_audit.validate_effective(&executor.ctx.terms, &HashMap::default()));
}

#[test]
fn provenance_surface_audit_requires_printed_complement_pairs() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("polarity_p", Sort::Bool);
    let not_p = executor.ctx.terms.mk_not_raw(p);
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_spelling(&mut executor.ctx.terms, p, "(= polarity_p true)",));
    assert!(audit.require_spelling(&mut executor.ctx.terms, not_p, "(= polarity_p false)",));
    audit.protect_operand(&mut executor.ctx.terms, p);
    let mut active = HashMap::default();
    active.insert(p, "(= polarity_p true)".to_string());
    active.insert(not_p, "(= polarity_p false)".to_string());
    assert!(!audit.validate_effective(&executor.ctx.terms, &active));
}

#[test]
fn provenance_surface_audit_replays_final_printed_farkas_rows() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("surface_fx", Sort::Int);
    let one = executor.ctx.terms.mk_int(1.into());
    let plus = executor
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [x, one], Sort::Int);
    let atom = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<"), [x, plus], Sort::Bool);
    let farkas = FarkasAnnotation::from_ints(&[1]);

    let mut nonlinear = ProvenanceSurfaceAudit::default();
    nonlinear.protect_farkas_lemma(&mut executor.ctx.terms, &[atom], &farkas);
    assert!(nonlinear.require_spelling(
        &mut executor.ctx.terms,
        plus,
        "(+ surface_fx (* 0 surface_fx surface_fx) 1)",
    ));
    let mut active = HashMap::default();
    active.insert(
        plus,
        "(+ surface_fx (* 0 surface_fx surface_fx) 1)".to_string(),
    );
    assert!(!nonlinear.validate_effective(&executor.ctx.terms, &active));

    let not_atom = executor.ctx.terms.mk_not_raw(atom);
    let double_not = executor.ctx.terms.mk_not_raw(not_atom);
    let mut negation_depth = ProvenanceSurfaceAudit::default();
    negation_depth.protect_farkas_lemma(&mut executor.ctx.terms, &[double_not], &farkas);
    assert!(!negation_depth.validate_effective(&executor.ctx.terms, &HashMap::default()));
}

#[test]
fn authenticated_alias_must_be_absent_from_old_proof_dag() {
    let mut executor = Executor::new();
    let source = executor.ctx.terms.mk_var("alias_source", Sort::Bool);
    let alias = executor.ctx.terms.mk_not_raw(source);
    let originals = vec![(source, FrontendTerm::Symbol("alias_source".to_string()))];
    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_original_as(&mut executor.ctx, &originals, source, alias,));
    let mut proof = Proof::new();
    proof.add_assume(alias, None);
    assert!(!audit.aliases_are_fresh_in(&proof, &executor.ctx.terms));
}

#[path = "proof_trust_surgery_provenance_or_surface_tests.rs"]
mod surface_tests;
