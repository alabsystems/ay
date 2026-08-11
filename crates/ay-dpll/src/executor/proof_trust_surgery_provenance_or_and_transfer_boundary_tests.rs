// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shape, overlap, and aggregate projection boundaries for transfer plans.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use super::super::and_conflict_fixture::{app, declare, symbol};
use super::super::ProvenanceOrPlan;
use super::tests::{plan_fixture, proof_vector_volume, transfer_fixture};
use super::{
    conjunctive_transfer_plan_shape_is_valid, flat_bool_and_children, mapping_for_target,
    remaining_target_set, target_and_branches, ProvenanceOrAndTransferOutcome,
    ProvenanceOrAndTransferPlan,
};
use crate::executor::proof_trust_surgery_provenance::{
    complement_of, OriginalSourceIndex, SurgeryPlanningBudget,
};
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor::Executor;

struct ManyToOneFixture {
    executor: Executor,
    plan: ProvenanceOrAndTransferPlan,
    not_goal: TermId,
}

fn many_to_one_fixture() -> ManyToOneFixture {
    let mut executor = Executor::new();
    for name in [
        "transfer_many_p",
        "transfer_many_q",
        "transfer_many_a",
        "transfer_many_b",
        "transfer_many_c",
    ] {
        declare(&mut executor, name, "Bool");
    }
    let parsed_p = symbol("transfer_many_p");
    let parsed_q = symbol("transfer_many_q");
    let parsed_a = symbol("transfer_many_a");
    let first = app("and", [parsed_p.clone(), parsed_a.clone()]);
    let second = app("and", [parsed_q.clone(), parsed_a]);
    let parsed_orig = app("or", [first, second]);
    let orig = executor
        .ctx
        .elaborate_surface_subterm(&parsed_orig)
        .expect("many-to-one source elaborates");
    let p = executor
        .ctx
        .elaborate_surface_subterm(&parsed_p)
        .expect("first support elaborates");
    let q = executor
        .ctx
        .elaborate_surface_subterm(&parsed_q)
        .expect("second support elaborates");
    let a = executor
        .ctx
        .elaborate_surface_subterm(&symbol("transfer_many_a"))
        .expect("shared child elaborates");
    let b = executor
        .ctx
        .elaborate_surface_subterm(&symbol("transfer_many_b"))
        .expect("unmatched child elaborates");
    let c = executor
        .ctx
        .elaborate_surface_subterm(&symbol("transfer_many_c"))
        .expect("unmatched child elaborates");
    let truth = executor.ctx.terms.mk_bool(true);
    let shared_target = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [truth, a], Sort::Bool);
    let unrelated = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [b, c], Sort::Bool);
    let goal =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [shared_target, unrelated], Sort::Bool);
    let not_goal = complement_of(&mut executor.ctx.terms, goal);
    let originals = vec![(orig, parsed_orig), (p, parsed_p), (q, parsed_q)];
    let sources = vec![orig, p, q];
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(goal, vec![sources.clone()]);
    let mut problem_scope = sources.clone();
    problem_scope.push(not_goal);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: problem_scope.clone(),
        problem_assertions: problem_scope,
        assertion_sources,
    });
    let source_index = OriginalSourceIndex::new(&originals);
    let plan = match executor.plan_provenance_or(
        &[goal],
        &originals,
        &source_index,
        &mut SurgeryPlanningBudget::new(),
    ) {
        Some(ProvenanceOrPlan::ConjunctiveTransfer(plan)) => plan,
        Some(_) => panic!("many-to-one fixture must select conjunctive transfer"),
        None => panic!("both source branches must map to the shared target"),
    };
    assert!(plan.outcomes.iter().all(|outcome| matches!(
        outcome,
        ProvenanceOrAndTransferOutcome::Map(mapping) if mapping.target == shared_target
    )));
    ManyToOneFixture {
        executor,
        plan,
        not_goal,
    }
}

fn projection_boundary_plan(
    terms: &mut TermStore,
    projections_per_branch: usize,
) -> ProvenanceOrAndTransferPlan {
    let support = terms.mk_var("transfer_boundary_support", Sort::Bool);
    let truth = terms.mk_bool(true);
    let mut source_disjuncts = Vec::new();
    let mut target_disjuncts = Vec::new();
    let mut outcomes = Vec::new();
    let supports: HashSet<TermId> = [support].into_iter().collect();
    for branch in 0..64 {
        let projected: Vec<_> = (0..projections_per_branch)
            .map(|index| terms.mk_var(format!("transfer_boundary_{branch}_{index}"), Sort::Bool))
            .collect();
        let mut source_children = vec![support];
        source_children.extend(projected.iter().copied());
        let source = terms.mk_app(Symbol::named("and"), source_children, Sort::Bool);
        let mut target_children = vec![truth];
        target_children.extend(projected);
        let target = terms.mk_app(Symbol::named("and"), target_children, Sort::Bool);
        let actual_source = flat_bool_and_children(terms, source, false).unwrap();
        let actual_target = flat_bool_and_children(terms, target, true).unwrap();
        let mapping = mapping_for_target(
            terms,
            source,
            &actual_source,
            target,
            &actual_target,
            &supports,
        )
        .unwrap();
        source_disjuncts.push(source);
        target_disjuncts.push(target);
        outcomes.push(ProvenanceOrAndTransferOutcome::Map(mapping));
    }
    let orig = terms.mk_app(Symbol::named("or"), source_disjuncts.clone(), Sort::Bool);
    let goal = terms.mk_app(Symbol::named("or"), target_disjuncts.clone(), Sort::Bool);
    let remaining_targets = remaining_target_set(&source_disjuncts, &outcomes).unwrap();
    ProvenanceOrAndTransferPlan {
        goal,
        orig,
        source_disjuncts,
        target_disjuncts,
        remaining_targets,
        authored_sources: vec![orig, support],
        outcomes,
    }
}

#[test]
fn generated_projection_cap_accepts_512_and_rejects_the_next_batch() {
    let mut terms = TermStore::new();
    let at_cap = projection_boundary_plan(&mut terms, 8);
    assert!(conjunctive_transfer_plan_shape_is_valid(
        &mut terms, &at_cap,
    ));
    assert!(at_cap.emitted_literal_volume().is_some());

    let over_cap = projection_boundary_plan(&mut terms, 9);
    assert!(!conjunctive_transfer_plan_shape_is_valid(
        &mut terms, &over_cap,
    ));
}

#[test]
fn many_to_one_target_collapse_has_exact_strict_residual_and_volume() {
    let mut fixture = many_to_one_fixture();
    let mapped_targets: HashSet<_> = fixture
        .plan
        .outcomes
        .iter()
        .filter_map(|outcome| match outcome {
            ProvenanceOrAndTransferOutcome::Map(mapping) => Some(mapping.target),
            ProvenanceOrAndTransferOutcome::Refute(_) => None,
        })
        .collect();
    assert_eq!(mapped_targets.len(), 1, "two sources share one target");
    assert_eq!(fixture.plan.remaining_targets.len(), 1);

    let mut proof = Proof::new();
    let mut assumes = HashMap::default();
    for &source in &fixture.plan.authored_sources {
        assumes.insert(source, proof.add_assume(source, None));
    }
    let terminal = fixture
        .executor
        .emit_provenance_or_and_transfer(&mut proof, &fixture.plan, &assumes)
        .expect("many-to-one residual emits exactly");
    assert_eq!(
        proof_vector_volume(&proof),
        fixture.plan.emitted_literal_volume().unwrap(),
        "many-to-one set collapse must be covered by the exact census",
    );
    let close = proof.add_assume(fixture.not_goal, None);
    proof.add_resolution(Vec::new(), fixture.plan.goal, terminal, close);
    ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms)
        .expect("many-to-one transfer remains a strict refutation");
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::True,
                    ..
                }
            ))
            .count(),
        1,
        "both mappings share the single true proof",
    );
}

#[test]
fn source_overlap_guard_is_load_bearing() {
    let mut fixture = many_to_one_fixture();
    let first_source = fixture.plan.outcomes[0].source();
    let ProvenanceOrAndTransferOutcome::Map(first_mapping) = &fixture.plan.outcomes[0] else {
        panic!("first source maps");
    };
    let target = first_mapping.target;
    let orig =
        fixture
            .executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [first_source, target], Sort::Bool);
    let TermData::App(Symbol::Named(head), source_disjuncts) = fixture.executor.ctx.terms.get(orig)
    else {
        panic!("overlap source stays an OR");
    };
    assert_eq!(head, "or");
    let source_disjuncts = source_disjuncts.clone();
    let supports: HashSet<_> = fixture
        .plan
        .authored_sources
        .iter()
        .copied()
        .filter(|source| *source != fixture.plan.orig)
        .collect();
    let target_children =
        flat_bool_and_children(&fixture.executor.ctx.terms, target, true).unwrap();
    let outcomes: Vec<_> = source_disjuncts
        .iter()
        .map(|&source| {
            let source_children =
                flat_bool_and_children(&fixture.executor.ctx.terms, source, false).unwrap();
            ProvenanceOrAndTransferOutcome::Map(
                mapping_for_target(
                    &mut fixture.executor.ctx.terms,
                    source,
                    &source_children,
                    target,
                    &target_children,
                    &supports,
                )
                .expect("every overlap mapping is otherwise exact"),
            )
        })
        .collect();
    let remaining_targets = remaining_target_set(&source_disjuncts, &outcomes).unwrap();
    let overlap = ProvenanceOrAndTransferPlan {
        goal: fixture.plan.goal,
        orig,
        source_disjuncts,
        target_disjuncts: fixture.plan.target_disjuncts.clone(),
        remaining_targets,
        authored_sources: std::iter::once(orig)
            .chain(supports.iter().copied())
            .collect(),
        outcomes,
    };
    assert!(overlap.target_disjuncts.contains(&target));
    assert!(overlap.source_disjuncts.contains(&target));
    assert_eq!(overlap.remaining_targets, vec![target]);
    assert!(!conjunctive_transfer_plan_shape_is_valid(
        &mut fixture.executor.ctx.terms,
        &overlap,
    ));
}

#[test]
fn wrong_orig_shape_fails_closed() {
    let mut fixture = transfer_fixture();
    let mut wrong_orig = plan_fixture(&mut fixture);
    let old_orig = wrong_orig.orig;
    let bad_orig = fixture
        .executor
        .ctx
        .terms
        .mk_var("transfer_wrong_orig", Sort::Bool);
    wrong_orig.orig = bad_orig;
    *wrong_orig
        .authored_sources
        .iter_mut()
        .find(|source| **source == old_orig)
        .unwrap() = bad_orig;
    assert!(!conjunctive_transfer_plan_shape_is_valid(
        &mut fixture.executor.ctx.terms,
        &wrong_orig,
    ));

    for (name, bad_orig) in [
        (
            "arity",
            fixture.executor.ctx.terms.mk_app(
                Symbol::named("or"),
                [wrong_orig.source_disjuncts[0]],
                Sort::Bool,
            ),
        ),
        (
            "sort",
            fixture.executor.ctx.terms.mk_app(
                Symbol::named("or"),
                wrong_orig.source_disjuncts.clone(),
                Sort::Int,
            ),
        ),
    ] {
        let mut malformed = plan_fixture(&mut fixture);
        let old = malformed.orig;
        malformed.orig = bad_orig;
        *malformed
            .authored_sources
            .iter_mut()
            .find(|source| **source == old)
            .unwrap() = bad_orig;
        assert!(
            !conjunctive_transfer_plan_shape_is_valid(&mut fixture.executor.ctx.terms, &malformed,),
            "wrong source {name} must fail closed",
        );
    }

    let p = fixture
        .executor
        .ctx
        .terms
        .mk_var("transfer_shape_p", Sort::Bool);
    let q = fixture
        .executor
        .ctx
        .terms
        .mk_var("transfer_shape_q", Sort::Bool);
    let nested = fixture
        .executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let nested_branch =
        fixture
            .executor
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [nested, p], Sort::Bool);
    let valid_branch = fixture
        .executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let nested_goal = fixture.executor.ctx.terms.mk_app(
        Symbol::named("or"),
        [nested_branch, valid_branch],
        Sort::Bool,
    );
    assert!(target_and_branches(&fixture.executor.ctx.terms, nested_goal).is_none());

    let int_child = fixture
        .executor
        .ctx
        .terms
        .mk_var("transfer_shape_int", Sort::Int);
    let wrong_sort_branch =
        fixture
            .executor
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [p, int_child], Sort::Bool);
    let wrong_sort_goal = fixture.executor.ctx.terms.mk_app(
        Symbol::named("or"),
        [wrong_sort_branch, valid_branch],
        Sort::Bool,
    );
    assert!(target_and_branches(&fixture.executor.ctx.terms, wrong_sort_goal).is_none());
}
