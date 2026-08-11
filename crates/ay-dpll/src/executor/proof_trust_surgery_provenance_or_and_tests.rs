// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact conjunctive provenance-OR planning and emission tests.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, ProofStep, Sort, Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::and_conflict::exact_flat_and_or_surface_matches;
use super::and_conflict_fixture::{
    app, declare, equality, four_branch_fixture, numeral, plan_fixture, symbol,
};
use super::ProvenanceOrPlan;
use crate::executor::proof_surface_syntax::{collect_surface_term_overrides, format_frontend_term};
use crate::executor::proof_trust_surgery_provenance::{
    complement_of, OriginalSourceIndex, ProvenanceSurfaceAudit, SurgeryPlanningBudget,
    MAX_FARKAS_ATTEMPTS,
};
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor::Executor;

#[test]
fn conjunctive_or_chooses_first_replayed_surface_order_core_and_emits_strictly() {
    let mut fixture = four_branch_fixture();
    let plan = plan_fixture(&mut fixture);
    let expected_conjuncts = [
        equality(symbol("v0_1"), numeral("0")),
        equality(symbol("v0_1"), numeral("0")),
        equality(symbol("v1"), numeral("1")),
        equality(symbol("v0"), numeral("1")),
    ]
    .map(|surface| {
        fixture
            .executor
            .ctx
            .elaborate_surface_subterm(&surface)
            .expect("expected branch row elaborates")
    });
    assert_eq!(
        plan.refutations
            .iter()
            .map(|refutation| refutation.conjunct)
            .collect::<Vec<_>>(),
        expected_conjuncts.to_vec(),
        "D2 has two valid cores; the earlier v0_1 row must win deterministically",
    );
    let authored_positions = [3u32, 2, 1, 1];
    assert!(
        plan.refutations
            .iter()
            .zip(authored_positions)
            .any(|(refutation, surface_index)| refutation.index != surface_index),
        "the positive control must exercise authored order differing from canonical storage",
    );
    for refutation in &plan.refutations {
        let ay_core::TermData::App(_, conjuncts) =
            fixture.executor.ctx.terms.get(refutation.disjunct)
        else {
            panic!("authenticated branch is an AND");
        };
        assert_eq!(
            conjuncts.get(refutation.index as usize),
            Some(&refutation.conjunct),
            "stored AndPos index must remain the native canonical position",
        );
    }

    let mut proof = Proof::new();
    let mut assumes = HashMap::default();
    for &source in &plan.authored_sources {
        assumes.insert(source, proof.add_assume(source, None));
    }
    let terminal = fixture
        .executor
        .emit_provenance_or_and_conflict(&mut proof, &plan, &assumes)
        .expect("checked plan emits");
    assert_eq!(terminal.0 as usize, proof.steps.len() - 1);
    let not_goal = complement_of(&mut fixture.executor.ctx.terms, plan.goal);
    let downstream = proof.add_assume(not_goal, None);
    proof.add_resolution(Vec::new(), plan.goal, terminal, downstream);
    let quality = ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms)
        .expect("conjunctive OR refutation is strict");
    assert_eq!(quality.trust_count, 0);
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::Step {
                    rule: ay_core::AletheRule::AndPos(_),
                    ..
                }
            ))
            .count(),
        4,
    );

    let mut overrides = HashMap::default();
    let mut audit = ProvenanceSurfaceAudit::default();
    for (canonical, parsed) in &fixture.originals {
        assert!(collect_surface_term_overrides(
            &mut fixture.executor.ctx,
            *canonical,
            parsed,
            &mut overrides,
        ));
        assert!(audit.require_original(&mut fixture.executor.ctx, &fixture.originals, *canonical,));
    }
    ProvenanceOrPlan::ConjunctiveConflict(plan)
        .protect_surface_operands(&mut audit, &mut fixture.executor.ctx.terms);
    assert!(audit.validate_effective(&fixture.executor.ctx.terms, &overrides));
}

#[test]
fn conjunctive_goal_allows_authenticated_descendants_but_rejects_root_override() {
    let mut fixture = four_branch_fixture();
    let mut plan = plan_fixture(&mut fixture);
    declare(&mut fixture.executor, "root_only_reversed", "Int");
    let reversed_surface = equality(symbol("root_only_reversed"), numeral("1"));
    let reversed_equality = fixture
        .executor
        .ctx
        .elaborate_surface_subterm(&reversed_surface)
        .expect("fresh authored equality elaborates");
    let opposite_surface = equality(numeral("1"), symbol("root_only_reversed"));
    assert_eq!(
        fixture
            .executor
            .ctx
            .elaborate_surface_subterm(&opposite_surface),
        Some(reversed_equality),
        "reversed authored equality must retain the same canonical identity",
    );
    let canonical_equality =
        ay_proof::format_term_alethe(&fixture.executor.ctx.terms, reversed_equality);
    assert_ne!(format_frontend_term(&reversed_surface), canonical_equality);
    fixture
        .originals
        .push((reversed_equality, reversed_surface));
    let goal = fixture.executor.ctx.terms.mk_app(
        Symbol::named("or"),
        [reversed_equality, plan.goal],
        Sort::Bool,
    );
    plan.goal = goal;

    let mut effective = HashMap::default();
    let mut audit = ProvenanceSurfaceAudit::default();
    for (canonical, parsed) in &fixture.originals {
        assert!(collect_surface_term_overrides(
            &mut fixture.executor.ctx,
            *canonical,
            parsed,
            &mut effective,
        ));
        assert!(audit.require_original(&mut fixture.executor.ctx, &fixture.originals, *canonical,));
    }
    assert_ne!(
        effective.get(&reversed_equality),
        Some(&canonical_equality),
        "positive control needs an authenticated reversed equality descendant",
    );
    ProvenanceOrPlan::ConjunctiveConflict(plan)
        .protect_surface_operands(&mut audit, &mut fixture.executor.ctx.terms);
    assert!(audit.validate_effective(&fixture.executor.ctx.terms, &effective));

    let mut root_overridden = effective;
    root_overridden.insert(
        goal,
        ay_proof::format_term_alethe(&fixture.executor.ctx.terms, goal),
    );
    assert!(!audit.validate_effective(&fixture.executor.ctx.terms, &root_overridden));
}

#[test]
fn failed_direct_conjunct_attempts_consume_the_shared_farkas_budget() {
    let mut fixture = four_branch_fixture();
    let source_index = OriginalSourceIndex::new(&fixture.originals);
    let dummy = fixture
        .executor
        .ctx
        .terms
        .mk_var("and_or_attempt_dummy", Sort::Bool);
    let mut planning = SurgeryPlanningBudget::new();
    for _ in 1..MAX_FARKAS_ATTEMPTS {
        assert!(planning.spend_farkas_attempt(&fixture.executor.ctx.terms, &[dummy]));
    }
    assert!(fixture
        .executor
        .plan_provenance_or_and_conflict(
            &[fixture.goal],
            &fixture.originals,
            &source_index,
            &mut planning,
        )
        .is_none(),
        "the first unrelated arithmetic row spends the last attempt; the later conflict must decline",
    );
}

#[test]
fn conjunctive_or_surface_requires_flat_exact_unique_permutations() {
    let mut fixture = four_branch_fixture();
    let (orig, parsed) = &fixture.originals[0];
    let ay_core::TermData::App(_, disjuncts) = fixture.executor.ctx.terms.get(*orig).clone() else {
        panic!("fixture source is an OR");
    };
    assert!(exact_flat_and_or_surface_matches(
        &mut fixture.executor.ctx,
        parsed,
        &disjuncts,
    ));

    let FrontendTerm::App(_, surface_disjuncts) = parsed else {
        panic!("fixture source is parsed as OR");
    };
    let mut reordered = surface_disjuncts.clone();
    reordered.swap(0, 1);
    assert!(exact_flat_and_or_surface_matches(
        &mut fixture.executor.ctx,
        &app("or", reordered),
        &disjuncts,
    ));
    let mut reordered_children = surface_disjuncts.clone();
    let FrontendTerm::App(_, first_children) = &reordered_children[0] else {
        panic!("first branch is parsed as AND");
    };
    let mut first_children = first_children.clone();
    first_children.swap(0, 3);
    reordered_children[0] = app("and", first_children);
    assert!(exact_flat_and_or_surface_matches(
        &mut fixture.executor.ctx,
        &app("or", reordered_children),
        &disjuncts,
    ));
    let mut duplicated_disjunct = surface_disjuncts.clone();
    duplicated_disjunct[1] = duplicated_disjunct[0].clone();
    assert!(!exact_flat_and_or_surface_matches(
        &mut fixture.executor.ctx,
        &app("or", duplicated_disjunct),
        &disjuncts,
    ));
    let FrontendTerm::App(_, first_children) = &surface_disjuncts[0] else {
        panic!("first branch is parsed as AND");
    };
    let nested = app(
        "and",
        [
            app("and", first_children[..2].iter().cloned()),
            first_children[2].clone(),
            first_children[3].clone(),
        ],
    );
    let mut nested_disjuncts = surface_disjuncts.clone();
    nested_disjuncts[0] = nested;
    assert!(!exact_flat_and_or_surface_matches(
        &mut fixture.executor.ctx,
        &app("or", nested_disjuncts),
        &disjuncts,
    ));

    let FrontendTerm::App(_, duplicated_children) = &surface_disjuncts[1] else {
        panic!("second branch is parsed as AND");
    };
    let mut duplicated_children = duplicated_children.clone();
    duplicated_children[3] = duplicated_children[0].clone();
    let mut duplicated_disjuncts = surface_disjuncts.clone();
    duplicated_disjuncts[1] = app("and", duplicated_children);
    assert!(!exact_flat_and_or_surface_matches(
        &mut fixture.executor.ctx,
        &app("or", duplicated_disjuncts),
        &disjuncts,
    ));
}

#[test]
fn conjunctive_or_rejects_multiple_exact_authored_or_sources() {
    let mut fixture = four_branch_fixture();
    let original_source_set: Vec<TermId> =
        fixture.originals.iter().map(|(term, _)| *term).collect();
    fixture
        .executor
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("fixture provenance exists")
        .assertion_sources
        .insert(
            fixture.goal,
            vec![original_source_set.clone(), original_source_set.clone()],
        );
    let original_index = OriginalSourceIndex::new(&fixture.originals);
    assert!(fixture
        .executor
        .plan_provenance_or_and_conflict(
            &[fixture.goal],
            &fixture.originals,
            &original_index,
            &mut SurgeryPlanningBudget::new(),
        )
        .is_none());
    fixture
        .executor
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("fixture provenance exists")
        .assertion_sources
        .insert(fixture.goal, vec![original_source_set]);

    let parsed_second = fixture.originals[0].1.clone();
    let FrontendTerm::App(_, branches) = &parsed_second else {
        panic!("fixture source is parsed as OR");
    };
    let mut branches = branches.clone();
    let FrontendTerm::App(_, first_branch) = &branches[0] else {
        panic!("fixture branch is parsed as AND");
    };
    let mut first_branch = first_branch.clone();
    first_branch[1] = symbol("p");
    branches[0] = app("and", first_branch);
    let parsed_second = app("or", branches);
    let second = fixture
        .executor
        .ctx
        .elaborate_surface_subterm(&parsed_second)
        .expect("second exact OR elaborates");
    assert_ne!(second, fixture.originals[0].0);
    fixture.originals.push((second, parsed_second));
    let source_set: Vec<TermId> = fixture.originals.iter().map(|(term, _)| *term).collect();
    fixture
        .executor
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("fixture provenance exists")
        .assertion_sources
        .insert(fixture.goal, vec![source_set]);
    let index = OriginalSourceIndex::new(&fixture.originals);
    assert!(fixture
        .executor
        .plan_provenance_or_and_conflict(
            &[fixture.goal],
            &fixture.originals,
            &index,
            &mut SurgeryPlanningBudget::new(),
        )
        .is_none());
}

#[test]
fn conjunct_rows_colliding_with_authored_supports_do_not_gain_authority() {
    let mut executor = Executor::new();
    for name in ["cx", "cy"] {
        declare(&mut executor, name, "Int");
    }
    for name in ["cp", "cq"] {
        declare(&mut executor, name, "Bool");
    }
    let sx = equality(symbol("cx"), numeral("0"));
    let sy = equality(symbol("cy"), numeral("0"));
    let parsed_or = app(
        "or",
        [
            app("and", [sx.clone(), symbol("cp")]),
            app("and", [sy.clone(), symbol("cq")]),
        ],
    );
    let orig = executor
        .ctx
        .elaborate_surface_subterm(&parsed_or)
        .expect("collision OR elaborates");
    let sx_term = executor
        .ctx
        .elaborate_surface_subterm(&sx)
        .expect("x support elaborates");
    let sy_term = executor
        .ctx
        .elaborate_surface_subterm(&sy)
        .expect("y support elaborates");
    let originals = vec![(orig, parsed_or), (sx_term, sx), (sy_term, sy)];
    let g0 = executor.ctx.terms.mk_var("collision_g0", Sort::Bool);
    let g1 = executor.ctx.terms.mk_var("collision_g1", Sort::Bool);
    let goal = executor.ctx.terms.mk_or(vec![g0, g1]);
    let source_set = vec![orig, sx_term, sy_term];
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(goal, vec![source_set.clone()]);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: source_set.clone(),
        problem_assertions: source_set,
        assertion_sources,
    });
    let source_index = OriginalSourceIndex::new(&originals);
    assert!(executor
        .plan_provenance_or_and_conflict(
            &[goal],
            &originals,
            &source_index,
            &mut SurgeryPlanningBudget::new(),
        )
        .is_none());
}

#[test]
fn malformed_conjunctive_plan_declines_before_mutating_proof() {
    let mut fixture = four_branch_fixture();
    let mut plan = plan_fixture(&mut fixture);
    let first_disjunct = plan.refutations[0].disjunct;
    let first_index = plan.refutations[0].index;
    let ay_core::TermData::App(_, conjuncts) = fixture.executor.ctx.terms.get(first_disjunct)
    else {
        panic!("fixture branch is an AND");
    };
    plan.refutations[0].index = ((first_index as usize + 1) % conjuncts.len()) as u32;
    let mut proof = Proof::new();
    let marker = proof.add_assume(fixture.goal, None);
    let before = format!("{:?}", proof.steps);
    let mut assumes = HashMap::default();
    for &source in &plan.authored_sources {
        assumes.insert(source, marker);
    }
    assert!(fixture
        .executor
        .emit_provenance_or_and_conflict(&mut proof, &plan, &assumes)
        .is_none());
    assert_eq!(format!("{:?}", proof.steps), before);
}
