// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused planning, emission, and boundary tests for conjunctive transfer.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermId};

use super::super::and_conflict_fixture::{app, declare, equality, numeral, symbol};
use super::super::ProvenanceOrPlan;
use super::{ProvenanceOrAndTransferOutcome, ProvenanceOrAndTransferPlan};
use crate::executor::proof_surface_syntax::collect_surface_term_overrides;
use crate::executor::proof_trust_surgery_provenance::{
    complement_of, OriginalSourceIndex, ProvenanceSurfaceAudit, SurgeryPlanningBudget,
};
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor::Executor;

pub(super) struct TransferFixture {
    pub(super) executor: Executor,
    pub(super) goal: TermId,
    pub(super) not_goal: TermId,
    pub(super) originals: Vec<(TermId, ay_frontend::command::Term)>,
    pub(super) problem_scope: Vec<TermId>,
}

pub(super) fn transfer_fixture() -> TransferFixture {
    let mut executor = Executor::new();
    for name in ["transfer_x", "transfer_y"] {
        declare(&mut executor, name, "Int");
    }
    for name in ["transfer_p", "transfer_q"] {
        declare(&mut executor, name, "Bool");
    }
    let sx = equality(symbol("transfer_x"), numeral("0"));
    let sy = equality(symbol("transfer_y"), numeral("0"));
    let x1 = equality(symbol("transfer_x"), numeral("1"));
    let parsed_orig = app(
        "or",
        [
            app("and", [sx.clone(), sy.clone(), symbol("transfer_p")]),
            app("and", [x1, symbol("transfer_q")]),
        ],
    );
    let orig = executor
        .ctx
        .elaborate_surface_subterm(&parsed_orig)
        .expect("source OR elaborates");
    let sx_id = executor
        .ctx
        .elaborate_surface_subterm(&sx)
        .expect("x support elaborates");
    let sy_id = executor
        .ctx
        .elaborate_surface_subterm(&sy)
        .expect("y support elaborates");
    let p = executor
        .ctx
        .elaborate_surface_subterm(&symbol("transfer_p"))
        .expect("p elaborates");
    let q = executor
        .ctx
        .elaborate_surface_subterm(&symbol("transfer_q"))
        .expect("q elaborates");
    let truth = executor.ctx.terms.mk_bool(true);
    let falsity = executor.ctx.terms.mk_bool(false);
    let mapped = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [truth, truth, p], Sort::Bool);
    let impossible = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [falsity, q], Sort::Bool);
    let goal = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), [mapped, impossible], Sort::Bool);
    let not_goal = complement_of(&mut executor.ctx.terms, goal);
    let originals = vec![(orig, parsed_orig), (sx_id, sx), (sy_id, sy)];
    let provenance_sources = vec![orig, sx_id, sy_id];
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(goal, vec![provenance_sources.clone()]);
    let mut problem_scope = provenance_sources;
    problem_scope.push(not_goal);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: problem_scope.clone(),
        problem_assertions: problem_scope.clone(),
        assertion_sources,
    });
    TransferFixture {
        executor,
        goal,
        not_goal,
        originals,
        problem_scope,
    }
}

pub(super) fn plan_fixture(fixture: &mut TransferFixture) -> ProvenanceOrAndTransferPlan {
    let source_index = OriginalSourceIndex::new(&fixture.originals);
    match fixture.executor.plan_provenance_or(
        &[fixture.goal],
        &fixture.originals,
        &source_index,
        &mut SurgeryPlanningBudget::new(),
    ) {
        Some(ProvenanceOrPlan::ConjunctiveTransfer(plan)) => plan,
        Some(_) => panic!("fixture must select conjunctive transfer"),
        None => panic!("one branch maps and one branch has an exact conflict"),
    }
}

pub(super) fn proof_vector_volume(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .map(|step| match step {
            ProofStep::Assume(_) => 1,
            ProofStep::Resolution { clause, .. } => clause.len(),
            ProofStep::Step { clause, args, .. } => clause.len() + args.len(),
            ProofStep::TheoryLemma { clause, farkas, .. } => {
                clause.len()
                    + farkas
                        .as_ref()
                        .map_or(0, |annotation| annotation.coefficients.len())
            }
            _ => 0,
        })
        .sum()
}

#[test]
fn support_to_true_transfer_emits_exact_strict_residuals() {
    let mut fixture = transfer_fixture();
    let plan = plan_fixture(&mut fixture);
    assert_eq!(plan.outcomes.len(), 2);
    assert!(matches!(
        &plan.outcomes[0],
        ProvenanceOrAndTransferOutcome::Map(_)
    ));
    assert!(matches!(
        &plan.outcomes[1],
        ProvenanceOrAndTransferOutcome::Refute(_)
    ));
    let ProvenanceOrAndTransferOutcome::Map(mapping) = &plan.outcomes[0] else {
        unreachable!()
    };
    assert!(mapping.has_true);
    assert_eq!(
        mapping
            .target_children
            .iter()
            .filter(|&&term| matches!(
                fixture.executor.ctx.terms.get(term),
                ay_core::TermData::Const(ay_core::Constant::Bool(true))
            ))
            .count(),
        2,
        "duplicate true children remain load-bearing in and_neg",
    );

    let mut proof = Proof::new();
    let mut assumes = HashMap::default();
    for &source in &plan.authored_sources {
        assumes.insert(source, proof.add_assume(source, None));
    }
    let terminal = fixture
        .executor
        .emit_provenance_or_and_transfer(&mut proof, &plan, &assumes)
        .expect("checked transfer emits");
    assert_eq!(
        proof_vector_volume(&proof),
        plan.emitted_literal_volume()
            .expect("checked plan has bounded vector volume"),
        "preflight must count every emitted clause, certificate, and argument",
    );
    let close = proof.add_assume(fixture.not_goal, None);
    proof.add_resolution(Vec::new(), fixture.goal, terminal, close);
    let quality = ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms)
        .expect("transfer proof is strict");
    assert_eq!(quality.trust_count, 0);
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::AndNeg,
                    ..
                }
            ))
            .count(),
        1,
    );
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
    );

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
    ProvenanceOrPlan::ConjunctiveTransfer(plan)
        .protect_surface_operands(&mut audit, &mut fixture.executor.ctx.terms);
    assert!(audit.validate_effective(&fixture.executor.ctx.terms, &effective));
    let truth = fixture.executor.ctx.terms.mk_bool(true);
    effective.insert(truth, "(= 0 0)".to_string());
    assert!(
        !audit.validate_effective(&fixture.executor.ctx.terms, &effective),
        "the emitted true unit must reject a noncanonical active spelling",
    );
    effective.remove(&truth);
    effective.insert(
        fixture.goal,
        ay_proof::format_term_alethe(&fixture.executor.ctx.terms, fixture.goal),
    );
    assert!(
        !audit.validate_effective(&fixture.executor.ctx.terms, &effective),
        "a direct goal override must not mask authenticated descendants",
    );
}

#[test]
fn tampered_transfer_declines_before_proof_mutation() {
    let mut fixture = transfer_fixture();
    let mut plan = plan_fixture(&mut fixture);
    let ProvenanceOrAndTransferOutcome::Map(mapping) = &mut plan.outcomes[0] else {
        panic!("first branch maps");
    };
    mapping.target_children.pop();
    let mut proof = Proof::new();
    let marker = proof.add_assume(fixture.goal, None);
    let before = format!("{:?}", proof.steps);
    let assumes = plan
        .authored_sources
        .iter()
        .copied()
        .map(|source| (source, marker))
        .collect();
    assert!(fixture
        .executor
        .emit_provenance_or_and_transfer(&mut proof, &plan, &assumes)
        .is_none());
    assert_eq!(format!("{:?}", proof.steps), before);
}

#[test]
fn transfer_rejects_two_distinct_target_permutations_for_one_source_branch() {
    let mut fixture = transfer_fixture();
    let plan = plan_fixture(&mut fixture);
    let ProvenanceOrAndTransferOutcome::Map(mapping) = &plan.outcomes[0] else {
        panic!("first branch maps");
    };
    let mut reordered_children = mapping.target_children.clone();
    reordered_children.rotate_left(1);
    let reordered =
        fixture
            .executor
            .ctx
            .terms
            .mk_app(Symbol::named("and"), reordered_children, Sort::Bool);
    assert_ne!(reordered, mapping.target);
    let other_target = plan
        .target_disjuncts
        .iter()
        .copied()
        .find(|target| *target != mapping.target)
        .expect("fixture has an unmatched false target");
    let ambiguous_goal = fixture.executor.ctx.terms.mk_app(
        Symbol::named("or"),
        [mapping.target, reordered, other_target],
        Sort::Bool,
    );
    let source_set: Vec<_> = fixture.originals.iter().map(|(term, _)| *term).collect();
    fixture
        .executor
        .proof_problem_assertion_provenance
        .as_mut()
        .unwrap()
        .assertion_sources
        .insert(ambiguous_goal, vec![source_set]);
    let source_index = OriginalSourceIndex::new(&fixture.originals);
    assert!(fixture
        .executor
        .plan_provenance_or_and_transfer(
            &[ambiguous_goal],
            &fixture.originals,
            &source_index,
            &mut SurgeryPlanningBudget::new(),
        )
        .is_none());
}
