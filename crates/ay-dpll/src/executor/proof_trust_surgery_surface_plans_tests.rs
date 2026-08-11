// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Defined-ITE coverage for both retained-surface plan lanes.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, Symbol, TermId};
use ay_frontend::command::{
    Command, Constant as FrontendConstant, Sort as FrontendSort, Term as FrontendTerm,
};

use super::*;
use crate::executor::proof_repair::proof_trust_surgery_ite::ProvenanceIteSource;
use crate::executor::proof_repair::proof_trust_surgery_provenance::{
    OriginalSourceIndex, SurgeryPlanningBudget,
};
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;

struct DefinedFixture {
    originals: Vec<(TermId, FrontendTerm)>,
    active: HashMap<TermId, String>,
    source: TermId,
    bound: TermId,
    goal: TermId,
}

fn declare_int(executor: &mut Executor, name: &str) -> TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(
            name.to_string(),
            FrontendSort::Simple("Int".to_string()),
        ))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

fn symbol(name: &str) -> FrontendTerm {
    FrontendTerm::Symbol(name.to_string())
}

fn app(head: &str, operands: Vec<FrontendTerm>) -> FrontendTerm {
    FrontendTerm::App(head.to_string(), operands)
}

fn defined_fixture(executor: &mut Executor) -> DefinedFixture {
    for name in ["plan_i", "plan_j", "plan_e", "plan_f"] {
        let _ = declare_int(executor, name);
    }
    let parsed = app(
        "=",
        vec![
            symbol("plan_i"),
            app(
                "ite",
                vec![
                    app(
                        "=",
                        vec![
                            symbol("plan_j"),
                            FrontendTerm::Const(FrontendConstant::Numeral("1".to_string())),
                        ],
                    ),
                    app("+", vec![symbol("plan_e"), symbol("plan_f")]),
                    symbol("plan_e"),
                ],
            ),
        ],
    );
    let source = executor
        .ctx
        .elaborate_surface_subterm(&parsed)
        .expect("defining equality elaborates");
    let orig = executor
        .raw_intern_surface(&parsed)
        .expect("defining equality raw-interns");
    assert_ne!(source, orig);
    let TermData::App(Symbol::Named(op), sides) = executor.ctx.terms.get(orig).clone() else {
        panic!("raw source must be an equality")
    };
    assert_eq!(op, "=");
    let [defined, ite_term] = sides.as_slice() else {
        panic!("raw source must be binary")
    };
    let (defined, ite_term) = (*defined, *ite_term);
    let TermData::Ite(cond, then_term, else_term) = *executor.ctx.terms.get(ite_term) else {
        panic!("raw source must name an ITE")
    };
    let bound_parsed = app(
        "<",
        vec![
            symbol("plan_i"),
            FrontendTerm::Const(FrontendConstant::Numeral("0".to_string())),
        ],
    );
    let bound = executor
        .ctx
        .elaborate_surface_subterm(&bound_parsed)
        .expect("authored arithmetic bound elaborates");
    let lifted_then = executor
        .ctx
        .terms
        .substitute(bound, &[defined], &[then_term]);
    let lifted_else = executor
        .ctx
        .terms
        .substitute(bound, &[defined], &[else_term]);
    let goal = executor
        .ctx
        .terms
        .mk_ite_raw(cond, lifted_then, lifted_else);
    assert_ne!(source, goal);

    let mut active = HashMap::default();
    for (canonical, surface) in [(source, &parsed), (bound, &bound_parsed)] {
        assert!(
            crate::executor::proof_surface_syntax::collect_surface_term_overrides(
                &mut executor.ctx,
                canonical,
                surface,
                &mut active,
            )
        );
    }
    DefinedFixture {
        originals: vec![(source, parsed), (bound, bound_parsed)],
        active,
        source,
        bound,
        goal,
    }
}

fn finish_audit(
    executor: &mut Executor,
    audit: ProvenanceSurfaceAudit,
    mut effective: HashMap<TermId, String>,
    fixture: &DefinedFixture,
) {
    let mut old_proof = Proof::new();
    old_proof.add_assume(fixture.bound, None);
    old_proof.add_rule_step(
        AletheRule::Trust,
        vec![fixture.goal],
        Vec::new(),
        Vec::new(),
    );
    assert!(audit.aliases_are_fresh_in(&old_proof, &executor.ctx.terms));
    assert!(audit.merge_into(&mut effective));
    assert!(audit.validate_effective(&executor.ctx.terms, &effective));
}

#[test]
fn legacy_defined_ite_plan_registers_its_raw_equality_as_arithmetic() {
    let mut executor = Executor::new();
    let fixture = defined_fixture(&mut executor);
    let source_index = OriginalSourceIndex::new(&fixture.originals);
    let mut planning = SurgeryPlanningBudget::new();
    let plan = executor
        .plan_ite_lift(
            &[fixture.goal],
            &fixture.originals,
            &source_index,
            &mut planning,
        )
        .expect("legacy planner recognizes the Defined source and bound");
    assert_eq!(plan.defining_source, Some(fixture.source));
    assert_eq!(plan.bound, Some(fixture.bound));
    assert!(executor.quad_lemma_valid(plan.eq_then, plan.orig, fixture.bound, plan.lifted_then,));
    assert!(executor.quad_lemma_valid(plan.eq_else, plan.orig, fixture.bound, plan.lifted_else,));
    let mut plans = HashMap::default();
    plans.insert(0, plan);
    let audit = executor
        .plan_retained_surface_audit(
            &fixture.originals,
            &plans,
            &HashMap::default(),
            &HashMap::default(),
            &HashMap::default(),
            &HashMap::default(),
            &HashMap::default(),
        )
        .expect("legacy Defined source is accepted");
    finish_audit(&mut executor, audit, fixture.active.clone(), &fixture);
}

#[test]
fn provenance_defined_ite_plan_registers_its_raw_equality_as_arithmetic() {
    let mut executor = Executor::new();
    let fixture = defined_fixture(&mut executor);
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(fixture.goal, vec![vec![fixture.source, fixture.bound]]);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: vec![fixture.source, fixture.bound],
        problem_assertions: vec![fixture.source, fixture.bound],
        assertion_sources,
    });
    let source_index = OriginalSourceIndex::new(&fixture.originals);
    let mut planning = SurgeryPlanningBudget::new();
    let plan = executor
        .plan_provenance_ite_lift(
            &[fixture.goal],
            &fixture.originals,
            &source_index,
            &mut planning,
        )
        .expect("provenance planner recognizes the Defined source and support");
    assert_eq!(plan.defining_source, Some(fixture.source));
    assert_eq!(plan.supports, [fixture.bound]);
    assert!(matches!(&plan.source, ProvenanceIteSource::Defined { .. }));
    let mut plans = HashMap::default();
    plans.insert(0, plan);
    let audit = executor
        .plan_retained_surface_audit(
            &fixture.originals,
            &HashMap::default(),
            &plans,
            &HashMap::default(),
            &HashMap::default(),
            &HashMap::default(),
            &HashMap::default(),
        )
        .expect("provenance Defined source is accepted");
    finish_audit(&mut executor, audit, fixture.active.clone(), &fixture);
}
