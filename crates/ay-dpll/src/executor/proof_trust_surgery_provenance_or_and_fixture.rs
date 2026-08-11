// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test fixture for conjunctive provenance-OR repair.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId};
use ay_frontend::command::{Command, Constant, Sort as FrontendSort, Term as FrontendTerm};

use super::{ProvenanceOrAndConflictPlan, ProvenanceOrPlan};
use crate::executor::proof_trust_surgery_provenance::{
    complement_of, OriginalSourceIndex, SurgeryPlanningBudget,
};
use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor::Executor;

pub(super) fn symbol(name: &str) -> FrontendTerm {
    FrontendTerm::Symbol(name.to_string())
}

pub(super) fn numeral(value: &str) -> FrontendTerm {
    FrontendTerm::Const(Constant::Numeral(value.to_string()))
}

pub(super) fn app(head: &str, operands: impl IntoIterator<Item = FrontendTerm>) -> FrontendTerm {
    FrontendTerm::App(head.to_string(), operands.into_iter().collect())
}

pub(super) fn equality(left: FrontendTerm, right: FrontendTerm) -> FrontendTerm {
    app("=", [left, right])
}

pub(super) fn declare(executor: &mut Executor, name: &str, sort: &str) {
    executor
        .ctx
        .process_command(&Command::DeclareConst(
            name.to_string(),
            FrontendSort::Simple(sort.to_string()),
        ))
        .expect("fixture declaration succeeds");
}

pub(super) struct Fixture {
    pub(super) executor: Executor,
    pub(super) goal: TermId,
    pub(super) not_goal: TermId,
    pub(super) originals: Vec<(TermId, FrontendTerm)>,
    pub(super) provenance_sources: Vec<TermId>,
    pub(super) problem_scope: Vec<TermId>,
}

pub(super) fn four_branch_fixture() -> Fixture {
    let mut executor = Executor::new();
    for name in ["v0", "v1", "v0_1", "v1_1"] {
        declare(&mut executor, name, "Int");
    }
    for name in ["p", "q", "r", "and_or_goal_left", "and_or_goal_right"] {
        declare(&mut executor, name, "Bool");
    }
    let eq = |name: &str, value: &str| equality(symbol(name), numeral(value));
    let nested_or = app("or", [symbol("p"), symbol("q")]);
    let nested_ite = app("ite", [symbol("p"), symbol("q"), symbol("r")]);
    let branches = vec![
        app(
            "and",
            [
                eq("v0", "0"),
                nested_ite.clone(),
                eq("v1_1", "1"),
                eq("v0_1", "0"),
            ],
        ),
        app(
            "and",
            [
                eq("v0", "0"),
                eq("v1_1", "1"),
                eq("v0_1", "0"),
                eq("v1", "1"),
            ],
        ),
        app("and", [nested_or, eq("v1", "1"), eq("v0_1", "1")]),
        app("and", [nested_ite, eq("v0", "1"), eq("v1_1", "1")]),
    ];
    let parsed_or = app("or", branches);
    let orig = executor
        .ctx
        .elaborate_surface_subterm(&parsed_or)
        .expect("authored OR elaborates");
    let parsed_supports = vec![eq("v0", "0"), eq("v1", "0"), eq("v0_1", "1")];
    let mut originals = vec![(orig, parsed_or)];
    for parsed in parsed_supports {
        let canonical = executor
            .ctx
            .elaborate_surface_subterm(&parsed)
            .expect("support elaborates");
        originals.push((canonical, parsed));
    }

    let left = executor
        .ctx
        .elaborate_surface_subterm(&symbol("and_or_goal_left"))
        .expect("declared left goal symbol elaborates");
    let right = executor
        .ctx
        .elaborate_surface_subterm(&symbol("and_or_goal_right"))
        .expect("declared right goal symbol elaborates");
    assert_eq!(*executor.ctx.terms.sort(left), Sort::Bool);
    assert_eq!(*executor.ctx.terms.sort(right), Sort::Bool);
    let goal = executor.ctx.terms.mk_or(vec![left, right]);
    // Keep this as the raw complement used by the native Resolution rule.
    // Frontend elaboration of `(not (or ...))` would De-Morgan the term and
    // therefore would not authorize the same proof pivot.
    let not_goal = complement_of(&mut executor.ctx.terms, goal);

    let provenance_sources: Vec<TermId> = originals.iter().map(|(term, _)| *term).collect();
    let mut problem_scope = provenance_sources.clone();
    problem_scope.push(not_goal);
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(goal, vec![provenance_sources.clone()]);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: problem_scope.clone(),
        problem_assertions: problem_scope.clone(),
        assertion_sources,
    });
    Fixture {
        executor,
        goal,
        not_goal,
        originals,
        provenance_sources,
        problem_scope,
    }
}

/// Route through the production dispatcher and require this fixture to select
/// the conjunctive-conflict lane rather than a legacy OR repair.
pub(super) fn plan_fixture(fixture: &mut Fixture) -> ProvenanceOrAndConflictPlan {
    let source_index = OriginalSourceIndex::new(&fixture.originals);
    let mut planning = SurgeryPlanningBudget::new();
    match fixture.executor.plan_provenance_or(
        &[fixture.goal],
        &fixture.originals,
        &source_index,
        &mut planning,
    ) {
        Some(ProvenanceOrPlan::ConjunctiveConflict(plan)) => plan,
        Some(_) => panic!("fixture must select conjunctive provenance-OR conflict"),
        None => panic!("all four authenticated branches have exact arithmetic conflicts"),
    }
}
