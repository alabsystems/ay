// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-collision and admission controls use the production helpers and
//! real assumption solver; no mocked verdict grants a core or proof claim.

use super::*;
use crate::pdr::config::PdrConfig;
use crate::pdr::solver::spacer_core::oracle::ProxiedOutcome;
use crate::pdr::solver::PdrSolver;
use crate::smt::{SmtContext, SmtResult};
use crate::{CancellationToken, ChcDtConstructor, ChcDtSelector, ChcProblem, ChcVar, PredicateId};
use std::sync::{atomic::AtomicBool, Arc};
use std::time::Duration;

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn p(index: usize) -> ChcExpr {
    var(
        &format!("{}{index}", super::super::PROXY_PREFIX),
        ChcSort::Bool,
    )
}

fn solver() -> PdrSolver {
    PdrSolver::new(
        ChcProblem::new(),
        PdrConfig {
            verbose: false,
            ..PdrConfig::default()
        },
    )
}

#[test]
fn a_source_proxy_spelling_under_negation_and_true_is_really_sat() {
    let bg = [ChcExpr::not(p(0))];
    let lits = [ChcExpr::Bool(true)];
    let original = SmtContext::new().check_sat_with_assumption_conjuncts(&bg, &lits);
    assert!(
        matches!(original, SmtResult::Sat(_)),
        "original query is SAT: {original:?}"
    );
    let result = solver().proxied_assumption_solve(&bg, &lits, None);
    assert!(
        matches!(result, ProxiedOutcome::Sat(_)),
        "fresh proxy must preserve SAT"
    );
    assert_eq!(
        fresh(&bg, &lits, &mut Admission::new(), &mut || true),
        Some(vec![p(1)])
    );
}

#[test]
fn fresh_proxies_preserve_a_real_unsat_literal_and_a_background_refutation() {
    let bg = [ChcExpr::not(p(0))];
    let result = solver().proxied_assumption_solve(&bg, &[p(0)], None);
    assert!(matches!(result, ProxiedOutcome::Unsat { core, exact: true } if core == vec![true]));
    let contradiction = [p(0), ChcExpr::not(p(0))];
    let result = solver().proxied_assumption_solve(&contradiction, &[ChcExpr::Bool(true)], None);
    assert!(matches!(result, ProxiedOutcome::UnsatEmpty));
}

#[test]
fn occupied_slots_and_prefix_variants_do_not_determine_core_indices() {
    let bg = [
        p(0),
        p(2),
        var("__sc_lit_01", ChcSort::Bool),
        var("__sc_lit_", ChcSort::Bool),
    ];
    let lits = [p(4), ChcExpr::Bool(true)];
    let mut credit = Admission::new();
    let proxies = fresh(&bg, &lits, &mut credit, &mut || true).unwrap();
    assert_eq!(proxies, vec![p(1), p(3)]);
    assert_eq!(
        map(&[p(3), p(3)], &proxies, &mut credit, &mut || true),
        Some(vec![false, true])
    );
}

#[test]
fn variables_functions_predicates_and_testers_all_reserve_their_spelling() {
    let bg = [
        var("__sc_lit_0", ChcSort::Int),
        ChcExpr::FuncApp("__sc_lit_1".into(), ChcSort::Int, vec![Arc::new(p(2))]),
        ChcExpr::PredicateApp(
            "__sc_lit_3".into(),
            PredicateId::new(0),
            vec![Arc::new(p(4))],
        ),
        ChcExpr::IsTesterMarker("__sc_lit_5".into()),
    ];
    assert_eq!(
        fresh(
            &bg,
            &[ChcExpr::Bool(true)],
            &mut Admission::new(),
            &mut || true
        ),
        Some(vec![p(6)])
    );
}

#[test]
fn nominal_datatype_constructor_selector_and_nested_array_sorts_are_reserved() {
    let sort = ChcSort::Datatype {
        name: "__sc_lit_0".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "__sc_lit_1".into(),
            selectors: vec![ChcDtSelector {
                name: "__sc_lit_2".into(),
                sort: ChcSort::Array(
                    Box::new(ChcSort::Int),
                    Box::new(ChcSort::Uninterpreted("__sc_lit_3".into())),
                ),
            }],
        }]),
    };
    let bg = [
        ChcExpr::ConstArrayMarker(sort),
        ChcExpr::ConstArray(ChcSort::Uninterpreted("__sc_lit_4".into()), Arc::new(p(5))),
    ];
    assert_eq!(
        fresh(
            &bg,
            &[ChcExpr::Bool(true)],
            &mut Admission::new(),
            &mut || true
        ),
        Some(vec![p(6)])
    );
}

#[test]
fn a_deep_shared_dag_is_censused_without_depth_cutoffs_or_tree_expansion() {
    let mut shared = Arc::new(p(0));
    for _ in 0..800 {
        shared = Arc::new(ChcExpr::Op(
            crate::ChcOp::And,
            vec![Arc::clone(&shared), Arc::clone(&shared)],
        ));
    }
    let bg = [ChcExpr::Op(
        crate::ChcOp::And,
        vec![Arc::clone(&shared), Arc::clone(&shared)],
    )];
    assert_eq!(
        fresh(
            &bg,
            &[ChcExpr::Bool(true)],
            &mut Admission::new(),
            &mut || true
        ),
        Some(vec![p(1)])
    );
    // ChcExpr's production destructor drains children iteratively, including
    // a shared DAG's last reference; moving its fields out would bypass Drop.
    drop(bg);
    drop(shared);
}

#[test]
fn foreign_wrong_sort_and_malformed_core_terms_refuse_instead_of_emptying() {
    let proxies = [p(5), p(8)];
    for core in [
        vec![p(0)],
        vec![var("__sc_lit_05", ChcSort::Bool)],
        vec![var("__sc_lit_5", ChcSort::Int)],
        vec![ChcExpr::not(p(5))],
    ] {
        let mut credit = Admission::new();
        assert_eq!(map(&core, &proxies, &mut credit, &mut || true), None);
        assert_eq!(
            map(&[], &proxies, &mut credit, &mut || true),
            None,
            "refusal is sticky"
        );
    }
    assert_eq!(
        map(&[], &proxies, &mut Admission::new(), &mut || true),
        Some(vec![false, false])
    );
}

#[test]
fn cancellation_inside_a_long_name_is_polled_and_stays_refused() {
    let bg = [var(&"n".repeat(10_000), ChcSort::Bool)];
    let mut polls = 0;
    let mut credit = Admission::new();
    let result = fresh(&bg, &[ChcExpr::Bool(true)], &mut credit, &mut || {
        polls += 1;
        polls < 200
    });
    assert!(result.is_none());
    assert_eq!(polls, 200);
    assert_eq!(
        fresh(&[], &[ChcExpr::Bool(true)], &mut credit, &mut || true),
        None
    );
}

#[test]
fn source_census_exhaustion_never_returns_a_partial_namespace() {
    let bg = [var(
        &"x".repeat(crate::expr::MAX_PREPROCESSING_NODES),
        ChcSort::Bool,
    )];
    let mut credit = Admission::new();
    assert_eq!(
        fresh(&bg, &[ChcExpr::Bool(true)], &mut credit, &mut || true),
        None
    );
    assert_eq!(map(&[], &[], &mut credit, &mut || true), None);
}

#[test]
fn attribution_uses_the_remaining_preparation_credit_not_a_new_budget() {
    let mut credit = Admission::new();
    let proxies = fresh(&[], &[ChcExpr::Bool(true)], &mut credit, &mut || true).unwrap();
    // Exhaust the ACTUAL shared ledger, rather than a fresh mapping allowance.
    let remaining = credit.remaining.unwrap();
    credit.spend(remaining, &mut || true).unwrap();
    assert_eq!(map(&proxies, &proxies, &mut credit, &mut || true), None);
}

#[test]
fn precancelled_and_expired_queries_never_enter_the_smt_oracle() {
    let token = CancellationToken::new();
    token.cancel();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    }
    .with_cancellation_token(Some(token));
    let mut cancelled = PdrSolver::new(ChcProblem::new(), config);
    assert!(matches!(
        cancelled.proxied_assumption_solve(&[], &[ChcExpr::Bool(true)], None),
        ProxiedOutcome::Unknown
    ));
    assert_eq!(cancelled.spacer_stats.smt_solves_total, 0);
    let mut expired = solver();
    let deadline = ay_core::time::Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("fixture instant supports a one-millisecond offset");
    assert!(matches!(
        expired.proxied_assumption_solve(&[], &[ChcExpr::Bool(true)], Some(deadline)),
        ProxiedOutcome::Unknown
    ));
    assert_eq!(expired.spacer_stats.smt_solves_total, 0);
}

#[test]
fn an_existing_memory_soft_trip_refuses_before_smt_entry() {
    let mut solver = solver();
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _scope = ay_sys::enter_memory_group(group);
    ay_sys::charge_current_for_testing(2 * 1024 * 1024);
    assert!(matches!(
        solver.proxied_assumption_solve(&[], &[ChcExpr::Bool(true)], None),
        ProxiedOutcome::Unknown
    ));
    assert_eq!(solver.spacer_stats.smt_solves_total, 0);
}

#[test]
fn recursive_sort_cloning_is_refused_before_the_existing_depth_boundary() {
    let mut sort = ChcSort::Int;
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH {
        sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(sort));
    }
    let root = var("a", sort);
    assert_eq!(Admission::new().root_copy(&root, &mut || true), None);
}
