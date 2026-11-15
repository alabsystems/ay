// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rung 0 (CHC-COMP 2026) bridge-hygiene regression locks: the SMT lane pin,
//! sort-unique executor declarations, the Search-lane EqDiffVar policy, and
//! the post-deadline refusal.

use super::sort_unique::SortUniqueRenaming;
use super::{ScopedSmtDeadline, SmtContext, SmtLane, SmtResult, SmtValue};
use crate::expr::lookup_model_value;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

fn ivar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn bvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

#[test]
fn default_contexts_are_verification_lane_and_engines_opt_into_search() {
    assert_eq!(SmtContext::new().lane(), SmtLane::Verification);
    assert_eq!(SmtContext::default().lane(), SmtLane::Verification);
    assert_eq!(SmtContext::new_search().lane(), SmtLane::Search);
    let problem = crate::ChcProblem::new();
    assert_eq!(problem.make_smt_context().lane(), SmtLane::Verification);
    assert_eq!(problem.make_search_smt_context().lane(), SmtLane::Search);
    // Every validator builds `PdrConfig { strict_proofs: true, ..Default }`
    // and `BmcConfig::default()`; both must land on the Verification lane.
    assert_eq!(crate::PdrConfig::default().smt_lane, SmtLane::Verification);
    assert_eq!(crate::BmcConfig::default().smt_lane, SmtLane::Verification);
    let verifier = crate::PdrSolver::new(
        crate::ChcProblem::new(),
        crate::PdrConfig {
            strict_proofs: true,
            ..crate::PdrConfig::default()
        },
    );
    assert_eq!(verifier.smt_lane(), SmtLane::Verification);
    let engine = crate::PdrSolver::new(
        crate::ChcProblem::new(),
        crate::PdrConfig::default().with_smt_lane(SmtLane::Search),
    );
    assert_eq!(engine.smt_lane(), SmtLane::Search);
    // `reset()` preserves the lane (engine-level policy, not query state).
    let mut smt = SmtContext::new_search();
    smt.reset();
    assert_eq!(smt.lane(), SmtLane::Search);
}

#[test]
fn search_lane_disables_eq_diffvar_and_verification_keeps_it() {
    assert!(SmtContext::new_search().executor_disables_eq_diffvar());
    assert!(!SmtContext::new().executor_disables_eq_diffvar());
}

#[test]
fn sort_unique_renaming_plan_qualifies_the_second_sort() {
    let vars = vec![
        ChcVar::new("J", ChcSort::Int),
        ChcVar::new("K", ChcSort::Int),
        ChcVar::new("J", ChcSort::Bool),
    ];
    let plan = SortUniqueRenaming::plan(&vars).expect("J clashes");
    assert_eq!(plan.len(), 1);
    let renamed = plan.renamed_vars(&vars);
    // Bool ranks before Int: `J:Bool` keeps `J`, `J:Int` becomes `J!Int`.
    assert_eq!(renamed[0], ChcVar::new("J!Int", ChcSort::Int));
    assert_eq!(renamed[1], ChcVar::new("K", ChcSort::Int));
    assert_eq!(renamed[2], ChcVar::new("J", ChcSort::Bool));
    let names: std::collections::HashSet<&str> = renamed.iter().map(|v| v.name.as_str()).collect();
    assert_eq!(names.len(), 3, "every name is sort-unique");
    // No clash -> no plan.
    assert!(SortUniqueRenaming::plan(&vars[..2]).is_none());
    // A session that already declared `J` as Int keeps it, whatever the rank.
    let plan =
        SortUniqueRenaming::plan_with_reserved(&vars, |n| (n == "J").then_some(ChcSort::Int))
            .expect("J clashes with the session");
    let renamed = plan.renamed_vars(&vars);
    assert_eq!(renamed[0], ChcVar::new("J", ChcSort::Int));
    assert_eq!(renamed[2], ChcVar::new("J!Bool", ChcSort::Bool));
    // `apply` renames only the qualified variable, in the body too.
    let expr = ChcExpr::and(ChcExpr::eq(ivar("J"), ChcExpr::Int(1)), bvar("J"));
    let out = SortUniqueRenaming::plan(&expr.vars())
        .expect("clash")
        .apply(&expr);
    let out_vars: Vec<ChcVar> = out.vars();
    assert!(
        out_vars.contains(&ChcVar::new("J!Int", ChcSort::Int)),
        "{out_vars:?}"
    );
    assert!(
        out_vars.contains(&ChcVar::new("J", ChcSort::Bool)),
        "{out_vars:?}"
    );
    assert!(
        !out_vars.contains(&ChcVar::new("J", ChcSort::Int)),
        "{out_vars:?}"
    );
}

#[test]
fn lookup_model_value_prefers_the_sort_matching_entry() {
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("J".to_string(), SmtValue::Bool(true));
    model.insert("J!Int".to_string(), SmtValue::Int(7));
    assert_eq!(
        lookup_model_value(&model, &ChcVar::new("J", ChcSort::Bool)),
        Some(&SmtValue::Bool(true))
    );
    assert_eq!(
        lookup_model_value(&model, &ChcVar::new("J", ChcSort::Int)),
        Some(&SmtValue::Int(7))
    );
    // No qualified entry: today's behavior (the plain entry) is kept.
    assert_eq!(
        lookup_model_value(&model, &ChcVar::new("J", ChcSort::Real)),
        Some(&SmtValue::Bool(true))
    );
    assert_eq!(
        lookup_model_value(&model, &ChcVar::new("K", ChcSort::Int)),
        None
    );
}

/// Regression for MICROBENCH_QUERY_REPLAY §4 item ii: one query carrying
/// `J:Int` and `J:Bool` used to be serialized with two `(declare-const J ..)`
/// lines and rejected by the frontend (`ambiguous nullary symbol`) -> Unknown.
#[test]
fn executor_decides_a_query_with_one_name_in_two_sorts() {
    let j_int = ChcVar::new("J", ChcSort::Int);
    let j_bool = ChcVar::new("J", ChcSort::Bool);
    let expr = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(j_int.clone()), ChcExpr::Int(7)),
        ChcExpr::var(j_bool.clone()),
    );
    let smt = SmtContext::new_search();
    let result = smt.check_sat_via_executor(&expr, &FxHashMap::default(), Duration::from_secs(20));
    let SmtResult::Sat(model) = result else {
        panic!("expected Sat, got {result:?}");
    };
    assert_eq!(lookup_model_value(&model, &j_int), Some(&SmtValue::Int(7)));
    assert_eq!(
        lookup_model_value(&model, &j_bool),
        Some(&SmtValue::Bool(true))
    );

    let unsat = ChcExpr::and(expr.clone(), ChcExpr::not(ChcExpr::var(j_bool.clone())));
    assert!(matches!(
        smt.check_sat_via_executor(&unsat, &FxHashMap::default(), Duration::from_secs(20)),
        SmtResult::Unsat
    ));

    // The internal lane emits the same sort-unique key layout, so its strict
    // model validation is exact too (both lanes, both sorts assigned).
    for mut ctx in [SmtContext::new(), SmtContext::new_search()] {
        let result = ctx.check_sat_with_timeout(&expr, Duration::from_secs(20));
        let SmtResult::Sat(model) = result else {
            panic!("expected Sat on lane {:?}, got {result:?}", ctx.lane());
        };
        assert_eq!(lookup_model_value(&model, &j_int), Some(&SmtValue::Int(7)));
        assert_eq!(
            lookup_model_value(&model, &j_bool),
            Some(&SmtValue::Bool(true))
        );
        assert!(matches!(
            ctx.check_sat_with_timeout(&unsat, Duration::from_secs(20)),
            SmtResult::Unsat
        ));
    }
}

#[test]
fn expired_lane_deadline_refuses_check_sat_and_cancels_engine_loops() {
    let _guard = ScopedSmtDeadline::install(Duration::ZERO);
    std::thread::sleep(Duration::from_millis(2));
    let mut smt = SmtContext::new_search();
    let expr = ChcExpr::eq(ivar("x"), ChcExpr::Int(1));
    let refused_before = super::check_sat::post_deadline_refusals();
    assert!(matches!(smt.check_sat(&expr), SmtResult::Unknown));
    assert!(matches!(
        smt.check_sat_with_executor_fallback(&expr),
        SmtResult::Unknown
    ));
    assert!(super::check_sat::post_deadline_refusals() >= refused_before + 2);
    assert!(crate::engine_config::ChcEngineConfig::default().is_cancelled());
}

/// Another thread's post-deadline refusals are not this thread's, so the
/// `>= refused_before + 2` read above cannot be satisfied by a concurrent test.
#[test]
fn post_deadline_refusal_count_is_scoped_to_the_refusing_thread() {
    let before = super::check_sat::post_deadline_refusals();
    std::thread::spawn(|| {
        let _guard = ScopedSmtDeadline::install(Duration::ZERO);
        std::thread::sleep(Duration::from_millis(2));
        let mut smt = SmtContext::new_search();
        let expr = ChcExpr::eq(ivar("x"), ChcExpr::Int(1));
        assert!(matches!(smt.check_sat(&expr), SmtResult::Unknown));
        assert_eq!(
            super::check_sat::post_deadline_refusals(),
            1,
            "the refusing thread counts its own refusal"
        );
    })
    .join()
    .expect("refusing thread");
    assert_eq!(super::check_sat::post_deadline_refusals(), before);
}
