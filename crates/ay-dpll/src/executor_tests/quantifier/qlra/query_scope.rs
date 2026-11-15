// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane decides the AUTHORED scope only, so it must be inert whenever the
//! public query is something else (`qlra_query_is_not_authored_scope`).
//!
//! Measured regression: `maxsmt_oll_quantified_hard_falls_back` answered
//! `unknown` instead of `sat`. The MaxSMT search asserts `(or soft_i relax_i)`
//! as transient hard roots and probes with a raw same-context `check_sat`; the
//! lane solved the authored roots without those clauses, and the independent
//! model gate withheld its model (`(or (not a) __ay_soft_relax_0) evaluates to
//! false`).

use super::{assert_lane_sat, run};
use crate::executor::Executor;
use crate::SolveResult;
use ay_core::Sort;
use ay_frontend::parse;

/// A valid linear universal the lane itself publishes `sat` on, beside a
/// ground Boolean hard constraint.
const HARD: &str = "(set-logic LRA)(declare-const c Real)\
     (declare-const a Bool)(declare-const b Bool)\
     (assert (forall ((x Real)) (xor (> x c) (<= x c))))(assert (or a b))";

fn run_script(script: &str, lane: bool) -> Vec<String> {
    let _no_qsat = super::without_qsat();
    let _flags = (!lane).then(|| {
        ay_core::misc_test_override::set(ay_core::MiscCliFlags {
            no_qlra_cegqi: true,
            ..ay_core::misc_cli_flags().clone()
        })
    });
    let mut exec = Executor::new();
    exec.set_timeout(Some(super::QUERY_TIMEOUT));
    exec.execute_all(&parse(script).expect("parse"))
        .expect("execute")
}

#[test]
fn soft_constraints_keep_the_lane_inert_and_the_optimum_intact() {
    // Non-vacuity: without soft constraints the lane owns this problem.
    assert_lane_sat("hard-only", &format!("{HARD}(check-sat)"));

    let maxsmt = format!(
        "{HARD}(assert-soft (not a) :weight 1)(assert-soft (not b) :weight 1)\
         (check-sat)(get-objectives)"
    );
    let with_lane = run_script(&maxsmt, true);
    assert_eq!(with_lane[0], "sat", "MaxSMT verdict: {with_lane:?}");
    assert!(
        with_lane[1].contains("( 1)"),
        "exactly one soft is violated at the optimum: {with_lane:?}"
    );
    assert_eq!(
        with_lane,
        run_script(&maxsmt, false),
        "the lane must leave an optimization query exactly as without it"
    );
    assert!(
        !run(&maxsmt).recognized,
        "the lane must not even search a query that carries soft constraints"
    );
}

#[test]
fn a_transient_hard_root_outside_the_authored_scope_keeps_the_lane_inert() {
    let _no_qsat = super::without_qsat();
    let mut exec = Executor::new();
    exec.set_timeout(Some(super::QUERY_TIMEOUT));
    exec.execute_all(&parse(&format!("{HARD}(declare-const d Bool)")).expect("parse"))
        .expect("execute");

    // Non-vacuity: over exactly the authored scope the lane publishes.
    assert!(matches!(exec.check_sat(), Ok(SolveResult::Sat)));
    assert_eq!(
        exec.statistics().get_string("qlra.gate"),
        Some("confirmed"),
        "the lane must own the authored-only query"
    );

    // The shape the MaxSMT search builds: a query-local hard root that is not
    // an authored assertion. `d` occurs nowhere in the authored scope, so a
    // lane model of that scope says nothing about it.
    let d = exec.ctx.terms.mk_var("d", Sort::Bool);
    let base = exec.ctx.assertions.len();
    exec.ctx
        .add_transient_assertion_with_parsed(d, ay_frontend::Term::Symbol("__test__".into()));
    let result = exec.check_sat();
    let inert = exec
        .statistics()
        .get_string("qlra.inert")
        .map(str::to_string);
    let recognized = exec.statistics().extra.contains_key("qlra.recognized");
    exec.ctx.truncate_assertions(base);

    assert_eq!(inert.as_deref(), Some("query-window-not-authored"));
    assert!(!recognized, "an inert lane must not search");
    assert!(
        matches!(result, Ok(SolveResult::Sat)),
        "the legacy path decides the whole query, transient root included: {result:?}"
    );
}

/// `qlra_lane_admissible` keeps the lane off for `check-sat-assuming`
/// (non-empty `last_assumptions`). In an incremental session (`incremental_mode`,
/// set by the first `push`) the lane runs only on the `Unknown` fallback
/// (M4, `m4_incremental.rs`), so a query the legacy path decides never
/// reaches it.
#[test]
fn assumption_and_incremental_queries_keep_the_lane_inert() {
    const UNIVERSAL: &str = "(set-logic LRA)(declare-const c Real)(declare-const p Bool)\
         (assert (forall ((x Real)) (xor (> x c) (<= x c))))";
    assert_lane_sat("plain", &format!("{UNIVERSAL}(check-sat)"));

    let assuming = run(&format!("{UNIVERSAL}(check-sat-assuming (p))"));
    assert!(
        !assuming.recognized,
        "check-sat-assuming must not reach the lane"
    );
    assert_ne!(assuming.verdict, "unsat", "p = true satisfies the query");

    let pushed = run(&format!("{UNIVERSAL}(push 1)(assert p)(check-sat)(pop 1)"));
    assert!(
        !pushed.recognized,
        "an incremental query the legacy path decides must not reach the lane"
    );
    assert_ne!(pushed.verdict, "unsat", "p = true satisfies the query");
}
