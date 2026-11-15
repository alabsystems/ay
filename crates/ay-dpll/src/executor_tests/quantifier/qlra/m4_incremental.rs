// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M4: the nested lane in an INCREMENTAL session (`qlra_lane/incremental.rs`).
//!
//! The lane runs on the `Unknown` fallback of an incremental check-sat, over
//! that check's authored window, and carries each quantifier node's instance
//! log and exact flag from one check-sat to the next in a session cache bound
//! to the term store's structural epoch (`cegqi/lra_nested/session.rs`).
//!
//! The fixture is LOIS `incremental0` check-sat 93 (Kopczynski; cvc5 1.3.0
//! and the lane one-shot: `sat`): `aj` is the least upper bound of the open
//! interval `(ac, ad)`. The legacy quantifier path answers `unknown` on it in
//! an incremental session, so every verdict asserted here as the lane's is
//! also pinned to the lane's own statistics.

use super::without_qsat;
use crate::Executor;
use ay_frontend::parse;

const PRELUDE: &str = "(set-logic LRA)(declare-const ac Real)(declare-const ad Real)\
     (declare-const aj Real)(declare-const al Real)(declare-const p Bool)";

/// `aj` bounds `(ac, ad)` from above.
const UPPER: &str = "(assert (forall ((ah Real)) (or (>= ac ah) (>= ah ad) (>= aj ah))))";

/// No bound below `aj` does: a nested `∀∃`.
const LEAST: &str = "(assert (forall ((ak Real)) (or (exists ((ah Real)) \
     (and (> ah ac) (> ad ah) (> ah ak))) (>= ak aj))))";

/// One check-sat's public verdict and the lane's statistics for it.
#[derive(Debug)]
struct Step {
    verdict: String,
    recognized: bool,
    retry: bool,
    gate: Option<String>,
    hits: u64,
    session_nodes: u64,
    oracle_calls: u64,
}

fn session() -> Executor {
    let mut exec = Executor::new();
    exec.set_timeout(Some(super::QUERY_TIMEOUT));
    exec
}

/// Run `smt` (ending in one `check-sat`) on the live session.
fn step(exec: &mut Executor, smt: &str) -> Step {
    let outputs = exec
        .execute_all(&parse(smt).expect("parse"))
        .expect("execute");
    let stats = exec.statistics();
    Step {
        verdict: outputs
            .iter()
            .rev()
            .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .unwrap_or_default(),
        recognized: stats.extra.contains_key("qlra.recognized"),
        retry: stats.get_int("qlra.incremental_retry") == Some(1),
        gate: stats.get_string("qlra.gate").map(str::to_string),
        hits: stats.get_int("qlra.session_hits").unwrap_or(0),
        session_nodes: stats.get_int("qlra.session_nodes").unwrap_or(0),
        oracle_calls: stats.get_int("qlra.oracle_calls").unwrap_or(0),
    }
}

fn assert_lane_published_sat(name: &str, step: &Step) {
    assert_eq!(step.verdict, "sat", "{name}: {step:?}");
    assert!(
        step.retry,
        "{name}: the incremental fallback must run: {step:?}"
    );
    assert_eq!(
        step.gate.as_deref(),
        Some("confirmed"),
        "{name}: the lane's gate arm must be the publisher: {step:?}"
    );
}

#[test]
fn an_incremental_unknown_falls_back_to_the_lane() {
    let _no_qsat = without_qsat();
    let mut exec = session();
    let first = step(
        &mut exec,
        &format!("{PRELUDE}(push 1)(assert (> ad ac))(push 1){UPPER}{LEAST}(check-sat)"),
    );
    assert_lane_published_sat("lub", &first);
    assert!(first.session_nodes >= 3, "the search is cached: {first:?}");

    // Non-vacuity: the same session without the lane answers `unknown`.
    let _off = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_cegqi: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let mut legacy = session();
    let without = step(
        &mut legacy,
        &format!("{PRELUDE}(push 1)(assert (> ad ac))(push 1){UPPER}{LEAST}(check-sat)"),
    );
    assert_eq!(without.verdict, "unknown", "legacy alone: {without:?}");
    assert!(!without.recognized && !without.retry);
}

/// The lane decides each check's OWN authored window: a root popped with
/// its scope is gone from the next check's roots, and one asserted in a
/// later scope is in them.
#[test]
fn a_root_leaving_scope_leaves_the_lane_roots() {
    let _no_qsat = without_qsat();
    let mut exec = session();
    let pinned_low = step(
        &mut exec,
        &format!(
            "{PRELUDE}(push 1)(assert (> ad ac))(push 1){UPPER}{LEAST}\
             (assert (< aj ad))(check-sat)"
        ),
    );
    assert_ne!(
        pinned_low.verdict, "sat",
        "the least upper bound is ad, never below it: {pinned_low:?}"
    );

    // The pinning root leaves scope: the lub alone is satisfiable, and the
    // lane publishes it (it could not if `aj < ad` were still a root).
    let lub = step(
        &mut exec,
        &format!("(pop 1)(push 1){UPPER}{LEAST}(check-sat)"),
    );
    assert_lane_published_sat("after pop", &lub);

    // A later scope pins it again: whatever the cache holds, never `sat`.
    let pinned_again = step(&mut exec, "(assert (< aj ad))(check-sat)");
    assert_ne!(pinned_again.verdict, "sat", "{pinned_again:?}");
}

/// Quantified roots of an OUTER scope keep their quantifier terms across
/// `pop`/`push`, so the next check's search starts from what the previous
/// one logged for them.
#[test]
fn the_session_cache_hits_after_pop() {
    let _no_qsat = without_qsat();
    let mut exec = session();
    let first = step(
        &mut exec,
        &format!(
            "{PRELUDE}(push 1)(assert (> ad ac)){UPPER}{LEAST}\
             (push 1)(assert (>= al aj))(check-sat)"
        ),
    );
    assert_lane_published_sat("first", &first);
    assert_eq!(first.hits, 0, "nothing cached yet: {first:?}");

    let second = step(&mut exec, "(pop 1)(push 1)(assert (<= al aj))(check-sat)");
    assert_lane_published_sat("second", &second);
    assert!(
        second.hits >= 3,
        "the outer roots' nodes are seeded from the cache: {second:?}"
    );

    // The seed is used: the same check in a fresh session asks the oracle
    // more often.
    let mut fresh = session();
    let cold = step(
        &mut fresh,
        &format!(
            "{PRELUDE}(push 1)(assert (> ad ac)){UPPER}{LEAST}\
             (push 1)(assert (<= al aj))(check-sat)"
        ),
    );
    assert_lane_published_sat("cold", &cold);
    assert_eq!(cold.hits, 0);
    assert!(
        second.oracle_calls < cold.oracle_calls,
        "a seeded search starts ahead: warm {second:?} cold {cold:?}"
    );
}

/// A structural epoch change of the term store (here a rollback that does
/// not go through the lane's re-binding; a compaction is pinned in
/// `cegqi/lra_nested/session_tests.rs`) clears the cache: the next search
/// starts from nothing, and still decides.
#[test]
fn a_store_epoch_change_clears_the_session_cache() {
    let _no_qsat = without_qsat();
    let mut exec = session();
    let first = step(
        &mut exec,
        &format!(
            "{PRELUDE}(push 1)(assert (> ad ac)){UPPER}{LEAST}\
             (push 1)(assert (>= al aj))(check-sat)"
        ),
    );
    assert_lane_published_sat("first", &first);
    assert!(exec.qlra_session_cache_is_live());

    // An empty rollback: no id is recycled, but the store's generation moves.
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    exec.ctx.terms.rollback_to(checkpoint);
    assert!(!exec.qlra_session_cache_is_live());

    let second = step(&mut exec, "(pop 1)(push 1)(assert (<= al aj))(check-sat)");
    assert_lane_published_sat("second", &second);
    assert_eq!(
        second.hits, 0,
        "the retired cache seeds nothing: {second:?}"
    );
}

/// `check-sat-assuming` is not shown sound for the lane's authored-scope
/// publication, and an optimization query is not the authored scope: the
/// incremental fallback stays inert for both.
#[test]
fn the_incremental_fallback_stays_inert_off_the_authored_scope() {
    let _no_qsat = without_qsat();
    let mut exec = session();
    let assuming = step(
        &mut exec,
        &format!(
            "{PRELUDE}(push 1)(assert (> ad ac))(push 1){UPPER}{LEAST}\
             (check-sat-assuming (p))"
        ),
    );
    assert!(
        !assuming.recognized && !assuming.retry,
        "check-sat-assuming must not reach the lane: {assuming:?}"
    );
    assert_ne!(assuming.verdict, "unsat");

    // The assumption is also asserted, so the query window equals the
    // authored scope as a set: only the assumption guard keeps it inert.
    let mut exec = session();
    let asserted = step(
        &mut exec,
        &format!(
            "{PRELUDE}(push 1)(assert (> ad ac))(push 1){UPPER}{LEAST}(assert p)\
             (check-sat-assuming (p))"
        ),
    );
    assert!(
        !asserted.recognized && !asserted.retry,
        "check-sat-assuming must not reach the lane: {asserted:?}"
    );
    assert_ne!(asserted.verdict, "unsat");

    let mut exec = session();
    let soft = step(
        &mut exec,
        &format!(
            "{PRELUDE}(push 1)(assert (> ad ac))(push 1){UPPER}{LEAST}\
             (assert-soft (> al aj) :weight 1)(check-sat)"
        ),
    );
    assert!(
        !soft.recognized && !soft.retry,
        "a query with soft constraints must not reach the lane: {soft:?}"
    );
    assert_ne!(soft.verdict, "unsat");
}
