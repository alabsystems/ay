// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn int_array_var(name: &str) -> ChcVar {
    ChcVar::new(
        name,
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    )
}

fn select_eq(var: &ChcVar, idx: i128, value: i128) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(var.clone()), ChcExpr::Int(idx)),
        ChcExpr::Int(value),
    )
}

#[test]
fn test_persistent_executor_context_reuses_background_across_queries() {
    let a = int_array_var("A");
    let background = select_eq(&a, 0, 42);
    let mut ctx = PersistentExecutorSmtContext::new();
    let propagated = FxHashMap::default();

    assert!(ctx.ensure_background(&background, Duration::from_secs(5)));

    let first = ctx.check_query(&ChcExpr::Bool(true), &propagated, Duration::from_secs(5));
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected SAT for background-only query, got {first:?}"
    );

    let second = ctx.check_query(
        &ChcExpr::not(select_eq(&a, 0, 42)),
        &propagated,
        Duration::from_secs(5),
    );
    assert!(
        matches!(second, SmtResult::Unsat),
        "expected UNSAT when query contradicts persistent background, got {second:?}"
    );
}

#[test]
fn test_persistent_executor_context_rebuilds_when_background_changes() {
    let a = int_array_var("A");
    let background_one = select_eq(&a, 0, 1);
    let background_two = select_eq(&a, 0, 2);
    let mut ctx = PersistentExecutorSmtContext::new();
    let propagated = FxHashMap::default();

    assert!(ctx.ensure_background(&background_one, Duration::from_secs(5)));
    let first = ctx.check_query(&ChcExpr::Bool(true), &propagated, Duration::from_secs(5));
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected SAT for first background, got {first:?}"
    );

    assert!(ctx.ensure_background(&background_two, Duration::from_secs(5)));
    let second = ctx.check_query(&select_eq(&a, 0, 1), &propagated, Duration::from_secs(5));
    assert!(
        matches!(second, SmtResult::Unsat),
        "expected UNSAT after background rebuild, got {second:?}"
    );
}

/// Inc-21: the dv-off retry sets `:ay-eq-diffvar false` on the PERSISTENT
/// session (set-option is not undone by pop), so the attempt must restore it
/// before returning — later queries on the same session must run with the
/// EqDiffVar pass enabled again.
#[test]
fn test_persistent_dv_off_attempt_isolated_per_query() {
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(7));
    let mut ctx = PersistentExecutorSmtContext::new();
    let propagated = FxHashMap::default();
    assert!(ctx.ensure_background(&background, Duration::from_secs(5)));

    // Drive a dv-off attempt directly (the retry path's second leg).
    let (result, raw_unknown) = ctx.check_query_attempt(
        &background,
        &ChcExpr::Bool(true),
        &propagated,
        Duration::from_secs(5),
        true,
    );
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected SAT for trivial dv-off attempt, got {result:?}"
    );
    assert!(!raw_unknown, "SAT attempt must not flag a raw unknown");

    // Isolation: the option must read `true` on the session after the
    // attempt (the per-run gate only honors an explicit `false`).
    let opt = ctx
        .backend
        .exec
        .execute(&Command::GetOption("ay-eq-diffvar".to_string()))
        .expect("get-option execution")
        .expect("get-option output");
    assert_eq!(
        opt, "(:ay-eq-diffvar true)",
        "dv-off option must be restored on the persistent session"
    );

    // And the same session still answers follow-up queries (this one goes
    // through `check_query`, i.e. the retry-eligible Int path).
    let second = ctx.check_query(
        &ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(7))),
        &propagated,
        Duration::from_secs(5),
    );
    assert!(
        matches!(second, SmtResult::Unsat),
        "expected UNSAT for contradiction after dv-off attempt, got {second:?}"
    );
    // A direct attempt never flips the session preference (only a definitive
    // verdict from the RETRY leg of `check_query` does).
    assert!(
        !ctx.dv_off_preferred(),
        "direct attempts must not flip the dv preference"
    );
}

/// Inc-21: with the session preference set to dv-off-first, `check_query`
/// still answers correctly on Int queries (the dv-off attempt runs first and
/// must restore the session option, leaving later queries unaffected).
#[test]
fn test_persistent_dv_off_preferred_session_still_answers() {
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(3));
    let mut ctx = PersistentExecutorSmtContext::new();
    let propagated = FxHashMap::default();
    assert!(ctx.ensure_background(&background, Duration::from_secs(5)));
    assert!(!ctx.dv_off_preferred());
    ctx.prefer_dv_off_first();
    assert!(ctx.dv_off_preferred());

    let sat = ctx.check_query(
        &ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(3)),
        &propagated,
        Duration::from_secs(5),
    );
    assert!(
        matches!(sat, SmtResult::Sat(_)),
        "expected SAT under dv-off-first preference, got {sat:?}"
    );

    let unsat = ctx.check_query(
        &ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(3))),
        &propagated,
        Duration::from_secs(5),
    );
    assert!(
        matches!(unsat, SmtResult::Unsat),
        "expected UNSAT under dv-off-first preference, got {unsat:?}"
    );

    // The session option ends restored (the dv-off attempts clean up).
    let opt = ctx
        .backend
        .exec
        .execute(&Command::GetOption("ay-eq-diffvar".to_string()))
        .expect("get-option execution")
        .expect("get-option output");
    assert_eq!(opt, "(:ay-eq-diffvar true)");
}
