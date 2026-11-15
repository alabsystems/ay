// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! model-checker-consumer ask 2026-10-14: a straight-line alloc/realloc CHC whose every
//! error rule is unreachable (z3: unsat at once) stayed `unknown` in process
//! at 20 s and 120 s.
//!
//! The BV-native acyclic probe inlines the whole chain and refutes the
//! collapsed query, but the Safe answer stands only once the back-translated
//! model validates on the original clauses. Each transition check pinned the
//! validity array `obj_valid` to a store chain after more than eight other
//! definitions; the check substituted at most eight, so the array stayed, the
//! query went to the proof-carrying executor (about a second per clause, and
//! `unknown` where the BV/LIA tautology check refuses an array query), and
//! validation ran out of time. The unsafe twin keeps the assertion's error
//! rule and asserts that the first element reads 43.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const REALLOC_GROW: &str =
    include_str!("../fixtures/model_checker_consumer_realloc_grow_pre_discharge.smt2");

/// The asserted value: `(not (= v20 42))` reaches `error_p26`.
const ASSERTION_42: &str = "(= |v20| #x0000002a)";
const ASSERTION_43: &str = "(= |v20| #x0000002b)";
const ASSERTION_ERROR: u32 = 26;

fn solve(source: &str, release_budget: Duration) -> VerifiedChcResult {
    let problem = ChcParser::parse(source).unwrap_or_else(|err| panic!("fixture parses: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("fixture validates: {err}"));
    let budget = if cfg!(debug_assertions) {
        release_budget * 4
    } else {
        release_budget
    };
    AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    )
    .solve()
}

/// The `error_pN` indices a line of the fixture mentions.
fn error_indices(line: &str) -> Vec<u32> {
    line.match_indices("error_p")
        .filter_map(|(at, tag)| {
            let digits: String = line[at + tag.len()..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect();
            digits.parse().ok()
        })
        .collect()
}

#[test]
#[timeout(300_000)]
fn realloc_grow_pre_discharge_vc_is_safe() {
    let result = solve(REALLOC_GROW, Duration::from_secs(30));
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "every error rule is unreachable (z3: unsat); got {result:?}"
    );
}

/// Negative twin: the same program asserting that the first element reads 43
/// reaches the assertion's error, and the answer is a validated
/// counterexample. Only that error rule is kept; the full twin below keeps
/// all 39.
#[test]
#[timeout(300_000)]
fn realloc_grow_asserting_43_is_unsafe() {
    assert_eq!(REALLOC_GROW.matches(ASSERTION_42).count(), 3);
    let unsafe_twin = REALLOC_GROW
        .replace(ASSERTION_42, ASSERTION_43)
        .lines()
        .filter(|line| error_indices(line).iter().all(|&n| n == ASSERTION_ERROR))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(unsafe_twin.contains("error_p26"));
    let result = solve(&unsafe_twin, Duration::from_secs(30));
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "the first element holds 42, so asserting 43 fails (z3: sat); got {result:?}"
    );
}

/// The FULL negative twin: all 39 error rules, asserting 43. The inlined error
/// disjunction gives each path its own `obj_valid := (store (const true) 66
/// true)`, which the term store folds to `(const true)`; ay-dpll used to refuse
/// those models (`arrays-read-conflict-uneval`). The query-only landing (or,
/// failing it, the exact-path replay) reaches Unsafe either way, so this pins
/// the verdict; the counterfactual is the ay-dpll `qf_aufbv_forced_definition`
/// tests.
#[test]
#[timeout(300_000)]
fn realloc_grow_full_twin_asserting_43_is_unsafe() {
    assert_eq!(REALLOC_GROW.matches(ASSERTION_42).count(), 3);
    let unsafe_twin = REALLOC_GROW.replace(ASSERTION_42, ASSERTION_43);
    let errors: std::collections::BTreeSet<u32> =
        unsafe_twin.lines().flat_map(error_indices).collect();
    assert_eq!(errors.len(), 39, "every error rule is kept");
    let result = solve(&unsafe_twin, Duration::from_secs(30));
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "the first element holds 42, so asserting 43 fails (z3: sat); got {result:?}"
    );
}

/// The full twin with the failing assertion's two rules (`error_p26 =>
/// error` and the `bb12` rule that reaches `error_p26`) moved last. The
/// clause set is unchanged; only its order differs.
///
/// The bounded replay takes the original paths in clause order, so it reached
/// this path last: about 27 s, `unknown` both in a plain solve (whose probe
/// has 15 s) and with a 30 s budget. The query-only landing back-translates
/// the collapsed query's own model instead, whatever the order. The landing
/// itself is pinned by `adaptive_multi_pred::query_only_landing` tests; the
/// debug budget here is four times the release one, wide enough for the
/// replay too.
#[test]
#[timeout(300_000)]
fn realloc_grow_full_twin_with_the_failing_path_last_is_unsafe() {
    let unsafe_twin = REALLOC_GROW.replace(ASSERTION_42, ASSERTION_43);
    let (moved, mut kept): (Vec<&str>, Vec<&str>) = unsafe_twin.lines().partition(|line| {
        line.starts_with("(rule") && error_indices(line).contains(&ASSERTION_ERROR)
    });
    assert_eq!(
        moved.len(),
        2,
        "the error rule and the rule that reaches it"
    );
    let query = kept
        .iter()
        .position(|line| *line == "(query error)")
        .unwrap_or_else(|| panic!("the fixture ends with its query"));
    kept.splice(query..query, moved);
    let reordered = kept.join("\n");
    let result = solve(&reordered, Duration::from_secs(30));
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "the clause set of the full twin, so asserting 43 still fails (z3: sat); got {result:?}"
    );
}
