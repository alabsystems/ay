// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M-A2 lazy-persistent-combiner SHADOW differential
//! (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2 / LAZY-M3 §M3.2).
//!
//! The shadow arm (`Executor::set_auflia_persistent_shadow`) is
//! `#[cfg(debug_assertions)]`, so this whole differential module is gated the
//! same way — it is entirely absent from release builds (where the shadow does
//! not exist and the lazy AUFLIA loop runs the fresh-per-round combiner only).
//!
//! For a spread of QF_ALIA / QF_AUFLIA instances with known verdicts, each is
//! solved with the shadow ARMED. Every round of the lazy AUFLIA loop, a SECOND
//! `TheoryCombiner` — created ONCE at the start of the loop and `soft_reset_warm`
//! (warm-reset) each round — is driven over the SAME synced assignment as the
//! authoritative fresh-per-round combiner, and its verdict + reason-set are
//! diffed against the fresh one. The FRESH path stays authoritative: the
//! persistent path never overrides a verdict, and its combiner borrows a private
//! term-store snapshot, so it cannot perturb any solving behavior.
//!
//! THE GATE: `verdict_disagree == 0` (and `reasonset_disagree == 0`) across every
//! engaged round of every instance. The engaged-round and warm-reset counts are
//! REPORTED (the frozen-snapshot shadow only engages on the no-new-term prefix —
//! the executor-borrow limitation documented on `soft_reset_warm`; partial
//! engagement is expected and is not a failure). A verdict disagreement is a
//! soundness signal — the stale-speculative-merge-across-warm-reset hazard — and
//! is never something to paper over.
#![cfg(debug_assertions)]

use super::*;

struct ShadowStats {
    engaged: u64,
    skipped: u64,
    warm_resets: u64,
    verdict_disagree: u64,
    verdict_kind_differ: u64,
    reasonset_disagree: u64,
    first_divergence: Option<String>,
}

/// Solve `input` with the M-A2 lazy-persistent-combiner shadow armed. Returns
/// the final check-sat verdict and the shadow diagnostic counters.
fn solve_with_shadow(input: &str) -> (String, ShadowStats) {
    let commands = parse(input).expect("parse A2 shadow differential instance");
    let mut exec = Executor::new();
    exec.set_auflia_persistent_shadow(true);
    let outputs = exec
        .execute_all(&commands)
        .expect("execute A2 shadow differential instance");
    let verdict = outputs.last().cloned().unwrap_or_default();
    let s = exec.statistics();
    let stats = ShadowStats {
        engaged: s.get_int("auflia.shadow.engaged_rounds").unwrap_or(0),
        skipped: s.get_int("auflia.shadow.skipped_rounds").unwrap_or(0),
        warm_resets: s.get_int("auflia.shadow.warm_resets").unwrap_or(0),
        verdict_disagree: s.get_int("auflia.shadow.verdict_disagree").unwrap_or(0),
        verdict_kind_differ: s.get_int("auflia.shadow.verdict_kind_differ").unwrap_or(0),
        reasonset_disagree: s.get_int("auflia.shadow.reasonset_disagree").unwrap_or(0),
        first_divergence: s
            .get_string("auflia.shadow.first_divergence")
            .map(str::to_owned),
    };
    (verdict, stats)
}

/// `(name, smt2, expected_verdict)`. Each instance carries substantive integer
/// arithmetic (comparisons / `+`) so it routes through the lazy AUFLIA loop
/// (`solve_auf_lia`) rather than the pure Array+EUF fast path, giving the shadow
/// a chance to engage.
const CASES: &[(&str, &str, &str)] = &[
    (
        "alia_diff_index_unsat",
        r#"
        (set-logic QF_ALIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (>= i 0))
        (assert (= (select (store a i 42) (+ i 0)) 43))
        (check-sat)
        "#,
        "unsat",
    ),
    (
        "alia_offset_index_sat",
        r#"
        (set-logic QF_ALIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun v () Int)
        (assert (>= i 0))
        (assert (= (select (store a (+ i 1) v) (+ i 1)) v))
        (check-sat)
        "#,
        "sat",
    ),
    (
        "auflia_store_overwrite_unsat",
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (assert (>= i 0))
        (assert (not (= (select (store (store a i v1) i v2) i) v2)))
        (check-sat)
        "#,
        "unsat",
    ),
    (
        "auflia_two_selects_sat",
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (>= i 0))
        (assert (>= j 0))
        (assert (not (= i j)))
        (assert (= (select a i) 3))
        (assert (= (select a j) 5))
        (check-sat)
        "#,
        "sat",
    ),
    (
        "alia_bounded_distinct_store_sat",
        r#"
        (set-logic QF_ALIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (>= i 0))
        (assert (< i 5))
        (assert (distinct i j))
        (assert (= (select (store a i 7) j) (select a j)))
        (check-sat)
        "#,
        "sat",
    ),
    (
        "auflia_store_chain_sat",
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun k () Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (>= i 0))
        (assert (not (= i j)))
        (assert (not (= j k)))
        (assert (= (select (store (store a i x) j y) k) (select a k)))
        (check-sat)
        "#,
        "sat",
    ),
    (
        "alia_conflicting_stores_unsat",
        r#"
        (set-logic QF_ALIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun i () Int)
        (assert (>= i 0))
        (assert (= a (store b i 1)))
        (assert (= a (store b i 2)))
        (check-sat)
        "#,
        "unsat",
    ),
    (
        "alia_pure_lia_over_select_sat",
        r#"
        (set-logic QF_ALIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (>= (select a i) 0))
        (assert (<= (select a i) 10))
        (assert (= (+ (select a i) i) 12))
        (assert (>= i 0))
        (check-sat)
        "#,
        "sat",
    ),
    // Boolean-enumeration shapes: the disjunctions force the SAT solver to try
    // several assignments over BASE array atoms, each theory-inconsistent, so
    // the lazy loop runs multiple theory-CONFLICT rounds over pre-snapshot atoms
    // (no new asserted atoms are minted between them). These are the rounds that
    // actually exercise `soft_reset_warm` on the create-once persistent combiner
    // (engaged round > 0 ⇒ warm-reset).
    (
        "alia_select_value_enum_unsat",
        r#"
        (set-logic QF_ALIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (>= i 0))
        (assert (= (select a i) 5))
        (assert (or (= (select a i) 1) (= (select a i) 2)))
        (check-sat)
        "#,
        "unsat",
    ),
    (
        "alia_select_value_enum3_unsat",
        r#"
        (set-logic QF_ALIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (>= i 0))
        (assert (= (select a i) 9))
        (assert (or (= (select a i) 1) (= (select a i) 2) (= (select a i) 3)))
        (check-sat)
        "#,
        "unsat",
    ),
    (
        "auflia_select_value_enum_sat",
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (>= i 0))
        (assert (or (= (select a i) 1) (= (select a i) 2)))
        (assert (or (= (select a i) 2) (= (select a i) 3)))
        (assert (not (= (select a i) 1)))
        (check-sat)
        "#,
        "sat",
    ),
];

#[test]
fn a2_persistent_combiner_shadow_matches_fresh_verdicts() {
    let mut total_engaged = 0u64;
    let mut total_skipped = 0u64;
    let mut total_warm_resets = 0u64;
    let mut total_verdict_disagree = 0u64;
    let mut total_verdict_kind_differ = 0u64;
    let mut total_reasonset_disagree = 0u64;
    let mut instances_engaged = 0usize;

    for (name, src, expected) in CASES {
        let (verdict, stats) = solve_with_shadow(src);

        // Baseline sanity: the authoritative (fresh) path returns the known
        // verdict. If this trips, the sample instance itself moved — fix the
        // instance, never mask a shadow divergence behind a moved baseline.
        assert_eq!(
            &verdict, expected,
            "{name}: authoritative verdict changed (expected {expected}, got {verdict})"
        );

        total_engaged += stats.engaged;
        total_skipped += stats.skipped;
        total_warm_resets += stats.warm_resets;
        total_verdict_disagree += stats.verdict_disagree;
        total_verdict_kind_differ += stats.verdict_kind_differ;
        total_reasonset_disagree += stats.reasonset_disagree;
        if stats.engaged > 0 {
            instances_engaged += 1;
        }

        eprintln!(
            "A2 shadow {name}: verdict={verdict} engaged={} warm_resets={} skipped={} \
             verdict_disagree={} verdict_kind_differ={} reasonset_disagree={}",
            stats.engaged,
            stats.warm_resets,
            stats.skipped,
            stats.verdict_disagree,
            stats.verdict_kind_differ,
            stats.reasonset_disagree,
        );

        // THE A2 GATE (per-instance): the create-once + warm-reset persistent
        // combiner agrees with the fresh combiner on every engaged round.
        assert_eq!(
            stats.verdict_disagree,
            0,
            "{name}: M-A2 persistent-combiner shadow VERDICT-disagreed on {} engaged round(s); \
             first divergence: {}",
            stats.verdict_disagree,
            stats.first_divergence.as_deref().unwrap_or("<unrecorded>")
        );
        assert_eq!(
            stats.reasonset_disagree,
            0,
            "{name}: M-A2 persistent-combiner shadow REASON-SET-disagreed on {} engaged round(s); \
             first divergence: {}",
            stats.reasonset_disagree,
            stats.first_divergence.as_deref().unwrap_or("<unrecorded>")
        );
    }

    // Aggregate gate + engagement report.
    assert_eq!(
        total_verdict_disagree, 0,
        "M-A2 shadow verdict DISAGREE total must be 0, got {total_verdict_disagree}"
    );
    assert_eq!(
        total_reasonset_disagree, 0,
        "M-A2 shadow reason-set DISAGREE total must be 0, got {total_reasonset_disagree}"
    );

    // Non-vacuity: the shadow must actually engage on at least one round across
    // the whole spread (otherwise the differential proves nothing). Partial
    // engagement (the frozen-snapshot no-new-term prefix) is expected — the
    // engaged/warm-reset totals are surfaced for the record.
    assert!(
        total_engaged > 0,
        "M-A2 shadow engaged on ZERO rounds across the spread — the frozen-snapshot \
         gate rejected every round; the differential proved nothing"
    );

    eprintln!(
        "A2 shadow differential: instances_engaged={}/{} total_engaged_rounds={} \
         total_warm_resets={} total_skipped={} DISAGREE(refutation)={} \
         kind_differ(benign)={} DISAGREE(reason-set)={}",
        instances_engaged,
        CASES.len(),
        total_engaged,
        total_warm_resets,
        total_skipped,
        total_verdict_disagree,
        total_verdict_kind_differ,
        total_reasonset_disagree,
    );
}
