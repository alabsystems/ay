// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Admission barriers for the persistent FP lane.

use super::*;

fn output_verdicts(out: &[String]) -> Vec<&str> {
    out.iter()
        .map(String::as_str)
        .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .collect()
}

fn engagement_count(out: &[String]) -> usize {
    out.iter()
        .filter(|line| line.contains("fp-incremental.solves"))
        .count()
}

fn engagement_by_query(out: &[String]) -> Vec<bool> {
    let mut engaged = Vec::new();
    for line in out {
        if matches!(line.trim(), "sat" | "unsat" | "unknown") {
            engaged.push(false);
        } else if line.contains("fp-incremental.solves") {
            *engaged
                .last_mut()
                .expect("statistics marker appeared before a verdict") = true;
        }
    }
    engaged
}

/// Independent `push/assert/check/pop` queries do not reuse a live assertion.
/// Persisting across them made the SMT-COMP `image_filter` session 17x slower
/// than the stateless path. Admission must not pay even one speculative seed
/// solve: all three queries stay on fresh stateless solvers.
#[test]
fn fp_incremental_never_seeds_on_disjoint_query_batches() {
    let smt = format!(
        "{DECLS}\
         (push 1)\n\
         (assert (fp.lt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (pop 1)\n(push 1)\n\
         (assert (fp.gt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (pop 1)\n(push 1)\n\
         (assert (fp.isNormal z))\n\
         (check-sat)\n(get-info :all-statistics)\n"
    );
    let out = solve_authored_vec(&smt);
    assert_eq!(output_verdicts(&out), ["sat", "sat", "sat"]);

    assert_eq!(
        engagement_count(&out),
        0,
        "a disjoint batch must never construct a persistent solver: {out:?}"
    );
}

/// A stable authored assertion is not evidence of useful reuse unless its DAG
/// actually mentions FP. Without this barrier, `anchor` admits the first query
/// and keeps every later disjoint FP circuit on the pathological persistent
/// shape that made `image_filter` 17x slower.
#[test]
fn fp_incremental_ignores_a_stable_non_fp_anchor() {
    let smt = format!(
        "{DECLS}(declare-fun anchor () Bool)\n(assert anchor)\n\
         (push 1)\n(assert (fp.lt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n\
         (push 1)\n(assert (fp.gt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n\
         (push 1)\n(assert (fp.isNormal z))\n\
         (check-sat)\n(get-info :all-statistics)\n"
    );
    let out = solve_authored_vec(&smt);
    assert_eq!(output_verdicts(&out), ["sat", "sat", "sat"]);
    assert_eq!(
        engagement_count(&out),
        0,
        "a Bool-only anchor admitted disjoint FP query batches: {out:?}"
    );
}

/// Even an FP-relevant anchor is insufficient when every scoped batch adds a
/// novel FP root. An existential overlap check would admit on `isPositive z`
/// and retain every disjoint circuit, recreating the 17x `image_filter` tail.
/// Admission therefore requires the whole current FP-relevant root set to have
/// been observed, not merely one root in it.
#[test]
fn fp_incremental_stable_fp_anchor_cannot_admit_disjoint_batches() {
    let smt = format!(
        "{DECLS}(assert (fp.isPositive z))\n\
         (push 1)\n(assert (fp.lt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n\
         (push 1)\n(assert (fp.gt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n\
         (push 1)\n(assert (fp.isNormal z))\n\
         (check-sat)\n(get-info :all-statistics)\n"
    );
    let out = solve_authored_vec(&smt);
    assert_eq!(output_verdicts(&out), ["sat", "sat", "sat"]);
    assert_eq!(
        engagement_by_query(&out),
        [false, false, false],
        "a stable FP anchor admitted novel scoped FP batches: {out:?}"
    );
}

/// Partial overlap must obey the same full-set rule after persistence is live.
/// The stable anchor admits neither novel `A` nor novel `B`; each complete set
/// must first be observed, and only its identical repeat may engage. Replacing
/// `all` with `any` in either admission branch makes this barrier fail.
#[test]
fn fp_incremental_active_partial_overlap_restarts_before_readmission() {
    let smt = format!(
        "{DECLS}(assert (fp.isPositive z))\n\
         (push 1)\n(assert (fp.lt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n\
         (push 1)\n(assert (fp.gt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n"
    );
    let out = solve_authored_vec(&smt);
    assert_eq!(output_verdicts(&out), ["sat", "sat", "sat", "sat"]);
    assert_eq!(
        engagement_by_query(&out),
        [false, true, false, true],
        "partial FP-root overlap bypassed full-set admission: {out:?}"
    );
}

/// Exact assertion identity across authored queries is sufficient evidence to
/// admit persistence. The first query is the observation and stays stateless;
/// the identical second query must engage the lane.
#[test]
fn fp_incremental_admits_exact_live_assertion_reuse() {
    let smt = format!(
        "{DECLS}(push 1)\n(assert (fp.lt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n"
    );
    let out = solve_authored_vec(&smt);
    assert_eq!(output_verdicts(&out), ["sat", "sat"]);

    assert_eq!(
        engagement_count(&out),
        1,
        "the second exact-reuse query was not admitted: {out:?}"
    );
}

/// Once persistence has engaged, a novel FP root tears the SAT state down and
/// answers that query statelessly. The teardown is deliberately non-sticky:
/// the first novel query records its complete root set, so an identical repeat
/// can rebuild persistence. A third check proves the rebuilt lane remains live.
#[test]
fn fp_incremental_active_novel_set_restarts_then_readmits() {
    let smt = format!(
        "{DECLS}(push 1)\n(assert (fp.lt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n\
         (push 1)\n(assert (fp.gt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n"
    );
    let out = solve_authored_vec(&smt);
    assert_eq!(output_verdicts(&out), ["sat", "sat", "sat", "sat", "sat"]);
    assert_eq!(
        engagement_by_query(&out),
        [false, true, false, true, true],
        "a novel set did not tear down once and then re-admit: {out:?}"
    );
    assert!(
        out.iter().all(|line| !line.contains("(error")),
        "teardown corrupted the pending scope stack: {out:?}"
    );
}

/// `(reset)` starts a new problem, so it must clear the deferred restart and
/// the old scope/probe state. A new FP base assertion is then an exact pre-push
/// anchor and must engage on its first check-sat.
#[test]
fn fp_incremental_reset_clears_deferred_restart_state() {
    let smt = format!(
        "{DECLS}(push 1)\n(assert (fp.lt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (check-sat)\n(get-info :all-statistics)\n(pop 1)\n\
         (push 1)\n(assert (fp.gt x y))\n\
         (check-sat)\n(get-info :all-statistics)\n\
         (reset)\n{DECLS}(assert (fp.isNormal z))\n(push 1)\n\
         (check-sat)\n(get-info :all-statistics)\n"
    );
    let out = solve_authored_vec(&smt);
    assert_eq!(output_verdicts(&out), ["sat", "sat", "sat", "sat"]);
    assert_eq!(
        engagement_count(&out),
        2,
        "reset did not clear the deferred restart and old FP scope state: {out:?}"
    );
    assert!(
        out.iter().all(|line| !line.contains("(error")),
        "reset left a corrupt pending scope stack: {out:?}"
    );
}
