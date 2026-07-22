// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression tests for the incremental QF_LRA engine lane (S1,
//! `AY_LRA_INC_ENGINE` / `Executor::lra_inc_engine_override`).
//!
//! The engine lane reuses the persist-SAT lane's session-persistent SAT solver
//! but puts it in `set_ic3_mode()` with scoped BVE disabled and
//! `set_inc_engine_reset_mode(true)`, so every per-check-sat reset takes the
//! state-preserving incremental reset (`reset_search_state_incremental`)
//! instead of the full reset — the level-0 trail, watches, VSIDS heap and
//! learned clauses persist across check-sats.
//!
//! REGRESSION (#8078): before the deferral fix, the per-check-sat delta Tseitin
//! clauses were added to the arena WITHOUT watches (they took the non-deferral
//! branch of `add_clause_unscoped_inner` because `assumption_cache_valid` is
//! false after per-check var growth), and the forced incremental reset then
//! skipped `initialize_watches` — leaving the newest clauses invisible to BCP.
//! In debug this panicked (`BUG [#8078]: BCP missed conflict!`); in release it
//! silently solved a clause SUBSET (a candidate false SAT caught only by the
//! fail-closed re-validation backstop). The fix gates the clause-add deferral
//! on `inc_engine_reset_mode`, so the delta clauses stay deferred and the
//! incremental reset's `attach_new_clauses_incremental` builds their watches.
//!
//! These tests pin the engine lane programmatically via `lra_inc_engine_override`
//! (no env-var mutation, which races under parallel test execution) and assert
//! it (a) never panics and (b) returns EXACTLY the from-scratch ground truth on
//! push/pop QF_LRA scripts — the exact `(push 1) … (check-sat) (pop 1)` shape of
//! the target hybrid_networks incremental benchmarks.

use std::time::Duration;

use crate::Executor;
use ay_frontend::parse;

const SOLVE_TIMEOUT: Duration = Duration::from_secs(30);

/// Run an SMT-LIB script through a fresh executor with the incremental-engine
/// lane pinned by `override`, returning the verdict of every check-sat in order.
fn run_verdicts(script: &str, inc_engine_override: Option<bool>) -> Vec<String> {
    let mut exec = Executor::new();
    exec.lra_inc_engine_override = inc_engine_override;
    exec.set_timeout(Some(SOLVE_TIMEOUT));
    let mut verdicts = Vec::new();
    for cmd in &parse(script).expect("script parses") {
        if let Some(out) = exec.execute(cmd).expect("command executes") {
            verdicts.push(out);
        }
    }
    verdicts
}

/// Alternating push/check/pop/check: every post-`push` check is unsat ONLY
/// because the scoped assertion is honored, and each matching post-`pop` check
/// is sat because it is correctly discarded. Before the #8078 fix the engine
/// lane panicked on this shape.
const PUSH_CHECK_POP_CHECK_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0))
(check-sat)
(push 1)
(assert (<= x (- 1)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= y x))
(assert (>= y 5))
(assert (<= x 3))
(check-sat)
(pop 1)
(check-sat)
(assert (<= x 10))
(check-sat)
";

/// A BMC-shaped monotone accumulation with a scoped property per step — closest
/// to the real hybrid_networks trace (assert base rows, then
/// `(push 1) (assert property) (check-sat) (pop 1)` repeatedly). Each check
/// grows the SAT var set (the exact condition that invalidates
/// `assumption_cache_valid` and triggered the missed-watch bug).
const BMC_STEP_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-const s0 Real)
(declare-const s1 Real)
(declare-const s2 Real)
(declare-const s3 Real)
(assert (= s0 0))
(assert (<= (- s1 s0) 1))
(push 1)
(assert (>= s1 10))
(check-sat)
(pop 1)
(assert (<= (- s2 s1) 1))
(push 1)
(assert (>= s2 10))
(check-sat)
(pop 1)
(assert (<= (- s3 s2) 1))
(push 1)
(assert (>= s3 10))
(check-sat)
(pop 1)
(check-sat)
";

/// The engine lane must match from-scratch ground truth on push/check/pop/check
/// AND must not panic (the #8078 BCP-missed-conflict regression). The ground
/// truth is pinned by the explicit engine-off/from-scratch override.
#[test]
fn inc_engine_push_check_pop_check_matches_ground_truth() {
    let ground_truth = run_verdicts(PUSH_CHECK_POP_CHECK_SCRIPT, Some(false));
    assert_eq!(
        ground_truth,
        vec!["sat", "unsat", "sat", "unsat", "sat", "sat"],
        "sanity: from-scratch pin must be the known ground truth"
    );
    assert_eq!(
        run_verdicts(PUSH_CHECK_POP_CHECK_SCRIPT, Some(true)),
        ground_truth,
        "inc-engine lane must match from-scratch ground truth (no false SAT, \
         no missed conflict) on push/check/pop/check"
    );
}

/// INV: a pushed property that makes the check unsat must NOT be dropped to a
/// false SAT under the engine lane, and must not leak past the matching pop.
#[test]
fn inc_engine_scoped_property_not_dropped() {
    let script = "\
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 100))
(check-sat)
(push 1)
(assert (<= x 0))
(check-sat)
(pop 1)
(check-sat)
";
    assert_eq!(
        run_verdicts(script, Some(true)),
        vec!["sat", "unsat", "sat"],
        "inc-engine: scoped (<= x 0) must be honored (pushed check unsat, never \
         a false SAT) and discarded after pop (sat)"
    );
}

/// The BMC-shaped monotone accumulation (per-check var growth) must match
/// ground truth under the engine lane. This is the exact condition
/// (assumption_cache_valid false at delta-clause add time) that produced the
/// unwatched-clause missed-conflict bug.
#[test]
fn inc_engine_bmc_step_accumulation_matches_ground_truth() {
    let ground_truth = run_verdicts(BMC_STEP_SCRIPT, Some(false));
    // s_{i} constrained to within 1 of s_{i-1} starting at 0 can never reach 10
    // in a few steps, so each pushed `>= 10` check is unsat; the final
    // unconstrained check is sat.
    assert_eq!(
        run_verdicts(BMC_STEP_SCRIPT, Some(true)),
        ground_truth,
        "inc-engine lane must match from-scratch ground truth on a BMC-shaped \
         monotone accumulation with per-step scoped properties"
    );
}
