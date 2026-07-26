// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-global memo that lets the external-invariant validation path REUSE
//! the acyclic-BMC safety proof the solve lane already computed, instead of
//! recomputing the identical exhaustive acyclic BMC from scratch.
//!
//! ## Why this exists
//!
//! For a dead-end-pruned (acyclic-modulo-dead-end) CHC, [`crate::AdaptivePortfolio`]
//! proves safety by exhaustive acyclic BMC and ships an EMPTY certificate. An
//! out-of-crate re-validation caller (model-checker-consumer) then re-parses the ORIGINAL,
//! un-stripped problem and hands it to
//! [`crate::engines::validate_external_invariant_model`], whose empty-model path
//! runs `run_scalar_acyclic_bmc_certificate` — which strips the same dead-end
//! cycle and RE-RUNS the very same exhaustive acyclic BMC. On
//! count_zero/loop_with_old that turned an ~8.5 s proof into ~17 s (solve
//! ~8.5 s + validate ~8.5 s), pushing them over the driver's 15 s gate.
//!
//! This memo closes that gap: when the solve lane's direct exact BMC run (or
//! the final original-problem re-proof) establishes an acyclic-BMC empty-model
//! Safe for a dead-end-stripped problem, it records the fact here; the
//! validation path consults it and, on an EXACT structural match at a
//! sufficient exhaustive depth, returns the already-established verdict
//! without re-running BMC.
//!
//! ## Soundness (this is a verdict-critical path)
//!
//! - An entry is inserted ONLY immediately after BMC has *actually proved* the
//!   stripped problem safe by complete exhaustive acyclic BMC — never from the
//!   generic result finalizer, an unproven or merely-labelled Safe, or a
//!   genuinely-unsafe problem. The stored fact is exactly "acyclic BMC proved
//!   this problem safe through this depth", the SAME fact the validation
//!   re-run would independently establish.
//! - The key is the problem's full [`ChcProblem::structural_identity`]. The map
//!   is keyed by that `String`, so a "hit" means the identity strings are
//!   byte-for-byte equal — i.e. structurally identical problems — with NO hash
//!   collision able to surface another problem's verdict.
//! - The consult site in `run_scalar_acyclic_bmc_certificate` is placed AFTER
//!   the eligibility gates, zero-budget rejection, and pre-cancellation
//!   rejection. It also requires the cached proof depth to cover the freshly
//!   recomputed exhaustive depth. A hit can therefore only REPLACE the
//!   redundant BMC run with its own already-established result. It never
//!   bypasses a gate, accepts a shallower proof, or accepts an empty model
//!   without a proof.
//!
//! The reuse is therefore exactly equivalent to re-running the proof; on any
//! non-match the caller falls back to the correct-but-slower re-run unchanged.

use crate::ChcProblem;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// Upper bound on retained entries. When exceeded the memo is cleared wholesale
/// — a cleared memo only ever costs a recomputation, never correctness. The
/// solve→validate handoff is immediate (the same problem, back-to-back), so
/// even a small cap serves the hot path; this bound just keeps memory flat
/// across a long multi-file driver run.
const MAX_ENTRIES: usize = 512;

fn cache() -> &'static Mutex<HashMap<String, usize>> {
    static CACHE: OnceLock<Mutex<HashMap<String, usize>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Record that the solve lane proved `problem` — which MUST already be
/// dead-end-stripped (i.e. the exact problem the validation re-run classifies)
/// — safe by complete exhaustive acyclic BMC at unroll bound `depth`.
///
/// Call this ONLY at a point where the solve lane has genuinely established the
/// acyclic-BMC empty-model Safe; never speculatively.
pub(crate) fn record_acyclic_bmc_safe(problem: &ChcProblem, depth: usize) {
    let key = problem.structural_identity();
    let mut guard = cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if guard.len() >= MAX_ENTRIES {
        guard.clear();
    }
    guard
        .entry(key)
        .and_modify(|recorded| *recorded = (*recorded).max(depth))
        .or_insert(depth);
}

/// Look up a previously-recorded acyclic-BMC safety proof for `problem` (the
/// stripped problem). `Some(depth)` means the solve lane already established
/// this exact problem safe by complete acyclic BMC through that bound. The
/// caller must still require that `depth` covers its freshly recomputed
/// exhaustive bound before returning Safe instead of re-running the proof.
pub(crate) fn lookup_acyclic_bmc_safe(problem: &ChcProblem) -> Option<usize> {
    let key = problem.structural_identity();
    let guard = cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    guard.get(&key).copied()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcParser, ChcProblem, ChcSort};

    fn parse(input: &str) -> ChcProblem {
        ChcParser::parse(input).expect("test CHC parses")
    }

    // A tiny acyclic 2-predicate scalar DAG (safe): p0 holds x=0, p1 holds
    // x=1 from p0, query asserts p1 => x<2 (unsatisfiable body, so safe).
    const SAFE_DAG: &str = "\
(set-logic HORN)
(declare-fun p0 (Int) Bool)
(declare-fun p1 (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p0 x))))
(assert (forall ((x Int) (y Int)) (=> (and (p0 x) (= y (+ x 1))) (p1 y))))
(assert (forall ((x Int)) (=> (and (p1 x) (>= x 2)) false)))
(check-sat)
";

    #[test]
    fn record_then_lookup_hits_on_identical_reparse() {
        // Two SEPARATE parses of the same input must share one identity.
        let a = parse(SAFE_DAG);
        let b = parse(SAFE_DAG);
        assert_eq!(a.structural_identity(), b.structural_identity());
        record_acyclic_bmc_safe(&a, 3);
        assert_eq!(lookup_acyclic_bmc_safe(&b), Some(3));
        record_acyclic_bmc_safe(&a, 2);
        assert_eq!(
            lookup_acyclic_bmc_safe(&b),
            Some(3),
            "a shallower repeat must not erase the stronger cached proof"
        );
        record_acyclic_bmc_safe(&a, 4);
        assert_eq!(lookup_acyclic_bmc_safe(&b), Some(4));
    }

    #[test]
    fn distinct_problems_do_not_share_a_verdict() {
        let safe = parse(
            "\
(set-logic HORN)
(declare-fun distinct_cache_p0 (Int) Bool)
(declare-fun distinct_cache_p1 (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (distinct_cache_p0 x))))
(assert (forall ((x Int) (y Int))
  (=> (and (distinct_cache_p0 x) (= y (+ x 1))) (distinct_cache_p1 y))))
(assert (forall ((x Int))
  (=> (and (distinct_cache_p1 x) (>= x 2)) false)))
(check-sat)
",
        );
        // Structurally different problem: different bound in the query.
        let other = parse(
            "\
(set-logic HORN)
(declare-fun q0 (Int) Bool)
(declare-fun q1 (Int) Bool)
(assert (forall ((x Int)) (=> (= x 5) (q0 x))))
(assert (forall ((x Int) (y Int)) (=> (and (q0 x) (= y (+ x 2))) (q1 y))))
(assert (forall ((x Int)) (=> (and (q1 x) (>= x 100)) false)))
(check-sat)
",
        );
        assert_ne!(safe.structural_identity(), other.structural_identity());
        record_acyclic_bmc_safe(&safe, 7);
        // `other` was never recorded, so it must miss (never inherit `safe`'s
        // verdict) even though both are acyclic 2-predicate scalar DAGs.
        assert_eq!(lookup_acyclic_bmc_safe(&other), None);
    }

    #[test]
    fn datatype_registry_delimiters_cannot_alias_structural_identity() {
        let first_constructors = vec![("C1".to_owned(), Vec::new())];
        let second_constructors = vec![("C2".to_owned(), vec![("field".to_owned(), ChcSort::Int)])];

        let mut split = parse(SAFE_DAG);
        split.add_datatype_def("A".to_owned(), first_constructors.clone());
        split.add_datatype_def("T".to_owned(), second_constructors.clone());

        // Under the former line-oriented encoding, this public-API name
        // injected a fake datatype entry boundary:
        //
        //   d A=<first_constructors>
        //   d T=<second_constructors>
        //
        // and made this one-entry registry byte-identical to `split`.
        let mut fused = parse(SAFE_DAG);
        fused.add_datatype_def(
            format!("A={first_constructors:?}\nd T"),
            second_constructors,
        );

        assert_ne!(
            split.structural_identity(),
            fused.structural_identity(),
            "distinct datatype registries must have distinct cache identities"
        );
        record_acyclic_bmc_safe(&split, 3);
        assert_eq!(
            lookup_acyclic_bmc_safe(&fused),
            None,
            "a delimiter-bearing datatype name must not inherit another problem's Safe proof"
        );
    }
}
