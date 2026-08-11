// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression gate for BV-MBQI's SYMBOLIC ENTAILMENT discharge (`eb118111e`).
//!
//! BV-MBQI can only PROVE a `forall` by covering its binders' entire domain.
//! Enumeration does that by visiting every value, so it is confined to
//! `BV_EXHAUSTIVE_MAX_WIDTH = 8` (256 values/binder). The entailment check
//! reaches the same conclusion with ONE ground solve at any width: it skolemizes
//! the binders, builds `G AND NOT body[skolem]` over the GROUND slice `G` of the
//! assertions, and refutes it. `UNSAT` establishes `G |= forall x. body` over the
//! whole domain; `G` is Sat, so a model of `G` satisfies the forall too.
//!
//! Two things make this fragile enough to need a gate:
//!
//!   * The Sat is only emitted because `bv_quantifier_full_domain_proof` is honoured at
//!     BOTH quantifier gates — `map_quantifier_result` and the post-restore
//!     `explicit_certificate` list. Dropping it from either silently returns the
//!     answers to `unknown`: a COMPLETENESS regression, which trips no soundness
//!     canary and which the library test suite does not cover.
//!   * The certificate authorises a Sat that otherwise fails closed, so widening
//!     it is a WRONG-ANSWER risk in the other direction. `bug04_signed_min`
//!     pins that side.
//!
//! Verified to discriminate: before `eb118111e` the two wide-binder files
//! answered `unknown (:reason-unknown (incomplete quantifier-unhandled))`.

mod common;

fn solve_one(rel: &str) -> String {
    let path = common::workspace_path(rel);
    assert!(
        path.is_file(),
        "regression asset missing: {} — it is committed in-tree and must not be deleted",
        path.display()
    );
    let smt = std::fs::read_to_string(&path).expect("read regression asset");
    let outputs = common::solve_vec(&smt);
    outputs.first().cloned().unwrap_or_else(|| {
        panic!("no answer produced for {rel}");
    })
}

/// A width-32 forall that enumeration structurally cannot reach.
#[test]
fn wide_binder_forall_is_discharged_by_entailment() {
    assert_eq!(
        solve_one("benchmarks/smt/regression/bv_mbqi_entailment/wide_binder_sat.smt2"),
        "sat",
        "BV-MBQI failed to discharge a width-32 forall. The likely cause is that \
         `bv_quantifier_full_domain_proof` is no longer honoured at one of the two \
         quantifier gates (`map_quantifier_result`, or the post-restore \
         `explicit_certificate` list in result_mapping.rs). Do NOT weaken this to \
         accept `unknown` — losing the answer is the regression."
    );
}

/// The refutation direction at the same width.
#[test]
fn wide_binder_counterexample_still_refutes() {
    assert_eq!(
        solve_one("benchmarks/smt/regression/bv_mbqi_entailment/wide_binder_unsat.smt2"),
        "unsat",
        "the entailment check must still hand back a model-based counterexample \
         at widths enumeration cannot cover"
    );
}

/// The soundness side: a non-exhaustive pass must never conclude Sat.
#[test]
fn heuristic_sample_may_not_conclude_sat() {
    assert_eq!(
        solve_one("benchmarks/smt/regression/bv_mbqi_entailment/bug04_signed_min.smt2"),
        "unsat",
        "#bug04 regressed to a WRONG ANSWER: a boundary sample that misses the \
         `bvneg` signed-min witness concluded Sat. Only a pass covering the \
         binder's ENTIRE domain (exhaustive enumeration, or an entailment \
         refutation) may conclude Sat."
    );
}
