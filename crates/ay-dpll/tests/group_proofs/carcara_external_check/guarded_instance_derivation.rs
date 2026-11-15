// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guarded-instance refutations (#guarded-instance-checked-derivation), end to
//! end against pinned Carcara in the plain invocation.
//!
//! The guarded lane asserts `(or (not q) B[t̄])` against the proxy `q` of an
//! un-entailed universal `Q`; that clause is never an input, so a refutation
//! resting on it used to publish a lone `hole`. Consequence replay now derives
//! the clause's resolvent on `q` from the authored `(or L… Q …)` by `or` +
//! `forall_inst` + `resolution`, and those refutations publish a document the
//! checker re-derives.
//!
//! The planner's surface gate is what keeps that lane from publishing a
//! document the checker REJECTS: elaboration folds `(ite c true Q)` into the
//! same `(or c Q)` root, and a stitched proof over the folded root printed an
//! `assume` the input never states (measured: carcara `invalid` at the
//! `assume`, where the refutation was `holey` before). This pins both halves
//! end to end, since no checked-in corpus problem reaches the lane.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip,
    solve_or_fail_closed_and_maybe_get_proof, solve_unsat_and_get_proof, CarcaraVerdict,
};
use ntest::timeout;

/// Guarded refutations whose authored root is WRITTEN as the `or`: each must
/// publish a hole-free document pinned Carcara accepts.
const DERIVED: [(&str, &str); 3] = [
    (
        "guarded_ematched",
        "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const c Bool)(declare-const d Bool)\
         (assert (or c (forall ((x Int)) (> (f x) 0))))(assert (or (not c) d))(assert (not d))\
         (assert (< (f 1) 0))(check-sat)",
    ),
    (
        "guarded_enumerated",
        "(set-logic UFLIA)(declare-const c Bool)(declare-const d Bool)(declare-const y Int)\
         (assert (or c (forall ((x Int)) (> (+ x y) 100))))(assert (or (not c) d))(assert (not d))\
         (assert (< y 0))(check-sat)",
    ),
    (
        "guarded_two_roots",
        "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const c Bool)(declare-const d Bool)\
         (declare-const e Bool)(assert (or c (forall ((x Int)) (> (f x) 0))))\
         (assert (or e (forall ((x Int)) (> (f x) 0))))(assert (or (not c) d))(assert (not d))\
         (assert (< (f 1) 0))(check-sat)",
    ),
];

/// Guarded refutations the lane may NOT render as written: a root elaboration
/// folds into the `or` (`ite`, `not`/`and`), and roots whose literals it
/// reorders or that carry two universals. An `unsat` they publish may be
/// `holey` (a disclosed gap) or fail closed as `unknown`, but never carries a
/// document the checker rejects.
const NEVER_INVALID: [(&str, &str); 5] = [
    (
        "guarded_ite_folded",
        "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const c Bool)(declare-const d Bool)\
         (assert (ite c true (forall ((x Int)) (> (f x) 0))))(assert (or (not c) d))\
         (assert (not d))(assert (< (f 1) 0))(check-sat)",
    ),
    (
        "guarded_ite_folded_enumerated",
        "(set-logic UFLIA)(declare-const c Bool)(declare-const d Bool)(declare-const y Int)\
         (assert (ite c true (forall ((x Int)) (> (+ x y) 100))))(assert (or (not c) d))\
         (assert (not d))(assert (< y 0))(check-sat)",
    ),
    (
        "guarded_not_and_folded",
        "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const c Bool)(declare-const d Bool)\
         (assert (not (and (not c) (not (forall ((x Int)) (> (f x) 0))))))\
         (assert (or (not c) d))(assert (not d))(assert (< (f 1) 0))(check-sat)",
    ),
    (
        "guarded_permuted_three_literals",
        "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const c Bool)(declare-const d Bool)\
         (declare-const e Bool)(declare-const y Int)(assert (or e (forall ((x Int)) (> (f x) 0))))\
         (assert (or (< y 0) (forall ((x Int)) (> (f x) 0)) c))(assert (or (not c) d))\
         (assert (or (not (< y 0)) d))(assert (not d))(assert (< (f 1) 0))(check-sat)",
    ),
    (
        "guarded_two_universal_literals",
        "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-fun g (Int) Int)\
         (declare-const c Bool)(declare-const d Bool)\
         (assert (or c (forall ((x Int)) (> (f x) 0)) (forall ((x Int)) (> (g x) 0))))\
         (assert (or (not c) d))(assert (not d))(assert (< (f 1) 0))(assert (< (g 2) 0))\
         (check-sat)",
    ),
];

/// COUNTERFACTUAL: before the derivation each document was the single
/// `(step t0 (cl) :rule hole)` (carcara `holey`), so the hole-free assertion
/// fails; drop the `plan_guarded_clausal_instances` call and it fails again.
#[test]
#[timeout(120_000)]
fn guarded_refutations_publish_documents_the_checker_accepts() {
    for (label, problem) in DERIVED {
        let proof = solve_unsat_and_get_proof(problem, label);
        for forbidden in [":rule hole", ":rule trust"] {
            assert!(
                !proof.contains(forbidden),
                "{label}: the guarded instance must be derived, not a {forbidden}:\n{proof}"
            );
        }
        assert!(
            proof.contains(":rule forall_inst"),
            "{label}: the guarded instance is a `forall_inst` step:\n{proof}"
        );
        if let Some(carcara) = require_carcara_or_skip() {
            assert_eq!(
                carcara_verdict_without_allowances(&carcara, label, problem, &proof),
                CarcaraVerdict::Valid,
                "{label}: pinned carcara must re-derive every step:\n{proof}"
            );
        }
    }
}

/// COUNTERFACTUAL: make `guarded_source_is_written_as_this_clause` return
/// `true` and `guarded_ite_folded` prints `(assume … (or c (forall …)))`, which
/// the checker rejects (`invalid`) — this fails.
#[test]
#[timeout(120_000)]
fn a_guarded_root_the_lane_cannot_render_never_publishes_a_rejected_document() {
    for (label, problem) in NEVER_INVALID {
        let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(problem, label) else {
            continue;
        };
        if let Some(carcara) = require_carcara_or_skip() {
            assert_ne!(
                carcara_verdict_without_allowances(&carcara, label, problem, &proof),
                CarcaraVerdict::Invalid,
                "{label}: a published document must never be one the checker rejects:\n{proof}"
            );
        }
    }
}
