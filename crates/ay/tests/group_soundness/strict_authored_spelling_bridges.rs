// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored spellings whose certificate the printer refused are strict
//! premises now, and a spelling pinned carcara cannot expand still is not.
//!
//! MEASURED at `e9ba9acac`: each script below answered `unsat` under
//! `ay --proof` with `c ay.proof.artifact-refused` and no document, and
//! `--strict-proofs` answered `unknown` ("incomplete proof-unrenderable"):
//! a negative fold over an operand that keeps its own authored spelling
//! (`(= (bvult b #x03) false)`), `(not (distinct x y))` feeding a `cong`, and
//! `(=> (>= y 0) (<= x 3))` beside the row that confines `(<= 0 y)`. Every
//! strict route now answers `unsat` with a certificate that assumes only what
//! the input asserts (`alethe_printer/authored_assume/`). A negated CHAINED
//! comparison has no pinned-carcara rule and keeps the strict `unknown`.
//!
//! The operand-swapped comparison schema behind the third must never publish
//! a strict certificate pinned carcara rejects: a `forall_inst` instance whose
//! comparison is ground (`(> 5 7)` from a pattern-guarded `(> 5 w)`) has no
//! checked `comp_simplify` reversal, because pinned carcara EVALUATES
//! `(< 7 5)`. MEASURED before `comparison_reversal_step` declined that pair:
//! `--strict-proofs` printed `unsat` with `unsat_admission=strict-proof` over
//! a document pinned carcara answered `invalid`.

use super::strict_admission_routes::{
    authored_assertions, premise_assumes, run_route, unproved_rules, StrictRoute, ALL_ROUTES,
};
use crate::alethe_dialect_disclosure::pinned_carcara_verdict;
use ntest::timeout;

const BRIDGED: [(&str, &str); 3] = [
    (
        "negative_fold",
        "(set-logic QF_BV)\n(declare-const b (_ BitVec 8))\n\
         (assert (= (bvult b #x03) false))\n(assert (bvult b #x03))\n(check-sat)\n",
    ),
    (
        "negated_distinct_cong",
        "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n\
         (assert (not (distinct x y)))\n(assert (> x (+ y 2)))\n(check-sat)\n",
    ),
    (
        "implication_beside_antecedent",
        "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n\
         (assert (=> (>= y 0) (<= x 3)))\n(assert (> x 5))\n(assert (>= y 0))\n(check-sat)\n",
    ),
];

/// Pinned carcara (canonical invocation) must re-derive the strict
/// certificate in full; skipped when carcara is not installed.
fn assert_carcara_valid(context: &str, script: &str, document: &str) {
    let dir = tempfile::tempdir().expect("tempdir");
    let (problem, proof) = (dir.path().join("q.smt2"), dir.path().join("q.alethe"));
    std::fs::write(&problem, script).expect("write the query");
    std::fs::write(&proof, document).expect("write the certificate");
    if let Some((verdict, stderr)) = pinned_carcara_verdict(&problem, &proof) {
        assert_eq!(verdict, "valid", "{context}\ncarcara: {stderr}");
    }
}

#[test]
#[timeout(600_000)]
fn a_bridged_authored_spelling_is_a_strict_premise() {
    for (label, script) in BRIDGED {
        let authored = authored_assertions(script);
        for route in ALL_ROUTES {
            let outcome = run_route(route, script);
            let context = format!("{label}: {}", outcome.context);
            assert_eq!(outcome.verdicts, ["unsat"], "{context}");
            if matches!(route, StrictRoute::StdinPlain) {
                continue;
            }
            assert_eq!(unproved_rules(&outcome.document), 0, "{context}");
            let assumes = premise_assumes(&outcome.document);
            assert!(!assumes.is_empty(), "{context}");
            for assume in &assumes {
                assert!(
                    authored.contains(assume),
                    "strict published a certificate assuming `{assume}`, which the input does \
                     not assert: {context}"
                );
            }
            if matches!(route, StrictRoute::File) {
                assert_carcara_valid(&context, script, &outcome.document);
            }
        }
    }
}

/// NEGATIVE TWIN: pinned carcara has no rule that expands a chained
/// comparison, so its negation is no strict premise and no route answers
/// `unsat`.
#[test]
#[timeout(600_000)]
fn a_negated_chained_comparison_is_still_no_strict_premise() {
    let script = "(set-logic QF_LIA)\n(declare-const x Int)\n\
                  (assert (not (> x 60000 0)))\n(assert (> x 60000))\n(check-sat)\n";
    for route in ALL_ROUTES {
        let outcome = run_route(route, script);
        assert_eq!(outcome.verdicts, ["unknown"], "{}", outcome.context);
    }
}

/// Pattern-guarded instances whose comparison turns ground: strict publishes
/// `unsat` with a certificate pinned carcara re-derives in full.
const GROUND_COMPARISON_INSTANCES: [(&str, &str); 2] = [
    (
        "pattern_int",
        "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n\
         (assert (forall ((w Int)) (! (=> (P w) (> 5 w)) :pattern ((P w)))))\n\
         (assert (P 7))\n(check-sat)\n",
    ),
    (
        "bounded_array_vc",
        "(set-logic UFLIA)\n(declare-fun a (Int) Int)\n\
         (assert (forall ((i Int)) (! (=> (> 10 i) (>= (a i) 0)) :pattern ((a i)))))\n\
         (assert (< (a 2) 0))\n(check-sat)\n",
    ),
];

#[test]
#[timeout(600_000)]
fn a_ground_comparison_instance_never_publishes_a_rejected_strict_certificate() {
    for (label, script) in GROUND_COMPARISON_INSTANCES {
        let outcome = run_route(StrictRoute::File, script);
        let context = format!("{label}: {}", outcome.context);
        assert_eq!(outcome.verdicts, ["unsat"], "{context}");
        assert_eq!(unproved_rules(&outcome.document), 0, "{context}");
        assert_carcara_valid(&context, script, &outcome.document);
    }
}
