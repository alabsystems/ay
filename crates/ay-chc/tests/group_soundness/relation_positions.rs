// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relation applications outside `and` in a clause never make a safe system
//! Unsafe.
//!
//! The CHC parser took body atoms only from `and`; a relation application
//! under `or`/`not`/`ite`/`=`, or in a non-relation head, stayed in the
//! background constraint, where the SMT encoding reads it as a FREE Bool
//! variable. Every system below is safe (z3 5.1: `sat`) and AY answered
//! `unsat` on each at default and `--competition`. Found by the 2026-09-29 CHC
//! differential generator (`scripts/differential/gen/chc`, shape `spell`).
//! The parser now lifts top-level conjuncts into body atoms and refuses the
//! rest, so each is either decided correctly or not parsed at all.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const PREFIX: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)
(assert (P 1))
(assert (forall ((x Int)) (=> (P x) (Q (+ x 1)))))
";

/// Safe systems: P = {1}, Q = {2} (plus what the case adds, all at most 4), R = {}.
const SAFE_QUERIES: &[(&str, &str)] = &[
    ("or-in-body", "(assert (forall ((x Int)) (=> (and (P x) (or (Q x) (R x))) false)))"),
    ("not-in-body", "(assert (forall ((x Int)) (=> (and (Q x) (not (P x)) (> x 5)) false)))"),
    ("not-head", "(assert (forall ((x Int)) (=> (Q x) (not (P x)))))"),
    ("or-head", "(assert (forall ((x Int)) (=> (Q x) (or (not (P x)) (> x 5)))))"),
    ("implies-head", "(assert (forall ((x Int)) (=> (Q x) (=> (P x) (> x 5)))))"),
    ("negated-query", "(assert (forall ((x Int)) (not (and (P x) (< x 0)))))"),
    // A conjunctive head and a nested positive forall/implication head: Q stays {2}, 3, 4.
    ("conjunctive-head", "(assert (forall ((x Int)) (=> (P x) (and (Q (+ x 2)) (Q (+ x 3))))))\n\
                          (assert (forall ((z Int)) (=> (and (Q z) (> z 5)) false)))"),
    ("nested-forall-head", "(assert (forall ((x Int)) (=> (P x) (forall ((y Int)) (=> (and (> y x) (< y 5)) (Q y))))))\n\
                            (assert (forall ((z Int)) (=> (and (Q z) (> z 5)) false)))"),
];

fn check(label: &str, input: &str) {
    let Ok(problem) = ChcParser::parse(input) else {
        return; // refused: fail-closed
    };
    for strict_proofs in [false, true] {
        let mut config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
        config.strict_proofs = strict_proofs;
        let result = AdaptivePortfolio::new(problem.clone(), config).solve();
        assert!(
            !matches!(result, VerifiedChcResult::Unsafe(_)),
            "{label} is safe (z3: sat); strict_proofs = {strict_proofs}: {result:?}"
        );
    }
}

#[test]
#[timeout(300_000)]
fn relations_outside_and_never_make_a_safe_system_unsafe() {
    for (label, query) in SAFE_QUERIES {
        check(label, &format!("{PREFIX}{query}\n(check-sat)\n"));
    }
}

#[test]
#[timeout(180_000)]
fn a_conjunction_of_facts_is_not_a_false_query() {
    check(
        "conjunction-fact",
        "(set-logic HORN)
         (declare-fun P (Int) Bool)
         (declare-fun Q (Int) Bool)
         (assert (and (P 0) (Q 1)))
         (assert (forall ((x Int)) (=> (and (P x) (> x 0)) false)))
         (check-sat)",
    );
}
