// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end: quantified SAT certificates over an asserted `(and …)` root.
//!
//! LOIS (SMT-LIB `LRA/20160930-Kopczynski-LOIS`) asserts each query as ONE
//! root `(and (forall ..) ground ..)`. With proofs on, a quantified `sat`
//! needs a certificate the publication gate accepts, and every certificate
//! partition used to decline such a root outright ("non-forall, non-ground-
//! Bool assertion"), publishing `unknown` for 26 single queries that answer
//! `sat` the moment the same conjuncts are asserted separately. The
//! certificates now partition the root's conjunct view while the gate still
//! binds the witness to the authored root.
//!
//! The fixtures are reduced LOIS queries (incremental0, check-sats 29, 65 and
//! 70; cvc5 and z3 answer `sat` on each). The negative control is UNSAT: a
//! certificate that certified the universal leaf and dropped its ground
//! sibling would publish `sat` for it.

use ntest::timeout;

const PROOFS: &str = "(set-option :produce-proofs true)\n(set-option :produce-models true)\n";

fn results(body: &str) -> Vec<String> {
    crate::common::solve_authored_vec(&format!("{PROOFS}{body}"))
}

fn assert_sat(body: &str, label: &str) {
    let results = results(body);
    assert_eq!(
        results.first().map(String::as_str),
        Some("sat"),
        "{label}: expected sat, got {results:?}"
    );
}

/// LOIS incremental0 #29: one universal plus three ground bounds, all under
/// one `and` spine.
#[test]
#[timeout(60000)]
fn lois_upper_bound_and_root_is_sat() {
    assert_sat(
        "(set-logic LRA)
         (declare-const b Real)
         (declare-const a Real)
         (declare-const c Real)
         (declare-const h Real)
         (assert (and (forall ((g Real)) (or (or (or (> b g) (> a g)) (> c g)) (>= g h)))
                      (and (and (>= h b) (>= h a)) (>= h c))))
         (check-sat)",
        "lois-i0-029",
    );
}

/// LOIS incremental0 #65: a separate ground root plus an and-root whose
/// all-zero interpretation fails, so the certificate must search past
/// combination 0.
#[test]
#[timeout(60000)]
fn lois_strict_pair_and_root_is_sat() {
    assert_sat(
        "(set-logic LRA)
         (declare-const r Real)
         (declare-const s Real)
         (assert (> s r))
         (declare-const x Real)
         (assert (and (forall ((w Real)) (or (or (> r w) (> s w)) (>= w x)))
                      (and (>= x r) (>= x s))))
         (check-sat)",
        "lois-i0-065",
    );
}

/// LOIS incremental0 #70: two and-roots, each with its own universal, sharing
/// the interpretation of `r` and `s`.
#[test]
#[timeout(60000)]
fn lois_two_and_roots_share_one_interpretation() {
    assert_sat(
        "(set-logic LRA)
         (declare-const r Real)
         (declare-const s Real)
         (assert (> s r))
         (declare-const aa Real)
         (assert (and (forall ((w Real)) (or (or (> r w) (> s w)) (>= w aa)))
                      (and (>= aa r) (>= aa s))))
         (declare-const ab Real)
         (assert (and (forall ((w Real)) (or (or (> r w) (> s w)) (>= w ab)))
                      (and (>= ab r) (>= ab s))))
         (check-sat)",
        "lois-i0-070",
    );
}

/// NEGATIVE CONTROL: `∀g. a > g ∨ g ≥ h` holds iff `h ≤ a`, and the sibling
/// leaf demands `h > a`. UNSAT; `sat` here is the dropped-sibling wrong-SAT.
#[test]
#[timeout(60000)]
fn and_root_with_a_contradicting_ground_leaf_is_never_sat() {
    let results = results(
        "(set-logic LRA)
         (declare-const a Real)
         (declare-const h Real)
         (assert (and (forall ((g Real)) (or (> a g) (>= g h))) (> h a)))
         (check-sat)",
    );
    assert!(
        !results.iter().any(|r| r == "sat"),
        "an UNSAT and-root must never be certified sat, got {results:?}"
    );
}
