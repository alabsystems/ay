// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the guarded-split rule's ZERO-SPLIT arm: the base rows
//! alone, with the clause's EQUALITY literals substituted, are already
//! infeasible over ℤ.
//!
//! No case analysis is involved and none is claimed — `¬C` entails every base
//! row, so refuting the base rows refutes `¬C`. The arm exists because BOTH
//! shipped lattice rules skip equality literals entirely (`parse_int_bound`
//! returns `None` for `=`), and on this corpus family the parity lives in
//! nothing else.
//!
//! Split out of `lia_guarded_split_diseq_tests` to keep both files inside the
//! quality gate's per-file size limit; the literal model, the clause builders
//! and the independent evaluator live in the parent module and are re-used
//! here through `use super::*`.

use super::*;
use crate::{Sort, TermStore};
use num_bigint::BigInt;

/// Which guard of the zero-split arm each test defends.
pub(super) const ZERO_SPLIT_GUARD_LEDGER: &[(&str, &str, bool)] = &[
    (
        "equality_substitution_refutes: the base rows must be refuted by the \
         SAME `branch_refuted` the split arms use — no weaker test",
        "rejects_base_rows_that_are_satisfiable_over_the_integers",
        true,
    ),
    (
        "equality_substitution_refutes: at least ONE equality row is required \
         (SCOPE — without one this degenerates to the cheaper cut rule every \
         caller has already asked; requiring it costs completeness nowhere \
         and cannot admit a false clause)",
        "declines_a_pure_inequality_clause_that_carries_no_equality_row",
        false,
    ),
    (
        "equality_substitution_refutes: MAX_GUARDED_ROWS bounds the \
         substitution, declining OUTRIGHT rather than truncating (SCOPE — a \
         work bound; a larger row set only strengthens the hypothesis being \
         refuted)",
        "declines_a_clause_whose_equality_rows_pass_the_row_cap",
        false,
    ),
];

#[test]
fn zero_split_guard_ledger_names_a_test_per_guard() {
    assert_eq!(ZERO_SPLIT_GUARD_LEDGER.len(), 3);
    assert_eq!(
        ZERO_SPLIT_GUARD_LEDGER
            .iter()
            .filter(|(_, _, c)| *c)
            .count(),
        1
    );
}

/// The corpus clause, copied literally from the census dump of
/// `benchmarks/smt/QF_LIA/int_incompleteness2.smt2`:
///
/// ```text
/// (cl (not (= (+ (* k3 3) r) (+ (* k1 3) (* k2 6)))) (not (<= 1 r))
///     (not (<= r 2)))
/// ```
///
/// The negation asserts `3k3 + r = 3k1 + 6k2` and `1 <= r <= 2`. The equality
/// makes `r` a multiple of 3, and `[1, 2]` holds none — rationally it is
/// satisfiable at `r = 3/2, k1 = k2 = 0, k3 = 1/2`, so no Farkas certificate
/// exists. There is NO positive `=` and NO `(not (or ..))` literal, so both
/// split arms have nothing to split on.
#[test]
fn accepts_the_corpus_divisibility_conflict_with_no_split_source() {
    let mut terms = TermStore::new();
    let k1 = terms.mk_var("k1", Sort::Int);
    let k2 = terms.mk_var("k2", Sort::Int);
    let k3 = terms.mk_var("k3", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let three_k3 = terms.mk_mul(vec![three, k3]);
    let lhs = terms.mk_add(vec![three_k3, r]);
    let three_b = terms.mk_int(BigInt::from(3));
    let three_k1 = terms.mk_mul(vec![three_b, k1]);
    let six = terms.mk_int(BigInt::from(6));
    let six_k2 = terms.mk_mul(vec![six, k2]);
    let rhs = terms.mk_add(vec![three_k1, six_k2]);
    let eq = terms.mk_eq(lhs, rhs);
    let l0 = terms.mk_not_raw(eq);
    let one = terms.mk_int(BigInt::from(1));
    let lower = terms.mk_le(one, r);
    let l1 = terms.mk_not_raw(lower);
    let two = terms.mk_int(BigInt::from(2));
    let upper = terms.mk_le(r, two);
    let l2 = terms.mk_not_raw(upper);
    let clause = vec![l0, l1, l2];

    assert!(
        !recognize_int_bound_lattice_gap(&terms, &clause),
        "precondition: the bound-lattice rule never reads the equality"
    );
    assert!(
        !recognize_int_cut_lattice_gap(&terms, &clause),
        "precondition: the cut-lattice rule never reads the equality either, \
         and `1 <= r <= 2` alone has attainable values"
    );
    assert!(
        recognize_int_guarded_split_gap(&terms, &clause),
        "the zero-split arm must certify the corpus divisibility conflict"
    );

    // Independent re-evaluation over an integer box.
    for k1 in -6..=6i64 {
        for k2 in -6..=6i64 {
            for k3 in -6..=6i64 {
                for r in -6..=6i64 {
                    let witness = 3 * k3 + r == 3 * k1 + 6 * k2;
                    assert!(
                        !witness || !(1 <= r) || !(r <= 2),
                        "accepted clause is FALSE at k1={k1} k2={k2} k3={k3} r={r}"
                    );
                }
            }
        }
    }
}

/// FALSIFYING ASSIGNMENT `x = 0, y = 0`: the equality `2x + y = 0` holds and
/// `0 <= y <= 1` holds, so every literal of the clause is false. The base rows
/// are satisfiable over ℤ and the arm must decline.
#[test]
fn rejects_base_rows_that_are_satisfiable_over_the_integers() {
    let spec = [eq_row([2, 1, 0], 0), ge([0, 1, 0], 0), le([0, 1, 0], 1)];
    assert!(
        falsified_at(&spec, [0, 0, 0]),
        "the negative's own witness must falsify the clause"
    );
    assert!(
        !recognizes(&spec),
        "ACCEPTED a clause false at x = 0, y = 0"
    );
}

/// SCOPE: a clause with no equality row at all is left to the cut rule. The
/// clause below IS a genuine integer tautology (`2y ∈ [1, 1]` has no integer
/// solution) and the cut rule accepts it, so the decline here is the scope
/// guard and nothing else — no validity is lost, only a duplicate route.
#[test]
fn declines_a_pure_inequality_clause_that_carries_no_equality_row() {
    let spec = [ge([0, 2, 0], 1), le([0, 2, 0], 1)];
    let mut terms = TermStore::new();
    let clause = build_clause(&mut terms, &spec);
    assert!(
        recognize_int_cut_lattice_gap(&terms, &clause),
        "the shipped cut rule owns this shape"
    );
    assert!(
        !recognize_int_guarded_split_gap(&terms, &clause),
        "the zero-split arm requires an equality row"
    );
}

/// The row cap declines OUTRIGHT rather than truncating, so acceptance can
/// never depend on literal order. The unpadded core is accepted, so the
/// decline is the cap and nothing else.
#[test]
fn declines_a_clause_whose_equality_rows_pass_the_row_cap() {
    let core = [eq_row([3, 1, 0], 0), ge([0, 1, 0], 1), le([0, 1, 0], 2)];
    assert!(recognizes(&core), "the unpadded core must be accepted");

    let mut spec = core.to_vec();
    for k in 0..120i64 {
        spec.push(eq_row([0, 0, 1], 10_000 + k));
    }
    assert!(
        !recognizes(&spec),
        "a clause past the row cap must be declined, not truncated"
    );
}

/// SWEEP — the divisibility family, exhaustive and EXACT.
///
/// ```text
/// (cl (not (= (a·x + y) k)) (< y lo) (not (<= y hi)))
/// ```
///
/// Validity is decided by an independent finite enumeration of `[lo, hi]`:
/// a falsifier exists iff some `y` there satisfies `y ≡ k (mod a)`.
#[test]
fn sweep_zero_split_divisibility_family_is_exact() {
    let mut accepts = 0usize;
    let mut rejects = 0usize;
    for a in 1..=4i64 {
        for k in -4..=4i64 {
            for lo in -4..=4i64 {
                for hi in -4..=4i64 {
                    let spec = [eq_row([a, 1, 0], k), ge([0, 1, 0], lo), le([0, 1, 0], hi)];
                    let accepted = recognizes(&spec);
                    let ground_truth = !(lo..=hi).any(|y| y.rem_euclid(a) == k.rem_euclid(a));
                    assert_eq!(
                        accepted, ground_truth,
                        "verdict/enumeration mismatch a={a} k={k} lo={lo} hi={hi}"
                    );
                    if accepted {
                        accepts += 1;
                        for x in -8..=8i64 {
                            for y in -8..=8i64 {
                                assert!(
                                    spec.iter().any(|lit| lit.holds([x, y, 0])),
                                    "accepted clause FALSE at x={x} y={y} \
                                     (a={a} k={k} lo={lo} hi={hi})"
                                );
                            }
                        }
                    } else {
                        rejects += 1;
                    }
                }
            }
        }
    }
    assert_eq!(accepts + rejects, 4 * 9 * 9 * 9);
    assert!(accepts > 50 && rejects > 50, "{accepts} / {rejects}");
}
