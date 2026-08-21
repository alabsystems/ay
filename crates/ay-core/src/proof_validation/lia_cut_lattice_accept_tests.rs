// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The shapes the rank-1 two-row integer cut recognizer EXISTS for.
//!
//! Split out of `lia_cut_lattice_tests` to keep both files inside the quality
//! gate's per-file size limit; the literal model and clause builders live in
//! the parent module and are re-used here through `use super::*`.
//!
//! Every accept records why the shipped single-form `IntBoundLatticeGap` rule
//! cannot reach it, and every accept is re-evaluated at every point of an
//! integer box by the parent module's plain-`i64` evaluator.

use super::*;
use crate::TermStore;
use num_bigint::BigInt;

// ---------------------------------------------------------------------------
// Accepts — the shapes the rule exists for.
// ---------------------------------------------------------------------------

/// THE TARGET. The verbatim #4751 empty-clause-closer head, built from its own
/// term shapes rather than from the `LitSpec` model:
///
/// ```text
/// (cl (not (<= -2 (+ D (* A -4)))) (not true) (not (<= 0 A)) (not (<= 0 C))
///     (not (<= 0 (+ C (- A)))) (not (<= 0 D))
///     (not (< (+ D (* A -2) -2) -2)))
/// ```
///
/// Its bounds sit on five different linear forms and no form carries both
/// directions, which is exactly why the shipped `IntBoundLatticeGap` rule
/// declines it. The two-row cut closes it: `D >= 0` with `2A - D >= 1` gives
/// `2A >= 1`, and `4A - D <= 2` with `2A - D >= 1` gives `2A <= 1`.
#[test]
fn accepts_the_benchmark_empty_clause_closer_head() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);
    let d = terms.mk_var("D", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let minus_two = terms.mk_int(BigInt::from(-2));
    let minus_four = terms.mk_int(BigInt::from(-4));
    let two = terms.mk_int(BigInt::from(2));

    let minus_four_a = terms.mk_mul(vec![minus_four, a]);
    let d_minus_four_a = terms.mk_add(vec![d, minus_four_a]);
    let l0 = terms.mk_le(minus_two, d_minus_four_a);
    let l0 = terms.mk_not(l0);

    let truth = terms.mk_bool(true);
    let l1 = terms.mk_not(truth);

    let l2 = terms.mk_le(zero, a);
    let l2 = terms.mk_not(l2);
    let l3 = terms.mk_le(zero, c);
    let l3 = terms.mk_not(l3);

    let neg_a = terms.mk_neg(a);
    let c_minus_a = terms.mk_add(vec![c, neg_a]);
    let l4 = terms.mk_le(zero, c_minus_a);
    let l4 = terms.mk_not(l4);

    let l5 = terms.mk_le(zero, d);
    let l5 = terms.mk_not(l5);

    let minus_two_a = terms.mk_mul(vec![minus_two, a]);
    let minus_two_again = terms.mk_int(BigInt::from(-2));
    let inner = terms.mk_add(vec![d, minus_two_a, minus_two_again]);
    let rhs = terms.mk_int(BigInt::from(-2));
    let l6 = terms.mk_lt(inner, rhs);
    let l6 = terms.mk_not(l6);
    let _ = two;

    let clause = vec![l0, l1, l2, l3, l4, l5, l6];

    assert!(
        !recognize_int_bound_lattice_gap(&terms, &clause),
        "precondition: the shipped single-form rule must decline this head, \
         otherwise the cut rule would be unnecessary"
    );
    let core = int_cut_lattice_gap_core(&terms, &clause)
        .expect("the two-row cut must certify the closer head");
    assert_eq!(core.gcd, BigInt::from(2));
    assert_eq!(core.lower, BigInt::from(1));
    assert_eq!(core.upper, BigInt::from(1));
    assert!(
        matches!(core.lower_row, CutRow::Combination { .. })
            && matches!(core.upper_row, CutRow::Combination { .. }),
        "both sides must come from a COMBINATION — this is what the shipped \
         rule cannot do: {core:?}"
    );
    // The derived form is `2A`, on one variable, with coefficient 2.
    assert_eq!(core.form.len(), 1);
    assert_eq!(core.form.get(&a), Some(&BigInt::from(2)));

    // Independent re-evaluation: no integer point in a generous box falsifies
    // the clause. `(not true)` is false everywhere, so the box search is over
    // the six arithmetic literals.
    for av in -20..=20i64 {
        for cv in -20..=20i64 {
            for dv in -20..=20i64 {
                // Every arithmetic literal is the NEGATION of one atom, so the
                // clause is true at a point exactly when some atom is FALSE.
                // `(not true)` is false everywhere and contributes nothing.
                let clause_true = dv - 4 * av < -2
                    || av < 0
                    || cv < 0
                    || cv - av < 0
                    || dv < 0
                    || dv - 2 * av - 2 >= -2;
                assert!(
                    clause_true,
                    "accepted clause is false at A={av} C={cv} D={dv}"
                );
            }
        }
    }
}

/// The rule SUBSUMES the shipped single-form one: `2q ∈ [1, 1]` still accepts,
/// and both sides are read straight off literals with no combination.
#[test]
fn subsumes_the_plain_bound_lattice_gap() {
    let spec = [ge([2, 0, 0], 1), le([2, 0, 0], 1)];
    let mut terms = TermStore::new();
    let clause = build_clause(&mut terms, &spec);
    assert!(recognize_int_bound_lattice_gap(&terms, &clause));
    let core = int_cut_lattice_gap_core(&terms, &clause).expect("accepts");
    assert!(matches!(core.lower_row, CutRow::Literal(_)));
    assert!(matches!(core.upper_row, CutRow::Literal(_)));
    assert_eq!(core.gcd, BigInt::from(2));
}

/// Both directions reached by elimination: `2x + y ∈ [1, 1]` with `y ∈ [0, 0]`
/// gives `2x ∈ [1, 1]`, impossible over ℤ. Rationally satisfiable at
/// `x = 1/2, y = 0`, so no Farkas certificate exists.
#[test]
fn accepts_a_pair_eliminated_in_both_directions() {
    let spec = [
        ge([2, 1, 0], 1),
        le([2, 1, 0], 1),
        ge([0, 1, 0], 0),
        le([0, 1, 0], 0),
    ];
    let core = accept_and_re_evaluate(&spec, 14);
    assert_eq!(core.gcd, BigInt::from(2));
}

/// NON-UNIT multipliers, and the witness reports them. `3x - 2y >= 1` with
/// `3y >= 2` needs `λ = 3, μ = 2` to cancel `y`, giving `9x >= 7`; with
/// `9x <= 8` the range `[7, 8]` holds no multiple of 9.
#[test]
fn accepts_non_unit_multipliers_and_reports_them() {
    let spec = [ge([3, -2, 0], 1), ge([0, 3, 0], 2), le([9, 0, 0], 8)];
    let core = accept_and_re_evaluate(&spec, 14);
    assert_eq!(core.gcd, BigInt::from(9));
    assert_eq!(core.lower, BigInt::from(7));
    assert_eq!(core.upper, BigInt::from(8));
    let CutRow::Combination {
        left_multiplier,
        right_multiplier,
        ..
    } = &core.lower_row
    else {
        panic!("the lower bound must be a combination: {core:?}");
    };
    let multipliers = (left_multiplier.clone(), right_multiplier.clone());
    assert!(
        multipliers == (BigInt::from(3), BigInt::from(2))
            || multipliers == (BigInt::from(2), BigInt::from(3)),
        "expected the canonical cancelling pair, got {multipliers:?}"
    );
}

/// Only the TIGHTEST bound in each direction closes the gap: the loose pair
/// `9x ∈ [3, 8]` contains 0's neighbour 9? no — it contains no multiple of 9
/// either, so the discriminating case is the reverse. Here the loose lower
/// bound `9x >= -20` leaves `[-20, 8]` (which contains 0), and only the tight
/// `9x >= 7` closes it; if the pool kept the first bound seen instead of the
/// tightest, this clause would be declined.
#[test]
fn accepts_only_when_the_tightest_derived_pair_conflicts() {
    let spec = [
        ge([3, -2, 0], -22),
        ge([3, -2, 0], 1),
        ge([0, 3, 0], 2),
        le([9, 0, 0], 8),
    ];
    let core = accept_and_re_evaluate(&spec, 14);
    assert_eq!(core.lower, BigInt::from(7), "the loose row must lose");
}
