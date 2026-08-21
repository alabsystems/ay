// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive sweeps for the rank-1 two-row integer cut recognizer.
//!
//! Split out of `lia_cut_lattice_tests` to keep both files inside the quality
//! gate's per-file size limit; the literal model and clause builders live in
//! the parent module and are re-used here through `use super::*`.
//!
//! Every ACCEPT is re-evaluated at every point of an integer box with a plain
//! `i64` evaluator that shares no code with the recognizer. Where the box
//! decides validity EXACTLY the sweep is an iff-check against an independent
//! ground-truth model; elsewhere it is a falsification search, which is the
//! direction that matters — an accept the box falsifies would be UNSOUND.

use super::*;
use crate::TermStore;

/// Smallest multiple of `g` that is `>= lo` overshoots `hi`, computed with
/// plain `i64` ceiling division — deliberately not the recognizer's
/// `BigInt::div_ceil`.
fn no_multiple_in_range(g: i64, lo: i64, hi: i64) -> bool {
    assert!(g > 0);
    let mut k = lo.div_euclid(g);
    while k * g < lo {
        k += 1;
    }
    k * g > hi
}

/// SWEEP 1 — the two-row cut family, exhaustive and EXACT.
///
/// The system is `a·x + y ∈ [lo, hi]` together with `y ∈ [0, 0]`, whose only
/// integer solutions have `a·x ∈ [lo, hi]`. Every falsifying point therefore
/// has `|a·x| <= 6` and `y = 0`, so the ±12 box below decides validity exactly
/// and the sweep checks BOTH directions against an independent `gcd` model.
#[test]
fn sweep_two_row_elimination_box_is_exact_in_both_directions() {
    let mut accepts = 0usize;
    let mut rejects = 0usize;
    for a in 1..=5i64 {
        for lo in -6..=6i64 {
            for hi in -6..=6i64 {
                let spec = [
                    ge([a, 1, 0], lo),
                    le([a, 1, 0], hi),
                    ge([0, 1, 0], 0),
                    le([0, 1, 0], 0),
                ];
                let mut terms = TermStore::new();
                let clause = build_clause(&mut terms, &spec);
                let accepted = recognize_int_cut_lattice_gap(&terms, &clause);
                let falsifier = falsifying_point(&spec, 12);
                if accepted {
                    accepts += 1;
                    assert_eq!(
                        falsifier, None,
                        "ACCEPTED a={a} lo={lo} hi={hi} but it is falsified at {falsifier:?}",
                    );
                    // Independent re-evaluation at every point of the box.
                    for x in -12..=12i64 {
                        for y in -12..=12i64 {
                            assert!(
                                spec.iter().any(|lit| lit.holds([x, y, 0])),
                                "accepted clause false at x={x} y={y} (a={a} lo={lo} hi={hi})",
                            );
                        }
                    }
                } else {
                    rejects += 1;
                }
                assert_eq!(
                    accepted,
                    falsifier.is_none(),
                    "verdict/ground-truth mismatch at a={a} lo={lo} hi={hi}",
                );
                // Independent ground truth: the derived form is `a·x`, whose
                // attainable values are the multiples of `a`.
                assert_eq!(
                    accepted,
                    no_multiple_in_range(a, lo, hi) || lo > hi,
                    "independent gcd model disagrees at a={a} lo={lo} hi={hi}",
                );
            }
        }
    }
    assert_eq!(accepts + rejects, 5 * 13 * 13);
    assert!(accepts > 100 && rejects > 100, "{accepts} / {rejects}");
}

/// SWEEP 2 — NON-UNIT multipliers, exhaustive over the cancelling pair.
///
/// `p·x - q·y >= lo` with `q·y >= m` eliminates `y` at `λ = q/g, μ = p/g`,
/// deriving a lower bound on `(p·q/g)·x`; the third row supplies the upper
/// bound directly. A falsifier needs `|x| <= 8` and `|y| <= 8` for these
/// ranges, so the ±10 box is a genuine falsification search.
#[test]
fn sweep_non_unit_multiplier_pairs_never_accept_a_falsifiable_clause() {
    let mut accepts = 0usize;
    let mut checked = 0usize;
    for p in 1..=4i64 {
        for q in 1..=4i64 {
            for lo in -4..=4i64 {
                for m in -4..=4i64 {
                    for hi in -6..=6i64 {
                        let spec = [ge([p, -q, 0], lo), ge([0, q, 0], m), le([p * q, 0, 0], hi)];
                        let mut terms = TermStore::new();
                        let clause = build_clause(&mut terms, &spec);
                        checked += 1;
                        if !recognize_int_cut_lattice_gap(&terms, &clause) {
                            continue;
                        }
                        accepts += 1;
                        assert_eq!(
                            falsifying_point(&spec, 10),
                            None,
                            "ACCEPTED p={p} q={q} lo={lo} m={m} hi={hi} but it is falsifiable",
                        );
                        for x in -10..=10i64 {
                            for y in -10..=10i64 {
                                assert!(
                                    spec.iter().any(|lit| lit.holds([x, y, 0])),
                                    "accepted clause false at x={x} y={y} \
                                     (p={p} q={q} lo={lo} m={m} hi={hi})",
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(checked, 4 * 4 * 9 * 9 * 13);
    assert!(
        accepts > 200,
        "the sweep must actually exercise the cut path: {accepts} accepts"
    );
}

/// SWEEP 3 — three-variable chains, a falsification search.
///
/// `x - y >= b0`, `y - z >= b1`, `k·z >= b2` and `k·x <= hi` reach a bound on
/// `k·x` only through two successive eliminations, which this rank-1 rule
/// CANNOT do. The sweep's job is therefore twofold: no accept may be
/// falsifiable, and the accept count records exactly how much of the family
/// the bounded rule reaches.
#[test]
fn sweep_three_variable_chains_never_accept_a_falsifiable_clause() {
    let mut accepts = 0usize;
    let mut checked = 0usize;
    for b0 in -3..=3i64 {
        for b1 in -3..=3i64 {
            for k in 1..=4i64 {
                for b2 in -3..=3i64 {
                    for hi in -4..=4i64 {
                        let spec = [
                            ge([1, -1, 0], b0),
                            ge([0, 1, -1], b1),
                            ge([0, 0, k], b2),
                            le([k, 0, 0], hi),
                        ];
                        let mut terms = TermStore::new();
                        let clause = build_clause(&mut terms, &spec);
                        checked += 1;
                        if !recognize_int_cut_lattice_gap(&terms, &clause) {
                            continue;
                        }
                        accepts += 1;
                        assert_eq!(
                            falsifying_point(&spec, 10),
                            None,
                            "ACCEPTED b0={b0} b1={b1} k={k} b2={b2} hi={hi} but it is falsifiable",
                        );
                    }
                }
            }
        }
    }
    assert_eq!(checked, 7 * 7 * 4 * 7 * 9);
    assert!(
        accepts > 0,
        "the chain family must not be vacuously all-declines"
    );
}

/// SWEEP 4 — every clause the recognizer accepts anywhere in a mixed box is
/// re-checked by the independent evaluator, including clauses built from a
/// MIX of literal-read and derived bounds, and including clauses that carry
/// irrelevant extra literals. This is the direction that catches an unsound
/// accept regardless of which arm produced it.
#[test]
fn sweep_mixed_clauses_with_irrelevant_literals_stay_sound() {
    let mut accepts = 0usize;
    let mut checked = 0usize;
    for a in 1..=4i64 {
        for lo in -5..=5i64 {
            for hi in -5..=5i64 {
                for noise in -3..=3i64 {
                    let spec = [
                        ge([a, 1, 0], lo),
                        le([a, 1, 0], hi),
                        ge([0, 1, 0], 0),
                        le([0, 1, 0], 0),
                        // Irrelevant literals: a bound on a third variable and
                        // a loose bound on the same derived form.
                        ge([0, 0, 1], noise),
                        le([0, 0, 1], noise + 40),
                        ge([a, 1, 0], lo - 30),
                    ];
                    let mut terms = TermStore::new();
                    let clause = build_clause(&mut terms, &spec);
                    checked += 1;
                    if !recognize_int_cut_lattice_gap(&terms, &clause) {
                        continue;
                    }
                    accepts += 1;
                    assert_eq!(
                        falsifying_point(&spec, 9),
                        None,
                        "ACCEPTED a={a} lo={lo} hi={hi} noise={noise} but it is falsifiable",
                    );
                }
            }
        }
    }
    assert_eq!(checked, 4 * 11 * 11 * 7);
    assert!(accepts > 100, "{accepts}");
}
