// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive sweeps for the integer bound-lattice recognizer.
//!
//! Split out of `lia_bound_lattice_tests` to keep both files inside the quality
//! gate's per-file size limit; the literal model and clause builders live in
//! the parent module and are re-used here through `use super::*`.
//!
//! Every ACCEPT is re-evaluated at every point of an integer box with a plain
//! `i64` evaluator that shares no code with the recognizer, and the exact
//! ground truth is recomputed from an independent `gcd` model.

use super::*;
use crate::TermStore;

/// Smallest multiple of `g` that is `>= lo`, computed with plain `i64` ceiling
/// division — deliberately not the recognizer's `BigInt::div_ceil`.
fn no_multiple_in_range(g: i64, lo: i64, hi: i64) -> bool {
    assert!(g > 0);
    let mut k = lo.div_euclid(g);
    while k * g < lo {
        k += 1;
    }
    k * g > hi
}

#[test]
fn sweep_single_variable_box_is_exact_and_every_accept_re_evaluates_true() {
    // For `c·x ∈ [lo, hi]` any falsifying x has |c·x| <= 6, hence |x| <= 6, so
    // the ±12 box below decides validity EXACTLY for this family. That makes
    // the sweep an iff-check, not just a falsification search.
    let mut accepts = 0usize;
    let mut rejects = 0usize;
    for c in 1..=5i64 {
        for lo in -6..=6i64 {
            for hi in -6..=6i64 {
                let spec = [lower_bound_on_x(c, lo), upper_bound_on_x(c, hi)];
                let mut terms = TermStore::new();
                let clause = build_clause(&mut terms, &spec);
                let accepted = recognize_int_bound_lattice_gap(&terms, &clause);
                let falsifier = falsifying_point(&spec, 12);
                if accepted {
                    accepts += 1;
                    assert_eq!(
                        falsifier, None,
                        "ACCEPTED c={c} lo={lo} hi={hi} but it is falsified at {falsifier:?}",
                    );
                    // Independent re-evaluation at every point of the box.
                    for x in -12..=12i64 {
                        assert!(
                            spec.iter().any(|lit| lit.holds(x, 0)),
                            "accepted clause false at x={x} (c={c} lo={lo} hi={hi})",
                        );
                    }
                } else {
                    rejects += 1;
                }
                assert_eq!(
                    accepted,
                    falsifier.is_none(),
                    "verdict/ground-truth mismatch at c={c} lo={lo} hi={hi}",
                );
                assert_eq!(accepted, no_multiple_in_range(c, lo, hi) || lo > hi);
            }
        }
    }
    assert_eq!(accepts + rejects, 5 * 13 * 13);
    assert!(accepts > 100 && rejects > 100, "{accepts} / {rejects}");
}

#[test]
fn sweep_two_variable_box_never_accepts_a_falsifiable_clause() {
    // Two-variable forms have falsifiers far outside any small box (2x+3y=0 at
    // x=3,y=-2), so the box is a FALSIFICATION SEARCH here and the exact
    // ground truth is the independent gcd computation.
    let mut accepts = 0usize;
    for a in 1..=6i64 {
        for b in 1..=6i64 {
            for lo in -4..=4i64 {
                for hi in -4..=4i64 {
                    let spec = [
                        LitSpec {
                            coeff_x: a,
                            coeff_y: b,
                            constant: 0,
                            cmp: Cmp::Lt,
                            rhs: lo,
                            negated: false,
                        },
                        LitSpec {
                            coeff_x: a,
                            coeff_y: b,
                            constant: 0,
                            cmp: Cmp::Le,
                            rhs: hi,
                            negated: true,
                        },
                    ];
                    let mut terms = TermStore::new();
                    let clause = build_clause(&mut terms, &spec);
                    let accepted = recognize_int_bound_lattice_gap(&terms, &clause);
                    let g = num_integer::Integer::gcd(&a, &b);
                    let expected = lo > hi || no_multiple_in_range(g, lo, hi);
                    assert_eq!(
                        accepted, expected,
                        "a={a} b={b} lo={lo} hi={hi}: recognizer {accepted}, gcd model {expected}",
                    );
                    if accepted {
                        accepts += 1;
                        assert_eq!(
                            falsifying_point(&spec, 14),
                            None,
                            "ACCEPTED a={a} b={b} lo={lo} hi={hi} but a falsifier exists",
                        );
                    }
                }
            }
        }
    }
    assert!(accepts > 100, "{accepts}");
}

#[test]
fn sweep_affine_offsets_never_accept_a_falsifiable_clause() {
    // The constant term is folded into the bound VALUE by `parse_int_bound`;
    // sweeping offsets checks that folding on both literals independently.
    for c in 1..=4i64 {
        for off_lo in -3..=3i64 {
            for off_hi in -3..=3i64 {
                for lo in -4..=4i64 {
                    for hi in -4..=4i64 {
                        let spec = [
                            LitSpec {
                                coeff_x: c,
                                coeff_y: 0,
                                constant: off_lo,
                                cmp: Cmp::Lt,
                                rhs: lo,
                                negated: false,
                            },
                            LitSpec {
                                coeff_x: c,
                                coeff_y: 0,
                                constant: off_hi,
                                cmp: Cmp::Le,
                                rhs: hi,
                                negated: true,
                            },
                        ];
                        let mut terms = TermStore::new();
                        let clause = build_clause(&mut terms, &spec);
                        if recognize_int_bound_lattice_gap(&terms, &clause) {
                            assert_eq!(
                                falsifying_point(&spec, 20),
                                None,
                                "ACCEPTED c={c} off=({off_lo},{off_hi}) lo={lo} hi={hi} \
                                 but a falsifier exists",
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn sweep_wide_clauses_with_irrelevant_literals_stay_sound() {
    // Bury a swept core inside decoy literals on a SECOND variable. The decoys
    // can only make the clause easier to satisfy for the adversary, so any
    // accept must still survive the falsification search.
    for c in 1..=4i64 {
        for lo in -4..=4i64 {
            for hi in -4..=4i64 {
                for decoy in -2..=2i64 {
                    let spec = [
                        LitSpec {
                            coeff_x: 0,
                            coeff_y: 5,
                            constant: 0,
                            cmp: Cmp::Le,
                            rhs: decoy,
                            negated: true,
                        },
                        lower_bound_on_x(c, lo),
                        LitSpec {
                            coeff_x: 0,
                            coeff_y: 1,
                            constant: 0,
                            cmp: Cmp::Lt,
                            rhs: decoy,
                            negated: false,
                        },
                        upper_bound_on_x(c, hi),
                    ];
                    let mut terms = TermStore::new();
                    let clause = build_clause(&mut terms, &spec);
                    if recognize_int_bound_lattice_gap(&terms, &clause) {
                        assert_eq!(
                            falsifying_point(&spec, 16),
                            None,
                            "ACCEPTED c={c} lo={lo} hi={hi} decoy={decoy} with a falsifier",
                        );
                    }
                }
            }
        }
    }
}
