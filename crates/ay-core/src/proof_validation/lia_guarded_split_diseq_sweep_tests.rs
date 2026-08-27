// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive sweeps for the guarded-split rule's disequality arm.
//!
//! Split out of `lia_guarded_split_diseq_tests` to keep both files inside the
//! quality gate's per-file size limit; the literal model and clause builders
//! live in the parent module and are re-used here through `use super::*`.
//!
//! SWEEP 1 is an EXACT iff-check: the parity family's validity is decided by
//! an independent finite ENUMERATION of the only variable a falsifier has any
//! freedom in, so both directions are pinned — an accept the enumeration
//! falsifies would be UNSOUND, and a decline it certifies is a completeness
//! gap the sweep would also report. SWEEPS 2 and 3 are falsification searches
//! over wider families, which is the direction that matters.

use super::*;

/// SWEEP 1 — the corpus parity family, exhaustive and EXACT.
///
/// ```text
/// (cl (not (= (a·x + y) k)) (< y lo) (not (<= y hi)) (= y v))
/// ```
///
/// The negation asserts `a·x + y = k`, `lo <= y <= hi` and `y != v`. Since
/// `y = k - a·x`, the reachable `y` are exactly `{ t : t ≡ k (mod a) }`, so a
/// falsifier exists iff some `y` in `[lo, hi]` satisfies `y ≡ k (mod a)` and
/// `y != v`. That is a FINITE enumeration over `[lo, hi]` and it decides
/// validity exactly — computed here with plain `i64` `rem_euclid`, sharing no
/// code with the recognizer.
#[test]
fn sweep_parity_family_is_exact_in_both_directions() {
    let mut accepts = 0usize;
    let mut rejects = 0usize;
    for a in 1..=4i64 {
        for k in -4..=4i64 {
            for lo in -4..=4i64 {
                for hi in -4..=4i64 {
                    for v in -4..=4i64 {
                        let spec = [
                            eq_row([a, 1, 0], k),
                            ge([0, 1, 0], lo),
                            le([0, 1, 0], hi),
                            diseq([0, 1, 0], v),
                        ];
                        let accepted = recognizes(&spec);
                        let ground_truth =
                            !(lo..=hi).any(|y| y.rem_euclid(a) == k.rem_euclid(a) && y != v);
                        assert_eq!(
                            accepted, ground_truth,
                            "verdict/enumeration mismatch a={a} k={k} lo={lo} \
                             hi={hi} v={v}"
                        );
                        if accepted {
                            accepts += 1;
                            // Independent re-evaluation at every point of a box.
                            for x in -8..=8i64 {
                                for y in -8..=8i64 {
                                    assert!(
                                        spec.iter().any(|lit| lit.holds([x, y, 0])),
                                        "accepted clause FALSE at x={x} y={y} \
                                         (a={a} k={k} lo={lo} hi={hi} v={v})"
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
    }
    assert_eq!(accepts + rejects, 4 * 9 * 9 * 9 * 9);
    assert!(accepts > 100 && rejects > 100, "{accepts} / {rejects}");
}

/// SWEEP 2 — a NON-UNIT coefficient on the SPLIT form.
///
/// The split literal is `(= (b·y) v)`, so the disequality is `b·y != v` and
/// the branches are `b·y >= v+1` and `b·y <= v-1`. That pair is sound for any
/// `b` (it is implied by the disequality over ℤ) but deliberately NOT tightest,
/// so this sweep is a falsification search rather than an iff-check: every
/// ACCEPT is re-evaluated at every point of a generous box.
#[test]
fn sweep_non_unit_split_coefficients_never_accept_a_falsifiable_clause() {
    let mut accepts = 0usize;
    let mut checked = 0usize;
    for b in 1..=4i64 {
        for lo in -4..=4i64 {
            for hi in -4..=4i64 {
                for v in -6..=6i64 {
                    let spec = [ge([0, b, 0], lo), le([0, b, 0], hi), diseq([0, b, 0], v)];
                    checked += 1;
                    if !recognizes(&spec) {
                        continue;
                    }
                    accepts += 1;
                    assert_eq!(
                        falsifying_point(&spec, 10),
                        None,
                        "ACCEPTED b={b} lo={lo} hi={hi} v={v} but it is falsifiable"
                    );
                    for y in -10..=10i64 {
                        assert!(
                            spec.iter().any(|lit| lit.holds([0, y, 0])),
                            "accepted clause FALSE at y={y} (b={b} lo={lo} hi={hi} v={v})"
                        );
                    }
                }
            }
        }
    }
    assert!(checked > 1000 && accepts > 20, "{accepts} / {checked}");
}

/// SWEEP 3 — IRRELEVANT literals and a second split candidate.
///
/// The accepted parity core is padded with a bound on a third variable that
/// takes no part in the refutation, and with a SECOND positive equality that
/// is not the one the refutation needs. Neither may change the verdict, and
/// no accept may be falsifiable — the padding literals are the ones a
/// truncating or order-sensitive implementation would trip on.
#[test]
fn sweep_irrelevant_literals_and_second_candidates_stay_sound() {
    let mut accepts = 0usize;
    let mut checked = 0usize;
    for k in -3..=3i64 {
        for hi in -3..=3i64 {
            for v in -3..=3i64 {
                for pad in -3..=3i64 {
                    let core = [
                        eq_row([2, 1, 0], k),
                        ge([0, 1, 0], 0),
                        le([0, 1, 0], hi),
                        diseq([0, 1, 0], v),
                    ];
                    let padded = [
                        core[0],
                        core[1],
                        le([0, 0, 1], pad),
                        core[2],
                        diseq([0, 0, 1], pad + 100),
                        core[3],
                    ];
                    let core_ok = recognizes(&core);
                    let padded_ok = recognizes(&padded);
                    checked += 1;
                    assert!(
                        !core_ok || padded_ok,
                        "padding removed an accept: k={k} hi={hi} v={v} pad={pad}"
                    );
                    if padded_ok {
                        accepts += 1;
                        assert_eq!(
                            falsifying_point(&padded, 8),
                            None,
                            "ACCEPTED a padded clause that is falsifiable: \
                             k={k} hi={hi} v={v} pad={pad}"
                        );
                    }
                }
            }
        }
    }
    assert!(checked > 300 && accepts > 10, "{accepts} / {checked}");
}

/// SWEEP 4 — the arm must never rescue a clause whose disequality is the ONLY
/// thing making it valid over ℚ but not over ℤ in the WRONG direction: a plain
/// bounded interval with no lattice obstruction. Every accept here must be a
/// genuine empty interval.
#[test]
fn sweep_plain_intervals_accept_only_genuinely_empty_ranges() {
    for lo in -5..=5i64 {
        for hi in -5..=5i64 {
            for v in -5..=5i64 {
                let spec = [ge([0, 1, 0], lo), le([0, 1, 0], hi), diseq([0, 1, 0], v)];
                let accepted = recognizes(&spec);
                // Ground truth: some integer in [lo, hi] other than v.
                let falsifiable = (lo..=hi).any(|y| y != v);
                assert_eq!(
                    accepted, !falsifiable,
                    "verdict/ground-truth mismatch lo={lo} hi={hi} v={v}"
                );
            }
        }
    }
}
