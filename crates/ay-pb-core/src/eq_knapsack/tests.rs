// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbLit, PbTerm};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn not(var: u32) -> PbLit {
    PbLit { var, negated: true }
}

fn ge_row(terms: &[(i128, PbLit)], rhs: i128) -> PbConstraint {
    PbConstraint {
        terms: terms
            .iter()
            .map(|&(coeff, l)| PbTerm {
                coeff,
                lits: vec![l],
            })
            .collect(),
        rel: PbRel::Ge,
        rhs,
    }
}

fn eq_row(terms: &[(i128, PbLit)], rhs: i128) -> PbConstraint {
    PbConstraint {
        rel: PbRel::Eq,
        ..ge_row(terms, rhs)
    }
}

fn never_stop() -> impl FnMut() -> bool {
    || false
}

#[test]
fn detects_eq_row() {
    // total = 15, raw target 8: orientation normalization flips every
    // item to the equivalent complement problem with target 7.
    let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 8)];
    let knap = EqKnapsack::detect(&rows).expect("must detect single Eq row");
    assert_eq!(knap.target, 7);
    assert_eq!(knap.items.len(), 3);
    assert!(knap.items.iter().all(|i| i.flipped));

    // A below-half target keeps the plain orientation.
    let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 7)];
    let knap = EqKnapsack::detect(&rows).expect("must detect single Eq row");
    assert_eq!(knap.target, 7);
    assert!(knap.items.iter().all(|i| !i.flipped));
}

#[test]
fn detects_complementary_ge_pair() {
    let rows = [
        ge_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 8),
        ge_row(&[(-3, lit(1)), (-5, lit(2)), (-7, lit(3))], -8),
    ];
    let knap = EqKnapsack::detect(&rows).expect("must detect complementary Ge pair");
    // Orientation-normalized: min(8, 15-8) = 7.
    assert_eq!(knap.target, 7);
    assert_eq!(knap.items.len(), 3);
}

#[test]
fn detects_pair_in_either_order() {
    let rows = [
        ge_row(&[(-3, lit(1)), (-5, lit(2))], -5),
        ge_row(&[(3, lit(1)), (5, lit(2))], 5),
    ];
    assert!(EqKnapsack::detect(&rows).is_some());
}

#[test]
fn detects_negated_literal_form() {
    // 3*~x1 + 5*x2 == 5  ->  -3*x1 + 5*x2 == 2  ->  flipped item on x1,
    // raw target 2 + 3 = 5; total = 8, so orientation normalization
    // complements both items down to target 3.
    let rows = [eq_row(&[(3, not(1)), (5, lit(2))], 5)];
    let knap = EqKnapsack::detect(&rows).expect("negated literals must canonicalize");
    assert_eq!(knap.target, 3);
    let flipped: Vec<bool> = knap.items.iter().map(|i| i.flipped).collect();
    assert_eq!(flipped, vec![false, true]);
}

#[test]
fn declines_non_complementary_pair() {
    let rows = [
        ge_row(&[(3, lit(1)), (5, lit(2))], 4),
        ge_row(&[(-3, lit(1)), (-5, lit(2))], -5),
    ];
    assert!(EqKnapsack::detect(&rows).is_none());
}

#[test]
fn declines_mismatched_vars() {
    let rows = [
        ge_row(&[(3, lit(1)), (5, lit(2))], 4),
        ge_row(&[(-3, lit(1)), (-5, lit(3))], -4),
    ];
    assert!(EqKnapsack::detect(&rows).is_none());
}

#[test]
fn declines_single_ge_row() {
    let rows = [ge_row(&[(3, lit(1)), (5, lit(2))], 4)];
    assert!(EqKnapsack::detect(&rows).is_none());
}

#[test]
fn declines_nonlinear_term() {
    let mut row = eq_row(&[(3, lit(1))], 3);
    row.terms.push(PbTerm {
        coeff: 2,
        lits: vec![lit(2), lit(3)],
    });
    assert!(EqKnapsack::detect(&[row]).is_none());
}

#[test]
fn merges_duplicate_vars() {
    // 3*x1 + 2*x1 == 5 -> single item coeff 5.
    let rows = [eq_row(&[(3, lit(1)), (2, lit(1))], 5)];
    let knap = EqKnapsack::detect(&rows).expect("duplicates must merge");
    assert_eq!(knap.items.len(), 1);
    assert_eq!(knap.items[0].coeff, 5);
}

#[test]
fn cancelled_duplicate_drops_to_zero_coeff() {
    // 3*x1 - 3*x1 + 5*x2 == 5 -> x1 vanishes.
    let rows = [eq_row(&[(3, lit(1)), (-3, lit(1)), (5, lit(2))], 5)];
    let knap = EqKnapsack::detect(&rows).expect("cancelled var must drop");
    assert_eq!(knap.items.len(), 1);
    assert_eq!(knap.items[0].var, 2);
}

#[test]
fn solve_sat_finds_witness() {
    let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 10)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    match knap.solve(&mut never_stop()) {
        EqKnapsackOutcome::Sat(assignment) => {
            let sum: i128 = assignment
                .iter()
                .map(|&(var, val)| match (var, val) {
                    (1, true) => 3,
                    (2, true) => 5,
                    (3, true) => 7,
                    _ => 0,
                })
                .sum();
            assert_eq!(sum, 10, "witness must satisfy the equality");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn solve_unsat_when_unreachable() {
    // 3, 5, 7: cannot make 4.
    let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 4)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);
}

#[test]
fn solve_unsat_target_out_of_range() {
    let rows = [eq_row(&[(3, lit(1))], 100)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);

    let rows = [eq_row(&[(3, lit(1))], -1)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);
}

#[test]
fn solve_with_flipped_items() {
    // 4*~x1 + 6*x2 == 4: x1 false, x2 false — or x1 true impossible
    // (target would need 0 or 6 from x2 alone: 4-... ). Enumerate:
    // x1=F,x2=F -> 4. SAT with x1 false.
    let rows = [eq_row(&[(4, not(1)), (6, lit(2))], 4)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    match knap.solve(&mut never_stop()) {
        EqKnapsackOutcome::Sat(assignment) => {
            let val = |v: u32| assignment.iter().find(|(var, _)| *var == v).unwrap().1;
            let lhs = 4 * i128::from(!val(1)) + 6 * i128::from(val(2));
            assert_eq!(lhs, 4);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn interrupt_is_inconclusive() {
    let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 10)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    let mut always_stop = || true;
    assert_eq!(
        knap.solve(&mut always_stop),
        EqKnapsackOutcome::Inconclusive
    );
}

#[test]
fn budget_declines_oversized_target() {
    // Both orientations exceed MAX_TARGET (total = 2*(MAX+5), target =
    // MAX+5 in either orientation), so the budget must decline.
    let big = i128::from(MAX_TARGET) + 5;
    let rows = [eq_row(&[(big, lit(1)), (big, lit(2))], big)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    assert!(!knap.within_budget());
}

#[test]
fn orientation_normalization_rescues_oversized_raw_target() {
    // Raw target MAX+5 exceeds the cap, but the complement target is 0,
    // so normalization keeps the instance solvable in budget.
    let big = i128::from(MAX_TARGET) + 5;
    let rows = [eq_row(&[(big, lit(1))], big)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    assert!(knap.within_budget());
    match knap.solve(&mut never_stop()) {
        EqKnapsackOutcome::Sat(assignment) => {
            assert_eq!(assignment, vec![(1, true)]);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn budget_accepts_trivially_unsat_huge_target() {
    // Out-of-range target never allocates, so it is always in budget and
    // resolves Unsat immediately.
    let rows = [eq_row(&[(3, lit(1))], i128::MAX / 2)];
    let knap = EqKnapsack::detect(&rows).unwrap();
    assert!(knap.within_budget());
    assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);
}

/// Deterministic xorshift for the differential test (no external deps).
struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound.max(1)
    }
}

/// Brute-force subset-sum ground truth: which assignments of the original
/// row variables satisfy the equality.
fn brute_force_sat(knap: &EqKnapsack) -> bool {
    let n = knap.items.len();
    for mask in 0u64..(1u64 << n) {
        let mut lhs: i128 = 0;
        for (i, item) in knap.items.iter().enumerate() {
            if (mask >> i) & 1 == 1 {
                lhs += i128::from(item.coeff);
            }
        }
        if lhs == knap.target {
            return true;
        }
    }
    false
}

/// DIFFERENTIAL GATE: the DP verdict must match brute-force enumeration
/// on thousands of random small equality knapsacks, and every SAT witness
/// must satisfy the equality exactly. This is the trust anchor for the
/// UNSAT path (which has no runtime witness).
#[test]
fn differential_dp_vs_brute_force() {
    let mut rng = XorShift(0x5eed_cafe_f00d_1234);
    for round in 0..4000 {
        let n = 1 + (rng.below(11) as usize); // 1..=11 items
        let mut terms = Vec::with_capacity(n);
        let mut total: i128 = 0;
        for v in 0..n {
            let coeff = 1 + rng.below(60) as i128;
            total += coeff;
            // Mix in negated literals and negative coefficients to
            // exercise canonicalization + flipping.
            let negate_lit = rng.below(4) == 0;
            let negate_coeff = rng.below(4) == 0;
            let l = if negate_lit {
                not(v as u32 + 1)
            } else {
                lit(v as u32 + 1)
            };
            terms.push((if negate_coeff { -coeff } else { coeff }, l));
        }
        // Target from slightly beyond the raw range so infeasible cases
        // (incl. out-of-range) are common.
        let raw_target = rng.below((2 * total + 20) as u64) as i128 - total / 2;
        let row = eq_row(&terms, raw_target);
        let Some(knap) = EqKnapsack::detect(&[row]) else {
            panic!("round {round}: detection must succeed on a linear Eq row");
        };
        let expected = brute_force_sat(&knap);
        match knap.solve(&mut never_stop()) {
            EqKnapsackOutcome::Sat(assignment) => {
                assert!(
                    expected,
                    "round {round}: DP said SAT, brute force says UNSAT"
                );
                // Witness must satisfy the equality on ORIGINAL vars.
                let lhs: i128 = knap
                    .items
                    .iter()
                    .map(|item| {
                        let value = assignment
                            .iter()
                            .find(|(var, _)| *var == item.var)
                            .expect("assignment covers every item var")
                            .1;
                        let used = value != item.flipped;
                        if used {
                            i128::from(item.coeff)
                        } else {
                            0
                        }
                    })
                    .sum();
                assert_eq!(lhs, knap.target, "round {round}: witness violates equality");
            }
            EqKnapsackOutcome::Unsat => {
                assert!(
                    !expected,
                    "round {round}: DP said UNSAT, brute force says SAT"
                );
            }
            EqKnapsackOutcome::Inconclusive => {
                panic!("round {round}: uninterrupted in-budget solve must be conclusive");
            }
        }
    }
}

/// The Ge-pair form must decide identically to the equivalent Eq row.
#[test]
fn differential_pair_vs_eq_row() {
    let mut rng = XorShift(0xabcd_ef01_2345_6789);
    for _ in 0..500 {
        let n = 1 + (rng.below(8) as usize);
        let mut terms = Vec::with_capacity(n);
        for v in 0..n {
            terms.push((1 + rng.below(40) as i128, lit(v as u32 + 1)));
        }
        let total: i128 = terms.iter().map(|(c, _)| *c).sum();
        let target = rng.below((total + 1) as u64) as i128;
        let neg_terms: Vec<(i128, PbLit)> = terms.iter().map(|&(c, l)| (-c, l)).collect();
        let eq = [eq_row(&terms, target)];
        let pair = [ge_row(&terms, target), ge_row(&neg_terms, -target)];
        let a = EqKnapsack::detect(&eq).unwrap().solve(&mut never_stop());
        let b = EqKnapsack::detect(&pair).unwrap().solve(&mut never_stop());
        match (&a, &b) {
            (EqKnapsackOutcome::Sat(_), EqKnapsackOutcome::Sat(_)) => {}
            (EqKnapsackOutcome::Unsat, EqKnapsackOutcome::Unsat) => {}
            other => panic!("Eq row and Ge pair disagree: {other:?}"),
        }
    }
}

#[test]
fn dpbits_shift_boundaries() {
    // Exercise word-boundary shifts explicitly.
    for &shift in &[1u64, 63, 64, 65, 127, 128, 129] {
        let mut bits = DpBits::new(300);
        bits.or_shifted_self(shift);
        assert!(bits.get(0));
        assert!(bits.get(shift), "bit {shift} must be reachable");
        bits.or_shifted_self(shift);
        assert!(bits.get(2 * shift), "bit {} must be reachable", 2 * shift);
        // Only {0, shift, 2*shift} are reachable; probe a non-member.
        assert!(!bits.get(2 * shift + 1));
    }
    // Shift beyond max_bit is a no-op.
    let mut bits = DpBits::new(10);
    bits.or_shifted_self(11);
    assert_eq!(bits.words[0], 1);
}
