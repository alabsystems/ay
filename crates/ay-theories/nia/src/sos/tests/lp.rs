// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the exact-rational Phase-1 simplex underneath the certificate
//! search — `lp_phase1_feasible` and the naive reference simplex it is pinned
//! against. Split from the parent test module along the LP/certificate
//! boundary: nothing in here builds, tampers with, verifies or renders an
//! `SosCertificate`; these tests only exercise the feasibility solver the
//! search calls into.

use super::*;

// ---------------------------------------------------------------------------
// LP feasibility solver.
// ---------------------------------------------------------------------------

#[test]
fn lp_simple_feasible() {
    // x + y = 1, x, y ≥ 0. Feasible; recovered point satisfies the equation.
    let a = vec![vec![r(1), r(1)]];
    let b = vec![r(1)];
    let sol = lp_phase1_feasible(a, b, 2).expect("feasible");
    assert_eq!(&sol[0] + &sol[1], r(1));
    assert!(!sol[0].is_negative() && !sol[1].is_negative());
}

#[test]
fn lp_infeasible_negative_target() {
    // x = −1 with x ≥ 0 is infeasible.
    let a = vec![vec![r(1)]];
    let b = vec![r(-1)];
    assert!(lp_phase1_feasible(a, b, 1).is_none());
}

#[test]
fn lp_two_row_feasible() {
    // x + y + z = 2, x − y = 0, all ≥ 0.
    let a = vec![vec![r(1), r(1), r(1)], vec![r(1), r(-1), r(0)]];
    let b = vec![r(2), r(0)];
    let sol = lp_phase1_feasible(a, b, 3).expect("feasible");
    assert_eq!(&sol[0] + &sol[1] + &sol[2], r(2));
    assert_eq!(&sol[0] - &sol[1], r(0));
}

/// Reference Phase-1 simplex written the naive way: reduced costs recomputed
/// from the basis on every pivot, and no zero-skipping in the pivot loops.
///
/// This is the formulation `lp_phase1_feasible` replaced (#nia-sos-lp-cost). It
/// exists only so [`lp_carried_cost_row_matches_naive_recompute`] can assert the
/// optimized version is not merely *a* correct simplex but the *same* one — same
/// Bland choices, same returned vector.
#[allow(clippy::needless_range_loop)] // Deliberate verbatim mirror of the pre-#nia-sos-lp-cost code.
fn lp_phase1_feasible_naive(
    mut a: Vec<Vec<BigRational>>,
    mut b: Vec<BigRational>,
    n: usize,
) -> Option<Vec<BigRational>> {
    let m = a.len();
    if m == 0 {
        return Some(vec![zero(); n]);
    }
    for i in 0..m {
        if b[i].is_negative() {
            for j in 0..n {
                a[i][j] = -&a[i][j];
            }
            b[i] = -&b[i];
        }
    }
    let total = n + m;
    let mut t: Vec<Vec<BigRational>> = vec![vec![zero(); total + 1]; m];
    for i in 0..m {
        for j in 0..n {
            t[i][j] = a[i][j].clone();
        }
        t[i][n + i] = one();
        t[i][total] = b[i].clone();
    }
    let mut basis: Vec<usize> = (0..m).map(|i| n + i).collect();
    let is_artificial = |k: usize| k >= n;
    loop {
        let mut entering = None;
        for j in 0..total {
            let mut rc = if is_artificial(j) { one() } else { zero() };
            for i in 0..m {
                if is_artificial(basis[i]) {
                    rc -= &t[i][j];
                }
            }
            if rc.is_negative() {
                entering = Some(j);
                break;
            }
        }
        let Some(e) = entering else { break };
        let mut leave: Option<usize> = None;
        let mut best: Option<BigRational> = None;
        for i in 0..m {
            if t[i][e].is_positive() {
                let ratio = &t[i][total] / &t[i][e];
                let take = match &best {
                    None => true,
                    Some(br) => ratio < *br || (ratio == *br && basis[i] < basis[leave.unwrap()]),
                };
                if take {
                    best = Some(ratio);
                    leave = Some(i);
                }
            }
        }
        let l = leave?;
        let piv = t[l][e].clone();
        for j in 0..=total {
            t[l][j] = &t[l][j] / &piv;
        }
        for i in 0..m {
            if i != l && !t[i][e].is_zero() {
                let factor = t[i][e].clone();
                for j in 0..=total {
                    let d = &factor * &t[l][j];
                    t[i][j] -= d;
                }
            }
        }
        basis[l] = e;
    }
    let mut obj = zero();
    for i in 0..m {
        if is_artificial(basis[i]) {
            obj += &t[i][total];
        }
    }
    if !obj.is_zero() {
        return None;
    }
    let mut x = vec![zero(); n];
    for i in 0..m {
        if basis[i] < n {
            x[basis[i]] = t[i][total].clone();
        }
    }
    Some(x)
}

#[test]
fn lp_carried_cost_row_matches_naive_recompute() {
    // Deterministic pseudo-random LPs, deliberately sparse and rank-deficient so
    // the pivot sequence is degenerate — that is where a cost row maintained by
    // row operations would diverge from a recomputed one if the update were
    // wrong, and where zero-skipping touches the most entries.
    let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut checked_feasible = 0usize;
    let mut checked_infeasible = 0usize;
    for case in 0..300 {
        let m = 1 + (case % 5);
        let n = 2 + (case % 7);
        let mut a: Vec<Vec<BigRational>> = Vec::new();
        for _ in 0..m {
            let mut row = Vec::new();
            for _ in 0..n {
                // ~40% zeros, coefficients in −3..=3, plus some halves so the
                // tableau carries real denominators.
                let x = next();
                let coeff = match x % 10 {
                    0..=3 => r(0),
                    4 => rf(1, 2),
                    5 => rf(-1, 2),
                    k => r(k as i64 % 4 - 2),
                };
                row.push(coeff);
            }
            a.push(row);
        }
        let b: Vec<BigRational> = (0..m)
            .map(|_| r((next() % 5) as i64 - 2))
            .collect::<Vec<_>>();

        let got = lp_phase1_feasible(a.clone(), b.clone(), n);
        let want = lp_phase1_feasible_naive(a, b, n);
        assert_eq!(
            got.is_some(),
            want.is_some(),
            "case {case}: feasibility verdict diverged"
        );
        match (got, want) {
            (Some(g), Some(w)) => {
                assert_eq!(g, w, "case {case}: returned vertex diverged");
                checked_feasible += 1;
            }
            (None, None) => checked_infeasible += 1,
            _ => unreachable!("verdict equality already asserted"),
        }
    }
    // Guard against a vacuous pass: the corpus must exercise both outcomes.
    assert!(
        checked_feasible >= 20 && checked_infeasible >= 20,
        "unbalanced corpus: {checked_feasible} feasible / {checked_infeasible} infeasible"
    );
}
