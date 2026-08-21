// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cost and DEGREE measurement for [`crate::explain`]. `#[ignore]`d: these are
//! measurements, not assertions, and they are slow on purpose.
//!
//! Run with:
//!
//! ```text
//! cargo test --release -p ay-nra --lib explain_cost -- --ignored --nocapture
//! ```
//!
//! # What is being measured, and why each one
//!
//!   * **Checker cost against conflict size.** `clause_is_valid` is
//!     `O(lits * cells)` exact sign evaluations at real algebraic points, and
//!     that primitive is the known ceiling: 584 us at degree 16, 6.7 ms at 32,
//!     215 ms at 64. The sweep says where the explanation layer sits under it.
//!   * **Minimization cost.** It multiplies the checker by the literal count, so
//!     it is the term most likely to dominate. `MINIMIZE_BUDGET` exists because
//!     of this measurement, not before it.
//!   * **DEGREE GROWTH under projection.** This is the one that decides whether
//!     the multivariate case is reachable at all. A resultant of two degree-`d`
//!     polynomials squares degree; the MV corpus median total degree is 3 and
//!     the usable endpoint degree is 3-4, so one projection step is affordable
//!     and the question is how many.
//!
//! # Why the sweeps are irregular
//!
//! The same reason `ialg_cost` gives: a previous harness swept powers of two and
//! straddled a cliff. The sizes here are 1, 2, 3, 5, 7, 11, 17, 23 and 31 — none
//! of them a power of two except the small ones that must be there anyway.

use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::Anum;
use crate::explain::{clause_is_valid, explain_univariate, project, relevant_pairs, ConflictLit};
use crate::ialg::SignCond;
use crate::mpbq::{Bq, BqInterval};
use crate::subresultant::{MPolyZ, Mono, RPoly};

/// Irregular sweep sizes: not a doubling ladder, so a cliff between powers of
/// two is visible rather than straddled.
const SIZES: [usize; 9] = [1, 2, 3, 5, 7, 11, 17, 23, 31];

fn ri(n: i64) -> Anum {
    Anum::rational(BigRational::from_integer(BigInt::from(n)))
}

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&x| BigInt::from(x)).collect()
}

/// The two roots of `x^2 - d`, ascending.
fn sqrt_pair(d: i64) -> Vec<Anum> {
    let p = ints(&[-d, 0, 1]);
    let neg = BqInterval::new(Bq::from_int(BigInt::from(-(d + 1))), Bq::zero()).expect("ordered");
    let pos = BqInterval::new(Bq::zero(), Bq::from_int(BigInt::from(d + 1))).expect("ordered");
    vec![
        Anum::from_poly_interval(&p, &neg).expect("one root"),
        Anum::from_poly_interval(&p, &pos).expect("one root"),
    ]
}

/// `n` linear literals `x - k > 0`, plus one `x - n < 0` that contradicts them.
/// Rational endpoints throughout: this isolates the SET machinery from the
/// algebraic-number cost.
fn rational_conflict(n: usize) -> Vec<ConflictLit> {
    let mut out: Vec<ConflictLit> = (0..n)
        .map(|k| ConflictLit {
            lit: i32::try_from(k + 1).expect("small"),
            p: ints(&[-(k as i64), 1]),
            cond: SignCond::Gt,
            roots: vec![ri(k as i64)],
        })
        .collect();
    out.push(ConflictLit {
        lit: i32::try_from(n + 1).expect("small"),
        p: ints(&[-(n as i64 - 1), 1]),
        cond: SignCond::Lt,
        roots: vec![ri(n as i64 - 1)],
    });
    out
}

/// `n` quadratic literals with IRRATIONAL endpoints: nested annuli
/// `x^2 - d_k > 0`, closed off by one `x^2 - d_last < 0` that empties it.
fn algebraic_conflict(n: usize) -> Vec<ConflictLit> {
    let ds: [i64; 8] = [2, 3, 5, 6, 7, 10, 11, 13];
    let mut out: Vec<ConflictLit> = (0..n)
        .map(|k| {
            let d = ds[k % ds.len()];
            ConflictLit {
                lit: i32::try_from(k + 1).expect("small"),
                p: ints(&[-d, 0, 1]),
                cond: SignCond::Gt,
                roots: sqrt_pair(d),
            }
        })
        .collect();
    out.push(ConflictLit {
        lit: i32::try_from(n + 1).expect("small"),
        p: ints(&[-2, 0, 1]),
        cond: SignCond::Lt,
        roots: sqrt_pair(2),
    });
    out
}

#[test]
fn measure_checker_cost() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n=== clause_is_valid: cost vs conflict size ===");
    println!(
        "{:>6}  {:>6}  {:>7}  {:>12}  {}",
        "lits", "roots", "cells", "us", "verdict"
    );
    for n in SIZES {
        for (label, lits) in [
            ("rational", rational_conflict(n)),
            ("algebraic", algebraic_conflict(n)),
        ] {
            let roots: usize = lits.iter().map(|l| l.roots.len()).sum();
            let t = Instant::now();
            let v = clause_is_valid(&lits);
            let us = t.elapsed().as_micros();
            println!(
                "{:>6}  {:>6}  {:>7}  {:>12}  {:?}  [{label}]",
                lits.len(),
                roots,
                2 * roots + 1,
                us,
                v
            );
        }
    }
}

#[test]
fn measure_producer_cost() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n=== explain_univariate: end to end, INCLUDING minimization ===");
    println!(
        "{:>6}  {:>6}  {:>12}  {:>10}  {}",
        "lits", "roots", "us", "clause", "shape"
    );
    for n in SIZES {
        for (label, lits) in [
            ("rational", rational_conflict(n)),
            ("algebraic", algebraic_conflict(n)),
        ] {
            let roots: usize = lits.iter().map(|l| l.roots.len()).sum();
            let t = Instant::now();
            let e = explain_univariate(&lits);
            let us = t.elapsed().as_micros();
            println!(
                "{:>6}  {:>6}  {:>12}  {:>10}  {label}",
                lits.len(),
                roots,
                us,
                e.map_or("None".to_string(), |e| e.len().to_string())
            );
        }
    }
}

/// A bivariate polynomial in `x` whose coefficients are polynomials in `y`.
fn bip(x_coeffs: &[&[(u32, i64)]]) -> RPoly<MPolyZ> {
    RPoly::from_coeffs(
        x_coeffs
            .iter()
            .map(|terms| {
                MPolyZ::from_terms(
                    terms
                        .iter()
                        .map(|&(e, c)| (Mono::var_pow(0, e), BigInt::from(c)))
                        .collect(),
                )
            })
            .collect(),
    )
}

/// `x^d - y^e`: total degree `max(d, e)`, and the cleanest dial for degree
/// growth under projection.
fn power_pair(d: usize, e: u32) -> RPoly<MPolyZ> {
    let mut cs: Vec<MPolyZ> = (0..=d).map(|_| MPolyZ::zero()).collect();
    cs[0] = MPolyZ::from_terms(vec![(Mono::var_pow(0, e), BigInt::from(-1))]);
    cs[d] = MPolyZ::from_terms(vec![(Mono::var_pow(0, 0), BigInt::one())]);
    RPoly::from_coeffs(cs)
}

#[test]
fn measure_projection_degree_growth() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n=== project: what it does to DEGREE ===");
    println!(
        "{:>10}  {:>8}  {:>9}  {:>7}  {:>12}  {}",
        "case", "deg in", "deg out", "factors", "us", "growth"
    );

    // The realistic conflict first: the MV corpus median total degree is 3.
    let realistic: Vec<(&str, Vec<RPoly<MPolyZ>>)> = vec![
        (
            "median-3",
            vec![
                // x^2 - y  (total degree 2) and x*y - 3 (total degree 2)
                bip(&[&[(1, -1)], &[], &[(0, 1)]]),
                bip(&[&[(0, -3)], &[(1, 1)]]),
            ],
        ),
        (
            "circle+line",
            vec![
                bip(&[&[(2, 1), (0, -4)], &[], &[(0, 1)]]),
                bip(&[&[(1, -1)], &[(0, 1)]]),
            ],
        ),
    ];
    for (name, polys) in &realistic {
        let t = Instant::now();
        let p = project(polys, &[(0, 1)]).expect("projected");
        let us = t.elapsed().as_micros();
        println!(
            "{:>10}  {:>8}  {:>9}  {:>7}  {:>12}  x{:.2}",
            name,
            p.in_max_total_degree,
            p.out_max_total_degree,
            p.factors.len(),
            us,
            f64::from(p.out_max_total_degree) / f64::from(p.in_max_total_degree.max(1))
        );
    }

    // Then the dial: x^d - y^d against x^d - y^d - 1, swept.
    for d in [2usize, 3, 4, 5, 6, 7, 9, 11] {
        let a = power_pair(d, u32::try_from(d).expect("small"));
        let mut b_coeffs: Vec<MPolyZ> = (0..=d).map(|_| MPolyZ::zero()).collect();
        b_coeffs[0] = MPolyZ::from_terms(vec![
            (
                Mono::var_pow(0, u32::try_from(d).expect("small")),
                BigInt::from(-1),
            ),
            (Mono::var_pow(0, 0), BigInt::from(-1)),
        ]);
        b_coeffs[d] = MPolyZ::from_terms(vec![(Mono::var_pow(0, 0), BigInt::one())]);
        let b = RPoly::from_coeffs(b_coeffs);
        let t = Instant::now();
        let Some(p) = project(&[a, b], &[(0, 1)]) else {
            println!(
                "{:>10}  {:>8}  {:>9}  {:>7}  {:>12}  DECLINED",
                format!("x^{d}"),
                d,
                "-",
                "-",
                "-"
            );
            continue;
        };
        let us = t.elapsed().as_micros();
        println!(
            "{:>10}  {:>8}  {:>9}  {:>7}  {:>12}  x{:.2}",
            format!("x^{d}-y^{d}"),
            p.in_max_total_degree,
            p.out_max_total_degree,
            p.factors.len(),
            us,
            f64::from(p.out_max_total_degree) / f64::from(p.in_max_total_degree.max(1))
        );
    }
}

#[test]
fn measure_relevant_pairs_reduction() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n=== relevant_pairs: how many resultants the restriction saves ===");
    println!(
        "{:>6}  {:>10}  {:>10}  {:>8}",
        "lits", "all pairs", "relevant", "saved"
    );
    for n in SIZES {
        let lits = algebraic_conflict(n);
        let all = lits.len() * (lits.len().saturating_sub(1)) / 2;
        let Some(rel) = relevant_pairs(&lits) else {
            println!(
                "{:>6}  {:>10}  {:>10}  {:>8}",
                lits.len(),
                all,
                "DECLINED",
                "-"
            );
            continue;
        };
        #[allow(clippy::cast_precision_loss)]
        let saved = if all == 0 {
            0.0
        } else {
            100.0 * (all - rel.len()) as f64 / all as f64
        };
        println!(
            "{:>6}  {:>10}  {:>10}  {:>7.1}%",
            lits.len(),
            all,
            rel.len(),
            saved
        );
    }
}
