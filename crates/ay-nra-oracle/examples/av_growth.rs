// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! INDEPENDENT growth sweep for `mpbq`, written against the facade only.
//!
//! Different depths from the lane's harness (irregular, and past every power of
//! two up to 16,384 = MAX_REFINE_STEPS), a different polynomial family, and a
//! `select_small` cost probe on the shape where it is supposed to pay.

use ay_nra::oracle_api::{obq_poly_sign_at, obq_select_small, OBq, OBqInterval};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::time::Instant;

fn bisect_bq(p: &[BigInt], lo: i64, hi: i64, steps: u32) -> (u32, u64, u128) {
    let mut iv = OBqInterval::new(
        &OBq::new(BigInt::from(lo), 0),
        &OBq::new(BigInt::from(hi), 0),
    )
    .unwrap();
    let s_lo = obq_poly_sign_at(p, &iv.lo()).unwrap();
    let t0 = Instant::now();
    for _ in 0..steps {
        let (l, mid, r) = iv.bisect().unwrap();
        let sm = obq_poly_sign_at(p, &mid).unwrap();
        iv = if sm == s_lo { r } else { l };
    }
    let us = t0.elapsed().as_micros();
    (
        iv.max_k(),
        iv.lo().numerator_bits() + iv.hi().numerator_bits(),
        us,
    )
}

fn ref_sign(p: &[BigInt], x: &BigRational) -> i32 {
    let mut acc = BigRational::zero();
    for c in p.iter().rev() {
        acc = acc * x + BigRational::from_integer(c.clone());
    }
    match acc.numer().sign() {
        num_bigint::Sign::Minus => -1,
        num_bigint::Sign::NoSign => 0,
        num_bigint::Sign::Plus => 1,
    }
}

fn bisect_rat(p: &[BigInt], lo: i64, hi: i64, steps: u32) -> (BigRational, BigRational, u128) {
    let two = BigRational::from_integer(BigInt::from(2));
    let mut a = BigRational::from_integer(BigInt::from(lo));
    let mut b = BigRational::from_integer(BigInt::from(hi));
    let s_lo = ref_sign(p, &a);
    let t0 = Instant::now();
    for _ in 0..steps {
        let m = (&a + &b) / &two;
        if ref_sign(p, &m) == s_lo {
            a = m;
        } else {
            b = m;
        }
    }
    let us = t0.elapsed().as_micros();
    (a, b, us)
}

fn run_depth_sweep(p: &[BigInt]) {
    println!("=== INDEPENDENT SWEEP: x^3 - 2 on (1, 2), irregular depths ===");
    println!("  depth    k  k==depth  bq bits    bq us   rat us    ratio  agree");
    let depths: [u32; 30] = [
        1, 3, 7, 15, 17, 31, 33, 63, 65, 100, 127, 129, 255, 257, 300, 335, 400, 500, 511, 513,
        700, 777, 999, 1023, 1025, 1500, 2000, 3000, 4095, 4097,
    ];
    let mut worst_ratio = 0f64;
    let mut all_linear = true;
    for d in depths {
        let (k, bits, bqus) = bisect_bq(p, 1, 2, d);
        let (a, b, ratus) = bisect_rat(p, 1, 2, d);
        // agreement: the dyadic interval must equal the rational one
        let (bqlo, bqhi) = {
            let mut iv =
                OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(2), 0))
                    .unwrap();
            let s_lo = obq_poly_sign_at(p, &iv.lo()).unwrap();
            for _ in 0..d {
                let (l, mid, r) = iv.bisect().unwrap();
                let sm = obq_poly_sign_at(p, &mid).unwrap();
                iv = if sm == s_lo { r } else { l };
            }
            (
                BigRational::new(iv.lo().numerator(), BigInt::one() << iv.lo().k()),
                BigRational::new(iv.hi().numerator(), BigInt::one() << iv.hi().k()),
            )
        };
        let agree = bqlo == a && bqhi == b;
        let linear = k == d;
        if !linear {
            all_linear = false;
        }
        let ratio = if bqus > 0 {
            ratus as f64 / bqus as f64
        } else {
            f64::NAN
        };
        if ratio.is_finite() && ratio > worst_ratio {
            worst_ratio = ratio;
        }
        println!(
            "  {d:>5}  {k:>4}  {linear:>8}  {bits:>7}  {bqus:>7}  {ratus:>7}  {ratio:>7.1}x  {agree}"
        );
    }
    println!("\n  k == depth at EVERY depth: {all_linear}");
}

fn run_ceiling(p: &[BigInt]) {
    println!("\n=== THE CEILING: 8192 and 16384 bisections (MAX_REFINE_STEPS) ===");
    for d in [8192u32, 16384] {
        let (k, bits, bqus) = bisect_bq(p, 1, 2, d);
        println!(
            "  depth {d:>6}  k={k:<6} k==depth={:<6} bits={bits:<7} bq {bqus} us",
            k == d
        );
    }
}

fn run_per_step_cost(p: &[BigInt]) {
    println!("\n=== PER-STEP COST (what an inner loop pays) ===");
    for d in [64u32, 256, 1024, 4096] {
        let (_, _, bqus) = bisect_bq(p, 1, 2, d);
        println!(
            "  {d:>5} steps: {:>8.3} us/step (dyadic)",
            bqus as f64 / d as f64
        );
    }
    for d in [64u32, 256, 1024] {
        let (_, _, ratus) = bisect_rat(p, 1, 2, d);
        println!(
            "  {d:>5} steps: {:>8.3} us/step (BigRational)",
            ratus as f64 / d as f64
        );
    }
}

fn run_straddle_selection() {
    println!("\n=== select_small on the STRADDLE shape (endpoints carry precision the width does not force) ===");
    for (lk, rk) in [
        (200u32, 100u32),
        (400, 40),
        (1000, 999),
        (2000, 8),
        (60, 59),
    ] {
        let lo = OBq::new(BigInt::one(), 0).sub(&OBq::inv_two_pow(lk));
        let hi = OBq::new(BigInt::one(), 0).add(&OBq::inv_two_pow(rk));
        let iv = OBqInterval::new(&lo, &hi).unwrap();
        let mid = iv.midpoint().unwrap();
        let t0 = Instant::now();
        let sel = obq_select_small(&iv).unwrap();
        let us = t0.elapsed().as_micros();
        println!(
            "  (1 - 2^-{lk}, 1 + 2^-{rk}):  midpoint k={:<5} select_small k={:<5} value={}/2^{}  ({us} us, ceiling {})",
            mid.k(),
            sel.0.k(),
            sel.0.numerator(),
            sel.0.k(),
            sel.1
        );
    }
}

fn run_adjacent_selection(p: &[BigInt]) {
    println!("\n=== select_small on a BISECTION-produced (adjacent) interval ===");
    for d in [120u32, 500, 1000] {
        let mut iv =
            OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(2), 0)).unwrap();
        let s_lo = obq_poly_sign_at(p, &iv.lo()).unwrap();
        for _ in 0..d {
            let (l, mid, r) = iv.bisect().unwrap();
            let sm = obq_poly_sign_at(p, &mid).unwrap();
            iv = if sm == s_lo { r } else { l };
        }
        let mid = iv.midpoint().unwrap();
        let t0 = Instant::now();
        let sel = obq_select_small(&iv).unwrap();
        let us = t0.elapsed().as_micros();
        println!(
            "  depth {d:>5}: midpoint k={:<6} select_small k={:<6} equal={} ({us} us)",
            mid.k(),
            sel.0.k(),
            mid.k() == sel.0.k()
        );
    }
}

fn main() {
    // x^3 - 2: the real root is cbrt(2), irrational, in (1, 2). This differs
    // from the lane harness's x^2 - 2 family.
    let p = vec![
        BigInt::from(-2),
        BigInt::zero(),
        BigInt::zero(),
        BigInt::one(),
    ];

    run_depth_sweep(&p);
    run_ceiling(&p);
    run_per_step_cost(&p);
    run_straddle_selection();
    run_adjacent_selection(&p);
}
