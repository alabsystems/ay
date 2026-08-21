// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cost measurement for [`crate::ialg`]. `#[ignore]`d: these are measurements,
//! not assertions, and they are slow on purpose.
//!
//! Run with:
//!
//! ```text
//! cargo test --release -p ay-nra --lib ialg_cost -- --ignored --nocapture
//! ```
//!
//! # Why the sweep is irregular
//!
//! A previous harness swept 8/16/.../256 and missed a cliff at 335-512 because
//! every sample was a power of two. The sizes here are deliberately not: they
//! include 3, 5, 12, 23, 47, 91, 150, 199, 251 and the two the doubling sweep
//! would have skipped over, 335 and 512, so a cliff between powers of two is
//! visible rather than straddled.

use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::Anum;
use crate::ialg::{
    classify_value, from_sign_condition, AEnd, AInterval, IntervalSet, Just, Made, SignCond,
};
use crate::mpbq::{Bq, BqInterval};

fn ri(n: i64) -> Anum {
    Anum::rational(BigRational::from_integer(BigInt::from(n)))
}

/// The positive root of `x^2 - d`.
fn sqrt(d: i64) -> Anum {
    let p = vec![BigInt::from(-d), BigInt::zero(), BigInt::one()];
    let iv = BqInterval::new(Bq::zero(), Bq::from_int(BigInt::from(d + 1))).expect("ordered");
    Anum::from_poly_interval(&p, &iv).expect("one root")
}

fn mk(lo: AEnd, lo_open: bool, hi: AEnd, hi_open: bool, lit: i32) -> AInterval {
    match AInterval::new(lo, lo_open, hi, hi_open, Just::of(lit).expect("nonzero"))
        .expect("decided")
    {
        Made::Iv(v) => v,
        Made::Empty => panic!("empty"),
    }
}

/// `n` disjoint rational intervals `[3k, 3k+1]`.
///
/// `None` past `MAX_INTERVALS`, which is the module refusing rather than the
/// harness crashing — the sweep deliberately runs past the ceiling so that the
/// refusal shows up as a measurement.
fn rational_set(n: usize, lit: i32) -> Option<IntervalSet> {
    let ivs: Vec<AInterval> = (0..n)
        .map(|k| {
            let k = k as i64;
            mk(
                AEnd::Fin(ri(3 * k)),
                false,
                AEnd::Fin(ri(3 * k + 1)),
                false,
                lit,
            )
        })
        .collect();
    IntervalSet::normalize(ivs)
}

/// `n` disjoint intervals whose endpoints are genuine ALGEBRAIC numbers.
///
/// Endpoints are `k*3 + sqrt(d)` for a rotating squarefree `d`, built by exact
/// algebraic addition, so each carries a real degree-2 defining polynomial and
/// every comparison goes through the certificate path rather than collapsing to
/// a rational compare.
fn algebraic_set(n: usize, lit: i32) -> Option<IntervalSet> {
    const DS: [i64; 4] = [2, 3, 5, 7];
    let mut ivs = Vec::with_capacity(n);
    for k in 0..n {
        let d = DS[k % DS.len()];
        let base = 3 * k as i64;
        let lo = ri(base).add(&sqrt(d))?;
        let hi = ri(base + 2).add(&sqrt(d))?;
        ivs.push(mk(AEnd::Fin(lo), true, AEnd::Fin(hi), true, lit));
    }
    IntervalSet::normalize(ivs)
}

fn load() -> String {
    std::fs::read_to_string("/proc/loadavg").map_or_else(
        |_| {
            std::process::Command::new("uptime")
                .output()
                .ok()
                .and_then(|o| String::from_utf8(o.stdout).ok())
                .and_then(|s| {
                    s.split("load averages:")
                        .nth(1)
                        .map(str::trim)
                        .map(String::from)
                })
                .unwrap_or_else(|| "?".to_string())
        },
        |s| s.split_whitespace().take(3).collect::<Vec<_>>().join(" "),
    )
}

/// Set size sweep, irregular on purpose.
const SIZES: [usize; 12] = [3, 5, 12, 23, 47, 91, 150, 199, 251, 256, 335, 512];

#[test]
fn ialg_cost_intersection_by_size() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== intersect / union / complement / pick by SET SIZE ==");
    println!("load average at start: {}", load());
    println!(
        "{:>6} {:>8} {:>12} {:>12} {:>12} {:>12}",
        "n", "kind", "build us", "intersect us", "complmt us", "pick us"
    );
    for &n in &SIZES {
        for kind in ["rational", "algebraic"] {
            let t0 = Instant::now();
            let a = if kind == "rational" {
                rational_set(n, 1)
            } else {
                algebraic_set(n, 1)
            };
            let build = t0.elapsed().as_micros();
            let Some(a) = a else {
                println!(
                    "{n:>6} {kind:>10} {build:>12} {:>12}   build REFUSED past the ceiling",
                    "-"
                );
                continue;
            };
            // A second set offset by half a cell, so the intersection is
            // non-trivial and the two-pointer scan advances both sides.
            let b = if kind == "rational" {
                rational_set(n, 2)
            } else {
                algebraic_set(n, 2)
            };
            let Some(b) = b else {
                continue;
            };
            let t = Instant::now();
            let inter = a.intersect(&b);
            let ius = t.elapsed().as_micros();
            let t = Instant::now();
            let comp = a.complement();
            let cus = t.elapsed().as_micros();
            let t = Instant::now();
            let pick = a.pick();
            let pus = t.elapsed().as_micros();
            println!(
                "{n:>6} {kind:>10} {build:>12} {ius:>12} {cus:>12} {pus:>12}   \
                 inter={} comp={} pick_rung={:?}",
                inter.map_or("DECLINED".to_string(), |s| s.len().to_string()),
                comp.map_or("DECLINED".to_string(), |s| s.len().to_string()),
                pick.map(|v| classify_value(&v)),
            );
        }
    }
    println!("load average at end: {}", load());
}

/// Endpoint DEGREE growth across a realistic sequence of intersections.
///
/// This is the number the layer underneath makes expensive: exact sign
/// evaluation at an algebraic point was measured at 120 us (deg 2), 584 us
/// (deg 16), 6.7 ms (deg 32), 215 ms (deg 64). An interval set multiplies that
/// by the number of endpoints, so what matters is whether repeated intersection
/// GROWS the degree.
#[test]
fn ialg_cost_endpoint_degree_growth() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== endpoint DEGREE across a chain of intersections ==");
    println!("load average at start: {}", load());
    println!(
        "{:>5} {:>10} {:>10} {:>12} {:>12}",
        "step", "intervals", "max deg", "elapsed us", "pick rung"
    );
    let Some(mut acc) = algebraic_set(16, 1) else {
        println!("could not build the initial algebraic set");
        return;
    };
    for step in 0..12i32 {
        let Some(next) = algebraic_set(16, step + 2) else {
            break;
        };
        let t = Instant::now();
        let Some(new) = acc.intersect(&next) else {
            println!("{step:>5}   INTERSECT DECLINED");
            break;
        };
        let us = t.elapsed().as_micros();
        acc = new;
        let max_deg = acc
            .intervals()
            .iter()
            .flat_map(|iv| [iv.lo().value(), iv.hi().value()])
            .flatten()
            .map(Anum::degree)
            .max()
            .unwrap_or(0);
        let rung = acc.pick().map(|v| classify_value(&v));
        println!(
            "{step:>5} {:>10} {max_deg:>10} {us:>12} {:>12}",
            acc.len(),
            format!("{rung:?}")
        );
        if acc.is_empty() {
            println!("      (set emptied — conflict)");
            break;
        }
    }
    println!("load average at end: {}", load());
}

/// `from_sign_condition` by root count, which is what a projection polynomial's
/// degree turns into.
#[test]
fn ialg_cost_sign_condition_by_root_count() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== from_sign_condition by ROOT COUNT ==");
    println!("load average at start: {}", load());
    println!(
        "{:>6} {:>12} {:>10} {:>12}",
        "roots", "elapsed us", "cells", "pick rung"
    );
    for &m in &[1usize, 2, 3, 5, 8, 13, 21, 34, 55, 89, 127] {
        // p = prod (x - k) for k in 0..m: m distinct integer roots.
        let mut p = vec![BigInt::one()];
        for k in 0..m {
            let lin = vec![BigInt::from(-(k as i64)), BigInt::one()];
            let mut out = vec![BigInt::zero(); p.len() + 1];
            for (i, x) in p.iter().enumerate() {
                for (j, y) in lin.iter().enumerate() {
                    out[i + j] += x * y;
                }
            }
            p = out;
        }
        let roots: Vec<Anum> = (0..m as i64).map(ri).collect();
        let t = Instant::now();
        let s = from_sign_condition(&p, &roots, SignCond::Gt, Just::none());
        let us = t.elapsed().as_micros();
        match s {
            Some(s) => println!(
                "{m:>6} {us:>12} {:>10} {:>12}",
                s.len(),
                format!("{:?}", s.pick().map(|v| classify_value(&v)))
            ),
            None => println!("{m:>6} {us:>12} {:>10}", "DECLINED"),
        }
    }
    println!("load average at end: {}", load());
}
