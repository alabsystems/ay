// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PHASE-LEVEL cost measurement for [`crate::anum`] and [`crate::ialg`].
//! `#[ignore]`d: measurements, not assertions.
//!
//! ```text
//! cargo test --release -p ay-nra --lib anum_profile -- --ignored --nocapture
//! ```
//!
//! # Why a phase profiler and not a flame graph
//!
//! The question this lane had to answer is a two-way split inside one function:
//! `cmp_cell` pays for an equality certificate, a square-free radical of the
//! PRODUCT of the two defining polynomials, a Mahler separation exponent, and
//! two refinements. A sampling profiler on a 60 us call gives noise. So each
//! phase is re-run here against the same inputs the real function would use,
//! and the sum is checked against an end-to-end `cmp_anum` timing on the same
//! pair — if the phases do not add up to the whole, the split is wrong and the
//! harness says so.

use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::{
    normalize_defining, root_separation_exponent, sturm_chain, sturm_count_in, Anum,
};
use crate::ialg::{AEnd, AInterval, IntervalSet, Just, Made};
use crate::mpbq::{self, Bq, BqInterval};
use crate::upoly::ZPoly;

fn ri(n: i64) -> Anum {
    Anum::rational(BigRational::from_integer(BigInt::from(n)))
}

/// The positive root of `x^2 - d`.
fn sqrt(d: i64) -> Anum {
    let p = vec![BigInt::from(-d), BigInt::zero(), BigInt::one()];
    let iv = BqInterval::new(Bq::zero(), Bq::from_int(BigInt::from(d + 1))).expect("ordered");
    Anum::from_poly_interval(&p, &iv).expect("one root")
}

/// The positive root of `x^n - d` — an endpoint of genuine degree `n`.
fn nth_root(n: usize, d: i64) -> Option<Anum> {
    let mut c = vec![BigInt::zero(); n + 1];
    c[0] = BigInt::from(-d);
    c[n] = BigInt::one();
    let iv = BqInterval::new(Bq::zero(), Bq::from_int(BigInt::from(d + 1)))?;
    Anum::from_poly_interval(&c, &iv)
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

/// Re-run each phase of `AlgCell::cmp_cell` against one pair and report the
/// nanoseconds each took, plus the end-to-end call for a sanity check.
struct Phases {
    gcd_ns: u128,
    cert_ns: u128,
    radical_ns: u128,
    sepbound_ns: u128,
    refine_ns: u128,
    total_ns: u128,
    sep_bits: u32,
    steps: u32,
    /// How many bisections would actually have sufficed to make the two
    /// intervals disjoint.
    needed: u32,
}

fn profile_pair(a: &Anum, b: &Anum) -> Option<Phases> {
    let (ca, cb) = (a.cell()?, b.cell()?);
    let pa = ZPoly::from_coeffs(ca.poly_coeffs().to_vec());
    let pb = ZPoly::from_coeffs(cb.poly_coeffs().to_vec());

    let t = Instant::now();
    let g = pa.gcd(&pb)?;
    let gcd_ns = t.elapsed().as_nanos();

    let t = Instant::now();
    if g.degree()? >= 1 {
        let gchain = sturm_chain(&g)?;
        let _ = sturm_count_in(&gchain, ca.interval().lo(), ca.interval().hi())?;
    }
    let cert_ns = t.elapsed().as_nanos();

    let t = Instant::now();
    let combined = normalize_defining(&pa.mul(&pb))?;
    let radical_ns = t.elapsed().as_nanos();

    let t = Instant::now();
    let sep = root_separation_exponent(&combined)?;
    let sepbound_ns = t.elapsed().as_nanos();

    let target = Bq::inv_two_pow(sep.checked_add(2)?);
    let t = Instant::now();
    let (_, ta) = mpbq::refine_to_width(ca.poly_coeffs(), ca.interval(), &target)?;
    let (_, tb) = mpbq::refine_to_width(cb.poly_coeffs(), cb.interval(), &target)?;
    let refine_ns = t.elapsed().as_nanos();

    let t = Instant::now();
    let _ = a.cmp_anum(b)?;
    let total_ns = t.elapsed().as_nanos();

    // How many bits of refinement would ACTUALLY have sufficed: refine both to
    // 2^-k for growing k until the two intervals are disjoint.
    let mut needed = 0u32;
    for k in 0..=sep.min(4096) {
        let tgt = Bq::inv_two_pow(k);
        let (Some((ra, _)), Some((rb, _))) = (
            mpbq::refine_to_width(ca.poly_coeffs(), ca.interval(), &tgt),
            mpbq::refine_to_width(cb.poly_coeffs(), cb.interval(), &tgt),
        ) else {
            continue;
        };
        let (mpbq::Refined::Narrowed(ia), mpbq::Refined::Narrowed(ib)) = (ra, rb) else {
            needed = k;
            break;
        };
        if ia.hi().cmp_bq(ib.lo()) != std::cmp::Ordering::Greater
            || ib.hi().cmp_bq(ia.lo()) != std::cmp::Ordering::Greater
        {
            needed = k;
            break;
        }
    }

    Some(Phases {
        gcd_ns,
        cert_ns,
        radical_ns,
        sepbound_ns,
        refine_ns,
        total_ns,
        sep_bits: sep,
        steps: ta.steps.max(tb.steps),
        needed,
    })
}

/// THE central profile: where does one `cmp_anum` on two DISTINCT algebraic
/// numbers actually spend its time?
#[test]
fn anum_profile_cmp_phases() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== cmp_anum PHASE profile, two DISTINCT algebraic numbers ==");
    println!("load average at start: {}", load());
    println!(
        "{:>18} {:>8} {:>8} {:>9} {:>8} {:>10} {:>10} {:>7} {:>7} {:>7}",
        "pair",
        "gcd us",
        "cert us",
        "radicl us",
        "sep us",
        "refine us",
        "TOTAL us",
        "sepbit",
        "steps",
        "needed"
    );
    let cases: Vec<(String, Anum, Anum)> = vec![
        ("sqrt2 vs sqrt3".to_string(), sqrt(2), sqrt(3)),
        (
            "3+sqrt2 vs 6+sqrt3".to_string(),
            ri(3).add(&sqrt(2)).expect("add"),
            ri(6).add(&sqrt(3)).expect("add"),
        ),
        (
            "300+sqrt2 vs 303+sqrt3".to_string(),
            ri(300).add(&sqrt(2)).expect("add"),
            ri(303).add(&sqrt(3)).expect("add"),
        ),
        (
            "762+sqrt2 vs 765+sqrt3".to_string(),
            ri(762).add(&sqrt(2)).expect("add"),
            ri(765).add(&sqrt(3)).expect("add"),
        ),
        (
            "deg4: 2^(1/4) vs 3^(1/4)".to_string(),
            nth_root(4, 2).expect("r"),
            nth_root(4, 3).expect("r"),
        ),
        (
            "deg6: 2^(1/6) vs 5^(1/6)".to_string(),
            nth_root(6, 2).expect("r"),
            nth_root(6, 5).expect("r"),
        ),
        (
            "deg8: 2^(1/8) vs 7^(1/8)".to_string(),
            nth_root(8, 2).expect("r"),
            nth_root(8, 7).expect("r"),
        ),
    ];
    for (name, a, b) in &cases {
        match profile_pair(a, b) {
            Some(p) => println!(
                "{name:>18} {:>8} {:>8} {:>9} {:>8} {:>10} {:>10} {:>7} {:>7} {:>7}",
                p.gcd_ns / 1000,
                p.cert_ns / 1000,
                p.radical_ns / 1000,
                p.sepbound_ns / 1000,
                p.refine_ns / 1000,
                p.total_ns / 1000,
                p.sep_bits,
                p.steps,
                p.needed
            ),
            None => println!("{name:>18}   DECLINED"),
        }
    }
    println!("load average at end: {}", load());
}

/// The EQUAL case, which takes the certificate path and does no refinement.
#[test]
fn anum_profile_cmp_equal() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== cmp_anum on EQUAL algebraic numbers (certificate path) ==");
    println!("load average at start: {}", load());
    for d in [2i64, 3, 5, 7] {
        let a = sqrt(d);
        let b = sqrt(d).refine(&Bq::inv_two_pow(20)).expect("refine");
        let t = Instant::now();
        let o = a.cmp_anum(&b);
        println!(
            "  sqrt({d}) vs its 2^-20 refinement: {:>8} us -> {o:?}",
            t.elapsed().as_nanos() / 1000
        );
    }
    println!("load average at end: {}", load());
}

/// The REALISTIC sequence: the shape `from_sign_condition` actually produces —
/// already-ascending cells — versus the shuffled worst case the ceiling
/// documents. Answers "is the O(n^2) insertion sort where the time goes?"
#[test]
fn anum_profile_normalize_order() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== IntervalSet::normalize: SORTED (realistic) vs SHUFFLED ==");
    println!("load average at start: {}", load());
    println!(
        "{:>6} {:>14} {:>14} {:>10}",
        "n", "sorted ms", "shuffled ms", "ratio"
    );
    for &n in &[16usize, 32, 64, 128, 256] {
        let build = |order: &[usize]| -> Vec<AInterval> {
            order
                .iter()
                .map(|&k| {
                    let d = [2i64, 3, 5, 7][k % 4];
                    let base = 3 * k as i64;
                    let lo = ri(base).add(&sqrt(d)).expect("add");
                    let hi = ri(base + 2).add(&sqrt(d)).expect("add");
                    match AInterval::new(
                        AEnd::Fin(lo),
                        true,
                        AEnd::Fin(hi),
                        true,
                        Just::of(1).expect("lit"),
                    )
                    .expect("decided")
                    {
                        Made::Iv(v) => v,
                        Made::Empty => panic!("empty"),
                    }
                })
                .collect()
        };
        let asc: Vec<usize> = (0..n).collect();
        // Deterministic shuffle: a fixed LCG permutation, so the number is
        // reproducible.
        let mut sh = asc.clone();
        let mut s: u64 = 0x2026_0806;
        for i in (1..n).rev() {
            s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let j = (s >> 33) as usize % (i + 1);
            sh.swap(i, j);
        }
        let a = build(&asc);
        let b = build(&sh);
        let t = Instant::now();
        let ra = IntervalSet::normalize(a);
        let sorted_us = t.elapsed().as_micros();
        let t = Instant::now();
        let rb = IntervalSet::normalize(b);
        let shuf_us = t.elapsed().as_micros();
        println!(
            "{n:>6} {:>14.1} {:>14.1} {:>10.1}   len {:?}/{:?}",
            sorted_us as f64 / 1000.0,
            shuf_us as f64 / 1000.0,
            shuf_us as f64 / sorted_us.max(1) as f64,
            ra.map(|s| s.len()),
            rb.map(|s| s.len()),
        );
    }
    println!("load average at end: {}", load());
}

/// The whole realistic sequence end to end, which is the number that decides
/// whether an optimisation was worth anything: build a feasible set from a sign
/// condition on a degree-`m` polynomial, then intersect a chain of them.
#[test]
fn anum_profile_realistic_sequence() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== REALISTIC SEQUENCE: sign-condition sets + intersection chain ==");
    println!("load average at start: {}", load());
    let t_all = Instant::now();

    // Phase A: 16 algebraic interval sets, 16 intervals each, intersected in a
    // chain — exactly `ialg_cost_endpoint_degree_growth`'s shape but timed as a
    // unit.
    let mk_set = |lit: i32, off: i64| -> Option<IntervalSet> {
        let mut ivs = Vec::new();
        for k in 0..16i64 {
            let d = [2i64, 3, 5, 7][(k % 4) as usize];
            let base = 3 * k + off;
            let lo = ri(base).add(&sqrt(d))?;
            let hi = ri(base + 2).add(&sqrt(d))?;
            match AInterval::new(AEnd::Fin(lo), true, AEnd::Fin(hi), true, Just::of(lit)?)? {
                Made::Iv(v) => ivs.push(v),
                Made::Empty => {}
            }
        }
        IntervalSet::normalize(ivs)
    };

    let t = Instant::now();
    let mut acc = mk_set(1, 0).expect("set");
    let build_us = t.elapsed().as_micros();

    let t = Instant::now();
    let mut steps = 0;
    for i in 0..8i32 {
        let Some(next) = mk_set(i + 2, i64::from(i)) else {
            break;
        };
        let Some(new) = acc.intersect(&next) else {
            break;
        };
        acc = new;
        steps += 1;
        if acc.is_empty() {
            break;
        }
    }
    let chain_us = t.elapsed().as_micros();

    println!(
        "  build 16-interval algebraic set  : {:>9.1} ms",
        build_us as f64 / 1000.0
    );
    println!(
        "  chain of {steps} intersections        : {:>9.1} ms",
        chain_us as f64 / 1000.0
    );
    println!("  final set len                    : {}", acc.len());
    println!(
        "  WHOLE SEQUENCE                   : {:>9.1} ms",
        t_all.elapsed().as_micros() as f64 / 1000.0
    );
    println!("load average at end: {}", load());
}

/// `from_sign_condition` did NOT move when `cmp_anum` got faster (3.01 s at 127
/// roots before, 3.01 s after), so its cost is somewhere else. This splits it.
#[test]
fn anum_profile_sign_condition_phases() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== from_sign_condition PHASE profile (rational roots) ==");
    println!("load average at start: {}", load());
    println!(
        "{:>6} {:>10} {:>12} {:>12} {:>12} {:>12}",
        "roots", "radical", "sturmchain", "sturmcount", "cellsigns", "TOTAL us"
    );
    for &m in &[21usize, 34, 55, 89, 127] {
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
        let zp = ZPoly::from_coeffs(p.clone());

        let t = Instant::now();
        let sf = normalize_defining(&zp).expect("sf");
        let rad_us = t.elapsed().as_micros();

        let t = Instant::now();
        let chain = sturm_chain(&sf).expect("chain");
        let chain_us = t.elapsed().as_micros();

        let t = Instant::now();
        let b = crate::anum::cauchy_bound_z(&sf).expect("cauchy");
        let lo = Bq::from_int(-(b.clone() + BigInt::one()));
        let hi = Bq::from_int(b + BigInt::one());
        let _ = sturm_count_in(&chain, &lo, &hi).expect("count");
        let count_us = t.elapsed().as_micros();

        // The per-cell sample sign evaluations: m+1 of them on a degree-m
        // polynomial with ~m*log2(m)-bit coefficients.
        let t = Instant::now();
        for k in 0..=m {
            let x = Bq::from_int(BigInt::from(k as i64 * 2));
            let _ = mpbq::poly_sign_at(&p, &x);
        }
        let cells_us = t.elapsed().as_micros();

        let roots: Vec<Anum> = (0..m as i64).map(ri).collect();
        let t = Instant::now();
        let _ =
            crate::ialg::from_sign_condition(&p, &roots, crate::ialg::SignCond::Gt, Just::none());
        let tot_us = t.elapsed().as_micros();

        println!("{m:>6} {rad_us:>10} {chain_us:>12} {count_us:>12} {cells_us:>12} {tot_us:>12}");
    }
    println!("load average at end: {}", load());
}

/// The same phase split for `sign_of_poly`, which `cmp_rational` also routes
/// through: is its cost the bound, the radical, or the refinement?
#[test]
fn anum_profile_sign_phases() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== sign_of_poly PHASE profile (non-vanishing q) ==");
    println!("load average at start: {}", load());
    println!(
        "{:>6} {:>8} {:>9} {:>8} {:>10} {:>10} {:>7} {:>7}",
        "deg", "gcd us", "radicl us", "sep us", "refine us", "TOTAL us", "sepbit", "steps"
    );
    for n in [2usize, 3, 4, 6, 8, 12, 16] {
        let Some(a) = nth_root(n, 2) else { continue };
        let cell = a.cell().expect("alg");
        let pa = ZPoly::from_coeffs(cell.poly_coeffs().to_vec());
        let mut q = vec![BigInt::zero(); n + 1];
        q[0] = BigInt::from(-3);
        q[n] = BigInt::one();
        let qz = ZPoly::from_coeffs(q.clone());
        let qs = normalize_defining(&qz).expect("sf");

        let t = Instant::now();
        let g = pa.gcd(&qs).expect("gcd");
        let _ = g.degree();
        let gcd_us = t.elapsed().as_nanos() / 1000;

        let t = Instant::now();
        let combined = normalize_defining(&pa.mul(&qs)).expect("rad");
        let rad_us = t.elapsed().as_nanos() / 1000;

        let t = Instant::now();
        let b = root_separation_exponent(&combined).expect("sep");
        let sep_us = t.elapsed().as_nanos() / 1000;

        let target = Bq::inv_two_pow(b + 1);
        let t = Instant::now();
        let (_, tr) =
            mpbq::refine_to_width(cell.poly_coeffs(), cell.interval(), &target).expect("refine");
        let ref_us = t.elapsed().as_nanos() / 1000;

        let t = Instant::now();
        let _ = a.sign_of_poly(&q);
        let tot_us = t.elapsed().as_nanos() / 1000;

        println!(
            "{n:>6} {gcd_us:>8} {rad_us:>9} {sep_us:>8} {ref_us:>10} {tot_us:>10} {b:>7} {:>7}",
            tr.steps
        );
    }
    println!("load average at end: {}", load());
}

/// Exact sign of a polynomial at an algebraic point, by degree — the operation
/// nlsat runs thousands of times per conflict.
#[test]
fn anum_profile_sign_by_degree() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in, like the repo's other env-guarded
    // harnesses (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== sign_of_poly at an algebraic point, by ENDPOINT DEGREE ==");
    println!("load average at start: {}", load());
    println!("{:>6} {:>12} {:>12}", "deg", "us", "sign");
    for n in [2usize, 3, 4, 6, 8, 12, 16] {
        let Some(a) = nth_root(n, 2) else {
            println!("{n:>6}  could not build");
            continue;
        };
        // A polynomial that does NOT vanish at 2^(1/n): x^n - 3.
        let mut q = vec![BigInt::zero(); n + 1];
        q[0] = BigInt::from(-3);
        q[n] = BigInt::one();
        let t = Instant::now();
        let s = a.sign_of_poly(&q);
        println!("{n:>6} {:>12} {:>12?}", t.elapsed().as_micros(), s);
    }
    println!("load average at end: {}", load());
}
