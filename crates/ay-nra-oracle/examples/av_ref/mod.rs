// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent `BigRational` model and adversarial verification driver.
//!
//! Every dyadic is modeled as a plain rational with no packed exponent. The
//! denominator exponent is recovered by division, sharing no representation
//! logic with the implementation under test.

use ay_nra::oracle_api::OBq;
use num_bigint::BigInt;
use num_rational::BigRational;

macro_rules! bad {
    ($n:expr, $($arg:tt)*) => {{
        println!("DIVERGENCE [case {}] {}", $n, format!($($arg)*));
        return false;
    }};
}

mod basic;
mod intervals;
mod model;
mod refinement;

/// Tiny deterministic xorshift64* generator, keeping runs reproducible.
pub(super) struct R(u64);

impl R {
    pub(super) fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub(super) fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }

    pub(super) fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }
}

pub(super) struct Case {
    pub(super) xa: i64,
    pub(super) xk: u32,
    pub(super) yk: u32,
    pub(super) x: OBq,
    pub(super) y: OBq,
    pub(super) rx: BigRational,
    pub(super) ry: BigRational,
}

impl Case {
    fn draw(rng: &mut R) -> Self {
        let (xa, xk, ya, yk) = match rng.below(6) {
            0 => (0, rng.below(40) as u32, 0, 0),
            1 => (rng.range(-8, 8), 0, rng.range(-8, 8), 0),
            2 => (
                rng.range(-4096, 4096),
                rng.below(60) as u32,
                rng.range(-4096, 4096),
                rng.below(60) as u32,
            ),
            3 => {
                // Equal values with deliberately different spellings.
                let a = rng.range(-100, 100);
                let k = rng.below(20) as u32;
                (a, k, a * 2, k + 1)
            }
            4 => (
                rng.range(-3, 3),
                rng.below(3) as u32,
                rng.range(-3, 3),
                rng.below(3) as u32,
            ),
            _ => (
                rng.range(-i64::pow(2, 40), i64::pow(2, 40)),
                rng.below(200) as u32,
                rng.range(-1000, 1000),
                rng.below(200) as u32,
            ),
        };
        Self {
            xa,
            xk,
            yk,
            x: OBq::new(BigInt::from(xa), xk),
            y: OBq::new(BigInt::from(ya), yk),
            rx: model::r_of(xa, xk),
            ry: model::r_of(ya, yk),
        }
    }
}

fn one_case(n: u64, rng: &mut R) -> bool {
    let case = Case::draw(rng);
    if !basic::check_canonical(n, &case)
        || !basic::check_arithmetic(n, &case, rng)
        || !basic::check_representability(n, rng)
        || !intervals::check(n, &case)
    {
        return false;
    }

    let polynomial = refinement::random_polynomial(rng);
    refinement::check_polynomial(n, &case, &polynomial)
        && refinement::check_step_bound(n, rng)
        && refinement::check_refine_width(n, rng)
        && refinement::check_enclosure(n, rng)
        && refinement::check_non_root(n, rng, &polynomial)
        && refinement::check_separation(n)
}

pub(super) fn run() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args
        .iter()
        .position(|a| a == "--seed")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    let cases: u64 = args
        .iter()
        .position(|a| a == "--cases")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000);

    let mut rng = R(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut ok = 0;
    let mut bad = 0;
    for i in 0..cases {
        if one_case(i, &mut rng) {
            ok += 1;
        } else {
            bad += 1;
            if bad >= 10 {
                println!("... stopping after 10 divergences");
                break;
            }
        }
    }
    println!("av_ref: seed {seed}, {cases} cases -> {ok} agreed, {bad} DIVERGED");
    if bad > 0 {
        std::process::exit(1);
    }
}
