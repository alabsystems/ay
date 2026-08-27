// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Starter subset of z3's own golden tests, transliterated as fixtures.
//!
//! Sources (z3 5.0.0, `src/test/`):
//!   * `upolynomial.cpp::tst_isolate_roots` — the root-isolation corpus,
//!     including the clustered `10000x-31` family, the degree-17 sparse
//!     polynomial and the `(x^5 - 10^9)^3` monster.
//!   * `upolynomial.cpp::tst_remove_one_half` — the `x = 1/2` rational root.
//!   * `upolynomial.cpp::tst_gcd` — including Knuth's coprime pair.
//!   * `upolynomial.cpp::tst_sturm` — the degree-10 Sturm-sequence input.
//!   * `algebraic.cpp::tst_wilkinson` — 20 integer roots.
//!   * `algebraic.cpp::tst_root` — `4^(1/2)` and `4^(1/4)`.
//!
//! The root fixtures reuse z3's own acceptance criterion verbatim
//! (`check_roots` in `upolynomial.cpp`): every expected value must be matched
//! by exactly one isolating marker — as an exact rational root, or as a strict
//! interval containing it. z3's own expectations for irrational roots are
//! decimal approximations, and they are kept as such here.

use ay_nra::oracle_api::{OAlg, OPoly, ORoot};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

use crate::checks::{ipoly, mul_coeffs, pow_coeffs, rat};
use crate::pmgr;
use crate::polygen;
use crate::z3::Z3;

/// One fixture's verdict.
pub(crate) struct GoldenResult {
    pub(crate) name: String,
    pub(crate) passed: bool,
    pub(crate) detail: String,
}

fn linear(a: i64, b: i64) -> Vec<BigRational> {
    // a*x + b, low-to-high.
    ipoly(&[b, a])
}

fn product(factors: &[Vec<BigRational>]) -> Vec<BigRational> {
    let mut acc = vec![BigRational::one()];
    for f in factors {
        acc = mul_coeffs(&acc, f);
    }
    acc
}

/// z3's `check_roots`: each expected value must be matched by exactly one
/// marker, and no marker may match two expectations.
fn check_expected_roots(markers: &[ORoot], expected: &[BigRational]) -> Result<(), String> {
    if markers.len() != expected.len() {
        return Err(format!(
            "expected {} roots, AY isolated {}",
            expected.len(),
            markers.len()
        ));
    }
    let mut visited = vec![false; markers.len()];
    for (i, r) in expected.iter().enumerate() {
        let mut found: Option<usize> = None;
        for (j, m) in markers.iter().enumerate() {
            let hit = match m {
                ORoot::Rational(q) => q == r,
                ORoot::Interval(lo, hi) => lo < r && r < hi,
            };
            if hit {
                if found.is_some() || visited[j] {
                    return Err(format!(
                        "expected root #{i} ({r}) matched more than one marker"
                    ));
                }
                found = Some(j);
                visited[j] = true;
            }
        }
        if found.is_none() {
            return Err(format!(
                "expected root #{i} ({r}) matched no marker; markers = {}",
                render_markers(markers)
            ));
        }
    }
    Ok(())
}

fn render_markers(markers: &[ORoot]) -> String {
    let parts: Vec<String> = markers
        .iter()
        .map(|m| match m {
            ORoot::Rational(r) => format!("[{r}]"),
            ORoot::Interval(lo, hi) => format!("({lo},{hi})"),
        })
        .collect();
    format!("{{{}}}", parts.join(", "))
}

include!("golden/root_fixtures.rs");
include!("golden/algebraic_fixtures.rs");
include!("golden/runner.rs");
