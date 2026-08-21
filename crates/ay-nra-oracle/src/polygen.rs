// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Seeded, reproducible generation of univariate polynomials with controlled
//! degree, coefficient size and sparsity, plus the adversarial shapes that
//! actually break real-root isolation: repeated roots, near-degenerate leading
//! coefficients, huge coefficients, tightly clustered rational roots, and the
//! degenerate zero / constant polynomials.
//!
//! The PRNG is a self-contained xoshiro256** seeded through splitmix64. It is
//! vendored (nine lines) rather than pulled from `rand` so that a reproducer
//! seed printed today reproduces byte-for-byte on any future toolchain,
//! independent of any crate's generator-stability policy.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// xoshiro256** — deterministic, seed-reproducible, dependency-free.
pub(crate) struct Rng {
    s: [u64; 4],
}

impl Rng {
    /// Seed via splitmix64, so even adjacent seeds decorrelate immediately.
    pub(crate) fn new(seed: u64) -> Self {
        let mut z = seed;
        let mut next = || {
            z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut x = z;
            x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            x ^ (x >> 31)
        };
        Self {
            s: [next(), next(), next(), next()],
        }
    }

    pub(crate) fn next_u64(&mut self) -> u64 {
        let result = self.s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = self.s[1] << 17;
        self.s[2] ^= self.s[0];
        self.s[3] ^= self.s[1];
        self.s[1] ^= self.s[2];
        self.s[0] ^= self.s[3];
        self.s[2] ^= t;
        self.s[3] = self.s[3].rotate_left(45);
        result
    }

    /// Uniform in `[0, n)`; `n == 0` yields 0.
    pub(crate) fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next_u64() % n
        }
    }

    /// Uniform in `[lo, hi]`.
    pub(crate) fn range(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        let span = u64::try_from(hi - lo).unwrap_or(0) + 1;
        lo + i64::try_from(self.below(span)).unwrap_or(0)
    }

    /// True with probability `num / den`.
    pub(crate) fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }

    /// A random integer whose magnitude is bounded by the given size class.
    fn int_of_class(&mut self, class: u8) -> BigInt {
        let magnitude = match class {
            0 => BigInt::from(self.range(0, 3)),
            1 => BigInt::from(self.range(0, 12)),
            2 => BigInt::from(self.range(0, 1000)),
            3 => BigInt::from(self.range(0, 1_000_000_000)),
            // Huge: a 96-to-128-bit magnitude assembled from three words.
            _ => {
                let a = BigInt::from(self.next_u64());
                let b = BigInt::from(self.next_u64());
                let c = BigInt::from(self.below(1 << 32));
                a + (b << 32) + (c << 96)
            }
        };
        if self.chance(1, 2) {
            -magnitude
        } else {
            magnitude
        }
    }

    /// A random rational with the given coefficient size class. Denominators
    /// appear one time in four, and are occasionally a power of ten (the shape
    /// that produces the `10000*x - 31` style clustered roots z3's own golden
    /// tests use).
    fn rational_of_class(&mut self, class: u8) -> BigRational {
        let num = self.int_of_class(class);
        if !self.chance(1, 4) {
            return BigRational::from_integer(num);
        }
        let den = if self.chance(1, 3) {
            BigInt::from(10u32).pow(u32::try_from(self.range(1, 5)).unwrap_or(1))
        } else {
            BigInt::from(self.range(1, 12))
        };
        BigRational::new(num, den)
    }
}

/// The adversarial shape a generated polynomial takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Shape {
    /// Every coefficient drawn independently.
    Dense,
    /// Most coefficients forced to zero.
    Sparse,
    /// The zero polynomial.
    Zero,
    /// A non-zero constant.
    Constant,
    /// Product of random linear factors — many simple rational roots.
    LinearProduct,
    /// Product of factors with deliberately repeated multiplicities.
    RepeatedRoots,
    /// A perfect square `q^2`: every real root doubled.
    PerfectSquare,
    /// `q * q'` — shares every multiple root of `q` with its derivative.
    TimesDerivative,
    /// Leading coefficient `±1` with all lower coefficients huge: the root
    /// magnitudes explode and the Cauchy bound is astronomically loose.
    NearDegenerateLead,
    /// Leading coefficient `±1/10^k` with modest lower coefficients: the same
    /// pathology from the other side.
    TinyLead,
    /// `(10^k x - a)(10^k x - a-1)...` — rational roots within `10^-k`.
    ClusteredRational,
    /// `x^n - c`, the shape whose roots are exactly `c^(1/n)`.
    PureRoot,
    /// `(x-1)(x-2)...(x-n)`, Wilkinson's polynomial.
    Wilkinson,
    /// All coefficients huge.
    HugeCoeffs,
    /// A small dense integer polynomial of degree >= 2. Not adversarial — it
    /// exists because the algebraic ARITHMETIC and COMPARISON checks need
    /// operands that actually have irrational roots, and the adversarial
    /// shapes mostly produce rational roots, no roots, or degrees the exact
    /// resultant path cannot afford.
    AlgebraicSmall,
}

impl Shape {
    /// Short stable name for reproducer dumps.
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Dense => "dense",
            Self::Sparse => "sparse",
            Self::Zero => "zero",
            Self::Constant => "constant",
            Self::LinearProduct => "linear-product",
            Self::RepeatedRoots => "repeated-roots",
            Self::PerfectSquare => "perfect-square",
            Self::TimesDerivative => "times-derivative",
            Self::NearDegenerateLead => "near-degenerate-lead",
            Self::TinyLead => "tiny-lead",
            Self::ClusteredRational => "clustered-rational",
            Self::PureRoot => "pure-root",
            Self::Wilkinson => "wilkinson",
            Self::HugeCoeffs => "huge-coeffs",
            Self::AlgebraicSmall => "algebraic-small",
        }
    }
}

/// Pick a shape. Ordinary dense/sparse polynomials stay the common case; the
/// adversarial shapes together take just under half the draws, because those
/// are where root isolation actually goes wrong.
fn pick_shape(rng: &mut Rng) -> Shape {
    match rng.below(100) {
        0..=24 => Shape::Dense,
        25..=39 => Shape::Sparse,
        40..=41 => Shape::Zero,
        42..=44 => Shape::Constant,
        45..=56 => Shape::LinearProduct,
        57..=66 => Shape::RepeatedRoots,
        67..=72 => Shape::PerfectSquare,
        73..=77 => Shape::TimesDerivative,
        78..=82 => Shape::NearDegenerateLead,
        83..=86 => Shape::TinyLead,
        87..=90 => Shape::ClusteredRational,
        91..=94 => Shape::PureRoot,
        95..=96 => Shape::Wilkinson,
        _ => Shape::HugeCoeffs,
    }
}

/// A generated polynomial plus the provenance needed to reproduce it.
#[derive(Clone, Debug)]
pub(crate) struct GenPoly {
    /// Low-to-high rational coefficients.
    pub(crate) coeffs: Vec<BigRational>,
    pub(crate) shape: Shape,
}

/// Multiply low-to-high coefficient vectors.
fn mul(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigRational::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        if x.is_zero() {
            continue;
        }
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

fn trim(mut v: Vec<BigRational>) -> Vec<BigRational> {
    while v.last().is_some_and(Zero::is_zero) {
        v.pop();
    }
    v
}

fn derivative(p: &[BigRational]) -> Vec<BigRational> {
    if p.len() < 2 {
        return Vec::new();
    }
    trim(
        p.iter()
            .enumerate()
            .skip(1)
            .map(|(i, c)| c * BigRational::from_integer(BigInt::from(i)))
            .collect(),
    )
}

/// Generate one polynomial suitable as an ALGEBRAIC-NUMBER operand.
///
/// Two thirds of the draws are a small dense integer polynomial of degree
/// `2..=max_degree`, which is the cheapest reliable source of irrational
/// roots; the rest come from the ordinary adversarial mix so the arithmetic
/// and comparison checks still see clustered, near-degenerate and repeated-root
/// inputs. Without this, a measured 97% of `algebraic-arith` cases were
/// inapplicable — the check existed but tested almost nothing.
pub(crate) fn gen_algebraic_operand(rng: &mut Rng, max_degree: usize) -> GenPoly {
    if rng.chance(2, 3) {
        let hi = i64::try_from(max_degree.max(2)).unwrap_or(2);
        let deg = usize::try_from(rng.range(2, hi)).unwrap_or(2);
        let mut v: Vec<BigRational> = (0..=deg).map(|_| rng.rational_of_class(1)).collect();
        if v[deg].is_zero() {
            v[deg] = BigRational::one();
        }
        return GenPoly {
            coeffs: trim(v),
            shape: Shape::AlgebraicSmall,
        };
    }
    gen_poly(rng, max_degree)
}

/// Generate one polynomial, of degree at most `max_degree`.
///
/// Each shape sizes itself to respect the cap — the composite ones
/// (`PerfectSquare`, `TimesDerivative`, the linear products) pick a base
/// degree small enough that the finished product still fits, so the cap never
/// costs the shape its defining property. [`clamp_degree`] is a backstop for
/// the case where a shape's arithmetic is nevertheless wrong.
pub(crate) fn gen_poly(rng: &mut Rng, max_degree: usize) -> GenPoly {
    let shape = pick_shape(rng);
    let coeffs = build(rng, shape, max_degree);
    GenPoly {
        coeffs: clamp_degree(trim(coeffs), max_degree),
        shape,
    }
}

/// Enforce the degree cap on shapes whose arithmetic can exceed it.
///
/// `PerfectSquare` squares a degree-`d` base and `TimesDerivative` multiplies
/// by a derivative, so both can land above `max_degree` — measured up to
/// degree 11 for a nominal cap of 8. Degree is the dominant term in AY's exact
/// Sturm cost (plain Euclidean remainder over `Q`, no subresultant PRS), so an
/// unannounced overshoot is exactly what turns a 3 ms case into a multi-minute
/// one.
///
/// KNOWN COST, stated rather than hidden: truncation drops the leading terms,
/// which destroys the structure those two shapes exist to create. Roughly one
/// `perfect-square` draw in five and two `times-derivative` draws in five come
/// out as an arbitrary degree-`max_degree` polynomial instead of a
/// repeated-root one. Multiplicity is still covered by `repeated-roots`, which
/// builds from linear factors and respects the cap by construction.
fn clamp_degree(coeffs: Vec<BigRational>, max_degree: usize) -> Vec<BigRational> {
    if coeffs.len() <= max_degree + 1 {
        return coeffs;
    }
    let mut v = coeffs;
    v.truncate(max_degree + 1);
    trim(v)
}

/// Generate one polynomial of a caller-chosen shape. Used by the shape
/// coverage test, which asserts every adversarial shape actually builds; the
/// fuzz driver itself draws shapes at random and reports the realised counts.
#[cfg(test)]
pub(crate) fn gen_poly_shaped(rng: &mut Rng, shape: Shape, max_degree: usize) -> GenPoly {
    GenPoly {
        coeffs: trim(build(rng, shape, max_degree)),
        shape,
    }
}

/// All shapes, for the coverage test.
#[cfg(test)]
pub(crate) const ALL_SHAPES: [Shape; 15] = [
    Shape::Dense,
    Shape::Sparse,
    Shape::Zero,
    Shape::Constant,
    Shape::LinearProduct,
    Shape::RepeatedRoots,
    Shape::PerfectSquare,
    Shape::TimesDerivative,
    Shape::NearDegenerateLead,
    Shape::TinyLead,
    Shape::ClusteredRational,
    Shape::PureRoot,
    Shape::Wilkinson,
    Shape::HugeCoeffs,
    Shape::AlgebraicSmall,
];

fn build(rng: &mut Rng, shape: Shape, max_degree: usize) -> Vec<BigRational> {
    let one = BigRational::one();
    match shape {
        Shape::AlgebraicSmall => {
            let hi = i64::try_from(max_degree.max(2)).unwrap_or(2);
            let deg = usize::try_from(rng.range(2, hi)).unwrap_or(2);
            let mut v: Vec<BigRational> = (0..=deg).map(|_| rng.rational_of_class(1)).collect();
            if v[deg].is_zero() {
                v[deg] = one;
            }
            v
        }
        Shape::Zero => Vec::new(),
        Shape::Constant => {
            let class = u8::try_from(rng.below(5)).unwrap_or(0);
            let c = rng.rational_of_class(class);
            if c.is_zero() {
                vec![one]
            } else {
                vec![c]
            }
        }
        Shape::Dense | Shape::Sparse | Shape::HugeCoeffs => {
            let class = if shape == Shape::HugeCoeffs {
                4
            } else {
                u8::try_from(rng.below(5)).unwrap_or(0)
            };
            // Huge coefficients get a tighter degree cap: the exact Sturm
            // sequence over Q grows the coefficients quadratically in the
            // degree, and past this the reference and AY both just get slow.
            let cap = if class >= 4 {
                max_degree.min(4)
            } else {
                max_degree
            };
            let deg = usize::try_from(rng.below(u64::try_from(cap).unwrap_or(1) + 1)).unwrap_or(1);
            let sparse = shape == Shape::Sparse;
            let mut v: Vec<BigRational> = (0..=deg)
                .map(|_| {
                    if sparse && rng.chance(3, 5) {
                        BigRational::zero()
                    } else {
                        rng.rational_of_class(class)
                    }
                })
                .collect();
            // Force a non-zero leading coefficient so the nominal degree is
            // honest (the zero polynomial has its own shape).
            if v[deg].is_zero() {
                v[deg] = one;
            }
            v
        }
        Shape::LinearProduct | Shape::RepeatedRoots => {
            let max_factors = max_degree.max(1).min(10);
            let n = usize::try_from(rng.below(u64::try_from(max_factors).unwrap_or(1)))
                .unwrap_or(0)
                + 1;
            let mut acc = vec![one.clone()];
            let mut degree = 0usize;
            for _ in 0..n {
                let a = BigRational::from_integer(BigInt::from(rng.range(1, 9)));
                let b = BigRational::from_integer(BigInt::from(rng.range(-9, 9)));
                let factor = vec![b, a];
                let mult = if shape == Shape::RepeatedRoots {
                    usize::try_from(rng.range(1, 3)).unwrap_or(1)
                } else {
                    1
                };
                for _ in 0..mult {
                    if degree + 1 > max_degree {
                        break;
                    }
                    acc = mul(&acc, &factor);
                    degree += 1;
                }
            }
            acc
        }
        Shape::PerfectSquare => {
            // Base degree 1..=max_degree/2 + 1, so the square can reach
            // max_degree + 2 and be truncated by `clamp_degree`. See that
            // function for what truncation costs this shape.
            let half = max_degree / 2;
            let deg =
                usize::try_from(rng.below(u64::try_from(half).unwrap_or(0) + 1)).unwrap_or(0) + 1;
            let class = u8::try_from(rng.below(3)).unwrap_or(0);
            let mut q: Vec<BigRational> = (0..=deg).map(|_| rng.rational_of_class(class)).collect();
            if q[deg].is_zero() {
                q[deg] = one;
            }
            mul(&q, &q)
        }
        Shape::TimesDerivative => {
            let half = max_degree / 2;
            let deg =
                usize::try_from(rng.below(u64::try_from(half).unwrap_or(0) + 1)).unwrap_or(0) + 2;
            let class = u8::try_from(rng.below(3)).unwrap_or(0);
            let mut q: Vec<BigRational> = (0..=deg).map(|_| rng.rational_of_class(class)).collect();
            if q[deg].is_zero() {
                q[deg] = one;
            }
            let dq = derivative(&q);
            if dq.is_empty() {
                q
            } else {
                mul(&q, &dq)
            }
        }
        Shape::NearDegenerateLead => {
            let deg = usize::try_from(rng.below(u64::try_from(max_degree.min(5)).unwrap_or(1)))
                .unwrap_or(0)
                + 1;
            let mut v: Vec<BigRational> = (0..deg).map(|_| rng.rational_of_class(4)).collect();
            v.push(if rng.chance(1, 2) { one.clone() } else { -one });
            v
        }
        Shape::TinyLead => {
            let deg = usize::try_from(rng.below(u64::try_from(max_degree.min(5)).unwrap_or(1)))
                .unwrap_or(0)
                + 1;
            let mut v: Vec<BigRational> = (0..deg).map(|_| rng.rational_of_class(2)).collect();
            let k = u32::try_from(rng.range(3, 12)).unwrap_or(3);
            let tiny = BigRational::new(BigInt::one(), BigInt::from(10u32).pow(k));
            v.push(if rng.chance(1, 2) {
                tiny.clone()
            } else {
                -tiny
            });
            v
        }
        Shape::ClusteredRational => {
            let k = u32::try_from(rng.range(2, 6)).unwrap_or(4);
            let scale = BigInt::from(10u32).pow(k);
            let base = rng.range(1, 99);
            let n = usize::try_from(rng.range(1, 3))
                .unwrap_or(1)
                .min(max_degree.max(1));
            let mut acc = vec![one];
            for i in 0..n {
                let factor = vec![
                    BigRational::from_integer(-BigInt::from(base + i64::try_from(i).unwrap_or(0))),
                    BigRational::from_integer(scale.clone()),
                ];
                acc = mul(&acc, &factor);
            }
            acc
        }
        Shape::PureRoot => {
            let n = usize::try_from(rng.range(2, i64::try_from(max_degree.max(2)).unwrap_or(2)))
                .unwrap_or(2);
            let class = u8::try_from(rng.below(4)).unwrap_or(0);
            let c = rng.rational_of_class(class);
            let mut v = vec![BigRational::zero(); n + 1];
            v[0] = -c;
            v[n] = one;
            v
        }
        Shape::Wilkinson => {
            let n = usize::try_from(rng.range(2, i64::try_from(max_degree.max(2)).unwrap_or(2)))
                .unwrap_or(2);
            let mut acc = vec![one];
            for i in 1..=n {
                acc = mul(
                    &acc,
                    &[
                        BigRational::from_integer(-BigInt::from(i)),
                        BigRational::one(),
                    ],
                );
            }
            acc
        }
    }
}

/// A random rational probe point, biased towards small magnitudes but
/// occasionally landing on an exact integer or a very large value.
pub(crate) fn gen_point(rng: &mut Rng) -> BigRational {
    match rng.below(10) {
        0..=3 => BigRational::from_integer(BigInt::from(rng.range(-10, 10))),
        4..=6 => BigRational::new(
            BigInt::from(rng.range(-100, 100)),
            BigInt::from(rng.range(1, 20)),
        ),
        7..=8 => BigRational::new(
            BigInt::from(rng.range(-1000, 1000)),
            BigInt::from(10u32).pow(u32::try_from(rng.range(0, 4)).unwrap_or(0)),
        ),
        _ => BigRational::from_integer(BigInt::from(rng.range(-1_000_000, 1_000_000))),
    }
}

/// A cheap static estimate of how much exact-arithmetic work a polynomial will
/// cost: `(degree + 1) * (widest coefficient in bits)`.
///
/// This exists because AY builds Sturm sequences with plain Euclidean
/// remainder over `Q` — no primitive-part reduction, no subresultant PRS — so
/// the intermediate coefficients grow multiplicatively with the degree. A
/// degree-5 polynomial with 128-bit coefficients puts thousands of bits into
/// every Sturm entry, and those entries are then evaluated at every bisection
/// point. Measured: such cases run tens of seconds each and starve the rest of
/// the campaign.
///
/// The driver skips cases above a threshold and REPORTS how many it skipped,
/// so the cost of the bound is visible rather than hidden.
#[must_use]
pub(crate) fn work_cost(coeffs: &[BigRational]) -> usize {
    let widest = coeffs
        .iter()
        .map(|c| c.numer().bits() + c.denom().bits())
        .max()
        .unwrap_or(0);
    (coeffs.len() + 1) * usize::try_from(widest).unwrap_or(usize::MAX)
}

/// Render coefficients as an SMT-LIB-ish polynomial for reproducer dumps.
pub(crate) fn render(coeffs: &[BigRational]) -> String {
    if coeffs.is_empty() {
        return "0".to_string();
    }
    let mut parts: Vec<String> = Vec::new();
    for (i, c) in coeffs.iter().enumerate().rev() {
        if c.is_zero() {
            continue;
        }
        let c_str = if c.denom().is_one() {
            c.numer().to_string()
        } else {
            format!("{}/{}", c.numer(), c.denom())
        };
        parts.push(match i {
            0 => c_str,
            1 => format!("({c_str})*x"),
            _ => format!("({c_str})*x^{i}"),
        });
    }
    if parts.is_empty() {
        "0".to_string()
    } else {
        parts.join(" + ")
    }
}

#[cfg(test)]
mod tests {
    use super::{gen_poly, gen_poly_shaped, render, work_cost, Rng, Shape, ALL_SHAPES};
    use num_traits::Zero;

    #[test]
    fn rng_is_reproducible_from_seed() {
        let a: Vec<u64> = (0..8).map(|_| Rng::new(12345).next_u64()).collect();
        let mut r = Rng::new(12345);
        let b: Vec<u64> = (0..8).map(|_| r.next_u64()).collect();
        // Every fresh Rng(12345) starts the same stream.
        assert_eq!(a[0], b[0]);
        // And the stream itself does not repeat immediately.
        assert_ne!(b[0], b[1]);
    }

    #[test]
    fn same_seed_gives_identical_polynomials() {
        let mut r1 = Rng::new(7);
        let mut r2 = Rng::new(7);
        for _ in 0..64 {
            let p = gen_poly(&mut r1, 8);
            let q = gen_poly(&mut r2, 8);
            assert_eq!(p.coeffs, q.coeffs);
            assert_eq!(p.shape, q.shape);
        }
    }

    #[test]
    fn every_shape_builds_within_reason() {
        let mut rng = Rng::new(99);
        for shape in ALL_SHAPES {
            for _ in 0..32 {
                let p = gen_poly_shaped(&mut rng, shape, 8);
                if shape == Shape::Zero {
                    assert!(p.coeffs.is_empty());
                } else {
                    assert!(!p.coeffs.is_empty(), "{} produced nothing", shape.name());
                }
                // No trailing zero coefficient survives trimming.
                assert!(!p.coeffs.last().is_some_and(Zero::is_zero));
            }
        }
    }

    /// Whatever the shapes do internally, `gen_poly` must never hand the
    /// driver a polynomial above the requested degree: the work budget and the
    /// campaign's throughput both depend on that cap holding.
    #[test]
    fn gen_poly_never_exceeds_its_degree_cap() {
        for cap in [2usize, 3, 5, 8] {
            let mut rng = Rng::new(1234 + cap as u64);
            for _ in 0..4000 {
                let p = gen_poly(&mut rng, cap);
                assert!(
                    p.coeffs.len() <= cap + 1,
                    "{} produced degree {} for cap {cap}",
                    p.shape.name(),
                    p.coeffs.len() - 1
                );
            }
        }
    }

    #[test]
    fn work_cost_separates_the_cheap_band_from_the_expensive_one() {
        let mut rng = Rng::new(4242);
        // A small dense polynomial is cheap; a huge-coefficient one is not.
        let small = gen_poly_shaped(&mut rng, Shape::AlgebraicSmall, 3);
        let huge = gen_poly_shaped(&mut rng, Shape::HugeCoeffs, 4);
        assert!(
            work_cost(&small.coeffs) < work_cost(&huge.coeffs),
            "small {} vs huge {}",
            work_cost(&small.coeffs),
            work_cost(&huge.coeffs)
        );
        // The zero polynomial costs nothing and must not underflow.
        assert_eq!(work_cost(&[]), 0);
    }

    #[test]
    fn render_is_readable() {
        let mut rng = Rng::new(1);
        let p = gen_poly_shaped(&mut rng, Shape::Wilkinson, 4);
        let s = render(&p.coeffs);
        assert!(s.contains('x'), "{s}");
    }
}
