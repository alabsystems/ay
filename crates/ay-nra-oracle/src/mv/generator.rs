// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to preserve the oracle API paths.

// ---------------------------------------------------------------------------
// Generated case
// ---------------------------------------------------------------------------

/// One multivariate case: a sample point given by defining polynomials and
/// root indices, plus a polynomial over those coordinates and the unknown.
pub(crate) struct GenMv {
    /// Defining polynomial for each coordinate `0 .. nvars`, low-to-high.
    pub(crate) defs: Vec<Vec<BigRational>>,
    /// Which ascending root of `defs[i]` this coordinate takes.
    pub(crate) picks: Vec<usize>,
    /// `(exponent vector over vars 0 ..= nvars, coefficient)`.
    pub(crate) terms: Vec<(Vec<u32>, BigInt)>,
    /// Number of ASSIGNED coordinates. The unknown is variable `nvars`.
    pub(crate) nvars: usize,
    /// Which generator shape produced this case.
    pub(crate) shape: &'static str,
}

impl GenMv {
    /// Degree of the univariate polynomial the elimination chain produces:
    /// each coordinate `i` is eliminated by a resultant against a defining
    /// polynomial of degree `deg(m_i)`, which multiplies the degree in the
    /// unknown by that much.
    ///
    /// `n` is how many coordinates the check actually assigns — the
    /// root-isolation checks assign `nvars`, the sign check assigns all of
    /// them.
    pub(crate) fn elimination_degree(&self, n: usize) -> usize {
        let x_deg = self
            .terms
            .iter()
            .map(|(e, _)| e.get(self.nvars).copied().unwrap_or(0) as usize)
            .max()
            .unwrap_or(0);
        let mut cost = x_deg.max(1);
        for d in self.defs.iter().take(n) {
            cost = cost.saturating_mul(d.len().saturating_sub(1).max(1));
        }
        cost
    }
}

fn small_int(rng: &mut Rng) -> BigInt {
    BigInt::from(rng.range(-4, 4))
}

fn nonzero_small_int(rng: &mut Rng) -> BigInt {
    let mut c = small_int(rng);
    if c.is_zero() {
        c = BigInt::from(1);
    }
    c
}

fn rat(c: &BigInt) -> BigRational {
    BigRational::from_integer(c.clone())
}

/// Coefficients of `sum_i c_i y^i` with a non-zero leading coefficient.
fn gen_def_poly(rng: &mut Rng) -> Vec<BigInt> {
    let deg = 1 + usize::try_from(rng.below(MAX_DEF_DEG as u64)).unwrap_or(0);
    let mut coeffs: Vec<BigInt> = (0..deg).map(|_| small_int(rng)).collect();
    coeffs.push(nonzero_small_int(rng));
    coeffs
}

/// Multiply two integer coefficient vectors.
fn mul_ints(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::from(0); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

/// Generate a case. Three shapes:
///
/// * `plain` — an unstructured polynomial over the coordinates. This is the
///   ordinary path: resultant elimination, univariate isolation, sieve.
/// * `conjugate-bait` — `p` is `x - y_0`, whose resultant against `y_0`'s
///   defining polynomial has a root for EVERY conjugate of `y_0`, of which
///   exactly one is a real root of `p` at the sample point. A missing sieve
///   shows up immediately.
/// * `shared-factor` — a linear factor `(y_0 - c)` is multiplied into both `p`
///   and `y_0`'s defining polynomial, so `Res_{y_0}(p, m_0)` vanishes
///   identically and the escape path is the only way to an answer.
pub(crate) fn gen_mv(rng: &mut Rng) -> GenMv {
    // One or two assigned coordinates. Two is where the interesting work is
    // (successive resultants, a separation bound over several coordinates),
    // but it is also where the degrees multiply, so it is the minority.
    let nvars = if rng.chance(1, 3) { 2 } else { 1 };
    let shape_roll = rng.below(10);

    let mut defs: Vec<Vec<BigInt>> = (0..=nvars).map(|_| gen_def_poly(rng)).collect();

    let (terms, shape) = if shape_roll < 2 {
        // conjugate-bait: x - y_0
        (
            vec![
                (vec![0; nvars + 1].with_at(nvars, 1), BigInt::from(1)),
                (vec![0; nvars + 1].with_at(0, 1), BigInt::from(-1)),
            ],
            "conjugate-bait",
        )
    } else if shape_roll < 5 {
        // shared-factor: (y_0 - c) * (a*x^2 + b*x + d), with (y_0 - c) also
        // multiplied into y_0's own defining polynomial.
        let c = small_int(rng);
        let linear = vec![-c.clone(), BigInt::from(1)];
        defs[0] = mul_ints(&defs[0], &linear);
        let a = nonzero_small_int(rng);
        let b = small_int(rng);
        let d = small_int(rng);
        // (y_0 - c) * (a x^2 + b x + d)
        let mut terms: Vec<(Vec<u32>, BigInt)> = Vec::new();
        for (xe, coeff) in [(2u32, a), (1, b), (0, d)] {
            if coeff.is_zero() {
                continue;
            }
            terms.push((
                vec![0; nvars + 1].with_at(0, 1).with_at(nvars, xe),
                coeff.clone(),
            ));
            terms.push((vec![0; nvars + 1].with_at(nvars, xe), -(&c * &coeff)));
        }
        (terms, "shared-factor")
    } else {
        // plain
        let nterms = 2 + usize::try_from(rng.below(4)).unwrap_or(0);
        let mut terms: Vec<(Vec<u32>, BigInt)> = Vec::new();
        for _ in 0..nterms {
            let mut exps = vec![0u32; nvars + 1];
            for e in exps.iter_mut().take(nvars) {
                *e = u32::try_from(rng.below(MAX_Y_DEG as u64 + 1)).unwrap_or(0);
            }
            exps[nvars] = u32::try_from(rng.below(MAX_X_DEG as u64 + 1)).unwrap_or(0);
            terms.push((exps, small_int(rng)));
        }
        // Guarantee the unknown actually appears, so the case is not a
        // degenerate "no roots by construction".
        terms.push((vec![0; nvars + 1].with_at(nvars, 1), nonzero_small_int(rng)));
        (terms, "plain")
    };

    GenMv {
        defs: defs.iter().map(|d| d.iter().map(rat).collect()).collect(),
        picks: (0..=nvars)
            .map(|_| usize::try_from(rng.next_u64() % 8).unwrap_or(0))
            .collect(),
        terms,
        nvars,
        shape,
    }
}

/// `vec.with_at(i, v)` — small helper so the shape tables above read as
/// exponent vectors instead of five lines of mutation each.
trait WithAt {
    fn with_at(self, i: usize, v: u32) -> Self;
}

impl WithAt for Vec<u32> {
    fn with_at(mut self, i: usize, v: u32) -> Self {
        self[i] = v;
        self
    }
}
