// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

// ==========================================================================
// SUITE B — randomized differential against z3 AND the independent model
// ==========================================================================

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

/// A wider generator than the oracle's: bigger degrees, bigger coefficients,
/// clustered roots, and intervals of every width from "widest isolating" to
/// `2^-60`.
fn wilkinson_poly(rng: &mut Rng) -> Vec<BigInt> {
    let n = rng.below(5) as i64 + 2;
    let mut p = vec![BigInt::one()];
    for i in 1..=n {
        let mut q = vec![BigInt::zero(); p.len() + 1];
        for (j, c) in p.iter().enumerate() {
            q[j] += c * BigInt::from(-i);
            q[j + 1] += c;
        }
        p = q;
    }
    p
}

fn gen_poly(rng: &mut Rng) -> (Vec<BigInt>, &'static str) {
    match rng.below(10) {
        0 => {
            // clustered: (x-a)(x-a-1/2^m)... via integer scaling
            let m = rng.below(20) as u32 + 1;
            let s = BigInt::one() << m;
            let a = BigInt::from(rng.range(-5, 5));
            // (s x - s a)(s x - s a - 1) = s^2 x^2 - ... roots a and a + 1/s
            let p0 = &(&s * &a) * (&(&s * &a) + BigInt::one());
            let p1 = -(&s * (&(&s * &a) * BigInt::from(2) + BigInt::one()));
            let p2 = &s * &s;
            (vec![p0, p1, p2], "clustered")
        }
        1 => {
            // Wilkinson-ish: product of (x - i)
            (wilkinson_poly(rng), "wilkinson")
        }
        2 => {
            // high-degree sparse: x^d - k
            let d = rng.below(12) as usize + 2;
            let k = rng.range(2, 200);
            let mut c = vec![BigInt::zero(); d + 1];
            c[0] = BigInt::from(-k);
            c[d] = BigInt::one();
            (c, "x^d-k")
        }
        3 => {
            // huge coefficients
            let d = rng.below(4) as usize + 2;
            let mut c: Vec<BigInt> = (0..=d)
                .map(|_| {
                    BigInt::from(rng.range(-1_000_000_000, 1_000_000_000))
                        * (BigInt::one() << rng.below(64) as u32)
                })
                .collect();
            if c[d].is_zero() {
                c[d] = BigInt::one();
            }
            (c, "huge-coeffs")
        }
        4 => {
            // repeated factors (square-free reduction has real work)
            let r = rng.range(-4, 4);
            let d = rng.range(2, 13);
            let quad = ints(&[-d, 0, 1]);
            let lin = ints(&[-r, 1]);
            let sq = pmul(&quad, &quad);
            (pmul(&sq, &lin), "multiplicity")
        }
        5 => {
            // random dense of odd degree (guaranteed real root)
            let d = 2 * (rng.below(3) as usize) + 3;
            let mut c: Vec<BigInt> = (0..=d).map(|_| BigInt::from(rng.range(-30, 30))).collect();
            if c[d].is_zero() {
                c[d] = BigInt::one();
            }
            (c, "dense-odd")
        }
        6 => {
            // near-rational: n^2 x^2 - (k n^2 + 1)
            let e = rng.below(40) as u32 + 1;
            let n = BigInt::one() << e;
            let n2 = &n * &n;
            let k = rng.range(2, 20);
            (
                vec![-(&n2 * BigInt::from(k) + BigInt::one()), BigInt::zero(), n2],
                "near-rational",
            )
        }
        7 => {
            // pure rational roots, dyadic and not
            let k = rng.below(6) as u32 + 1;
            let a = rng.range(-40, 40);
            let b = rng.range(-9, 9);
            (pmul(&ints(&[-a, 1i64 << k]), &ints(&[-b, 3])), "rational")
        }
        8 => {
            // cubic with 3 real roots, asymmetric
            let a = rng.range(-6, 6);
            let b = rng.range(-6, 6);
            let c = rng.range(-6, 6);
            (
                pmul(&pmul(&ints(&[-a, 1]), &ints(&[-b, 1])), &ints(&[-c, 1])),
                "three-linear",
            )
        }
        _ => {
            // x^2 - d, the classic
            let d = rng.range(2, 60);
            (ints(&[-d, 0, 1]), "quadratic")
        }
    }
}

fn pmul(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

/// Build an AY cell for z3's root `v` of `p`, at a randomly chosen interval
/// width (including the coarsest isolating one).
fn build_at(
    z3: &Z3,
    p: &[BigInt],
    v: Ast,
    rng: &mut Rng,
) -> Result<Option<(ODyadicAnum, BigRational, BigRational)>, &'static str> {
    let (lo, hi) = z3.bracket(v, 80).ok_or("bracketing a generated root")?;
    let eps = BigRational::new(BigInt::one(), BigInt::one() << 70u32);
    let (lo, hi) = if lo == hi {
        (&lo - &eps, &hi + &eps)
    } else {
        (lo, hi)
    };
    let mode = rng.below(3);
    if mode == 0 {
        // coarsest isolating
        for k in 0..=70u32 {
            if let Some(i) = ivq(&lo, &hi, k) {
                if let Some(a) = ODyadicAnum::from_poly_interval(p, &i) {
                    return Ok(Some((a, i.lo().to_rational(), i.hi().to_rational())));
                }
            }
        }
        Ok(None)
    } else {
        let k = if mode == 1 {
            40
        } else {
            20 + rng.below(45) as u32
        };
        let Some(i) = ivq(&lo, &hi, k) else {
            return Ok(None);
        };
        let Some(a) = ODyadicAnum::from_poly_interval(p, &i) else {
            return Ok(None);
        };
        Ok(Some((a, i.lo().to_rational(), i.hi().to_rational())))
    }
}
