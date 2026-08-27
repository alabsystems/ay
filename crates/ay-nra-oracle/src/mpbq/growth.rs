// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dyadic denominator-growth measurements.

use super::*;

// ===========================================================================
// Denominator growth — the `bq-growth` harness
// ===========================================================================

/// One row of the growth measurement.
pub(crate) struct GrowthRow {
    /// Number of bisections performed.
    pub(crate) steps: u32,
    /// `max_k` of the dyadic interval after `steps` bisections.
    pub(crate) dyadic_k: u32,
    /// Total bits stored by the dyadic interval (both numerators plus the two
    /// exponents' worth of implied denominator).
    pub(crate) dyadic_bits: u64,
    /// Bits in the widest numerator/denominator the `BigRational` bisection
    /// reached over the same run.
    pub(crate) rational_bits: u64,
    /// Wall time of the dyadic run, microseconds.
    pub(crate) dyadic_us: u128,
    /// Wall time of the `BigRational` run, microseconds.
    pub(crate) rational_us: u128,
    /// `k` of the point `select_small` returns at this depth.
    pub(crate) select_k: u32,
    /// `k` of the midpoint at this depth.
    pub(crate) mid_k: u32,
    /// Both runs agree on the interval, as rationals.
    pub(crate) agree: bool,
}

/// Measure denominator growth across a long refinement, dyadic vs
/// `BigRational`.
///
/// The rule this answers: *a refine loop that doubles `k` every step is correct
/// and useless.* The dyadic column must grow by exactly one per step; the
/// `BigRational` column is the same bisection over `num_rational`, and its
/// growth is what the dyadic layer is here to avoid.
///
/// Both runs bisect the same isolating interval of `x^2 - 2` and must stay
/// numerically identical throughout, which is checked (`agree`).
pub(crate) fn measure_growth(depths: &[u32]) -> Vec<GrowthRow> {
    let p_int = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let p_rat: Vec<BigRational> = p_int.iter().map(|c| BigRational::from(c.clone())).collect();
    let mut rows = Vec::new();

    for &steps in depths {
        // --- dyadic run ----------------------------------------------------
        let t0 = std::time::Instant::now();
        let Some(mut iv) = OBqInterval::new(
            &OBq::from_int(BigInt::one()),
            &OBq::from_int(BigInt::from(2)),
        ) else {
            continue;
        };
        for _ in 0..steps {
            let Some((left, mid, right)) = iv.bisect() else {
                break;
            };
            let s = obq_poly_sign_at(&p_int, &mid).unwrap_or(0);
            // p(1) < 0, so keep the half whose lower end is still negative.
            iv = if s < 0 { right } else { left };
        }
        let dyadic_us = t0.elapsed().as_micros();
        let dyadic_bits = iv.lo().numerator_bits()
            + iv.hi().numerator_bits()
            + u64::from(iv.lo().k())
            + u64::from(iv.hi().k());
        let select_k = obq_select_small(&iv).map_or(u32::MAX, |(v, _)| v.k());
        let mid_k = iv.midpoint().map_or(u32::MAX, |m| m.k());

        // --- BigRational run, the same bisection -------------------------
        let t1 = std::time::Instant::now();
        let two = BigRational::from(BigInt::from(2));
        let mut lo = BigRational::one();
        let mut hi = BigRational::from(BigInt::from(2));
        let mut rational_bits = 0u64;
        for _ in 0..steps {
            let mid = (&lo + &hi) / &two;
            let mut acc = BigRational::zero();
            let mut pow = BigRational::one();
            for c in &p_rat {
                acc += c * &pow;
                pow *= &mid;
            }
            if acc.numer().is_negative() {
                lo = mid;
            } else {
                hi = mid;
            }
            let w = lo.numer().bits() + lo.denom().bits() + hi.numer().bits() + hi.denom().bits();
            rational_bits = rational_bits.max(w);
        }
        let rational_us = t1.elapsed().as_micros();

        let agree = iv.lo().to_rational() == lo && iv.hi().to_rational() == hi;

        rows.push(GrowthRow {
            steps,
            dyadic_k: iv.max_k(),
            dyadic_bits,
            rational_bits,
            dyadic_us,
            rational_us,
            select_k,
            mid_k,
            agree,
        });
    }
    rows
}
