// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sparse-polynomial cost, decline, and growth measurements.

use super::*;

// ---------------------------------------------------------------------------
// Coefficient growth measurement
// ---------------------------------------------------------------------------

/// A remainder chain aborts once a coefficient passes this width. Reaching it
/// is the MEASUREMENT, not a failure: it records that the chain became
/// unusable rather than letting the process be killed by the OS.
///
/// MEASURED: without this guard the naive chain at depth 6 was SIGKILLed
/// (exit 137) on this machine after producing an 818-bit remainder at depth 5.
const CHAIN_BIT_ABORT: u64 = 60_000;

/// A remainder chain also aborts once a remainder passes this many terms —
/// sparse multivariate blow-up is in the TERM COUNT as much as in the
/// coefficients, and the term count is what actually exhausts memory.
const CHAIN_TERM_ABORT: usize = 40_000;

/// One row of the coefficient-growth measurement.
pub(crate) struct GrowthRow {
    /// How many cofactors were multiplied in on each side.
    pub(crate) depth: usize,
    /// Widest input coefficient, in bits.
    pub(crate) input_bits: u64,
    /// Widest coefficient in a plain pseudo-remainder chain, in bits: no
    /// content removal, no fraction-free division. This is what "naive" costs.
    pub(crate) naive_peak_bits: u64,
    /// Whether the naive chain hit an abort guard.
    pub(crate) naive_aborted: bool,
    /// Widest coefficient the SUBRESULTANT PRS produces on the path
    /// `polymanager::gcd` actually walks, in bits.
    pub(crate) prs_peak_bits: u64,
    /// Whether the subresultant chain hit an abort guard.
    pub(crate) prs_aborted: bool,
    /// Width of the answer the modular path reconstructed, in bits.
    pub(crate) mod_ans_bits: u64,
    /// Whether the two GCD implementations agreed.
    pub(crate) agreed: bool,
    /// Whether the modular path certified an answer at all.
    pub(crate) modular_certified: bool,
    /// Wall time of the PRS gcd, in microseconds.
    pub(crate) prs_us: u128,
    /// Wall time of the modular gcd, in microseconds.
    pub(crate) mod_us: u128,
    /// Widest TERM COUNT a plain pseudo-remainder chain reached.
    pub(crate) naive_peak_terms: usize,
    /// Widest TERM COUNT the subresultant PRS reached.
    ///
    /// Reported because a verifier showed the coefficient columns alone are
    /// misleading: on genuinely multivariate inputs the blow-up is in the term
    /// count and the wall time, NOT in the coefficient width, and this harness
    /// walked a univariate-in-`x` chain where that never showed.
    pub(crate) prs_peak_terms: usize,
}

/// One row of the MULTIVARIATE cost measurement.
///
/// Separate from [`GrowthRow`] because it measures a different failure mode.
/// `GrowthRow` walks a chain that is univariate in `x` with `y`/`z`
/// coefficients, where the subresultant PRS finishes in microseconds and the
/// coefficient ratio is the whole story. A verifier built genuinely
/// multivariate inputs and found the PRS taking SECONDS while returning a
/// 10-bit answer — cost that no coefficient-width column can show, on exactly
/// the inputs where `mod_gcd` declines. Any layer above that comes to depend on
/// `gcd` latency needs this table, not the other one.
pub(crate) struct MvCostRow {
    /// Human-readable shape.
    pub(crate) label: &'static str,
    /// Terms in each input.
    pub(crate) u_terms: usize,
    pub(crate) v_terms: usize,
    /// Degree of the inputs in the main variable.
    pub(crate) deg_x: u32,
    /// Widest input coefficient, in bits.
    pub(crate) input_bits: u64,
    /// Wall time of the PRS gcd, in MILLIseconds — the unit the answer needs.
    pub(crate) prs_ms: u128,
    /// Terms and width of the PRS answer.
    pub(crate) prs_ans_terms: usize,
    pub(crate) prs_ans_bits: u64,
    /// Wall time of both paths in MICROseconds.
    ///
    /// The modular column was milliseconds and now reads `0` on every shape,
    /// which hides the result rather than showing it. Microseconds is the unit
    /// the modular path needs, and the ratio is computed from these so a
    /// sub-millisecond win is not divided by a rounded-down zero.
    pub(crate) prs_us: u128,
    pub(crate) mod_us: u128,
    /// Whether the modular path certified an answer at all.
    pub(crate) mod_certified: bool,
    /// Whether the two agreed (vacuously true when the modular path declined).
    pub(crate) agreed: bool,
    /// WHY the modular path declined (`"certified"` when it did not).
    ///
    /// This column is the one the cost table was missing: "3 of 5 shapes
    /// decline" is a fact with no attached mechanism, and a fix aimed at the
    /// wrong mechanism is how a lane burns itself.
    pub(crate) decline_reason: &'static str,
    /// Primes the attempt actually entered, and evaluation points it consumed
    /// across every level. Together these say whether the work was spent or
    /// abandoned.
    pub(crate) primes_used: u32,
    pub(crate) eval_points: u32,
    /// Wall time of the DISPATCHING entry point `PolyManager::gcd`, in
    /// microseconds — what a caller above this layer actually pays. Distinct
    /// from `prs_us`, which times the PRS with the modular path disabled all
    /// the way down.
    pub(crate) gcd_us: u128,
    /// Whether the dispatching entry point returned the same answer as the
    /// PRS-only path. Preferring a CERTIFIED fast path must not change any
    /// answer, only the time taken to reach it.
    pub(crate) gcd_agrees: bool,
}

/// The multivariate shapes measured. Chosen to bracket the region a verifier
/// found expensive, not swept.
const MV_SHAPES: [(&str, usize, u32, u32, u64); 5] = [
    // label, terms per factor, max deg per var, vars, coefficient bound
    ("2var small", 3, 2, 2, 6),
    ("2var deg4 wide", 5, 4, 2, 64),
    ("3var deg3", 4, 3, 3, 64),
    ("3var deg5", 5, 5, 3, 1024),
    ("3var deg5 wide coeffs", 5, 5, 3, 1_048_576),
];

/// How many shapes the multivariate cost table has.
pub(crate) fn mv_shape_count() -> usize {
    MV_SHAPES.len()
}

/// Build the multivariate GCD problem for one shape.
///
/// Factored out of [`measure_mv_cost`] so that the decline census measures the
/// SAME instances the cost table times — a census taken on a differently
/// generated pool would answer a different question than the one the cost table
/// asks.
pub(crate) fn mv_instance(idx: usize) -> (OPolyMgr, OMgrPoly, OMgrPoly, &'static str) {
    let (label, nterms, maxdeg, nvars, coeff_bound) = MV_SHAPES[idx % MV_SHAPES.len()];
    let seed_offset = u64::try_from(idx).unwrap_or(u64::MAX);
    let mut rng = Rng::new(0xC057_0000u64.saturating_add(seed_offset));
    let mut m = OPolyMgr::new();

    let draw = |m: &mut OPolyMgr, rng: &mut Rng| -> OMgrPoly {
        let mut terms: Vec<(Vec<(u32, u32)>, BigInt)> = Vec::new();
        for _ in 0..nterms {
            let mut pows: Vec<(u32, u32)> = Vec::new();
            for v in 0..nvars {
                let e = u32::try_from(rng.below(u64::from(maxdeg) + 1)).unwrap_or(0);
                if e > 0 {
                    pows.push((v, e));
                }
            }
            let draw = i64::try_from(rng.below(coeff_bound * 2 + 1)).unwrap_or(0);
            let midpoint = i64::try_from(coeff_bound).unwrap_or(i64::MAX);
            let c = draw - midpoint;
            if c != 0 {
                terms.push((pows, BigInt::from(c)));
            }
        }
        if terms.is_empty() {
            terms.push((vec![(0, 1)], BigInt::one()));
        }
        m.mk(&terms)
    };

    // A planted common factor times a distinct cofactor on each side.
    let g = draw(&mut m, &mut rng);
    let a = draw(&mut m, &mut rng);
    let b = draw(&mut m, &mut rng);
    let u = m.mul(&g, &a);
    let v = m.mul(&g, &b);
    (m, u, v, label)
}

/// Build one multivariate GCD problem and MEASURE what it costs in wall time
/// and term count.
pub(crate) fn measure_mv_cost(idx: usize) -> MvCostRow {
    use std::time::Instant;
    let (mut m, u, v, label) = mv_instance(idx);

    let input_bits = m.max_coeff_bits(&u).max(m.max_coeff_bits(&v));
    let (u_terms, v_terms) = (m.len(&u), m.len(&v));
    let deg_x = m.degree(&u, X).max(m.degree(&v, X));

    let t0 = Instant::now();
    let prs = m.gcd_via_prs(&u, &v);
    let prs_us = t0.elapsed().as_micros();
    let tg = Instant::now();
    let dispatched = m.gcd(&u, &v);
    let gcd_us = tg.elapsed().as_micros();
    let t1 = Instant::now();
    let (modular, diag) = m.mod_gcd_diag(&u, &v);
    let mod_us = t1.elapsed().as_micros();
    let prs_ms = prs_us / 1000;

    let (prs_ans_terms, prs_ans_bits) = match &prs {
        Some(x) => (m.len(x), m.max_coeff_bits(x)),
        None => (0, 0),
    };
    MvCostRow {
        label,
        u_terms,
        v_terms,
        deg_x,
        input_bits,
        prs_ms,
        prs_ans_terms,
        prs_ans_bits,
        prs_us,
        mod_us,
        mod_certified: modular.is_some(),
        agreed: match (&prs, &modular) {
            (Some(x), Some(y)) => x == y,
            (_, None) => true, // a decline is not a disagreement
            _ => false,
        },
        decline_reason: diag.primary(),
        primes_used: diag.primes_used(),
        eval_points: diag.rec_points_tried(),
        gcd_us,
        gcd_agrees: dispatched == prs,
    }
}

/// One row of the DECLINE CENSUS: why `mod_gcd` gave up on one instance.
pub(crate) struct DeclineRow {
    pub(crate) label: &'static str,
    pub(crate) reason: &'static str,
    pub(crate) certified: bool,
    pub(crate) primes_used: u32,
    pub(crate) prime_bad_coeff: u32,
    pub(crate) prime_bad_lcg: u32,
    pub(crate) prime_rec_declined: u32,
    pub(crate) lc_gate_rejected: u32,
    pub(crate) cert_reject_u: u32,
    pub(crate) cert_reject_v: u32,
    pub(crate) rec_inner_declined: u32,
    pub(crate) rec_budget_exhausted: u32,
    pub(crate) rec_lch_mismatch: u32,
    pub(crate) rec_trialdiv_reject: u32,
    pub(crate) rec_unlucky_degree: u32,
    pub(crate) rec_base_failed: u32,
    pub(crate) rec_content_failed: u32,
    pub(crate) rec_points_tried: u32,
    pub(crate) rec_reset_smaller: u32,
    pub(crate) rec_max_points_at_level: u32,
    pub(crate) rec_max_deg_bound: u32,
}

fn decline_row(label: &'static str, d: &ay_nra::oracle_api::OModGcdDiag) -> DeclineRow {
    DeclineRow {
        label,
        reason: d.primary(),
        certified: d.certified(),
        primes_used: d.primes_used(),
        prime_bad_coeff: d.prime_bad_coeff(),
        prime_bad_lcg: d.prime_bad_lcg(),
        prime_rec_declined: d.prime_rec_declined(),
        lc_gate_rejected: d.lc_gate_rejected(),
        cert_reject_u: d.cert_reject_u(),
        cert_reject_v: d.cert_reject_v(),
        rec_inner_declined: d.rec_inner_declined(),
        rec_budget_exhausted: d.rec_budget_exhausted(),
        rec_lch_mismatch: d.rec_lch_mismatch(),
        rec_trialdiv_reject: d.rec_trialdiv_reject(),
        rec_unlucky_degree: d.rec_unlucky_degree(),
        rec_base_failed: d.rec_base_failed(),
        rec_content_failed: d.rec_content_failed(),
        rec_points_tried: d.rec_points_tried(),
        rec_reset_smaller: d.rec_reset_smaller(),
        rec_max_points_at_level: d.rec_max_points_at_level(),
        rec_max_deg_bound: d.rec_max_deg_bound(),
    }
}

/// Diagnose one multivariate shape from [`MV_SHAPES`].
pub(crate) fn diagnose_mv(idx: usize) -> DeclineRow {
    let (mut m, u, v, label) = mv_instance(idx);
    let (_, diag) = m.mod_gcd_diag(&u, &v);
    decline_row(label, &diag)
}

/// Diagnose one RANDOM case, drawn from exactly the generator the
/// `pm-mod-gcd` differential check uses, so the census population and the
/// checked population are the same one.
pub(crate) fn diagnose_random(rng: &mut Rng) -> Option<DeclineRow> {
    let g = gen_pm(rng);
    let mut m = OPolyMgr::new();
    let gg = m.mk(&g.g_terms);
    let aa = m.mk(&g.a_terms);
    let bb = m.mk(&g.b_terms);
    if m.is_zero(&gg) || m.is_zero(&aa) || m.is_zero(&bb) {
        return None;
    }
    let u = m.mul(&gg, &aa);
    let v = m.mul(&gg, &bb);
    if m.is_zero(&u) || m.is_zero(&v) {
        return None;
    }
    let (_, diag) = m.mod_gcd_diag(&u, &v);
    Some(decline_row(g.shape, &diag))
}

/// Walk a plain exact-pseudo-remainder chain and report the widest coefficient
/// it produced. No content removal and no fraction-free division: this is the
/// chain a first implementation writes, and the column it fills is the reason
/// z3 does not use one.
fn naive_chain_peak(m: &mut OPolyMgr, u: &OMgrPoly, v: &OMgrPoly) -> (u64, usize, bool) {
    let mut a = u.clone();
    let mut b = v.clone();
    if m.degree(&a, X) < m.degree(&b, X) {
        std::mem::swap(&mut a, &mut b);
    }
    let mut peak = m.max_coeff_bits(&a).max(m.max_coeff_bits(&b));
    let mut peak_terms = m.len(&a).max(m.len(&b));
    for _ in 0..16 {
        if m.is_zero(&b) || m.degree(&b, X) == 0 {
            return (peak, peak_terms, false);
        }
        let Some(pd) = m.pseudo_division(&a, &b, X, true) else {
            return (peak, peak_terms, false);
        };
        peak = peak.max(m.max_coeff_bits(&pd.rem));
        peak_terms = peak_terms.max(m.len(&pd.rem));
        if peak > CHAIN_BIT_ABORT || m.len(&pd.rem) > CHAIN_TERM_ABORT {
            return (peak, peak_terms, true);
        }
        a = b;
        b = pd.rem;
    }
    (peak, peak_terms, false)
}

/// Walk the SUBRESULTANT PRS exactly as `polymanager::gcd_prs` does — content
/// removed up front, and each remainder divided by `g * h^delta` — and report
/// the widest coefficient it produced.
///
/// This is a second, independent transcription of the same recurrence, written
/// against the public facade. Its answer is not compared to the manager's (the
/// manager's `gcd` is what the checks cover); what it is for is measuring the
/// intermediate widths the manager's own path passes through, which no
/// external observer can otherwise see.
fn subresultant_chain_peak(m: &mut OPolyMgr, u: &OMgrPoly, v: &OMgrPoly) -> (u64, usize, bool) {
    let mut a = u.clone();
    let mut b = v.clone();
    if m.degree(&a, X) < m.degree(&b, X) {
        std::mem::swap(&mut a, &mut b);
    }
    let (Some((_, _, mut pp_u)), Some((_, _, mut pp_v))) = (m.iccp(&a, X), m.iccp(&b, X)) else {
        return (0, 0, true);
    };
    let mut peak = m.max_coeff_bits(&pp_u).max(m.max_coeff_bits(&pp_v));
    let mut peak_terms = m.len(&pp_u).max(m.len(&pp_v));
    let mut gg = m.constant(BigInt::one());
    let mut hh = m.constant(BigInt::one());
    for _ in 0..16 {
        if m.is_zero(&pp_v) || m.degree(&pp_v, X) == 0 {
            return (peak, peak_terms, false);
        }
        let delta = m.degree(&pp_u, X) - m.degree(&pp_v, X);
        let Some(pd) = m.pseudo_division(&pp_u, &pp_v, X, true) else {
            return (peak, peak_terms, false);
        };
        let rem = pd.rem;
        peak = peak.max(m.max_coeff_bits(&rem));
        peak_terms = peak_terms.max(m.len(&rem));
        if peak > CHAIN_BIT_ABORT || m.len(&rem) > CHAIN_TERM_ABORT {
            return (peak, peak_terms, true);
        }
        if m.is_zero(&rem) || m.is_const(&rem) {
            return (peak, peak_terms, false);
        }
        let Some(mut next) = m.exact_div(&rem, &gg) else {
            return (peak, peak_terms, true);
        };
        for _ in 0..delta {
            match m.exact_div(&next, &hh) {
                Some(x) => next = x,
                None => return (peak, peak_terms, true),
            }
        }
        pp_u = pp_v;
        pp_v = next;
        peak = peak.max(m.max_coeff_bits(&pp_v));
        peak_terms = peak_terms.max(m.len(&pp_v));
        gg = m.lc(&pp_u, X);
        let mut new_h = m.constant(BigInt::one());
        for _ in 0..delta {
            new_h = m.mul(&new_h, &gg);
        }
        if delta > 1 {
            for _ in 0..delta - 1 {
                match m.exact_div(&new_h, &hh) {
                    Some(x) => new_h = x,
                    None => return (peak, peak_terms, true),
                }
            }
        }
        hh = new_h;
    }
    (peak, peak_terms, false)
}

/// Build an increasingly ill-conditioned GCD problem and MEASURE what each
/// implementation does to the coefficients.
///
/// The instance is a planted quadratic-in-`x` common factor multiplied by
/// `depth` distinct trivariate cofactors on each side. Coefficient growth in a
/// remainder sequence is driven by the number of steps, which is what `depth`
/// controls, so this is the axis that separates the three columns.
pub(crate) fn measure_growth(depth: usize) -> GrowthRow {
    use std::time::Instant;
    let mut m = OPolyMgr::new();
    // g = x^2 - 3xy + 7z
    let g = m.mk(&[
        (vec![(0, 2)], BigInt::from(1)),
        (vec![(0, 1), (1, 1)], BigInt::from(-3)),
        (vec![(2, 1)], BigInt::from(7)),
    ]);
    let mut u = g.clone();
    let mut v = g.clone();
    for k in 1..=depth as i64 {
        let f = m.mk(&[
            (vec![(0, 1)], BigInt::from(k)),
            (vec![(1, 1)], BigInt::from(k + 1)),
            (vec![], BigInt::from(k * 3 - 1)),
        ]);
        u = m.mul(&u, &f);
        let h = m.mk(&[
            (vec![(0, 1)], BigInt::from(k + 2)),
            (vec![(2, 1)], BigInt::from(-k)),
            (vec![], BigInt::from(k * 5 + 2)),
        ]);
        v = m.mul(&v, &h);
    }
    let input_bits = m.max_coeff_bits(&u).max(m.max_coeff_bits(&v));

    let t0 = Instant::now();
    let prs = m.gcd_via_prs(&u, &v);
    let prs_us = t0.elapsed().as_micros();
    let t1 = Instant::now();
    let modular = m.mod_gcd(&u, &v);
    let mod_us = t1.elapsed().as_micros();

    let (naive_peak_bits, naive_peak_terms, naive_aborted) = naive_chain_peak(&mut m, &u, &v);
    let (prs_peak_bits, prs_peak_terms, prs_aborted) = subresultant_chain_peak(&mut m, &u, &v);

    let mod_ans_bits = match &modular {
        Some(x) => m.max_coeff_bits(x),
        None => 0,
    };
    GrowthRow {
        depth,
        input_bits,
        naive_peak_bits,
        naive_aborted,
        prs_peak_bits,
        prs_aborted,
        mod_ans_bits,
        agreed: match (&prs, &modular) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        },
        modular_certified: modular.is_some(),
        prs_us,
        mod_us,
        naive_peak_terms,
        prs_peak_terms,
    }
}
