// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial factorization cost measurements.

use super::*;

// ---------------------------------------------------------------------------
// Cost measurement on ADVERSARIAL inputs
// ---------------------------------------------------------------------------

/// One row of the factorization cost table.
pub(crate) struct CostRow {
    pub(crate) family: &'static str,
    pub(crate) p: u64,
    pub(crate) degree: usize,
    pub(crate) factors: usize,
    pub(crate) us: u128,
    pub(crate) ddf_iters: u64,
    pub(crate) edf_attempts: u64,
    pub(crate) edf_splits: u64,
    pub(crate) powmods: u64,
    pub(crate) powmod_mults: u64,
    pub(crate) ok: bool,
}

/// Build `prod_{i=0}^{n-1} (x - i)` over `Z_p`: `n` distinct LINEAR factors.
///
/// This is the worst case for equal-degree factorization and the one that
/// hides an exponential: distinct-degree finishes in a single iteration and
/// hands Cantor-Zassenhaus one bucket containing all `n` factors, so every
/// factor has to be separated by random splitting.
fn split_family(m: &OZpMgr, n: usize) -> OUniZp {
    let mut f = m.one();
    for i in 0..n as u64 {
        let c = (m.p() - (i % m.p())) % m.p();
        f = m.mul(&f, &m.from_u64(vec![c, 1]));
    }
    f
}

/// An IRREDUCIBLE polynomial of degree `n` over `Z_p`, found by scanning.
///
/// This is the worst case for distinct-degree factorization: the loop cannot
/// exit early, so it runs the full `n/2` iterations, each doing a `powmod`
/// with exponent `p` on a degree-`n` modulus. Nothing is ever removed.
fn irreducible_family(m: &OZpMgr, n: usize) -> Option<OUniZp> {
    for seed in 1..4000u64 {
        let mut c = vec![0u64; n + 1];
        c[n] = 1;
        let mut s = seed;
        for slot in c.iter_mut().take(n) {
            s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            *slot = (s >> 33) % m.p();
        }
        let f = m.from_u64(c);
        if f.degree() != Some(n) {
            continue;
        }
        if m.is_irreducible(&f) == Some(true) {
            return Some(f);
        }
    }
    None
}

/// `(x^d + 1)^k`: a high multiplicity, which forces the square-free
/// decomposition to iterate before factorization starts.
fn power_family(m: &OZpMgr, base_deg: usize, k: usize) -> OUniZp {
    let mut c = vec![0u64; base_deg + 1];
    c[base_deg] = 1;
    c[0] = 1;
    let base = m.from_u64(c);
    let mut f = m.one();
    for _ in 0..k {
        f = m.mul(&f, &base);
    }
    f
}

fn measure(family: &'static str, m: &OZpMgr, f: &OUniZp) -> CostRow {
    let degree = f.degree().unwrap_or(0);
    m.reset_stats();
    let t0 = std::time::Instant::now();
    let res = m.factor(f);
    let us = t0.elapsed().as_micros();
    let s = m.stats();
    let (factors, ok) = match &res {
        Some((lc, fs)) => {
            // Verify the identity here too: a cost number for a WRONG answer
            // is worse than no number.
            let mut prod = m.from_u64(vec![*lc]);
            for (h, e) in fs {
                for _ in 0..*e {
                    prod = m.mul(&prod, h);
                }
            }
            (fs.len(), prod == *f)
        }
        None => (0, false),
    };
    CostRow {
        family,
        p: m.p(),
        degree,
        factors,
        us,
        ddf_iters: s.ddf_iters,
        edf_attempts: s.edf_attempts,
        edf_splits: s.edf_splits,
        powmods: s.powmods,
        powmod_mults: s.powmod_mults,
        ok,
    }
}

/// Measure factorization cost on adversarial families.
///
/// Not a differential check — there is nothing to compare against. It exists
/// because "the factorization is correct" says nothing about whether it is
/// exponential, and this campaign has already shipped a correct multivariate
/// GCD that took 20 seconds on a 25-term input because only coefficient width
/// was being measured.
pub(crate) fn measure_cost(max_n: usize) -> Vec<CostRow> {
    let mut rows = Vec::new();
    for p in [3u64, 101, 65_537] {
        let Some(m) = OZpMgr::new(p) else { continue };
        // Family 1: fully split — worst case for equal-degree.
        let mut n = 8;
        while n <= max_n {
            if u64::try_from(n).unwrap_or(u64::MAX) <= p {
                let f = split_family(&m, n);
                if f.degree() == Some(n) {
                    rows.push(measure("split-linear", &m, &f));
                }
            }
            n *= 2;
        }
        // Family 2: irreducible — worst case for distinct-degree.
        let mut n = 8;
        while n <= max_n {
            if let Some(f) = irreducible_family(&m, n) {
                rows.push(measure("irreducible", &m, &f));
            }
            n *= 2;
        }
        // Family 3: a high power — worst case for square-free decomposition.
        let mut k = 8;
        while k * 2 <= max_n {
            let f = power_family(&m, 2, k);
            rows.push(measure("power-of-quadratic", &m, &f));
            k *= 2;
        }
    }
    rows
}
