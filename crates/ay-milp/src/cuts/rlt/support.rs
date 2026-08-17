// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact product supports recognized from original rows and bounds.

use super::*;

/// An EXACT substitution for the product `y_ij = x_i·x_j`, established from the model's own rows
/// rather than from a bound. These are where RLT's strength lives: a purely McCormick-relaxed
/// product statement is usually implied by the row it came from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum RltExact {
    /// `x_i = 1 ⇒ x_j = 0` (a conflict), and `x_j` is a free binary. Then `y_ij = 0`:
    /// `x_i = 0` gives `y = 0`, and `x_i = 1` forces `x_j = 0` so again `y = 0`.
    Zero,
    /// The model asserts `x_j ≤ u·x_i` with `u > 0` and `l_j ≥ 0` (a variable upper bound whose
    /// SWITCH is the multiplier). Then `y_ij = x_j`: `x_i = 0` forces `0 ≤ x_j ≤ 0` so `x_j = 0`
    /// and `y = 0 = x_j`; `x_i = 1` gives `y = x_j` by definition. No relaxation at all.
    Equal,
}

/// Whether column `c` is a free binary — `Binary` KIND and bounds EXACTLY `[0,1]`.
///
/// The kind alone is not the predicate. Branching and presolve tighten bounds in place, and the
/// whole derivation below rests on `x_i ≥ 0` and `1 − x_i ≥ 0` being the model's own facts, and
/// on `x_i² = x_i`. This is the same class of error as the MIR substitution bug this crate
/// already shipped, where an integrality property was read off a column's KIND when it is a
/// property of its BOUND.
pub(super) fn rlt_free_binary(model: &Model, c: usize) -> bool {
    let col = Col(c as u32);
    model.col_kind(col) == ColKind::Binary && model.col_bounds(col) == (0.0, 1.0)
}

/// WHICH valid linear support was chosen for one product term. The CHOICE is made once, in
/// `f64`, and the same tag then produces the `f64` triple the screen uses and the `BigRational`
/// triple the emitted cut is built from — so the screen and the derivation can never disagree
/// about which inequality they are talking about.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum RltFace {
    /// The exact substitution `y_ij = 0` (a conflict).
    Zero,
    /// The exact substitution `y_ij = x_j` (a VUB switched by the multiplier).
    Equal,
    /// `y ≥ l_j·x_i`.
    M1,
    /// `y ≤ u_j·x_i`.
    M2,
    /// `y ≤ x_j − l_j(1−x_i)`.
    M3,
    /// `y ≥ x_j − u_j(1−x_i)`.
    M4,
}

impl RltFace {
    /// The support written as `y_ij ⋛ p·x_i + q·x_j + r`, in `f64`, for SCREENING only.
    pub(super) fn pqr_f64(self, lo: f64, up: f64) -> (f64, f64, f64) {
        match self {
            RltFace::Zero => (0.0, 0.0, 0.0),
            RltFace::Equal => (0.0, 1.0, 0.0),
            RltFace::M1 => (lo, 0.0, 0.0),
            RltFace::M2 => (up, 0.0, 0.0),
            RltFace::M3 => (lo, 1.0, -lo),
            RltFace::M4 => (up, 1.0, -up),
        }
    }

    /// The same support in EXACT rationals, which is what the emitted cut is built from.
    pub(super) fn pqr(self, lo: f64, up: f64) -> Option<(BigRational, BigRational, BigRational)> {
        let z = BigRational::zero;
        let one: BigRational = One::one();
        Some(match self {
            RltFace::Zero => (z(), z(), z()),
            RltFace::Equal => (z(), one, z()),
            RltFace::M1 => (exact(lo)?, z(), z()),
            RltFace::M2 => (exact(up)?, z(), z()),
            RltFace::M3 => {
                let l = exact(lo)?;
                (l.clone(), one, -l)
            }
            RltFace::M4 => {
                let u = exact(up)?;
                (u.clone(), one, -u)
            }
        })
    }
}

/// The TIGHTEST valid linear support for `y_ij = x_i·x_j` in the requested direction, at `x*`.
///
/// # The four McCormick faces, and why each is valid
///
/// For `x_i ∈ {0,1}` and `x_j ∈ [l_j, u_j]`, each of these holds at BOTH values of `x_i`, which
/// — the statement being linear in a binary — is the whole proof:
///
/// ```text
///   (M1)  y ≥ l_j·x_i            x_i=0: 0 ≥ 0.        x_i=1: x_j ≥ l_j.
///   (M4)  y ≥ x_j − u_j(1−x_i)   x_i=0: 0 ≥ x_j−u_j.  x_i=1: x_j ≥ x_j.
///   (M2)  y ≤ u_j·x_i            x_i=0: 0 ≤ 0.        x_i=1: x_j ≤ u_j.
///   (M3)  y ≤ x_j − l_j(1−x_i)   x_i=0: 0 ≤ x_j−l_j.  x_i=1: x_j ≤ x_j.
/// ```
///
/// M1/M3 need `l_j` finite, M2/M4 need `u_j` finite; a face whose bound is infinite is simply not
/// offered, and a term with no offered face declines the whole cut.
///
/// # Choosing per term is legitimate; combining is not
///
/// Each face is individually valid, so picking whichever is tightest AT `x*` per term is a free
/// choice — `x*` steers WHICH valid inequality is derived and never whether it is valid. What
/// would NOT be legitimate is substituting `max(M1, M4)`: that is not linear and not an
/// inequality of the model. The choice is made once, here, and frozen into the coefficients.
///
/// Ties keep the FIRST face considered (M1 before M4, M2 before M3) so the derivation is
/// deterministic — sequential choices reaching a coefficient through an unordered iteration is
/// how an A/B arm stops being reproducible. The comparison is `f64` on purpose: it decides only
/// WHICH valid inequality to derive, so its rounding cannot cost soundness, and it must be the
/// same comparison the screen makes.
pub(super) fn rlt_face(
    model: &Model,
    x_i: f64,
    x_j: f64,
    j: usize,
    want_lower: bool,
    ov: Option<RltExact>,
) -> Option<RltFace> {
    if let Some(k) = ov {
        // An exact substitution is a valid support in BOTH directions, and it is tight.
        return Some(match k {
            RltExact::Zero => RltFace::Zero,
            RltExact::Equal => RltFace::Equal,
        });
    }
    let (lo, up) = model.col_bounds(Col(j as u32));
    let mut best: Option<(f64, RltFace)> = None;
    let offer = |val: f64, f: RltFace, best: &mut Option<(f64, RltFace)>| {
        let take = match best {
            None => true,
            // want_lower: keep the LARGEST lower bound. Otherwise the SMALLEST upper bound.
            Some((v, _)) => {
                if want_lower {
                    val > *v
                } else {
                    val < *v
                }
            }
        };
        if take {
            *best = Some((val, f));
        }
    };
    if want_lower {
        if lo.is_finite() {
            offer(lo * x_i, RltFace::M1, &mut best);
        }
        if up.is_finite() {
            offer(up * x_i + x_j - up, RltFace::M4, &mut best);
        }
    } else {
        if up.is_finite() {
            offer(up * x_i, RltFace::M2, &mut best);
        }
        if lo.is_finite() {
            offer(lo * x_i + x_j - lo, RltFace::M3, &mut best);
        }
    }
    best.map(|(_, f)| f)
}

/// Every column that CONFLICTS with free binary `i` — `x_i = 1 ⇒ x_j = 0` — proven from one
/// ORIGINAL row plus the global bounds, in exact rationals.
///
/// This is the clique separator's lane B specialised to the pairs that contain `i`, which is what
/// makes it cheap enough to run per multiplier: only rows that CONTAIN `i` can constrain forcing
/// `i` on, so the scan is over `rows_of[i]`, not the matrix.
///
/// For a row side `Σ_k a_k·x_k ≤ c`, pay every column its least contribution over its box (a side
/// with an unbounded least contribution proves nothing and is skipped) and write
/// `slack = c − Σ_k min_k`. Forcing free binary `k` to 1 adds its SURPLUS `s_k = a_k − min_k ≥ 0`,
/// so forcing `i` and `k` both on overshoots exactly when `s_i + s_k > slack`. A packing row
/// `Σx ≤ 1` gives `slack = 1`, `s = 1`, `1+1 > 1` — the set-packing conflicts fall out of the
/// same test, so there is no separate lane A to keep in step.
///
/// Each returned edge is certified by this one exact comparison against one original row, and the
/// derivation consumes the set directly rather than searching over it, so there is no gap between
/// what was proven and what is used.
pub(super) fn rlt_conflicts(
    model: &Model,
    n_rows: usize,
    rows_of: &[Vec<u32>],
    i: usize,
) -> std::collections::BTreeSet<usize> {
    let mut out = std::collections::BTreeSet::new();
    let Some(rows) = rows_of.get(i) else {
        return out;
    };
    for &r in rows {
        let r = r as usize;
        if r >= n_rows {
            continue; // cut-slot rows never establish a globally valid conflict
        }
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 2 {
            continue;
        }
        for (sign, rhs) in [(1.0f64, ub), (-1.0, lb)] {
            if !rhs.is_finite() {
                continue;
            }
            let Some(rhs) = exact(sign * rhs) else {
                continue;
            };
            let mut minact = BigRational::zero();
            let mut surplus: Vec<(usize, BigRational)> = Vec::new();
            let mut s_i: Option<BigRational> = None;
            let mut ok = true;
            for &(c, raw) in coeffs {
                let Some(a) = exact(sign * raw) else {
                    ok = false;
                    break;
                };
                if a.is_zero() {
                    continue;
                }
                let (clo, cup) = model.col_bounds(Col(c));
                let bnd = if a.is_positive() { clo } else { cup };
                if !bnd.is_finite() {
                    ok = false;
                    break;
                }
                let Some(bnd) = exact(bnd) else {
                    ok = false;
                    break;
                };
                let m = &a * &bnd;
                if rlt_free_binary(model, c as usize) {
                    // A free binary can take 1, so the forcing is real; its surplus over the box
                    // floor is `a − a·bnd`.
                    let s = &a - &m;
                    if c as usize == i {
                        s_i = Some(s);
                    } else if s.is_positive() {
                        surplus.push((c as usize, s));
                    }
                }
                minact += m;
            }
            let (true, Some(s_i)) = (ok, s_i) else {
                continue;
            };
            if !s_i.is_positive() {
                continue; // forcing `i` on does not tighten this side at all
            }
            let slack = &rhs - &minact;
            if slack.is_negative() {
                // The row is violated at its own box minimum: that is an infeasibility for the LP
                // to report, not a conflict for a cut to exploit.
                continue;
            }
            for (k, s_k) in surplus {
                if &s_i + &s_k > slack {
                    out.insert(k);
                }
            }
        }
    }
    out
}

/// Every variable upper bound `x_j ≤ u·x_i` the ORIGINAL rows assert, indexed by the SWITCH `i`.
///
/// Deliberately re-derived here rather than taken from [`variable_upper_bounds`]: that function
/// scans `0..model.num_rows()` of whatever model it is handed, and the root loop hands separators
/// `work`, which grows a row per adopted cut. A VUB read off a CUT row is not a fact of the model
/// and must never reach an exact substitution. Bounded by `n_rows`, so only original rows count.
///
/// `l_j ≥ 0` is required and is load-bearing: the `y_ij = x_j` substitution needs `x_i = 0` to
/// force `x_j = 0`, and `x_j ≤ 0` only does that when `x_j` cannot go negative.
pub(super) fn rlt_vub_by_switch(
    model: &Model,
    n_rows: usize,
) -> std::collections::BTreeMap<usize, Vec<usize>> {
    let mut out: std::collections::BTreeMap<usize, Vec<usize>> = std::collections::BTreeMap::new();
    for r in 0..n_rows.min(model.num_rows()) {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        // `a_x·x + a_y·y ≤ 0` with exactly two columns and no lower side: the only two-column
        // shape that says `x ≤ u·y` outright.
        if coeffs.len() != 2 || !ub.is_finite() || ub.abs() > 0.0 || lb.is_finite() {
            continue;
        }
        for (p, q) in [(0usize, 1usize), (1, 0)] {
            let (cx, ax) = coeffs[p];
            let (cy, ay) = coeffs[q];
            let (jj, ii) = (cx as usize, cy as usize);
            if jj == ii || !(ax > 0.0 && ay < 0.0) {
                continue;
            }
            if !rlt_free_binary(model, ii) {
                continue; // the fixed-charge argument turns on the SWITCH being 0/1
            }
            if model.col_bounds(Col(cx)).0 < 0.0 {
                continue; // `x_i = 0 ⇒ x_j ≤ 0` only forces `x_j = 0` when `l_j ≥ 0`
            }
            let (Some(ax), Some(ay)) = (exact(ax), exact(ay)) else {
                continue;
            };
            let u = -(&ay / &ax);
            if u.is_positive() {
                let e = out.entry(ii).or_default();
                if !e.contains(&jj) {
                    e.push(jj);
                }
            }
        }
    }
    out
}
