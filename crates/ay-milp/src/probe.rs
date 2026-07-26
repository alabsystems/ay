// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root probing: tentatively fix a binary and re-run the exact bound
//! propagation, harvesting what that proves.
//!
//! # What it produces, and why each product is sound
//!
//! Base presolve ([`crate::presolve::tighten_bounds`]) reads bounds off the
//! rows *as they stand*. It never tentatively pins a column and re-propagates,
//! so it cannot see a reduction that only appears *conditional* on a binary's
//! value. Probing does exactly that: for a free binary `b` it clones the
//! (already base-presolved) model, fixes `b = v`, and hands the result to the
//! SAME proven exact rational propagation. Two things can come back:
//!
//! 1. **A FORCED FIXING.** If fixing `b = 1-v` makes the model
//!    [`Presolved::Infeasible`], then no feasible point has `b = 1-v`, so
//!    `b = v` in every feasible point. The fixing is admitted ONLY on that
//!    exact-infeasibility verdict — never from a float, never from the LP. This
//!    is domain reduction the base presolve provably cannot find, and it is the
//!    high-value, node-reducing product.
//!
//! 2. **AN IMPLIED CLIQUE.** If, under `b = v`, exact propagation collapses
//!    another free binary `j` to a point `w`, then every feasible point with
//!    `b = v` has `j = w`. That implication is a valid linear inequality over
//!    `{b, j}` (one of four `<=`/`>=` orientations), so adding it as a cut row
//!    removes no feasible integer point — it only strengthens the LP
//!    relaxation. The row is emitted in the standard clique form the existing
//!    cut framework already validates.
//!
//! Neither product can ever cut off a feasible point: the first rests on the
//! exact-infeasibility of the opposite branch, the second on an implication the
//! same exact propagation derived. The brute-force test at the bottom pins this
//! by enumeration.
//!
//! The float LP is used ONLY to *rank* which binaries are worth the exact
//! probe (fractional-at-root first) and to cap the count against the deadline.
//! It decides nothing: a bad ranking costs probe budget, never correctness.

use std::time::Instant;

use crate::model::{Col, ColKind, Model};
use crate::presolve::{tighten_bounds, tighten_bounds_opt, Presolved};

/// How the probe pass is budgeted.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ProbeCfg {
    /// Maximum number of binary columns to probe (each costs up to two exact
    /// propagations). Ranked by root-LP fractionality when `use_lp_rank`.
    pub(crate) cap: usize,
    /// Maximum number of clique rows to emit (0 disables clique emission).
    pub(crate) clique_cap: usize,
    /// Rank candidates by root-LP fractionality (else column order).
    pub(crate) use_lp_rank: bool,
}

/// The outcome of a root-probe pass.
pub(crate) enum RootProbe {
    /// Probing proved the model has no feasible point (a binary whose BOTH
    /// values are exact-infeasible, or the forced-fixing cascade contradicted).
    Infeasible,
    /// A (possibly) strengthened model plus a tally of what was applied.
    Probed {
        /// The model with forced fixings applied, re-cascaded through base
        /// presolve, and clique rows appended.
        model: Model,
        /// Forced fixings admitted (binaries proven to one value).
        forced: usize,
        /// Clique rows emitted.
        cliques: usize,
        /// Binary columns actually probed.
        probes: usize,
    },
}

/// A derived implication `x_b = v  =>  x_j = w`, over two binaries.
#[derive(Clone, Copy)]
struct Implication {
    b: u32,
    v: u8,
    j: u32,
    w: u8,
}

impl Implication {
    /// The clique row `(lb, ub, [(col, coeff)])` this implication licenses.
    /// Validity (all four cases remove only points the implication forbids):
    ///   * `1=>1`: `x_b - x_j <= 0`
    ///   * `1=>0`: `x_b + x_j <= 1`
    ///   * `0=>1`: `x_b + x_j >= 1`
    ///   * `0=>0`: `x_j - x_b <= 0`
    fn row(&self) -> (f64, f64, [(u32, f64); 2]) {
        match (self.v, self.w) {
            (1, 1) => (f64::NEG_INFINITY, 0.0, [(self.b, 1.0), (self.j, -1.0)]),
            (1, 0) => (f64::NEG_INFINITY, 1.0, [(self.b, 1.0), (self.j, 1.0)]),
            (0, 1) => (1.0, f64::INFINITY, [(self.b, 1.0), (self.j, 1.0)]),
            _ => (f64::NEG_INFINITY, 0.0, [(self.b, -1.0), (self.j, 1.0)]),
        }
    }

    /// A canonical key for dedup: two implications that denote the SAME row
    /// (e.g. `b=1=>j=0` and `j=1=>b=0` both give `x_b + x_j <= 1`) collapse to
    /// one key. Built from the row content with columns sorted.
    fn key(&self) -> (u64, [(u32, i64); 2]) {
        let (lb, ub, mut coeffs) = self.row();
        coeffs.sort_unstable_by_key(|&(c, _)| c);
        let bound = lb.to_bits() ^ ub.to_bits().rotate_left(1);
        (bound, coeffs.map(|(c, a)| (c, a as i64)))
    }
}

/// Whether column `c` is a free binary (`Binary` kind, bounds exactly `[0,1]`).
fn is_free_binary(model: &Model, c: usize) -> bool {
    let col = Col(c as u32);
    model.col_kind(col) == ColKind::Binary && model.col_bounds(col) == (0.0, 1.0)
}

/// Root-LP relaxation values per column, for candidate ranking. Best-effort:
/// `None` (fall back to column order) on any failure or non-optimal LP.
fn root_lp_values(model: &Model) -> Option<Vec<f64>> {
    use crate::session::LpSession;
    use crate::Outcome;
    // The continuous relaxation: same rows, same bounds, integrality dropped.
    let mut relaxed = model.clone();
    for spec in &mut relaxed.cols {
        spec.kind = ColKind::Continuous;
    }
    let opts = crate::SolveOpts::new().with_time_limit(std::time::Duration::from_secs_f64(2.0));
    let mut lp = LpSession::new(&relaxed, &opts).ok()?;
    match lp.optimize_model_objective().ok()? {
        Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
            use num_traits::ToPrimitive;
            Some(
                model_values
                    .iter()
                    .map(|v| v.to_f64().unwrap_or(0.0))
                    .collect(),
            )
        }
        _ => None,
    }
}

/// Ranked probe candidates: free binaries, most-fractional-at-root first when
/// LP values are available, else column order.
fn candidates(model: &Model, cfg: ProbeCfg) -> Vec<usize> {
    let mut cands: Vec<usize> = (0..model.num_cols())
        .filter(|&c| is_free_binary(model, c))
        .collect();
    if cfg.use_lp_rank {
        if let Some(vals) = root_lp_values(model) {
            // Ascending |v - 0.5|: a fractional binary (near 0.5) is where a
            // forced value or a live implication most changes the search.
            cands.sort_by(|&a, &b| {
                let fa = (vals.get(a).copied().unwrap_or(0.0) - 0.5).abs();
                let fb = (vals.get(b).copied().unwrap_or(0.0) - 0.5).abs();
                fa.partial_cmp(&fb).unwrap_or(std::cmp::Ordering::Equal)
            });
        }
    }
    cands.truncate(cfg.cap);
    cands
}

/// Run a budgeted root-probe pass on an already-base-presolved `model`.
pub(crate) fn root_probe(model: &Model, deadline: Option<Instant>, cfg: ProbeCfg) -> RootProbe {
    // Probing reads the exact matrix; on an inexact-coefficient model the exact
    // side-store lives on the ORIGINAL rows and base presolve already
    // fail-closes (it clones untouched). Match that: no probing there.
    if model.has_inexact_coeffs() {
        return RootProbe::Probed {
            model: model.clone(),
            forced: 0,
            cliques: 0,
            probes: 0,
        };
    }
    let trace = std::env::var_os("AY_MILP_TRACE").is_some();
    let expired = || deadline.is_some_and(|d| Instant::now() >= d);
    let cands = candidates(model, cfg);
    let n = model.num_cols();

    // Forced fixings collected as (col, value); implications collected raw.
    let mut forced: Vec<(u32, f64)> = Vec::new();
    let mut forced_seen = vec![false; n];
    let mut implications: Vec<Implication> = Vec::new();
    let mut probes = 0usize;
    let mut implied_total = 0usize;

    // One side of a probe: fix `b = v`, exact-propagate (no coef tightening).
    // Returns None if that fix is exact-INFEASIBLE, else the collapsed binaries.
    let probe_side = |b: usize, v: u8| -> Option<Vec<(u32, u8)>> {
        let mut mm = model.clone();
        mm.set_col_bounds(Col(b as u32), f64::from(v), f64::from(v));
        match tighten_bounds_opt(&mm, deadline, false) {
            Presolved::Infeasible => None,
            Presolved::Tightened(out) => {
                let mut collapsed = Vec::new();
                for &j in &cands {
                    if j == b {
                        continue;
                    }
                    let (lo, up) = out.col_bounds(Col(j as u32));
                    // A free binary collapsed to a single 0/1 point = implied.
                    if lo == up && (lo == 0.0 || lo == 1.0) {
                        collapsed.push((j as u32, lo as u8));
                    }
                }
                Some(collapsed)
            }
        }
    };

    for &b in &cands {
        if expired() {
            break;
        }
        // Skip a binary a prior cascade already forced (its box moved off 0/1).
        if !is_free_binary(model, b) || forced_seen[b] {
            continue;
        }
        probes += 1;
        let s0 = probe_side(b, 0);
        let s1 = probe_side(b, 1);
        match (s0, s1) {
            (None, None) => return RootProbe::Infeasible, // no feasible value
            (None, Some(imp1)) => {
                // b=0 infeasible => b MUST be 1.
                if !forced_seen[b] {
                    forced.push((b as u32, 1.0));
                    forced_seen[b] = true;
                }
                implied_total += imp1.len();
                if cfg.clique_cap > 0 {
                    implications.extend(imp1.into_iter().map(|(j, w)| Implication {
                        b: b as u32,
                        v: 1,
                        j,
                        w,
                    }));
                }
            }
            (Some(imp0), None) => {
                // b=1 infeasible => b MUST be 0.
                if !forced_seen[b] {
                    forced.push((b as u32, 0.0));
                    forced_seen[b] = true;
                }
                implied_total += imp0.len();
                if cfg.clique_cap > 0 {
                    implications.extend(imp0.into_iter().map(|(j, w)| Implication {
                        b: b as u32,
                        v: 0,
                        j,
                        w,
                    }));
                }
            }
            (Some(imp0), Some(imp1)) => {
                implied_total += imp0.len() + imp1.len();
                if cfg.clique_cap > 0 {
                    implications.extend(imp0.into_iter().map(|(j, w)| Implication {
                        b: b as u32,
                        v: 0,
                        j,
                        w,
                    }));
                    implications.extend(imp1.into_iter().map(|(j, w)| Implication {
                        b: b as u32,
                        v: 1,
                        j,
                        w,
                    }));
                }
            }
        }
    }

    // Apply forced fixings and re-cascade once through the FULL base presolve
    // (with coefficient tightening) — misc07's dense implication graph means a
    // handful of root fixings propagate to many more.
    let mut out = model.clone();
    for &(c, v) in &forced {
        out.fix_col(Col(c), v);
    }
    if !forced.is_empty() {
        match tighten_bounds(&out, deadline) {
            Presolved::Infeasible => return RootProbe::Infeasible,
            Presolved::Tightened(m) => out = *m,
        }
    }

    // Emit clique rows (deduped, capped). Each is valid for the model, so it is
    // valid for the cascaded `out` too (fixings only restrict).
    let mut cliques = 0usize;
    if cfg.clique_cap > 0 {
        use std::collections::HashSet;
        let mut seen: HashSet<(u64, [(u32, i64); 2])> = HashSet::new();
        for imp in &implications {
            if cliques >= cfg.clique_cap {
                break;
            }
            // A clique over a binary the cascade has since fixed is redundant.
            let (bl, bu) = out.col_bounds(Col(imp.b));
            let (jl, ju) = out.col_bounds(Col(imp.j));
            if bl == bu || jl == ju {
                continue;
            }
            if !seen.insert(imp.key()) {
                continue;
            }
            let (lb, ub, coeffs) = imp.row();
            let cols: Vec<(Col, f64)> = coeffs
                .iter()
                .map(|&(c, a)| (out.col_at(c as usize).expect("valid col"), a))
                .collect();
            out.add_row(lb, ub, &cols);
            cliques += 1;
        }
    }

    if trace {
        eprintln!(
            "AY_MILP_TRACE root-probe: {probes} binaries probed, FORCED={} \
             (cascaded box), {implied_total} implied fixings, {cliques} clique rows",
            forced.len()
        );
    }

    RootProbe::Probed {
        model: out,
        forced: forced.len(),
        cliques,
        probes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Sense;
    use num_rational::BigRational;

    fn cfg() -> ProbeCfg {
        ProbeCfg {
            cap: usize::MAX,
            clique_cap: usize::MAX,
            use_lp_rank: false,
        }
    }

    /// A forced fixing the base presolve cannot find: `x + y <= 1`,
    /// `x + y >= 1` over two binaries pins nothing on its own, but fixing
    /// `x = 0` forces `y = 1` and fixing `x = 1` forces `y = 0`. Add
    /// `y <= 0` (y fixed to 0) and now `x = 0` is infeasible, so probing must
    /// FORCE `x = 1`.
    #[test]
    fn probing_forces_a_binary_the_base_presolve_cannot() {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        // x + y >= 1, and y is pinned to 0 by a row => x must be 1.
        m.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0)]); // y <= 0
        let RootProbe::Probed { model, forced, .. } = root_probe(&m, None, cfg()) else {
            panic!("feasible");
        };
        assert!(forced >= 1, "x must be forced to 1");
        assert_eq!(model.col_bounds(x), (1.0, 1.0));
    }

    /// Both values of a binary infeasible => the whole model is infeasible.
    #[test]
    fn probing_detects_infeasibility() {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        // y pinned to 0, plus x=0 => (need x>=1) and x=1 => (2x<=1) both fail.
        m.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]); // x + y >= 1
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0)]); // y <= 0  => x >= 1
        m.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]); // x <= 0  => contradiction
        assert!(matches!(root_probe(&m, None, cfg()), RootProbe::Infeasible));
    }

    /// An implied clique is emitted and is valid: `x=1 => y=0` under a
    /// `2x + 2y <= 3` shape (over binaries, x=1 forces y=0).
    #[test]
    fn probing_emits_a_valid_clique() {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0), (y, 2.0)]); // x=1 => y<=0.5 => y=0
        let RootProbe::Probed { model, cliques, .. } = root_probe(&m, None, cfg()) else {
            panic!("feasible");
        };
        assert!(cliques >= 1, "x=1 => y=0 should emit a clique");
        // The clique cannot cut off a feasible point of the original.
        for a in 0..2 {
            for b in 0..2 {
                let p = vec![
                    BigRational::from_integer(a.into()),
                    BigRational::from_integer(b.into()),
                ];
                if m.check_point(&p).is_ok() {
                    assert!(model.check_point(&p).is_ok(), "clique cut off {p:?}");
                }
            }
        }
        let _ = Sense::Minimize;
    }

    /// THE SOUNDNESS PROPERTY, checked exhaustively: over random small binary
    /// models, NO forced fixing and NO emitted clique removes a feasible
    /// integer point. Mirrors `presolve::propagation_never_cuts_off_a_feasible_point`.
    #[test]
    fn probing_never_cuts_off_a_feasible_point() {
        let mut seed = 0x1234_5678_9abc_def0u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let dims = 5usize;
        for _ in 0..500 {
            let mut m = Model::new();
            let cols: Vec<_> = (0..dims).map(|_| m.add_binary_col()).collect();
            let nrows = 2 + (rnd().unsigned_abs() % 4) as usize;
            for _ in 0..nrows {
                let terms: Vec<_> = cols
                    .iter()
                    .map(|&c| (c, (rnd() % 7 - 3) as f64))
                    .filter(|&(_, a)| a != 0.0)
                    .collect();
                if terms.is_empty() {
                    continue;
                }
                let b = (rnd() % 9 - 2) as f64;
                if rnd() % 2 == 0 {
                    m.add_row(f64::NEG_INFINITY, b, &terms);
                } else {
                    m.add_row(b, f64::INFINITY, &terms);
                }
            }
            let probed = match root_probe(&m, None, cfg()) {
                RootProbe::Infeasible => {
                    // If probing claims infeasible, the original must truly have
                    // NO feasible 0/1 point.
                    for mask in 0..(1u32 << dims) {
                        let p: Vec<BigRational> = (0..dims)
                            .map(|k| BigRational::from_integer((((mask >> k) & 1) as i64).into()))
                            .collect();
                        assert!(
                            m.check_point(&p).is_err(),
                            "probe said INFEASIBLE but {p:?} is feasible"
                        );
                    }
                    continue;
                }
                RootProbe::Probed { model, .. } => model,
            };
            for mask in 0..(1u32 << dims) {
                let p: Vec<BigRational> = (0..dims)
                    .map(|k| BigRational::from_integer((((mask >> k) & 1) as i64).into()))
                    .collect();
                if m.check_point(&p).is_ok() {
                    assert!(
                        probed.check_point(&p).is_ok(),
                        "root probe cut off a feasible point {p:?}"
                    );
                }
            }
        }
    }

    /// Mixed binary + general-integer + continuous columns: probing must still
    /// never remove a feasible point (only binaries are probed/fixed; general
    /// integers may appear in implications' source but are never emitted as
    /// binary cliques).
    #[test]
    fn probing_sound_with_mixed_column_kinds() {
        let mut seed = 0xdead_beef_0bad_f00du64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        for _ in 0..300 {
            let mut m = Model::new();
            let b0 = m.add_binary_col();
            let b1 = m.add_binary_col();
            let gi = m.add_int_col(0.0, 3.0);
            let cont = m.add_col(0.0, 5.0);
            let cols = [b0, b1, gi, cont];
            for _ in 0..3 {
                let terms: Vec<_> = cols
                    .iter()
                    .map(|&c| (c, (rnd() % 5 - 2) as f64))
                    .filter(|&(_, a)| a != 0.0)
                    .collect();
                if terms.is_empty() {
                    continue;
                }
                let rhs = (rnd() % 9 - 2) as f64;
                if rnd() % 2 == 0 {
                    m.add_row(f64::NEG_INFINITY, rhs, &terms);
                } else {
                    m.add_row(rhs, f64::INFINITY, &terms);
                }
            }
            let probed = match root_probe(&m, None, cfg()) {
                RootProbe::Infeasible => continue,
                RootProbe::Probed { model, .. } => model,
            };
            // Enumerate the integer lattice; the continuous column is pinned at
            // several sample values to witness feasibility preservation.
            for a in 0..2 {
                for b in 0..2 {
                    for g in 0..4 {
                        for &cv in &[0.0, 2.5, 5.0] {
                            let p: Vec<BigRational> = vec![
                                BigRational::from_integer(a.into()),
                                BigRational::from_integer(b.into()),
                                BigRational::from_integer(g.into()),
                                BigRational::from_float(cv).unwrap(),
                            ];
                            if m.check_point(&p).is_ok() {
                                assert!(
                                    probed.check_point(&p).is_ok(),
                                    "root probe cut off feasible {p:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}
