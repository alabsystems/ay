// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact-rational bounded-variable simplex: ay-milp's certification rim.
//!
//! Every verdict it produces is exact, and certificate-bearing verdicts carry
//! model-level evidence ([`FarkasCertificate`] / optimality multipliers) that
//! [`crate::cert`] can re-verify without solver state. The float-first engine
//! uses this tier for exact replay and certificate extraction;
//! [`crate::LpSession`] runs on it directly.
//!
//! Method: Dutertre–de Moura bounded-variable simplex over
//! [`ay_lra::rational::Rational`] (inline i64 fast path, `BigRational`
//! fallback — the workspace's shared exact vocabulary). Variables are the
//! model's structural columns plus one logical variable per row
//! (`s_i = a_i·x`, bounded by the row's range). Feasibility is restored by
//! the standard violated-basic repair loop, optimization by a primal
//! improve loop with bound flips; both use Bland's smallest-index rule
//! throughout, so termination is guaranteed and iteration caps are a belt,
//! not the proof. Anything the budget cuts short is `Unknown` — never a
//! partial verdict (fail-closed).

use std::time::Instant;

use ay_lra::rational::Rational;
use num_rational::BigRational;
use num_traits::Zero;

use crate::cert::{BoundSide, FactRef, FarkasCertificate, Multiplier};
use crate::model::{exact, Col, Model, Row};
use crate::outcome::UnknownReason;

/// Iteration/deadline budget for one solve.
#[derive(Debug, Clone)]
pub(crate) struct Budget {
    pub deadline: Option<Instant>,
    pub max_iters: u64,
}

impl Budget {
    /// The default iteration cap for a problem with `vars` variables:
    /// generous (Bland terminates on its own), scaled to size.
    pub(crate) fn default_iters(vars: usize) -> u64 {
        20_000 + 200 * vars as u64
    }
}

/// A feasibility verdict.
#[derive(Debug)]
pub(crate) enum LpFeasibility {
    Feasible,
    Infeasible(FarkasCertificate),
    Unknown(UnknownReason),
}

/// An optimization verdict. `value` excludes the model's objective offset
/// (the session layer adds it); `multipliers` are the dual-bound evidence
/// over model facts, ready for [`crate::cert::OptimalityCertificate`].
#[derive(Debug)]
pub(crate) enum LpOptimum {
    Optimal {
        value: BigRational,
        multipliers: Vec<Multiplier>,
    },
    Unbounded,
    Infeasible(FarkasCertificate),
    Unknown(UnknownReason),
}

/// One tableau row: `basic = Σ terms` where every term variable is nonbasic.
/// Rows are homogeneous (no constant): logical variables carry the row
/// constants as bounds instead.
#[derive(Debug, Clone)]
struct TabRow {
    basic: u32,
    /// Sorted by variable index; no zeros.
    terms: Vec<(u32, Rational)>,
}

impl TabRow {
    fn coeff_of(&self, var: u32) -> Option<&Rational> {
        self.terms
            .binary_search_by_key(&var, |&(v, _)| v)
            .ok()
            .map(|i| &self.terms[i].1)
    }
}

/// The exact simplex state. Kept alive across re-solves by
/// [`crate::LpSession`] — the basis persists, so repeated `optimize` calls
/// warm-start (the L0 form of the design's "one factorized model, many
/// objectives").
pub(crate) struct ExactLp {
    n_structural: usize,
    lower: Vec<Option<Rational>>,
    upper: Vec<Option<Rational>>,
    values: Vec<Rational>,
    rows: Vec<TabRow>,
    /// var -> row index when basic.
    basic_of: Vec<Option<u32>>,
}

/// Direction a nonbasic variable is moved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dir {
    Up,
    Down,
}

impl ExactLp {
    /// Build from a model, relaxing integrality (binary columns become their
    /// `[lb, ub]` boxes). Model must be validated. An `Infeasible` verdict
    /// from the relaxation is valid for the unrelaxed model too.
    ///
    /// Construction itself is a full exact-rational pass over the matrix — on a
    /// 1.85M-nnz NN model it is SECONDS of gcd-reducing multiplies, and it used to
    /// run un-deadlined before `make_feasible`'s per-iteration checks could fire
    /// (a profiler sample of a deadline overshoot landed 53% of its hits here).
    /// [`Self::new_within`] bounds it; `new` remains for construction-time callers
    /// (sessions, tests) whose cost the caller owns.
    pub(crate) fn new(model: &Model) -> Self {
        Self::new_within(model, None).expect("no deadline to miss")
    }

    /// As [`Self::new`], declining (fail-closed) if `deadline` passes mid-build.
    pub(crate) fn new_within(model: &Model, deadline: Option<Instant>) -> Option<Self> {
        let n = model.num_cols();
        let m = model.num_rows();
        let total = n + m;
        let mut lower: Vec<Option<Rational>> = Vec::with_capacity(total);
        let mut upper: Vec<Option<Rational>> = Vec::with_capacity(total);
        let mut values: Vec<Rational> = Vec::with_capacity(total);
        for i in 0..n {
            let (lb, ub) = model.col_bounds(Col(i as u32));
            let lb = exact(lb).map(Rational::from_big);
            let ub = exact(ub).map(Rational::from_big);
            // Nonbasic start value: a finite bound, else 0.
            let v = lb
                .clone()
                .or_else(|| ub.clone())
                .unwrap_or_else(Rational::zero);
            lower.push(lb);
            upper.push(ub);
            values.push(v);
        }
        let mut rows = Vec::with_capacity(m);
        for r in 0..m {
            if r % 64 == 0 {
                if let Some(d) = deadline {
                    if Instant::now() >= d {
                        return None;
                    }
                }
            }
            let (coeffs, lb, ub) = model.row(Row(r as u32));
            // VERDICT-CRITICAL: the exact rim tableau is built from the TRUE
            // model. A rounded `f64` coefficient/bound is read from the
            // exact-rational side-store, so the rim produces Farkas/optimum
            // verdicts over the model the file actually wrote.
            let terms: Vec<(u32, Rational)> = coeffs
                .iter()
                .map(|&(c, a)| (c, Rational::from_big(model.row_coeff_exact(r, c, a))))
                .collect();
            let mut v = Rational::zero();
            for (c, a) in &terms {
                v += a.clone() * values[*c as usize].clone();
            }
            lower.push(model.row_lb_exact(r, lb).map(Rational::from_big));
            upper.push(model.row_ub_exact(r, ub).map(Rational::from_big));
            values.push(v);
            rows.push(TabRow {
                basic: (n + r) as u32,
                terms,
            });
        }
        let mut basic_of = vec![None; total];
        for (ri, row) in rows.iter().enumerate() {
            basic_of[row.basic as usize] = Some(ri as u32);
        }
        Some(Self {
            n_structural: n,
            lower,
            upper,
            values,
            rows,
            basic_of,
        })
    }

    /// The current structural point, exact.
    pub(crate) fn structural_values(&self) -> Vec<BigRational> {
        self.values[..self.n_structural]
            .iter()
            .map(Rational::to_big)
            .collect()
    }

    fn fact_of(&self, var: u32, side: BoundSide) -> FactRef {
        if (var as usize) < self.n_structural {
            FactRef::ColBound {
                col: Col(var),
                side,
            }
        } else {
            FactRef::RowBound {
                row: Row(var - self.n_structural as u32),
                side,
            }
        }
    }

    fn below_lower(&self, var: usize) -> bool {
        matches!(&self.lower[var], Some(lb) if self.values[var] < *lb)
    }

    fn above_upper(&self, var: usize) -> bool {
        matches!(&self.upper[var], Some(ub) if self.values[var] > *ub)
    }

    fn can_increase(&self, var: usize) -> bool {
        match &self.upper[var] {
            Some(ub) => self.values[var] < *ub,
            None => true,
        }
    }

    fn can_decrease(&self, var: usize) -> bool {
        match &self.lower[var] {
            Some(lb) => self.values[var] > *lb,
            None => true,
        }
    }

    /// Shift a nonbasic variable by `delta`, updating every dependent basic
    /// value.
    fn shift_nonbasic(&mut self, var: u32, delta: &Rational) {
        if delta.is_zero() {
            return;
        }
        self.values[var as usize] += delta.clone();
        for row in &self.rows {
            if let Some(c) = row.coeff_of(var) {
                let d = c.clone() * delta.clone();
                self.values[row.basic as usize] += d;
            }
        }
    }

    /// Algebraic pivot: `entering` (nonbasic, in row `ri`) becomes basic,
    /// the row's current basic leaves. Values are not touched.
    fn pivot(&mut self, ri: usize, entering: u32) {
        let row = &self.rows[ri];
        let leaving = row.basic;
        let c_e = row
            .coeff_of(entering)
            .expect("pivot: entering not in row")
            .clone();
        // x_e = (1/c_e)·x_leaving − Σ_{k≠e} (c_k/c_e)·x_k
        let inv = Rational::new(1, 1) / c_e;
        let mut new_terms: Vec<(u32, Rational)> = Vec::with_capacity(row.terms.len());
        for (v, c) in &row.terms {
            if *v == entering {
                continue;
            }
            new_terms.push((*v, -(c.clone() * inv.clone())));
        }
        new_terms.push((leaving, inv));
        new_terms.sort_unstable_by_key(|&(v, _)| v);
        let new_row = TabRow {
            basic: entering,
            terms: new_terms,
        };
        // Substitute x_e in every other row.
        for rj in 0..self.rows.len() {
            if rj == ri {
                continue;
            }
            let d = match self.rows[rj].coeff_of(entering) {
                Some(d) => d.clone(),
                None => continue,
            };
            let substituted = substitute(&self.rows[rj].terms, entering, &d, &new_row.terms);
            self.rows[rj].terms = substituted;
        }
        self.basic_of[leaving as usize] = None;
        self.basic_of[entering as usize] = Some(ri as u32);
        self.rows[ri] = new_row;
    }

    /// Phase A: repair basic-variable bound violations (Bland). On success
    /// every variable is within its bounds.
    pub(crate) fn make_feasible(&mut self, budget: &Budget) -> LpFeasibility {
        let mut iters: u64 = 0;
        loop {
            iters += 1;
            if iters > budget.max_iters {
                return LpFeasibility::Unknown(UnknownReason::IterationLimit);
            }
            // EVERY iteration, not every 64th. One iteration of an exact simplex is a pass in
            // rational arithmetic over every column, which on a model like nw04 (87,482 of them)
            // takes about a second -- so a check every 64 iterations first fires a minute after
            // the deadline it is supposed to be enforcing. `Instant::now()` costs ~20ns against
            // that; there was never anything to save by batching it.
            if let Some(d) = budget.deadline {
                if Instant::now() >= d {
                    return LpFeasibility::Unknown(UnknownReason::Timeout);
                }
            }
            // Smallest-index violated basic variable.
            let violated = self
                .rows
                .iter()
                .enumerate()
                .filter(|(_, row)| {
                    self.below_lower(row.basic as usize) || self.above_upper(row.basic as usize)
                })
                .min_by_key(|(_, row)| row.basic);
            let (ri, need_increase) = match violated {
                None => {
                    // Nonbasic variables sit at bounds or at 0 (free) by
                    // construction and only move within bounds; basics are
                    // now repaired.
                    return LpFeasibility::Feasible;
                }
                Some((ri, row)) => (ri, self.below_lower(row.basic as usize)),
            };
            let row = &self.rows[ri];
            let basic = row.basic;
            // Smallest-index nonbasic that can absorb the repair.
            let mut entering: Option<(u32, Rational)> = None;
            for (v, c) in &row.terms {
                let pos = c > &Rational::zero();
                let suitable = if need_increase {
                    // basic must increase: raise a positive-coeff var or
                    // lower a negative-coeff var.
                    (pos && self.can_increase(*v as usize))
                        || (!pos && self.can_decrease(*v as usize))
                } else {
                    (pos && self.can_decrease(*v as usize))
                        || (!pos && self.can_increase(*v as usize))
                };
                if suitable {
                    entering = Some((*v, c.clone()));
                    break; // terms sorted by index: first hit is Bland's choice
                }
            }
            let Some((evar, ecoeff)) = entering else {
                return LpFeasibility::Infeasible(self.farkas_from_row(ri, need_increase));
            };
            // Move entering so that basic lands exactly on its violated bound.
            let target = if need_increase {
                self.lower[basic as usize].clone().expect("violated lower")
            } else {
                self.upper[basic as usize].clone().expect("violated upper")
            };
            let delta_basic = target - self.values[basic as usize].clone();
            let delta_e = delta_basic / ecoeff;
            self.shift_nonbasic(evar, &delta_e);
            // basic now sits on its bound (exactly, by construction).
            self.pivot(ri, evar);
        }
    }

    /// The Farkas certificate from a conflicting row (no suitable entering
    /// variable). `need_increase` is the direction the basic variable had to
    /// move.
    fn farkas_from_row(&self, ri: usize, need_increase: bool) -> FarkasCertificate {
        let row = &self.rows[ri];
        let basic = row.basic;
        let mut multipliers = Vec::with_capacity(row.terms.len() + 1);
        let one = BigRational::from_integer(1.into());
        if need_increase {
            // basic < lb, and every term is saturated against raising it.
            multipliers.push(Multiplier {
                fact: self.fact_of(basic, BoundSide::Lower),
                coeff: one,
            });
            for (v, c) in &row.terms {
                let (side, coeff) = if c > &Rational::zero() {
                    (BoundSide::Upper, c.to_big())
                } else {
                    (BoundSide::Lower, -c.to_big())
                };
                multipliers.push(Multiplier {
                    fact: self.fact_of(*v, side),
                    coeff,
                });
            }
        } else {
            // basic > ub, and every term is saturated against lowering it.
            multipliers.push(Multiplier {
                fact: self.fact_of(basic, BoundSide::Upper),
                coeff: one,
            });
            for (v, c) in &row.terms {
                let (side, coeff) = if c > &Rational::zero() {
                    (BoundSide::Lower, c.to_big())
                } else {
                    (BoundSide::Upper, -c.to_big())
                };
                multipliers.push(Multiplier {
                    fact: self.fact_of(*v, side),
                    coeff,
                });
            }
        }
        FarkasCertificate { multipliers }
    }

    /// Phase B: minimize `Σ obj·x` (structural coefficients) from a feasible
    /// state. Returns the exact optimum and dual evidence.
    pub(crate) fn minimize(&mut self, obj: &[(u32, Rational)], budget: &Budget) -> LpOptimum {
        match self.make_feasible(budget) {
            LpFeasibility::Feasible => {}
            LpFeasibility::Infeasible(cert) => return LpOptimum::Infeasible(cert),
            LpFeasibility::Unknown(r) => return LpOptimum::Unknown(r),
        }
        // Express the objective over nonbasic variables.
        let mut d: Vec<(u32, Rational)> = Vec::new();
        for (v, c) in obj {
            if c.is_zero() {
                continue;
            }
            match self.basic_of[*v as usize] {
                None => merge_term(&mut d, *v, c.clone()),
                Some(ri) => {
                    for (tv, tc) in &self.rows[ri as usize].terms {
                        merge_term(&mut d, *tv, c.clone() * tc.clone());
                    }
                }
            }
        }
        let mut iters: u64 = 0;
        loop {
            iters += 1;
            if iters > budget.max_iters {
                return LpOptimum::Unknown(UnknownReason::IterationLimit);
            }
            // Every iteration -- see `make_feasible`.
            if let Some(dl) = budget.deadline {
                if Instant::now() >= dl {
                    return LpOptimum::Unknown(UnknownReason::Timeout);
                }
            }
            // Bland: smallest-index improving nonbasic.
            let mut chosen: Option<(u32, Rational, Dir)> = None;
            for (v, dc) in &d {
                debug_assert!(
                    self.basic_of[*v as usize].is_none(),
                    "obj term became basic"
                );
                if dc.is_zero() {
                    continue;
                }
                let dir = if dc < &Rational::zero() {
                    Dir::Up
                } else {
                    Dir::Down
                };
                let movable = match dir {
                    Dir::Up => self.can_increase(*v as usize),
                    Dir::Down => self.can_decrease(*v as usize),
                };
                if movable {
                    chosen = Some((*v, dc.clone(), dir));
                    break; // d kept sorted: first hit is Bland's choice
                }
            }
            let Some((evar, _, dir)) = chosen else {
                return self.optimal_from(&d);
            };
            // Step limit: own opposite bound, then ratio test over rows.
            let own_limit: Option<Rational> = match dir {
                Dir::Up => self.upper[evar as usize]
                    .as_ref()
                    .map(|ub| ub.clone() - self.values[evar as usize].clone()),
                Dir::Down => self.lower[evar as usize]
                    .as_ref()
                    .map(|lb| self.values[evar as usize].clone() - lb.clone()),
            };
            // (limit, limiting row, limiting basic var). Bland tie-break on
            // smallest basic index.
            let mut row_limit: Option<(Rational, usize, u32)> = None;
            for (ri, row) in self.rows.iter().enumerate() {
                let Some(c) = row.coeff_of(evar) else {
                    continue;
                };
                // basic delta per unit step: +c (Up) or −c (Down).
                let increases_basic = match dir {
                    Dir::Up => c > &Rational::zero(),
                    Dir::Down => c < &Rational::zero(),
                };
                let b = row.basic as usize;
                let room = if increases_basic {
                    self.upper[b]
                        .as_ref()
                        .map(|ub| ub.clone() - self.values[b].clone())
                } else {
                    self.lower[b]
                        .as_ref()
                        .map(|lb| self.values[b].clone() - lb.clone())
                };
                let Some(room) = room else { continue };
                let rate = c.clone().abs();
                let limit = room / rate;
                let replace = match &row_limit {
                    None => true,
                    Some((best, _, best_var)) => {
                        limit < *best || (limit == *best && row.basic < *best_var)
                    }
                };
                if replace {
                    row_limit = Some((limit, ri, row.basic));
                }
            }
            match (own_limit, row_limit) {
                (None, None) => return LpOptimum::Unbounded,
                (Some(own), None) => {
                    // Bound flip: move to the opposite bound.
                    let delta = signed(&own, dir);
                    self.shift_nonbasic(evar, &delta);
                }
                (own, Some((limit, ri, _))) => {
                    if let Some(own) = own {
                        if own <= limit {
                            let delta = signed(&own, dir);
                            self.shift_nonbasic(evar, &delta);
                            continue;
                        }
                    }
                    let delta = signed(&limit, dir);
                    self.shift_nonbasic(evar, &delta);
                    // Update the objective row: substitute the entering
                    // variable using the post-pivot row.
                    self.pivot(ri, evar);
                    let e_coeff = d
                        .binary_search_by_key(&evar, |&(v, _)| v)
                        .ok()
                        .map(|i| d[i].1.clone());
                    if let Some(dc) = e_coeff {
                        d.retain(|&(v, _)| v != evar);
                        let expr = self.rows[ri].terms.clone();
                        for (tv, tc) in expr {
                            merge_term(&mut d, tv, dc.clone() * tc);
                        }
                    }
                }
            }
        }
    }

    /// Build the optimality verdict from the reduced-cost row at optimum.
    fn optimal_from(&self, d: &[(u32, Rational)]) -> LpOptimum {
        let mut value = Rational::zero();
        let mut multipliers = Vec::new();
        for (v, dc) in d {
            if dc.is_zero() {
                continue;
            }
            value += dc.clone() * self.values[*v as usize].clone();
            // dc > 0: v is pinned at its lower bound (else it could improve).
            // dc < 0: pinned at its upper bound.
            let (side, coeff) = if dc > &Rational::zero() {
                (BoundSide::Lower, dc.to_big())
            } else {
                (BoundSide::Upper, -dc.to_big())
            };
            multipliers.push(Multiplier {
                fact: self.fact_of(*v, side),
                coeff,
            });
        }
        LpOptimum::Optimal {
            value: value.to_big(),
            multipliers,
        }
    }
}

/// `terms − d·x_e + d·expr`, keeping sorted order and dropping zeros.
/// `terms` must contain `x_e` with coefficient `d`.
fn substitute(
    terms: &[(u32, Rational)],
    evar: u32,
    d: &Rational,
    expr: &[(u32, Rational)],
) -> Vec<(u32, Rational)> {
    let mut out: Vec<(u32, Rational)> =
        terms.iter().filter(|&&(v, _)| v != evar).cloned().collect();
    for (v, c) in expr {
        merge_term(&mut out, *v, d.clone() * c.clone());
    }
    out
}

/// Add `coeff·var` into a sorted sparse vector, dropping resulting zeros.
fn merge_term(vec: &mut Vec<(u32, Rational)>, var: u32, coeff: Rational) {
    if coeff.is_zero() {
        return;
    }
    match vec.binary_search_by_key(&var, |&(v, _)| v) {
        Ok(i) => {
            vec[i].1 += coeff;
            if vec[i].1.is_zero() {
                vec.remove(i);
            }
        }
        Err(i) => vec.insert(i, (var, coeff)),
    }
}

/// `+magnitude` for `Up`, `−magnitude` for `Down`.
fn signed(magnitude: &Rational, dir: Dir) -> Rational {
    match dir {
        Dir::Up => magnitude.clone(),
        Dir::Down => -magnitude.clone(),
    }
}
