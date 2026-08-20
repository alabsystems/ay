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

/// Which structural columns start at their UPPER bound instead of the default
/// lower one — the exact rim's port of the f64 simplex's upper crash
/// (`ay_pb_core::optimize::safe_lp_bound::crash_at_upper`, `cb11447d8`).
///
/// WHY: the default start puts every structural on its lower bound, so on a
/// COVERING model (`a_rj > 0`, row lower bound `b_r > 0`, no row upper bound)
/// all `m` logical variables start BELOW their bound and [`ExactLp::make_feasible`]
/// has to walk every one of them out, one exact pivot each — and each pivot
/// substitutes the entering column into every other row, so the tableau fills in
/// and the rationals lengthen as it goes. MEASURED on `mw19_19` (467x466, HiGHS
/// milliseconds): 466 of 466 logicals violated at the start, 951 Phase I pivots
/// in 60s and still not feasible. Starting those columns at their upper bound
/// instead satisfies every row outright: same instance, 0 Phase I pivots, 4.3µs.
///
/// The decision is per column, on the single move `x_j: lower -> upper`
/// evaluated against the default point — `act_r` is row `r`'s activity there,
/// `span_j = ub_j - lb_j`, `delta = a_rj * span_j`:
///
/// * `gain` — violation the move actually removes, capped per row by what that
///   row is short (`max(0, lb_r - act_r)`) or over (`max(0, act_r - ub_r)`);
///   overshooting a satisfied row buys nothing;
/// * `harm` — violation it can create, charged IN FULL (`|delta|`) against the
///   row's opposite bound whenever that bound is finite, whatever slack the row
///   actually has.
///
/// Crash at upper iff `gain > harm` with a finite, positive span. Covering rows
/// give `gain > 0 = harm` (no finite row upper bound to charge), so every column
/// crashes; packing rows give `0 = gain < harm`, so none does. A row with BOTH
/// bounds finite charges at least as much harm as it credits gain, so
/// equality/ranged shapes — set partitioning above all — can never tip a column
/// and reproduce the old all-at-lower start term for term. Mixed models get the
/// per-column verdict, and Phase I repairs whatever the estimate got wrong.
///
/// NOT shape-gated: the per-column rule self-gates (a covering test is exactly
/// what `gain > harm` is), and a "does this model look like covering"
/// precondition would be a second, weaker copy of it that mixed models would
/// fall through.
///
/// WHY THE FULL HARM CHARGE IS THE LOAD-BEARING CHOICE: charging `|delta|`
/// against any finite opposite bound means a column can only tip when EVERY row
/// it raises is unbounded above and every row it lowers is unbounded below. So
/// a crashed column cannot increase any row's violation — and two crashed
/// columns cannot fight over a row either, since a row that one raises and
/// another lowers would need both `ub_r = +inf` and `lb_r = -inf`, which leaves
/// it unviolatable. The crashed start is therefore never worse than the
/// all-at-lower one, by construction rather than by measurement. The weaker
/// "harm = slack actually eaten" reading has no such property: it tips whole
/// set-partitioning models (`a_rj = 1`, `lb_r = ub_r = 1`) on the grounds that
/// the first unit of slack is free.
///
/// [`start_is_better`] then enforces the same property numerically before the
/// mask is adopted, and adds the one thing the algebra does not: a start that
/// is ALREADY feasible is left alone (nothing to gain, and a different starting
/// vertex on a degenerate LP is a different optimal vertex downstream).
///
/// EXACTNESS: this is a heuristic read of the model's `f64` view, and it moves
/// the STARTING POINT only — to a bound already held exactly in `upper`. No
/// verdict, Farkas certificate or multiplier depends on it; a wrong guess costs
/// pivots, never soundness. `f64` is therefore the right arithmetic here: two
/// cheap passes over the matrix rather than rational ones, on a construction
/// path that is already seconds on a 1.85M-nnz model.
fn upper_crash_mask(model: &Model, deadline: Option<Instant>) -> Option<Vec<bool>> {
    let n = model.num_cols();
    let m = model.num_rows();
    // The default (all-at-lower) start and each column's crash span, in f64.
    // A column with an infinite or empty span is not a candidate: its default
    // start is already the only finite bound it has, or it has none.
    let mut start = vec![0.0f64; n];
    let mut span = vec![0.0f64; n];
    for j in 0..n {
        let (lb, ub) = model.col_bounds(Col(j as u32));
        start[j] = if lb.is_finite() {
            lb
        } else if ub.is_finite() {
            ub
        } else {
            0.0
        };
        if lb.is_finite() && ub.is_finite() && ub > lb {
            span[j] = ub - lb;
        }
    }
    let mut gain = vec![0.0f64; n];
    let mut harm = vec![0.0f64; n];
    for r in 0..m {
        if r % 64 == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
            return None;
        }
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        let mut act = 0.0f64;
        for &(c, a) in coeffs {
            act += a * start[c as usize];
        }
        let short = if lb.is_finite() {
            (lb - act).max(0.0)
        } else {
            0.0
        };
        let over = if ub.is_finite() {
            (act - ub).max(0.0)
        } else {
            0.0
        };
        for &(c, a) in coeffs {
            let j = c as usize;
            let delta = a * span[j];
            if delta > 0.0 {
                gain[j] += delta.min(short);
                if ub.is_finite() {
                    harm[j] += delta;
                }
            } else if delta < 0.0 {
                gain[j] += (-delta).min(over);
                if lb.is_finite() {
                    harm[j] += -delta;
                }
            }
        }
    }
    let mask: Vec<bool> = (0..n)
        .map(|j| span[j] > 0.0 && gain[j].is_finite() && harm[j].is_finite() && gain[j] > harm[j])
        .collect();
    if !start_is_better(model, &mask, &start, &span, deadline)? {
        return Some(vec![false; n]);
    }
    Some(mask)
}

/// Does the crashed start leave the logicals in better shape than the
/// all-at-lower one? The DOMINANCE GUARD on [`upper_crash_mask`]: adopt the
/// mask only where it demonstrably helps, so no model can be handed a worse
/// start than the one it has today.
///
/// "Better" is measured the way Phase I pays for it — first on the NUMBER of
/// logicals outside their bounds (each one costs at least one exact repair
/// pivot, and each pivot substitutes into every row), then, on a tie, on total
/// violation. A tie in both keeps the old start: an equally-violated but
/// radically different starting vertex is a change with no case for it.
///
/// A non-finite activity anywhere (an overflowing `f64` dot product) declines
/// the crash outright — the estimate cannot be trusted on numbers it cannot
/// represent, and declining costs only the old behaviour.
///
/// This is a BELT, not the proof: the full harm charge in [`upper_crash_mask`]
/// already makes a crashed column unable to raise any row's violation, and a
/// non-empty mask means some row's shortfall strictly falls, so the guard
/// passes whenever it is consulted. It is kept because it costs one `f64` pass
/// on a rational construction path, it is what catches a rounding-tipped column
/// or a future weakening of the rule, and it states the invariant a reader
/// would otherwise have to re-derive.
fn start_is_better(
    model: &Model,
    mask: &[bool],
    start: &[f64],
    span: &[f64],
    deadline: Option<Instant>,
) -> Option<bool> {
    if !mask.iter().any(|&on| on) {
        return Some(false);
    }
    let (mut count_lower, mut count_crash) = (0usize, 0usize);
    let (mut viol_lower, mut viol_crash) = (0.0f64, 0.0f64);
    for r in 0..model.num_rows() {
        if r % 64 == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
            return None;
        }
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        let mut act_lower = 0.0f64;
        let mut act_crash = 0.0f64;
        for &(c, a) in coeffs {
            let j = c as usize;
            act_lower += a * start[j];
            act_crash += a * if mask[j] {
                start[j] + span[j]
            } else {
                start[j]
            };
        }
        if !act_lower.is_finite() || !act_crash.is_finite() {
            return Some(false);
        }
        for (act, count, viol) in [
            (act_lower, &mut count_lower, &mut viol_lower),
            (act_crash, &mut count_crash, &mut viol_crash),
        ] {
            let short = if lb.is_finite() {
                (lb - act).max(0.0)
            } else {
                0.0
            };
            let over = if ub.is_finite() {
                (act - ub).max(0.0)
            } else {
                0.0
            };
            if short > 0.0 || over > 0.0 {
                *count += 1;
                *viol += short + over;
            }
        }
    }
    Some(count_crash < count_lower || (count_crash == count_lower && viol_crash < viol_lower))
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
    /// [`Self::new_within`] bounds it; `new` remains for callers with no
    /// construction deadline whose cost the caller owns.
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
            if i & 0xff == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
                return None;
            }
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
        // Upper-bound crash (see [`upper_crash_mask`]): choose each structural's
        // starting bound BEFORE the rows are built, so the exact activity pass
        // below lands on the crashed point directly and no second rational pass
        // over the matrix is needed. Nonbasics still sit on a bound, which is
        // what `make_feasible`'s termination argument requires.
        let crash = upper_crash_mask(model, deadline)?;
        for (j, at_upper) in crash.iter().enumerate() {
            if *at_upper {
                if let Some(ub) = &upper[j] {
                    values[j] = ub.clone();
                }
            }
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
            let mut terms = Vec::with_capacity(coeffs.len());
            for (entry, &(c, a)) in coeffs.iter().enumerate() {
                if entry & 0xff == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
                    return None;
                }
                terms.push((c, Rational::from_big(model.row_coeff_exact(r, c, a))));
            }
            let mut v = Rational::zero();
            for (entry, (c, a)) in terms.iter().enumerate() {
                if entry & 0xff == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
                    return None;
                }
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
        let mut unlimited = |_| true;
        self.structural_values_with_work(&mut unlimited)
            .expect("unbounded exact point conversion")
    }

    pub(crate) fn structural_values_with_work<F>(&self, work: &mut F) -> Option<Vec<BigRational>>
    where
        F: FnMut(usize) -> bool + ?Sized,
    {
        let mut values = Vec::with_capacity(self.n_structural);
        for (index, value) in self.values[..self.n_structural].iter().enumerate() {
            if index & 0xff == 0 && !work(0x100.min(self.n_structural.saturating_sub(index))) {
                return None;
            }
            values.push(value.to_big());
        }
        Some(values)
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

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> Budget {
        Budget {
            deadline: None,
            max_iters: 10_000,
        }
    }

    /// No logical starts outside its bounds ⇔ `make_feasible` returns without
    /// pivoting once.
    fn phase_one_is_empty(lp: &ExactLp) -> bool {
        lp.rows
            .iter()
            .all(|row| !lp.below_lower(row.basic as usize) && !lp.above_upper(row.basic as usize))
    }

    fn unit_objective(n: u32) -> Vec<(u32, Rational)> {
        (0..n).map(|j| (j, Rational::new(1, 1))).collect()
    }

    /// COVERING — the class the crash exists for: every column tips to its
    /// upper bound, which leaves Phase I with nothing to repair, and the
    /// optimum is unchanged by the different starting point.
    #[test]
    fn covering_columns_crash_and_leave_phase_one_empty() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 1.0);
        let y = m.add_col(0.0, 1.0);
        let z = m.add_col(0.0, 1.0);
        m.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        m.add_row(1.0, f64::INFINITY, &[(y, 1.0), (z, 1.0)]);
        assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![true, true, true]);
        let mut lp = ExactLp::new(&m);
        assert!(phase_one_is_empty(&lp));
        // min x+y+z over that cover is 1 (y = 1), crash or no crash.
        let LpOptimum::Optimal { value, .. } = lp.minimize(&unit_objective(3), &budget()) else {
            panic!("covering LP must be optimal");
        };
        assert_eq!(value, BigRational::from_integer(1.into()));
    }

    /// PACKING — `gain` is 0 and `harm` is not, so nothing tips and the start
    /// is the historical all-at-lower one.
    #[test]
    fn packing_columns_do_not_crash() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 1.0);
        let y = m.add_col(0.0, 1.0);
        m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
        assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![false, false]);
        let lp = ExactLp::new(&m);
        assert!(lp.values[..2].iter().all(Rational::is_zero));
    }

    /// SET PARTITIONING — a row with both bounds finite charges at least as
    /// much harm as it credits gain, so an equality model can never tip a
    /// column. This is what keeps `air03`/`nw04`-shaped models on their old
    /// start.
    #[test]
    fn equality_rows_never_crash() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 1.0);
        let y = m.add_col(0.0, 1.0);
        let z = m.add_col(0.0, 1.0);
        m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        m.add_row(1.0, 1.0, &[(y, 1.0), (z, 1.0)]);
        assert_eq!(
            upper_crash_mask(&m, None).unwrap(),
            vec![false, false, false]
        );
    }

    /// A start that is already feasible is left alone: with nothing short,
    /// nothing has anything to gain, so no column tips and the starting vertex
    /// — which is what a degenerate LP's reported optimum hangs on — does not
    /// move.
    #[test]
    fn a_feasible_start_is_not_disturbed() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 1.0);
        let y = m.add_col(0.0, 1.0);
        // Covering-shaped (no finite row upper bound) but satisfied at x=y=0.
        m.add_row(0.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![false, false]);
        let lp = ExactLp::new(&m);
        assert!(lp.values[..2].iter().all(Rational::is_zero));
    }

    /// An unbounded column has no upper bound to crash to; a fixed column has
    /// nowhere to move. Neither is a candidate.
    #[test]
    fn infinite_and_empty_spans_are_not_candidates() {
        let mut m = Model::new();
        let free = m.add_col(0.0, f64::INFINITY);
        let fixed = m.add_col(1.0, 1.0);
        let boxed = m.add_col(0.0, 1.0);
        m.add_row(
            5.0,
            f64::INFINITY,
            &[(free, 1.0), (fixed, 1.0), (boxed, 1.0)],
        );
        assert_eq!(
            upper_crash_mask(&m, None).unwrap(),
            vec![false, false, true]
        );
    }

    /// The crash is a STARTING POINT, not a verdict: an infeasible covering
    /// model is still refuted, with the same exact answer either way.
    #[test]
    fn crash_does_not_change_an_infeasible_verdict() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 1.0);
        m.add_row(2.0, f64::INFINITY, &[(x, 1.0)]);
        assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![true]);
        let mut lp = ExactLp::new(&m);
        assert!(matches!(
            lp.make_feasible(&budget()),
            LpFeasibility::Infeasible(_)
        ));
    }
}
