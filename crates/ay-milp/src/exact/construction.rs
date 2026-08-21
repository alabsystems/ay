// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use num_integer::Integer as _;
use num_traits::One as _;

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
pub(super) fn upper_crash_mask(model: &Model, deadline: Option<Instant>) -> Option<Vec<bool>> {
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

struct StructuralStart {
    lower: Vec<Option<Rational>>,
    upper: Vec<Option<Rational>>,
    values: Vec<Rational>,
}

struct BuiltRow {
    tableau: TabRow,
    lower: Option<Rational>,
    upper: Option<Rational>,
    value: Rational,
    scale: Rational,
    convertible: bool,
}

fn structural_start(model: &Model, deadline: Option<Instant>) -> Option<StructuralStart> {
    let n = model.num_cols();
    let mut lower = Vec::with_capacity(n + model.num_rows());
    let mut upper = Vec::with_capacity(n + model.num_rows());
    let mut values = Vec::with_capacity(n + model.num_rows());
    for i in 0..n {
        if i & 0xff == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
            return None;
        }
        let (lb, ub) = model.col_bounds(Col(i as u32));
        let lb = exact(lb).map(Rational::from_big);
        let ub = exact(ub).map(Rational::from_big);
        let value = lb
            .clone()
            .or_else(|| ub.clone())
            .unwrap_or_else(Rational::zero);
        lower.push(lb);
        upper.push(ub);
        values.push(value);
    }

    // Choose the structural starting bounds before building rows, so their
    // exact activities land on the crashed point without a second matrix pass.
    let crash = upper_crash_mask(model, deadline)?;
    for (j, at_upper) in crash.into_iter().enumerate() {
        if at_upper {
            if let Some(ub) = &upper[j] {
                values[j] = ub.clone();
            }
        }
    }
    Some(StructuralStart {
        lower,
        upper,
        values,
    })
}

/// Integralise one row when doing so keeps every coefficient on the inline
/// path. A declined scale leaves the original reduced row untouched and locks
/// the solve out of the fraction-free representation.
fn integralize_terms(
    terms: Vec<(u32, Rational)>,
    lambda: BigInt,
    deadline: Option<Instant>,
) -> Option<(Vec<(u32, Rational)>, Rational, bool)> {
    let unit = Rational::new(1, 1);
    if lambda.is_one() {
        return Some((terms, unit, true));
    }

    let lambda = Rational::from_big(BigRational::from_integer(lambda));
    let mut scaled = Vec::with_capacity(terms.len());
    for (entry, (column, coefficient)) in terms.iter().enumerate() {
        if entry & 0xff == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
            return None;
        }
        let value = coefficient.clone() * lambda.clone();
        debug_assert!(is_integral(&value), "row scaling must integralise");
        if !value.is_small() {
            break;
        }
        scaled.push((*column, value));
    }
    if scaled.len() == terms.len() {
        Some((scaled, lambda, true))
    } else {
        Some((terms, unit, false))
    }
}

fn exact_activity(
    terms: &[(u32, Rational)],
    values: &[Rational],
    deadline: Option<Instant>,
) -> Option<Rational> {
    let mut value = Rational::zero();
    for (entry, (column, coefficient)) in terms.iter().enumerate() {
        if entry & 0xff == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
            return None;
        }
        value += coefficient.clone() * values[*column as usize].clone();
    }
    Some(value)
}

/// Build a tableau row from the model's exact side store. The positive row
/// scale changes only the spelling of the logical variable; row bounds,
/// activity, and exported multipliers are scaled consistently.
fn build_row(
    model: &Model,
    row: usize,
    n_structural: usize,
    values: &[Rational],
    deadline: Option<Instant>,
) -> Option<BuiltRow> {
    let (coefficients, lb, ub) = model.row(Row(row as u32));
    let mut terms = Vec::with_capacity(coefficients.len());
    let mut lambda = BigInt::one();
    for (entry, &(column, coefficient)) in coefficients.iter().enumerate() {
        if entry & 0xff == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
            return None;
        }
        let coefficient = Rational::from_big(model.row_coeff_exact(row, column, coefficient));
        if !is_integral(&coefficient) {
            lambda = lambda.lcm(&coefficient.denom());
        }
        terms.push((column, coefficient));
    }

    let (terms, scale, convertible) = integralize_terms(terms, lambda, deadline)?;
    let value = exact_activity(&terms, values, deadline)?;
    let lower = model
        .row_lb_exact(row, lb)
        .map(|bound| Rational::from_big(bound) * scale.clone());
    let upper = model
        .row_ub_exact(row, ub)
        .map(|bound| Rational::from_big(bound) * scale.clone());
    Some(BuiltRow {
        tableau: TabRow {
            basic: (n_structural + row) as u32,
            terms,
            den: Rational::new(1, 1),
        },
        lower,
        upper,
        value,
        scale,
        convertible,
    })
}

impl ExactLp {
    /// As Self::new, declining (fail-closed) if deadline passes mid-build.
    pub(crate) fn new_within(model: &Model, deadline: Option<Instant>) -> Option<Self> {
        let n = model.num_cols();
        let m = model.num_rows();
        let total = n + m;
        let StructuralStart {
            mut lower,
            mut upper,
            mut values,
        } = structural_start(model, deadline)?;
        let mut rows = Vec::with_capacity(m);
        let mut row_scale = Vec::with_capacity(m);
        let mut convertible = true;
        for row in 0..m {
            if row % 64 == 0 && deadline.is_some_and(|limit| Instant::now() >= limit) {
                return None;
            }
            let built = build_row(model, row, n, &values, deadline)?;
            lower.push(built.lower);
            upper.push(built.upper);
            values.push(built.value);
            row_scale.push(built.scale);
            convertible &= built.convertible;
            rows.push(built.tableau);
        }

        let mut basic_of = vec![None; total];
        for (index, row) in rows.iter().enumerate() {
            basic_of[row.basic as usize] = Some(index as u32);
        }
        Some(Self {
            n_structural: n,
            lower,
            upper,
            values,
            rows,
            basic_of,
            form: Form::Reduced,
            // The starting basis is the logicals, so its determinant is one.
            det: Rational::new(1, 1),
            row_scale,
            poisoned: false,
            convertible,
            window_entries: 0,
            window_inline: 0,
            window_pivots: 0,
            cold_windows: 0,
            census_seq: 0,
        })
    }
}
