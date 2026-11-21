// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read a model in MPS, the interchange format every MILP solver speaks.
//!
//! Until this existed, `ay-milp` could only be given a model through its Rust API, which meant
//! every number ever measured about it came from a generator in this repository. A solver that
//! cannot read MIPLIB cannot be COMPARED on MIPLIB, and an engine tuned only against its own
//! synthetic instances is tuned against its author's imagination.
//!
//! # Why this reader does arithmetic
//!
//! A file says `0.9`. There is no such `f64`. The nearest one is
//! `8106479329266893 / 9007199254740992`, which is a hair over nine tenths, and a solver that
//! reasons EXACTLY about that hair is reasoning about a model nobody wrote.
//!
//! On MIPLIB's `flugpl` the difference is total. The row `0.9·STM1 + ANM1 − STM2 = 0` with
//! `STM1` pinned to 60 demands `STM2 − ANM1 = 54`, which two integers can satisfy. Read `0.9`
//! as a double and it demands `STM2 − ANM1 = 54.00000000000000133…`, which no two integers can
//! satisfy — so the instance becomes *provably infeasible*, and an exact solver will say so,
//! correctly, about the wrong model. Float solvers never notice because a 1e-9 feasibility
//! tolerance swallows it.
//!
//! So numbers are parsed as exact rationals from their decimal text, and then each row is
//! multiplied through by the LCM of its denominators. Scaling a row by a positive constant does
//! not move its feasible set, and it leaves every coefficient an integer — which `f64` holds
//! exactly. The float lane still gets doubles; they are now the RIGHT doubles, and the exact rim
//! recovers the file's true numbers from them.
//!
//! The file itself is read by `ay_lp::parse_mps_exact`, the one MPS reader of AY (the MIPLIB
//! 2017 checker's reading, refusing a construct readers in common use read differently, and
//! keeping every number as the rational it denotes); this module builds the engine's model from
//! that reading. AY-N12: this module once had a reader of its own, which read some files
//! differently (lower-case markers, the last of two objective entries, a negative `UP` on a
//! column with lower bound 0, the default bounds of a marker integer column).

use std::fmt;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use crate::model::{Col, Model, Sense};

/// A model read from an MPS file, with the names needed to report a solution in the
/// caller's own vocabulary.
#[derive(Debug, Clone)]
pub struct MpsProblem {
    /// The model itself.
    pub model: Model,
    /// The `NAME` field, if the file gave one.
    pub name: String,
    /// Column names, indexed by [`Col::index`].
    pub col_names: Vec<String>,
    /// Constraint row names, indexed by [`crate::Row::index`].
    pub row_names: Vec<String>,
    /// The positive factor the objective was multiplied by to make its coefficients exactly
    /// representable. The model's optimum is this many times the FILE's optimum, so divide by it
    /// — exactly, it is a rational — to report a value in the caller's units.
    ///
    /// Scaling an objective by a positive constant cannot change WHICH point is optimal, only
    /// what that point's value is called.
    pub obj_scale: BigRational,
}

impl MpsProblem {
    /// Convert an objective value from the model's scaled units back to the file's.
    #[must_use]
    pub fn unscale(&self, value: &BigRational) -> BigRational {
        value / &self.obj_scale
    }

    /// The clause a DIAGNOSTIC line must carry when this reader scaled the objective.
    ///
    /// # The defect this closes
    ///
    /// `bab::diag_float_lp` prints `obj(min-form)=` and
    /// `session::diag_shipped_float_lp` prints `outcome=OPTIMAL value=… certified=true`,
    /// and BOTH are the value of [`Self::model`] — i.e. of the SCALED model. Only
    /// the `solve` CLI calls [`Self::unscale`]. On `gt2_lprelax.mps` the diag lanes
    /// therefore say `1682.529134` where the file's optimum is
    /// `13460.233074411897`: a factor of exactly 8, which is the RECIPROCAL of
    /// `obj_scale` (the binary prints `obj_scale=1/8`), not an error. Mind that
    /// direction — [`Self::unscale`] DIVIDES by `obj_scale`, so
    /// `1682.529134 / (1/8) = 13460.233072`. A reader who multiplies by 8
    /// instead of dividing by 1/8 happens to land right; one who divides by 8
    /// lands 64x off, in the docstring of the very function that exists to stop
    /// a scale factor being misread. An auditor checking a diag line against an
    /// external reference would otherwise read a correct, exactly-certified
    /// answer as an 8x wrong one.
    ///
    /// That is the same failure mode as the scaffold banner and the
    /// `RELAXATION-NOT-MODEL` banner: a line that can be pasted somewhere it will
    /// be misread. So the remedy is the same one — put it ON the line, because a
    /// separate header does not travel with the number.
    ///
    /// Empty when the scale is 1, which is the common case; a diagnostic that
    /// cries wolf on every model teaches readers to skip the clause.
    #[must_use]
    pub fn units_clause(&self) -> String {
        if self.obj_scale.is_one() {
            return String::new();
        }
        format!(
            " [UNITS: the objective above is in the READER'S SCALED units, not the file's. \
             obj_scale={}; divide by it for a value comparable to an external reference. \
             `ay-milp solve` already does.]",
            self.obj_scale
        )
    }
}

/// Why an MPS file could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MpsError {
    /// 1-based line number in the source (0 when the fault is the file as a whole).
    pub line: usize,
    /// What went wrong.
    pub message: String,
}

impl fmt::Display for MpsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MPS line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for MpsError {}

/// A column under construction: its bounds and type, before [`build`].
#[derive(Clone)]
struct ColBuild {
    lb: Option<BigRational>, // None = infinite on that side
    ub: Option<BigRational>,
    integral: bool,
}

/// Parse `text` as MPS: the one reading of `ay_lp::parse_mps_exact` (the
/// MIPLIB 2017 checker's reading, refusing where readers in common use
/// differ; documented construct by construct in `ay-lp/src/parser/mps.rs`),
/// built into a model by [`model_from_exact_problem`]. No tool of AY reads
/// an MPS file in a second way (AY-N12).
///
/// # Errors
/// Returns [`MpsError`] with the line of a malformed or refused construct
/// (`ay_lp`'s error), or for a row whose coefficients cannot be made exactly
/// representable without exceeding `f64`'s integer range.
pub fn read_mps(text: &str) -> Result<MpsProblem, MpsError> {
    let exact = ay_lp::parse_mps_exact(text).map_err(|e| match e {
        ay_lp::LpError::Parse { line, msg } => err(line, &msg),
        ay_lp::LpError::InvalidNumber { line, raw } => err(
            line,
            &format!("`{raw}` is not a number this reader accepts"),
        ),
        other => err(0, &other.to_string()),
    })?;
    model_from_exact_problem(&exact)
}

/// The model of an exactly read problem: column `j` is `exact.columns[j]`,
/// one row per constraint row, the same objective and constant, every number
/// the rational read.
///
/// # Errors
/// As [`model_from_exact`].
pub(crate) fn model_from_exact_problem(
    exact: &ay_lp::ExactProblem,
) -> Result<MpsProblem, MpsError> {
    let columns: Vec<RationalColumn> = exact
        .columns
        .iter()
        .map(|c| RationalColumn {
            name: c.name.clone(),
            lower: c.lower.clone(),
            upper: c.upper.clone(),
            integral: c.is_integral(),
            objective: c.objective.clone(),
        })
        .collect();
    let rows: Vec<RationalRow> = exact
        .rows
        .iter()
        .map(|r| RationalRow {
            name: r.name.clone(),
            coeffs: r.coeffs.clone(),
            lower: r.lower.clone(),
            upper: r.upper.clone(),
        })
        .collect();
    let sense = match exact.sense {
        ay_lp::Sense::Min => Sense::Minimize,
        ay_lp::Sense::Max => Sense::Maximize,
    };
    model_from_exact(&exact.name, sense, &columns, &rows, &exact.offset)
}

/// One column of a model given to [`model_from_exact`].
#[derive(Debug, Clone)]
pub struct RationalColumn {
    /// The column's name.
    pub name: String,
    /// Lower bound (`None` for none).
    pub lower: Option<BigRational>,
    /// Upper bound (`None` for none).
    pub upper: Option<BigRational>,
    /// Whether the column is integer.
    pub integral: bool,
    /// Objective coefficient.
    pub objective: BigRational,
}

/// One constraint row of a model given to [`model_from_exact`]:
/// `lower <= sum(coeffs) <= upper`, `None` for an open side.
#[derive(Debug, Clone)]
pub struct RationalRow {
    /// The row's name.
    pub name: String,
    /// `(column index, coefficient)` pairs; a repeated column is summed.
    pub coeffs: Vec<(usize, BigRational)>,
    /// Lower side (`None` for none).
    pub lower: Option<BigRational>,
    /// Upper side (`None` for none).
    pub upper: Option<BigRational>,
}

/// Build the model another reader read exactly, so that this engine solves
/// the model that reader's caller prints and checks.
///
/// Every number reaches [`build`] as the rational given, the same path a
/// number of [`read_mps`] takes: a value an `f64` holds goes to the float
/// lane as is, any other is scaled into one or kept in the exact side-store
/// (module docs). Nothing is rounded on the way in. Columns keep their order,
/// so column `j` of the result is `columns[j]`.
///
/// # Errors
/// [`MpsError`] (line 0) for a coefficient naming no column, or a row
/// [`read_mps`] would refuse (a number with no finite nonzero `f64`
/// representation even as advice).
pub fn model_from_exact(
    name: &str,
    sense: Sense,
    columns: &[RationalColumn],
    rows: &[RationalRow],
    offset: &BigRational,
) -> Result<MpsProblem, MpsError> {
    let cols = columns
        .iter()
        .map(|c| ColBuild {
            lb: c.lower.clone(),
            ub: c.upper.clone(),
            integral: c.integral,
        })
        .collect();
    let obj_coeff: Vec<BigRational> = columns.iter().map(|c| c.objective.clone()).collect();
    let mut row_bounds = Vec::with_capacity(rows.len());
    let mut row_names = Vec::with_capacity(rows.len());
    let mut nz = Vec::new();
    for (r, row) in rows.iter().enumerate() {
        row_bounds.push(Some((row.lower.clone(), row.upper.clone())));
        row_names.push(row.name.clone());
        for (c, v) in &row.coeffs {
            if *c >= columns.len() {
                return Err(err(
                    0,
                    &format!("row `{}` names column {c} of {}", row.name, columns.len()),
                ));
            }
            nz.push((r, *c, v.clone()));
        }
    }
    build(
        name.to_string(),
        sense,
        &row_bounds,
        &row_names,
        columns.iter().map(|c| c.name.clone()).collect(),
        cols,
        &obj_coeff,
        nz,
        offset,
    )
}

/// Turn the parsed rationals into a `Model`: exact values stay directly in its
/// `f64` lane; non-representable finite values use rounded advice proxies plus
/// the exact-rational verdict side-store.
#[allow(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::needless_pass_by_value
)]
fn build(
    name: String,
    sense: Sense,
    row_bounds: &[Option<(Option<BigRational>, Option<BigRational>)>],
    row_names: &[String],
    col_names: Vec<String>,
    cols: Vec<ColBuild>,
    obj_coeff: &[BigRational],
    nz: Vec<(usize, usize, BigRational)>,
    obj_offset: &BigRational,
) -> Result<MpsProblem, MpsError> {
    let mut model = Model::new();

    // ---- columns ----
    //
    // A column's bounds cannot be scaled: scaling a column rescales the VARIABLE, and an integer
    // variable does not survive that. So a bound that is not exactly representable is handled
    // where it can be handled exactly:
    //   * an integer column may be TIGHTENED to the integer inside it (`x >= 1/3` is `x >= 1`),
    //     which is not an approximation but a consequence;
    //   * a continuous column's bound becomes a singleton ROW, which then scales like any other.
    let mut extra_rows: Vec<(
        Vec<(usize, BigRational)>,
        Option<BigRational>,
        Option<BigRational>,
    )> = Vec::new();
    let mut handles: Vec<Col> = Vec::with_capacity(cols.len());
    for (j, c) in cols.iter().enumerate() {
        let mut lb = c.lb.clone();
        let mut ub = c.ub.clone();
        if c.integral {
            // Tighten to the integers the bound actually admits.
            lb = lb.map(|v| v.ceil());
            ub = ub.map(|v| v.floor());
        }
        // Anything still unrepresentable is pushed into a row rather than rounded.
        let mut push_bound_row = |v: &BigRational, lower: bool| {
            let terms = vec![(j, BigRational::one())];
            if lower {
                extra_rows.push((terms, Some(v.clone()), None));
            } else {
                extra_rows.push((terms, None, Some(v.clone())));
            }
        };
        let lb_f = match &lb {
            None => f64::NEG_INFINITY,
            Some(v) if exactly_f64(v) => to_f64(v),
            Some(v) => {
                push_bound_row(v, true);
                f64::NEG_INFINITY
            }
        };
        let ub_f = match &ub {
            None => f64::INFINITY,
            Some(v) if exactly_f64(v) => to_f64(v),
            Some(v) => {
                push_bound_row(v, false);
                f64::INFINITY
            }
        };
        handles.push(if c.integral {
            model.add_int_col(lb_f, ub_f)
        } else {
            model.add_col(lb_f, ub_f)
        });
    }

    // ---- constraint rows ----
    let mut by_row: Vec<Vec<(usize, BigRational)>> = vec![Vec::new(); row_bounds.len()];
    for (r, c, v) in nz {
        by_row[r].push((c, v));
    }
    let mut kept_names = Vec::new();
    for (r, bounds) in row_bounds.iter().enumerate() {
        let Some((lo, hi)) = bounds else {
            continue; // the objective, or a row that constrains nothing
        };
        add_scaled_row(
            &mut model,
            &handles,
            &by_row[r],
            lo.as_ref(),
            hi.as_ref(),
            &row_names[r],
        )?;
        kept_names.push(row_names[r].clone());
    }
    for (k, (terms, lo, hi)) in extra_rows.iter().enumerate() {
        add_scaled_row(
            &mut model,
            &handles,
            terms,
            lo.as_ref(),
            hi.as_ref(),
            "bound",
        )?;
        kept_names.push(format!("__bound{k}"));
    }

    // ---- objective ----
    //
    // Scaling the objective by a positive constant leaves the argmin alone and multiplies the
    // value, which the caller undoes exactly via `obj_scale`.
    let obj_scale = integralising_scale(obj_coeff.iter().chain(std::iter::once(obj_offset)));
    // The objective is renormalised by a power of two as well, for the same reason as the rows:
    // gen's came out at 2e9, which made the dual tolerance 2.0 and stopped any column from ever
    // pricing in.
    //
    // This is only safe because the search prunes on the objective's GRANULARITY rather than on
    // its integrality (see `objective_granularity`). Halving an objective's coefficients does not
    // weaken the "a bound of 156.2 cannot hold better than 157" argument -- it just makes the step
    // 1/2 instead of 1 -- but a search that asks "are these whole numbers?" throws the prune away
    // entirely, and on gt2 that was the difference between a proof in 0.1s and 574,358 nodes with
    // no proof at all.
    let obj_scale = &obj_scale
        * pow2_normaliser(
            obj_coeff.iter().chain(std::iter::once(obj_offset)),
            &obj_scale,
        );
    // Scale each objective coefficient EXACTLY; hand the float lane the `f64`
    // and record the true rational whenever the `f64` is only a rounded proxy.
    let mut obj: Vec<(Col, f64)> = Vec::new();
    let mut inexact_obj: Vec<(u32, BigRational)> = Vec::new();
    for (&h, a) in handles.iter().zip(obj_coeff.iter()) {
        let sv = a * &obj_scale;
        if sv.is_zero() {
            continue;
        }
        let f = to_f64(&sv);
        if !f.is_finite() || f == 0.0 {
            return Err(err(
                0,
                "an objective coefficient has no finite nonzero f64 representation",
            ));
        }
        obj.push((h, f));
        if !exactly_f64(&sv) {
            inexact_obj.push((h.0, sv));
        }
    }
    model.set_objective(&obj, sense);
    for (c, sv) in inexact_obj {
        model.record_inexact_obj_coeff(c, sv);
    }
    let offset_exact = obj_offset * &obj_scale;
    let offset_f = to_f64(&offset_exact);
    if !offset_f.is_finite() {
        return Err(err(
            0,
            "the objective offset has no finite f64 representation",
        ));
    }
    model.set_objective_offset(offset_f);
    if !exactly_f64(&offset_exact) {
        model.record_inexact_obj_offset(offset_exact);
    }

    Ok(MpsProblem {
        model,
        name,
        col_names,
        row_names: kept_names,
        obj_scale,
    })
}

/// Add one row, multiplied through by whatever makes its numbers exact.
///
/// The whole-row scale (LCM of denominators, then a magnitude-normalising power
/// of two) is applied EXACTLY, and the scaled coefficients/bounds are the row's
/// true rationals. Every one an `f64` can hold is handed to the float lane
/// verbatim, exactly as before. The ones it CANNOT hold (the LCM overflowed
/// `f64`'s exact integer range) are stored as a ROUNDED `f64` for the float lane
/// AND recorded, per-coefficient, in the model's exact-rational side-store — so
/// the exact rim, the point-check and the certificate verifier still reason
/// about the row the file actually wrote. This is per-coefficient: an `f64`-exact
/// entry in an otherwise-inexact row keeps the fast path.
fn add_scaled_row(
    model: &mut Model,
    handles: &[Col],
    terms: &[(usize, BigRational)],
    lo: Option<&BigRational>,
    hi: Option<&BigRational>,
    _name: &str,
) -> Result<(), MpsError> {
    let scale = integralising_scale(terms.iter().map(|(_, v)| v).chain(lo).chain(hi));
    // ...then bring the magnitude back down, by a POWER OF TWO.
    //
    // Clearing the denominators can leave a row enormous -- `qnet1` came out with coefficients of
    // 2.5e9 -- and the simplex sizes its tolerances off the largest number it can see. A dual
    // tolerance of `1e-9 * 2e9` is 2.0, which means no column ever prices in and a feasible LP is
    // declared infeasible on its first iteration. That is what happened to `gen`.
    //
    // Dividing by a power of two is EXACT in binary floating point, so the row stays exactly
    // representable -- which is the entire reason the scaling was done. Any positive factor
    // preserves the row's feasible set, so this is free.
    let scale = &scale * pow2_normaliser(terms.iter().map(|(_, v)| v).chain(lo).chain(hi), &scale);
    // MPS is column-major, so the ordinary reader path has already assembled
    // each row in strictly increasing column order. Preserve that canonical
    // representation directly. Non-contiguous repeated column records are
    // legal, though, so retain exact BTreeMap consolidation as the fail-safe
    // fallback rather than assuming generator behavior for correctness.
    let ordered_unique = terms
        .windows(2)
        .all(|pair| handles[pair[0].0].0 < handles[pair[1].0].0);
    let exact_by_col: Vec<(u32, BigRational)> = if ordered_unique {
        terms
            .iter()
            .filter_map(|(column, value)| {
                if value.is_zero() {
                    None
                } else {
                    Some((handles[*column].0, value * &scale))
                }
            })
            .collect()
    } else {
        let mut merged: std::collections::BTreeMap<u32, BigRational> =
            std::collections::BTreeMap::new();
        for (column, value) in terms {
            if value.is_zero() {
                continue;
            }
            let entry = merged
                .entry(handles[*column].0)
                .or_insert_with(BigRational::zero);
            *entry += value * &scale;
        }
        merged
            .into_iter()
            .filter(|(_, value)| !value.is_zero())
            .collect()
    };
    let mut coeffs: Vec<(u32, f64)> = Vec::with_capacity(exact_by_col.len());
    for &(c, ref sv) in &exact_by_col {
        let f = to_f64(sv);
        // Refuse ONLY what has no usable `f64` at all: a non-finite proxy, or a
        // nonzero true coefficient that would round to 0.0 (its term would
        // silently vanish). Neither can be represented even as advice.
        if !f.is_finite() || f == 0.0 {
            return Err(err(
                0,
                "a row coefficient has no finite nonzero f64 representation",
            ));
        }
        coeffs.push((c, f));
    }
    let lo_exact = lo.map(|v| v * &scale);
    let hi_exact = hi.map(|v| v * &scale);
    let lo_f = match &lo_exact {
        Some(v) => {
            let f = to_f64(v);
            if !f.is_finite() {
                return Err(err(0, "a row bound has no finite f64 representation"));
            }
            f
        }
        None => f64::NEG_INFINITY,
    };
    let hi_f = match &hi_exact {
        Some(v) => {
            let f = to_f64(v);
            if !f.is_finite() {
                return Err(err(0, "a row bound has no finite f64 representation"));
            }
            f
        }
        None => f64::INFINITY,
    };
    // `exact_by_col` is now sorted, unique and nonzero. Consume the prepared
    // float row rather than asking `Model::add_row` to copy/sort/dedup it a
    // second time.
    let row = model.add_row_sorted_unique(lo_f, hi_f, coeffs);
    // Record the TRUE rational wherever the `f64` is only a rounded proxy.
    for &(c, ref sv) in &exact_by_col {
        if !exactly_f64(sv) {
            model.record_inexact_row_coeff(row, c, sv.clone());
        }
    }
    if let Some(v) = &lo_exact {
        if !exactly_f64(v) {
            model.record_inexact_row_bound(row, true, v.clone());
        }
    }
    if let Some(v) = &hi_exact {
        if !exactly_f64(v) {
            model.record_inexact_row_bound(row, false, v.clone());
        }
    }
    Ok(())
}

/// A power of two that brings `vals * scale` into a sane magnitude.
///
/// Returns `2^-k` (or `2^k`), so multiplying the scale by it moves the row's largest entry toward
/// `TARGET` without disturbing a single bit: a power of two divides exactly in binary floating
/// point, so an exactly-representable row stays exactly representable.
fn pow2_normaliser<'a, I: Iterator<Item = &'a BigRational>>(
    vals: I,
    scale: &BigRational,
) -> BigRational {
    /// The magnitude a row's largest entry is aimed at.
    const TARGET: f64 = 1024.0;
    let mut biggest = 0.0f64;
    for v in vals {
        if v.is_zero() {
            continue;
        }
        let m = (v * scale).to_f64().unwrap_or(0.0).abs();
        if m > biggest {
            biggest = m;
        }
    }
    // DOWN ONLY. A row that is already a sane size is left exactly as it was -- there is nothing
    // to gain from inflating a small one, and every needless change to a coefficient is a change
    // to what the float lane sees.
    if biggest <= TARGET || !biggest.is_finite() {
        return BigRational::one();
    }
    let k = (biggest / TARGET).log2().ceil() as u32;
    let two = BigRational::from_integer(BigInt::from(2u8));
    let mut f = BigRational::one();
    for _ in 0..k {
        f /= &two;
    }
    f
}

/// The smallest positive rational that turns every one of `vals` into an integer.
///
/// That is the LCM of their denominators. Multiplying a row by it cannot move the row's feasible
/// set, and it leaves numbers an `f64` can hold without rounding — which is the whole point.
fn integralising_scale<'a, I: Iterator<Item = &'a BigRational>>(vals: I) -> BigRational {
    let mut l = BigInt::one();
    for v in vals {
        if v.is_zero() {
            continue;
        }
        let denominator = v.denom();
        // Exact f64s are dyadic, so parser-produced neural/network rows are
        // overwhelmingly powers of two in the denominator. Their LCM is just
        // the larger power: avoid running a BigInt GCD for every matrix term.
        // The moment either operand is not a power of two, retain the general
        // integer LCM path with identical mathematical semantics.
        match (
            power_of_two_exponent(&l),
            power_of_two_exponent(denominator),
        ) {
            (Some(current), Some(candidate)) if candidate > current => {
                l.clone_from(denominator);
            }
            (Some(_), Some(_)) => {}
            _ => l = l.lcm(denominator),
        }
    }
    BigRational::from_integer(l)
}

fn power_of_two_exponent(value: &BigInt) -> Option<u64> {
    let trailing = value.trailing_zeros()?;
    (value.bits() == trailing + 1).then_some(trailing)
}

/// Is `v` exactly an `f64`?
fn exactly_f64(v: &BigRational) -> bool {
    v.to_f64()
        .and_then(BigRational::from_float)
        .is_some_and(|back| back == *v)
}

fn to_f64(v: &BigRational) -> f64 {
    v.to_f64().unwrap_or(f64::NAN)
}

fn err(line: usize, message: &str) -> MpsError {
    MpsError {
        line,
        message: message.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole reason this reader does arithmetic: nine tenths is not a double.
    #[test]
    fn a_decimal_coefficient_is_read_as_the_rational_it_denotes() {
        let exact =
            ay_lp::parse_mps_exact("NAME t\nROWS\n N obj\nCOLUMNS\n    x obj 0.9\nENDATA\n")
                .expect("reads");
        let v = &exact.columns[0].objective;
        assert_eq!(*v, BigRational::new(9.into(), 10.into()));
        // ... and NOT the f64 nearest it, which is what `"0.9".parse::<f64>()` would have given.
        assert_ne!(*v, BigRational::from_float(0.9_f64).expect("finite"));
    }

    #[test]
    fn integralising_scale_handles_dyadic_and_general_denominators() {
        let dyadic = [
            BigRational::new(1.into(), 8.into()),
            BigRational::new(3.into(), 32.into()),
            BigRational::from_integer(7.into()),
        ];
        assert_eq!(
            integralising_scale(dyadic.iter()),
            BigRational::from_integer(32.into())
        );

        let general = [
            BigRational::new(1.into(), 6.into()),
            BigRational::new(1.into(), 10.into()),
            BigRational::new(1.into(), 7.into()),
        ];
        assert_eq!(
            integralising_scale(general.iter()),
            BigRational::from_integer(210.into())
        );
    }

    /// A row with a `0.9` in it must come out with coefficients an f64 holds exactly, and the
    /// SAME feasible set: scaling by 10 turns `0.9x - y = 0` into `9x - 10y = 0`.
    #[test]
    fn a_row_is_scaled_until_its_coefficients_are_exact() {
        let src = "\
NAME          t
ROWS
 N  obj
 E  r1
COLUMNS
    x         obj              1.0   r1                 0.9
    y         obj              1.0   r1                  -1
RHS
    R         r1                 0
BOUNDS
 UP B         x                 10
 UP B         y                 10
ENDATA
";
        let p = read_mps(src).expect("reads");
        let (coeffs, lb, ub) = p.model.row(p.model.row_at(0).expect("a row"));
        assert_eq!(lb, 0.0);
        assert_eq!(ub, 0.0);
        // 0.9 and -1, scaled by 10.
        assert_eq!(coeffs, &[(0, 9.0), (1, -10.0)]);
        // And every coefficient survives the round trip through the exact rim.
        for &(_, a) in coeffs {
            assert_eq!(
                BigRational::from_float(a).expect("finite"),
                BigRational::from_integer((a as i64).into())
            );
        }
    }

    /// Repeated entries of one (column, row) are summed; a column whose
    /// records are split by another column's is refused (the checker reads
    /// it as two columns), with its line.
    #[test]
    fn repeated_column_records_sum_and_split_ones_are_refused() {
        let summed = "\
NAME          repeats
ROWS
 N  obj
 E  r1
COLUMNS
    x         r1                 1
    x         r1                 2
    y         r1                 4
RHS
    R         r1                 7
ENDATA
";
        let problem = read_mps(summed).expect("reads repeated entries");
        let (coefficients, lower, upper) = problem
            .model
            .row(problem.model.row_at(0).expect("constraint row"));
        assert_eq!(coefficients, &[(0, 3.0), (1, 4.0)]);
        assert_eq!((lower, upper), (7.0, 7.0));
        let split = summed.replace(
            "    x         r1                 2\n    y         r1                 4\n",
            "    y         r1                 4\n    x         r1                 2\n",
        );
        assert_eq!(read_mps(&split).expect_err("split records").line, 8);
    }

    /// AY-N12: `read_mps` reads every file as `ay lp solve` does. Before, it
    /// was a second reader: it took lower-case markers, kept the last of two
    /// objective entries, gave an `UP` below 0 on a column with lower bound
    /// 0 a lower bound of -inf, and gave a marker integer column without
    /// bounds `[0, +inf)`. The first three are refused by the one reader
    /// (readers in common use differ); the last is the checker's `[0, 1]`.
    #[test]
    fn read_mps_reads_as_the_one_reader_does() {
        let refused = [
            "NAME L\nROWS\n N OBJ\n L C1\nCOLUMNS\n    M 'MARKER' 'intorg'\n    X OBJ -1 C1 2\n    M 'MARKER' 'intend'\nRHS\n    RHS C1 3\nENDATA\n",
            "NAME D\nROWS\n N OBJ\n L C1\nCOLUMNS\n    X OBJ -3 C1 1\n    X OBJ 2\nRHS\n    RHS C1 10\nENDATA\n",
            "NAME U\nROWS\n N OBJ\n L C1\nCOLUMNS\n    X OBJ 1 C1 1\nRHS\n    RHS C1 10\nBOUNDS\n UP BND X -1\nENDATA\n",
        ];
        for text in refused {
            let e = read_mps(text).expect_err("refused");
            assert!(e.line > 0, "{e}");
            assert!(ay_lp::parse_mps_exact(text).is_err());
        }
        let marker = "NAME B\nROWS\n N OBJ\n L C1\nCOLUMNS\n    M 'MARKER' 'INTORG'\n    X OBJ 1 C1 1\n    M 'MARKER' 'INTEND'\nRHS\n    RHS C1 5\nENDATA\n";
        let problem = read_mps(marker).expect("reads");
        let x = problem.model.col_at(0).expect("x");
        assert_eq!(problem.model.col_bounds(x), (0.0, 1.0));
        assert!(problem.model.col_kind(x).is_integral());
    }

    #[test]
    fn non_finite_objective_offset_is_rejected_without_panicking() {
        let src = "\
NAME          huge-offset
ROWS
 N  obj
COLUMNS
    x         obj                 1
RHS
    R         obj            -1e400
BOUNDS
 FX B         x                   0
ENDATA
";
        let e = read_mps(src).expect_err("offset has no finite advice representation");
        assert_eq!(e.line, 7, "{e:?}");
    }
}
