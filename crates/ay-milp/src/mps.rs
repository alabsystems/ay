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
//! Both the fixed-column and free-form layouts are accepted, because the difference between them
//! only matters for names with embedded spaces, which no benchmark uses. What is deliberately NOT
//! accepted, rather than guessed at: semi-continuous columns, SOS sets, and quadratic sections.
//! Each would need real modelling support, and reading one as though it were an ordinary column
//! would answer a question about a model the caller did not pose.

use std::collections::HashMap;
use std::fmt;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use smallvec::SmallVec;

use crate::model::{exact, Col, Model, Sense};

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

/// The row types MPS distinguishes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RowType {
    /// `N` — no constraint. The first one is the objective; any others are free rows.
    Free,
    /// `L` — `a·x <= rhs`.
    Le,
    /// `G` — `a·x >= rhs`.
    Ge,
    /// `E` — `a·x == rhs`.
    Eq,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Section {
    None,
    Rows,
    Columns,
    Rhs,
    Ranges,
    Bounds,
    ObjSense,
}

/// A column under construction: MPS gives its coefficients before its bounds.
#[derive(Clone)]
struct ColBuild {
    lb: Option<BigRational>, // None = infinite on that side
    ub: Option<BigRational>,
    integral: bool,
    /// Whether a `BOUNDS` entry has touched the lower bound. The `UP`-with-a-negative-value rule
    /// keys off exactly this.
    lb_set: bool,
}

/// Parse `text` as MPS.
///
/// # Errors
/// Returns [`MpsError`] on a malformed file, an unknown section, a reference to an undeclared row
/// or column, a construct this reader refuses to guess at (see the module docs), or a row whose
/// coefficients cannot be made exactly representable without exceeding `f64`'s integer range.
#[allow(clippy::too_many_lines)]
pub fn read_mps(text: &str) -> Result<MpsProblem, MpsError> {
    let mut name = String::new();
    let mut sense = Sense::Minimize;
    let mut section = Section::None;

    let mut row_type: Vec<RowType> = Vec::new();
    let mut row_names: Vec<String> = Vec::new();
    let mut row_of: HashMap<String, usize> = HashMap::new();
    let mut obj_row: Option<usize> = None;

    let mut col_names: Vec<String> = Vec::new();
    let mut col_of: HashMap<String, usize> = HashMap::new();
    let mut cols: Vec<ColBuild> = Vec::new();
    let mut obj_coeff: Vec<BigRational> = Vec::new();
    // (row, col, value) triples for the constraint rows.
    let mut nz: Vec<(usize, usize, BigRational)> = Vec::new();

    let mut rhs: Vec<BigRational> = Vec::new();
    let mut ranges: Vec<Option<BigRational>> = Vec::new();
    let mut obj_offset = BigRational::zero();
    let mut integral_now = false;
    // Generator-produced MPS files commonly repeat a very small coefficient
    // vocabulary thousands of times.  In particular, exact decimal expansions
    // of dyadic f64 values are expensive enough to parse that reconstructing the
    // same rational for every nonzero dominates small-model process wall.  Cache
    // only successful parses; callers still receive an owned value, and the
    // mathematical result is exactly `number(text, line)`.
    let mut number_cache: HashMap<&str, BigRational> = HashMap::new();

    for (i, raw) in text.lines().enumerate() {
        let line = i + 1;
        // A `*` in column 1 is a comment; a blank line is nothing.
        if raw.starts_with('*') || raw.trim().is_empty() {
            continue;
        }
        let indented = raw.starts_with([' ', '\t']);
        // Free-form MPS data lines normally contain at most two (name, value)
        // pairs. Keep those fields inline instead of allocating once per line;
        // SmallVec still preserves the reader's existing acceptance of longer
        // extension lines by spilling only those exceptional records.
        let f: SmallVec<[&str; 6]> = raw.split_whitespace().collect();
        if f.is_empty() {
            continue;
        }

        // An unindented line starts a section (MPS's only structural marker).
        if !indented {
            match f[0].to_ascii_uppercase().as_str() {
                "NAME" => {
                    name = (*f.get(1).unwrap_or(&"")).to_string();
                    section = Section::None;
                }
                "OBJSENSE" => {
                    // Either `OBJSENSE MAX` on one line, or the word on the next.
                    if let Some(w) = f.get(1) {
                        sense = parse_sense(w, line)?;
                        section = Section::None;
                    } else {
                        section = Section::ObjSense;
                    }
                }
                "ROWS" => section = Section::Rows,
                "COLUMNS" => section = Section::Columns,
                "RHS" => section = Section::Rhs,
                "RANGES" => section = Section::Ranges,
                "BOUNDS" => section = Section::Bounds,
                "ENDATA" => break,
                other => {
                    return Err(err(
                        line,
                        &format!(
                            "unsupported section `{other}` -- this reader will not guess at what \
                             it means"
                        ),
                    ))
                }
            }
            continue;
        }

        match section {
            Section::None => {}
            Section::ObjSense => {
                sense = parse_sense(f[0], line)?;
                section = Section::None;
            }
            Section::Rows => {
                let nm = *f.get(1).ok_or_else(|| err(line, "a row needs a name"))?;
                let ty = match f[0].to_ascii_uppercase().as_str() {
                    "N" => RowType::Free,
                    "L" => RowType::Le,
                    "G" => RowType::Ge,
                    "E" => RowType::Eq,
                    o => return Err(err(line, &format!("unknown row type `{o}`"))),
                };
                if ty == RowType::Free && obj_row.is_none() {
                    obj_row = Some(row_type.len());
                }
                row_of.insert(nm.to_string(), row_type.len());
                row_names.push(nm.to_string());
                row_type.push(ty);
                rhs.push(BigRational::zero());
                ranges.push(None);
            }
            Section::Columns => {
                // `MARKER` lines carry no data; they toggle integrality for what follows.
                if f.iter().any(|t| t.eq_ignore_ascii_case("'MARKER'")) {
                    if f.iter().any(|t| t.eq_ignore_ascii_case("'INTORG'")) {
                        integral_now = true;
                    } else if f.iter().any(|t| t.eq_ignore_ascii_case("'INTEND'")) {
                        integral_now = false;
                    }
                    continue;
                }
                let cname = f[0];
                let c = if let Some(&existing) = col_of.get(cname) {
                    existing
                } else {
                    let index = cols.len();
                    let owned_name = cname.to_owned();
                    col_of.insert(owned_name.clone(), index);
                    col_names.push(owned_name);
                    obj_coeff.push(BigRational::zero());
                    cols.push(ColBuild {
                        lb: Some(BigRational::zero()),
                        ub: None,
                        integral: integral_now,
                        lb_set: false,
                    });
                    index
                };
                // Two (row, value) pairs per line is the norm, not the exception.
                for pair in f[1..].chunks(2) {
                    let [rname, v] = pair else {
                        return Err(err(line, "a COLUMNS entry needs a row and a value"));
                    };
                    let r = *row_of
                        .get(*rname)
                        .ok_or_else(|| err(line, &format!("no row named `{rname}`")))?;
                    let v = cached_number(&mut number_cache, v, line)?;
                    if Some(r) == obj_row {
                        obj_coeff[c] = v;
                    } else if row_type[r] != RowType::Free {
                        nz.push((r, c, v));
                    }
                }
            }
            Section::Rhs => {
                for (rname, v) in pairs(&f) {
                    let r = *row_of
                        .get(rname)
                        .ok_or_else(|| err(line, &format!("no row named `{rname}`")))?;
                    let v = cached_number(&mut number_cache, v, line)?;
                    if Some(r) == obj_row {
                        // An RHS on the objective row is the NEGATIVE of the objective constant.
                        obj_offset = -v;
                    } else {
                        rhs[r] = v;
                    }
                }
            }
            Section::Ranges => {
                for (rname, v) in pairs(&f) {
                    let r = *row_of
                        .get(rname)
                        .ok_or_else(|| err(line, &format!("no row named `{rname}`")))?;
                    ranges[r] = Some(cached_number(&mut number_cache, v, line)?);
                }
            }
            Section::Bounds => {
                let ty = f[0].to_ascii_uppercase();
                // `FR`/`MI`/`PL`/`BV` take no value, so the column may be the 2nd or 3rd field.
                let (cname, val) = match f.len() {
                    0 | 1 => return Err(err(line, "a BOUNDS entry needs a column")),
                    2 => (f[1], None),
                    3 => {
                        // Either `TY set col` or `TY col value` -- tell them apart by asking
                        // whether the last field names a column we have seen.
                        if col_of.contains_key(f[2]) {
                            (f[2], None)
                        } else {
                            (f[1], Some(f[2]))
                        }
                    }
                    _ => (f[2], Some(f[3])),
                };
                let c = *col_of
                    .get(cname)
                    .ok_or_else(|| err(line, &format!("no column named `{cname}`")))?;
                let mut value = || -> Result<BigRational, MpsError> {
                    let v = val.ok_or_else(|| err(line, &format!("bound `{ty}` needs a value")))?;
                    cached_number(&mut number_cache, v, line)
                };
                match ty.as_str() {
                    "UP" | "UI" => {
                        let v = value()?;
                        // The format's ugliest corner: `UP` with a negative value on a column
                        // whose lower bound is still the default 0 means the modeller wanted a
                        // negative column, and 0 was never its intended floor. Every solver reads
                        // it this way; reading it literally yields an empty box.
                        if v.is_negative() && !cols[c].lb_set {
                            cols[c].lb = None;
                        }
                        cols[c].ub = Some(v);
                        cols[c].integral |= ty == "UI";
                    }
                    "LO" | "LI" => {
                        cols[c].lb = Some(value()?);
                        cols[c].lb_set = true;
                        cols[c].integral |= ty == "LI";
                    }
                    "FX" => {
                        let v = value()?;
                        cols[c].lb = Some(v.clone());
                        cols[c].ub = Some(v);
                        cols[c].lb_set = true;
                    }
                    "FR" => {
                        cols[c].lb = None;
                        cols[c].ub = None;
                        cols[c].lb_set = true;
                    }
                    "MI" => {
                        cols[c].lb = None;
                        cols[c].lb_set = true;
                    }
                    "PL" => cols[c].ub = None,
                    "BV" => {
                        cols[c].lb = Some(BigRational::zero());
                        cols[c].ub = Some(BigRational::one());
                        cols[c].lb_set = true;
                        cols[c].integral = true;
                    }
                    o => {
                        return Err(err(
                            line,
                            &format!(
                                "bound type `{o}` is not supported -- it would have to be \
                                 modelled, not approximated"
                            ),
                        ))
                    }
                }
            }
        }
    }

    build(
        name,
        sense,
        &row_type,
        &row_names,
        obj_row,
        col_names,
        cols,
        &obj_coeff,
        nz,
        &rhs,
        &ranges,
        &obj_offset,
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
    row_type: &[RowType],
    row_names: &[String],
    _obj_row: Option<usize>,
    col_names: Vec<String>,
    cols: Vec<ColBuild>,
    obj_coeff: &[BigRational],
    nz: Vec<(usize, usize, BigRational)>,
    rhs: &[BigRational],
    ranges: &[Option<BigRational>],
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
    let mut by_row: Vec<Vec<(usize, BigRational)>> = vec![Vec::new(); row_type.len()];
    for (r, c, v) in nz {
        by_row[r].push((c, v));
    }
    let mut kept_names = Vec::new();
    for (r, ty) in row_type.iter().enumerate() {
        let (lo, hi) = match ty {
            RowType::Free => continue, // the objective, or a row that constrains nothing
            RowType::Le => (None, Some(rhs[r].clone())),
            RowType::Ge => (Some(rhs[r].clone()), None),
            RowType::Eq => (Some(rhs[r].clone()), Some(rhs[r].clone())),
        };
        // RANGES turns a one-sided row into a two-sided one. The sign convention for `E` rows is
        // the format's, not mine: a positive range extends upward, a negative one downward.
        let (lo, hi) = match (&ranges[r], ty) {
            (None, _) => (lo, hi),
            (Some(g), RowType::Le) => (Some(&rhs[r] - g.abs()), hi),
            (Some(g), RowType::Ge) => (lo, Some(&rhs[r] + g.abs())),
            (Some(g), RowType::Eq) => {
                if g.is_negative() {
                    (Some(&rhs[r] + g), Some(rhs[r].clone()))
                } else {
                    (Some(rhs[r].clone()), Some(&rhs[r] + g))
                }
            }
            (Some(_), RowType::Free) => unreachable!("free rows are skipped above"),
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

/// Split a data line into (name, value) pairs, tolerating a leading set name.
///
/// `RHS`/`RANGES` lines carry an optional set name that nothing else references, so the field
/// count is the only thing that says whether it is there. An odd count means it is.
fn pairs<'text, 'slice>(
    f: &'slice [&'text str],
) -> impl Iterator<Item = (&'text str, &'text str)> + 'slice
where
    'text: 'slice,
{
    let body = if f.len().is_multiple_of(2) {
        f
    } else {
        &f[1..]
    };
    body.chunks(2).filter_map(|c| match c {
        [a, b] => Some((*a, *b)),
        _ => None,
    })
}

fn parse_sense(w: &str, line: usize) -> Result<Sense, MpsError> {
    match w.to_ascii_uppercase().as_str() {
        "MAX" | "MAXIMIZE" => Ok(Sense::Maximize),
        "MIN" | "MINIMIZE" => Ok(Sense::Minimize),
        o => Err(err(line, &format!("unknown objective sense `{o}`"))),
    }
}

/// Parse a number from its DECIMAL TEXT into the exact rational it denotes.
///
/// `"0.9"` is nine tenths. It is not `0.90000000000000002220446…`, which is what it becomes the
/// moment it passes through an `f64`, and the difference is the difference between solving the
/// file's model and solving a nearby one. See the module docs.
fn number(s: &str, line: usize) -> Result<BigRational, MpsError> {
    let t = s.trim();
    let bad = || err(line, &format!("`{s}` is not a number"));

    // MPS matrices are overwhelmingly integral after generator-side scaling.
    // Avoid building 10^0 and asking BigRational to run a GCD for that common
    // case. This is only a representation fast path: the returned integer is
    // exactly the same mathematical value as the general decimal parser.
    if !t
        .as_bytes()
        .iter()
        .any(|&byte| matches!(byte, b'.' | b'e' | b'E'))
    {
        let (digits, negative) = match t.strip_prefix('-') {
            Some(rest) => (rest, true),
            None => (t.strip_prefix('+').unwrap_or(t), false),
        };
        if !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()) {
            let magnitude: BigInt = digits.parse().map_err(|_| bad())?;
            return Ok(BigRational::from_integer(if negative {
                -magnitude
            } else {
                magnitude
            }));
        }
    }

    // Split off an exponent, then read the mantissa as a plain decimal.
    let (mant, exp) = match t.find(['e', 'E']) {
        Some(i) => {
            let e: i32 = t[i + 1..].parse().map_err(|_| bad())?;
            (&t[..i], e)
        }
        None => (t, 0),
    };
    let (mant, neg) = match mant.strip_prefix('-') {
        Some(r) => (r, true),
        None => (mant.strip_prefix('+').unwrap_or(mant), false),
    };
    let (int_part, frac_part) = match mant.find('.') {
        Some(i) => (&mant[..i], &mant[i + 1..]),
        None => (mant, ""),
    };
    if int_part.is_empty() && frac_part.is_empty() {
        return Err(bad());
    }
    let digits = format!("{int_part}{frac_part}");
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err(bad());
    }
    let magnitude: BigInt = digits.parse().map_err(|_| bad())?;
    let mut numer = if neg { -magnitude } else { magnitude };
    let decimal_power = i64::try_from(frac_part.len())
        .map_err(|_| bad())?
        .checked_sub(i64::from(exp))
        .ok_or_else(bad)?;
    let ten = BigInt::from(10u8);
    let denom = if decimal_power >= 0 {
        ten.pow(u32::try_from(decimal_power).map_err(|_| bad())?)
    } else {
        numer *= ten.pow(u32::try_from(-decimal_power).map_err(|_| bad())?);
        BigInt::one()
    };

    // Many generated MPS files print the complete decimal expansion of an
    // f64 dyadic. Recognize that case by exact cross multiplication and reuse
    // the already-reduced dyadic representation. A value such as 0.9 fails
    // this equality and takes the general decimal-rational path below.
    if let Ok(float) = t.parse::<f64>() {
        if let Some(candidate) = exact(float) {
            if &numer * candidate.denom() == candidate.numer() * &denom {
                return Ok(candidate);
            }
        }
    }

    Ok(BigRational::new(numer, denom))
}

fn cached_number<'a>(
    cache: &mut HashMap<&'a str, BigRational>,
    text: &'a str,
    line: usize,
) -> Result<BigRational, MpsError> {
    if let Some(value) = cache.get(text) {
        return Ok(value.clone());
    }
    let value = number(text, line)?;
    cache.insert(text, value.clone());
    Ok(value)
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
        let v = number("0.9", 1).expect("parses");
        assert_eq!(v, BigRational::new(9.into(), 10.into()));
        // ... and NOT the f64 nearest it, which is what `"0.9".parse::<f64>()` would have given.
        assert_ne!(v, BigRational::from_float(0.9_f64).expect("finite"));
    }

    #[test]
    fn scientific_and_signed_forms_parse() {
        assert_eq!(
            number("-1.5e-3", 1).expect("parses"),
            BigRational::new((-15).into(), 10_000.into())
        );
        assert_eq!(
            number("1e6", 1).expect("parses"),
            BigRational::from_integer(1_000_000.into())
        );
        assert_eq!(
            number("+60", 1).expect("parses"),
            BigRational::from_integer(60.into())
        );
    }

    #[test]
    fn complete_f64_decimal_expansions_reuse_the_exact_dyadic_value() {
        for encoded in [
            "1.00001013278961181640625",
            "0.0000000000000000000000000000000000000000001205116679319342680994407441629327872901025270013803563711078724145220331109840117278508841991424560546875",
        ] {
            let parsed = number(encoded, 1).expect("complete decimal expansion parses");
            let float: f64 = encoded.parse().expect("finite f64");
            assert_eq!(parsed, exact(float).expect("exact dyadic"));
        }
    }

    #[test]
    fn repeated_numbers_share_one_exact_parse_cache_entry() {
        let mut cache = HashMap::new();
        let encoded = "1.00001013278961181640625";
        let first = cached_number(&mut cache, encoded, 1).expect("first parse");
        let second = cached_number(&mut cache, encoded, 2).expect("cached parse");
        assert_eq!(first, second);
        assert_eq!(cache.len(), 1);

        // Invalid text must not poison a later line's diagnostic or the cache.
        assert_eq!(
            cached_number(&mut cache, "not-a-number", 17)
                .unwrap_err()
                .line,
            17
        );
        assert_eq!(cache.len(), 1);
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

    /// Although ordinary column-major MPS input yields already ordered rows,
    /// a repeated non-contiguous column record must still consolidate exactly.
    /// This pins the fallback behind the parser's prepared-row fast path.
    #[test]
    fn noncontiguous_column_records_still_sum_exactly() {
        let src = "\
NAME          repeats
ROWS
 N  obj
 E  r1
COLUMNS
    x         r1                 1
    y         r1                 4
    x         r1                 2
RHS
    R         r1                 7
ENDATA
";
        let problem = read_mps(src).expect("reads repeated columns");
        let (coefficients, lower, upper) = problem
            .model
            .row(problem.model.row_at(0).expect("constraint row"));
        assert_eq!(coefficients, &[(0, 3.0), (1, 4.0)]);
        assert_eq!((lower, upper), (7.0, 7.0));
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
        assert!(e.message.contains("objective offset"), "{e:?}");
    }
}
