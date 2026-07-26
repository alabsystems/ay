// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The solver-neutral MILP/LP model: columns, rows, bounds, objective.
//!
//! Bounds and coefficients use `f64`, and column indices remain stable in
//! insertion order. Exactness is the solver's internal concern: every finite
//! `f64` is converted to the exact rational it denotes (a dyadic), so nothing
//! is lost at this boundary.

use std::collections::HashMap;

use num_rational::BigRational;
use num_traits::Zero;

use crate::error::ModelError;

/// Exact-rational overrides for one row whose stored `f64` coefficients or
/// bounds are ROUNDED proxies for a true rational the `f64` cannot hold (see
/// [`Model::has_inexact_coeffs`]). Only the non-`f64`-exact entries are stored;
/// everything else stays on the fast `exact(f64)` path. Empty for every
/// all-`f64`-exact model.
#[derive(Debug, Clone, Default)]
pub(crate) struct ExactRow {
    /// Column index -> the TRUE rational coefficient (only for coeffs whose
    /// stored `f64` differs from the true value).
    pub(crate) coeffs: HashMap<u32, BigRational>,
    /// The TRUE lower bound, when the stored `f64` lb is a rounded proxy.
    pub(crate) lb: Option<BigRational>,
    /// The TRUE upper bound, when the stored `f64` ub is a rounded proxy.
    pub(crate) ub: Option<BigRational>,
}

/// A column (variable) handle. Index-stable: the `n`-th `add_col` returns
/// `Col` with index `n`, and `Outcome` model-value vectors are indexed the
/// same way.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Col(pub(crate) u32);

impl Col {
    /// The column's insertion-order index.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A row (constraint) handle. Index-stable like [`Col`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Row(pub(crate) u32);

impl Row {
    /// The row's insertion-order index.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Objective direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Sense {
    /// Minimize the objective.
    #[default]
    Minimize,
    /// Maximize the objective.
    Maximize,
}

/// Column integrality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum ColKind {
    /// A continuous (Real) column.
    #[default]
    Continuous,
    /// A 0/1 column. Bounds are always `[0, 1]` (possibly tightened by
    /// `fix_col`-style bound shrinking on the consumer side).
    Binary,
    /// A general integer column: any integer within `[lb, ub]`, which may be
    /// unbounded on either side.
    ///
    /// [`Binary`](ColKind::Binary) is not merely the `[0, 1]` case of this — it
    /// licenses the 0/1-specific machinery (cover cuts, the flip-and-swap local
    /// search) that a general integer column must be kept out of.
    Integer,
}

impl ColKind {
    /// Does this column have to take an integer value?
    #[must_use]
    pub fn is_integral(self) -> bool {
        matches!(self, Self::Binary | Self::Integer)
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ColSpec {
    pub(crate) lb: f64,
    pub(crate) ub: f64,
    pub(crate) obj: f64,
    pub(crate) kind: ColKind,
}

#[derive(Debug, Clone)]
pub(crate) struct RowSpec {
    pub(crate) lb: f64,
    pub(crate) ub: f64,
    /// Sorted by column index; no duplicates; no explicit zeros.
    pub(crate) coeffs: Vec<(u32, f64)>,
}

/// A MILP/LP model: bounded columns, range rows `lb <= a·x <= ub`, and an
/// optional linear objective.
///
/// One-sided rows and free columns use `±f64::INFINITY`; an equality row has
/// `lb == ub`. `Model` is plain data (`Send + Sync + Clone`) — sessions
/// ([`crate::LpSession`], [`crate::BabSession`]) hold the solver state.
#[derive(Debug, Clone, Default)]
pub struct Model {
    pub(crate) cols: Vec<ColSpec>,
    pub(crate) rows: Vec<RowSpec>,
    pub(crate) sense: Sense,
    pub(crate) obj_offset: f64,
    /// Whether an objective was ever set. An all-zero objective is a genuine
    /// optimization problem (optimum = the offset, attained at any feasible
    /// point), not the absence of one — so this cannot be recovered from the
    /// coefficients, which default to zero.
    pub(crate) has_objective: bool,
    /// EXACT-RATIONAL SIDE-STORE (empty for every all-`f64`-exact model).
    ///
    /// The `f64` matrix ([`ColSpec::obj`], [`RowSpec::coeffs`]/bounds) is the
    /// float lane's ADVICE copy. When a coefficient's true value is not an
    /// `f64` (`ran14x18-disj-8`, `timtab1`: scaling to clear denominators
    /// overflows `f64`'s exact integer range), the stored `f64` is a ROUNDED
    /// proxy and the TRUE rational lives here. Every VERDICT-critical exact
    /// consumer (`check_point`, `objective_value_at`, the exact rim, the
    /// certificate verifier) reads through the helper accessors below, which
    /// consult this store first, so a verdict is never re-adjudicated against a
    /// rounded coefficient. See `designs`/the r12 coverage change.
    pub(crate) exact_obj: HashMap<u32, BigRational>,
    /// TRUE objective offset, when the stored `f64` offset is a rounded proxy.
    pub(crate) exact_obj_offset: Option<BigRational>,
    /// Row index -> exact overrides for that row's rounded coefficients/bounds.
    pub(crate) exact_rows: HashMap<u32, ExactRow>,
    /// TRUE once any coefficient/bound could not be held exactly by its `f64`
    /// and its true rational was recorded above. Gates every side-store read;
    /// stays `false` (and the store empty) for the fast path.
    pub(crate) has_inexact_coeffs: bool,
    /// OPT-IN "margin reframe" hint (see [`Self::mark_margin_row`]). Names a
    /// single one-sided "band-violation" inequality row in an objective-≡0
    /// FEASIBILITY model: the row asserts a violation exists, and the model is
    /// infeasible exactly when the property holds. Naming it lets the session
    /// reframe feasibility into margin-OPTIMIZATION (minimize/maximize the
    /// row's form over the rest), waking the dual-bound pruning and
    /// reduced-cost fixing that lie DORMANT under a zero objective. `None`
    /// (the default) means no reframe — every model that never calls
    /// `mark_margin_row` is byte-identical, no gate required. The caller names
    /// the margin, so the reframe never has to GUESS which row is the
    /// violation; that is what makes this opt-in shape sound and robust.
    pub(crate) margin: Option<u32>,
}

impl Model {
    /// Create an empty model.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a continuous column with bounds `[lb, ub]` (use `±INFINITY` for
    /// a free side) and objective coefficient 0.
    ///
    /// # Panics
    /// Panics if a bound is NaN.
    pub fn add_col(&mut self, lb: f64, ub: f64) -> Col {
        assert!(!lb.is_nan() && !ub.is_nan(), "add_col: NaN bound");
        let idx = u32::try_from(self.cols.len()).expect("column count exceeds u32");
        self.cols.push(ColSpec {
            lb,
            ub,
            obj: 0.0,
            kind: ColKind::Continuous,
        });
        Col(idx)
    }

    /// Add a general integer column with bounds `[lb, ub]` (use `±INFINITY` for
    /// a free side) and objective coefficient 0.
    ///
    /// # Panics
    /// Panics if a bound is NaN.
    pub fn add_int_col(&mut self, lb: f64, ub: f64) -> Col {
        assert!(!lb.is_nan() && !ub.is_nan(), "add_int_col: NaN bound");
        let idx = u32::try_from(self.cols.len()).expect("column count exceeds u32");
        // A `[0, 1]` integer column IS a binary column, and saying so unlocks the 0/1
        // machinery (cover cuts, the flip/swap local search) on models -- MPS files
        // especially -- that declare their binaries the long way round.
        let kind = if lb == 0.0 && ub == 1.0 {
            ColKind::Binary
        } else {
            ColKind::Integer
        };
        self.cols.push(ColSpec {
            lb,
            ub,
            obj: 0.0,
            kind,
        });
        Col(idx)
    }

    /// Add a 0/1 column with objective coefficient 0.
    pub fn add_binary_col(&mut self) -> Col {
        let idx = u32::try_from(self.cols.len()).expect("column count exceeds u32");
        self.cols.push(ColSpec {
            lb: 0.0,
            ub: 1.0,
            obj: 0.0,
            kind: ColKind::Binary,
        });
        Col(idx)
    }

    /// Add a range row `lb <= coeffs·x <= ub`. Duplicate columns in `coeffs`
    /// are summed; zero coefficients are dropped.
    ///
    /// # Panics
    /// Panics if a bound is NaN, a coefficient is non-finite, or a column is
    /// out of range. Duplicate coefficients whose sum overflows are rejected
    /// too.
    pub fn add_row(&mut self, lb: f64, ub: f64, coeffs: &[(Col, f64)]) -> Row {
        assert!(!lb.is_nan() && !ub.is_nan(), "add_row: NaN bound");
        let mut merged: Vec<(u32, f64)> = Vec::with_capacity(coeffs.len());
        for &(col, a) in coeffs {
            assert!(a.is_finite(), "add_row: non-finite coefficient");
            assert!(
                col.index() < self.cols.len(),
                "add_row: column {} out of range ({} columns)",
                col.index(),
                self.cols.len()
            );
            merged.push((col.0, a));
        }
        merged.sort_unstable_by_key(|&(c, _)| c);
        merged.dedup_by(|later, first| {
            if later.0 == first.0 {
                first.1 += later.1;
                true
            } else {
                false
            }
        });
        assert!(
            merged.iter().all(|&(_, a)| a.is_finite()),
            "add_row: duplicate coefficient sum is non-finite"
        );
        merged.retain(|&(_, a)| a != 0.0);
        let idx = u32::try_from(self.rows.len()).expect("row count exceeds u32");
        self.rows.push(RowSpec {
            lb,
            ub,
            coeffs: merged,
        });
        Row(idx)
    }

    /// Replace an existing row's bounds and coefficients in place — the node-level
    /// CUT-SLOT primitive (`bab.rs`). The row count never changes, which is the whole
    /// point: every basis and every box stored against this model stays
    /// dimension-valid. Duplicate columns are summed and zeros dropped, exactly as
    /// `add_row` does, so a rewritten row is indistinguishable from a freshly added
    /// one.
    ///
    /// # Panics
    /// Panics if a bound is NaN, a coefficient is non-finite, a duplicate
    /// coefficient sum overflows, or a column or the row is out of range.
    pub(crate) fn set_row(&mut self, row: Row, lb: f64, ub: f64, coeffs: &[(Col, f64)]) {
        assert!(!lb.is_nan() && !ub.is_nan(), "set_row: NaN bound");
        assert!(
            row.index() < self.rows.len(),
            "set_row: row {} out of range ({} rows)",
            row.index(),
            self.rows.len()
        );
        let mut merged: Vec<(u32, f64)> = Vec::with_capacity(coeffs.len());
        for &(col, a) in coeffs {
            assert!(a.is_finite(), "set_row: non-finite coefficient");
            assert!(
                col.index() < self.cols.len(),
                "set_row: column {} out of range ({} columns)",
                col.index(),
                self.cols.len()
            );
            merged.push((col.0, a));
        }
        merged.sort_unstable_by_key(|&(c, _)| c);
        merged.dedup_by(|later, first| {
            if later.0 == first.0 {
                first.1 += later.1;
                true
            } else {
                false
            }
        });
        assert!(
            merged.iter().all(|&(_, a)| a.is_finite()),
            "set_row: duplicate coefficient sum is non-finite"
        );
        merged.retain(|&(_, a)| a != 0.0);
        self.rows[row.index()] = RowSpec {
            lb,
            ub,
            coeffs: merged,
        };
        // `set_row` replaces the row's semantics.  Any exact override attached
        // to the old row would otherwise survive and make verdict-critical
        // readers adjudicate the replacement against stale coefficients.
        self.exact_rows.remove(&row.0);
        self.refresh_inexact_flag();
    }

    /// Set the linear objective: coefficients (unmentioned columns get 0) and
    /// direction. Replaces any previous objective.
    ///
    /// # Panics
    /// Panics if a coefficient is non-finite or a column is out of range.
    pub fn set_objective(&mut self, coeffs: &[(Col, f64)], sense: Sense) {
        // Replacing the objective also replaces its exact side-store.  The MPS
        // reader calls this first and records the new overrides immediately
        // afterwards; ordinary API callers must not inherit the parsed
        // objective's old true rationals.
        self.exact_obj.clear();
        for spec in &mut self.cols {
            spec.obj = 0.0;
        }
        for &(col, a) in coeffs {
            assert!(a.is_finite(), "set_objective: non-finite coefficient");
            assert!(
                col.index() < self.cols.len(),
                "set_objective: column {} out of range ({} columns)",
                col.index(),
                self.cols.len()
            );
            self.cols[col.index()].obj = a;
        }
        self.sense = sense;
        self.has_objective = true;
        self.refresh_inexact_flag();
    }

    /// Replace a column's bounds (the branch-and-bound node primitive).
    ///
    /// # Panics
    /// Panics if a bound is NaN.
    pub(crate) fn set_col_bounds(&mut self, col: Col, lb: f64, ub: f64) {
        assert!(!lb.is_nan() && !ub.is_nan(), "set_col_bounds: NaN bound");
        self.cols[col.index()].lb = lb;
        self.cols[col.index()].ub = ub;
    }

    /// Set a constant objective offset (added to every objective value).
    ///
    /// # Panics
    /// Panics if `offset` is non-finite.
    pub fn set_objective_offset(&mut self, offset: f64) {
        assert!(
            offset.is_finite(),
            "set_objective_offset: non-finite offset"
        );
        self.obj_offset = offset;
        // Same replacement rule as `set_objective`: a previous parser-owned
        // exact offset no longer describes this value.
        self.exact_obj_offset = None;
        self.has_objective = true;
        self.refresh_inexact_flag();
    }

    /// Name `row` as the "margin" (band-violation) row of an objective-≡0
    /// FEASIBILITY model, opting this model into the MARGIN REFRAME (see
    /// [`crate::BabSession::check`] and the `margin` module).
    ///
    /// `row` must be a single ONE-SIDED inequality — `c·x <= t` (finite upper
    /// bound, infinite lower) or `c·x >= t` (finite lower, infinite upper) —
    /// with at least one coefficient; it is the row asserting a violation
    /// exists, so that the model is infeasible exactly when the checked
    /// property holds. Marking it lets the session solve the equivalent margin
    /// OPTIMIZATION (minimize/maximize `c·x` over the other rows), reviving the
    /// dual-bound pruning and reduced-cost fixing that a zero objective leaves
    /// dormant — while mapping the reframed optimum back to the ORIGINAL
    /// feasibility verdict with a valid exact certificate.
    ///
    /// The caller names the margin, so the reframe never guesses which row is
    /// the violation. The hint is advisory to correctness: the session
    /// re-validates every verdict against this model regardless, and declines
    /// the reframe (falling back to the plain feasibility solve) whenever the
    /// row or objective does not fit the shape at solve time.
    ///
    /// # Errors
    /// [`ModelError::Unsupported`] if `row` is out of range, has no
    /// coefficients, or is not a single one-sided inequality (an equality,
    /// a two-sided range, or a free row).
    pub fn mark_margin_row(&mut self, row: Row) -> Result<(), ModelError> {
        let idx = row.index();
        let spec = self.rows.get(idx).ok_or_else(|| ModelError::Unsupported {
            reason: format!("margin row {idx} is out of range"),
        })?;
        if spec.coeffs.is_empty() {
            return Err(ModelError::Unsupported {
                reason: format!("margin row {idx} has no coefficients"),
            });
        }
        let one_sided = spec.lb.is_finite() ^ spec.ub.is_finite();
        if !one_sided {
            return Err(ModelError::Unsupported {
                reason: format!(
                    "margin row {idx} is not a single one-sided inequality \
                     (needs exactly one finite bound)"
                ),
            });
        }
        self.margin = Some(idx as u32);
        Ok(())
    }

    /// The marked margin row, if any (see [`Self::mark_margin_row`]).
    #[must_use]
    pub fn margin_row(&self) -> Option<Row> {
        self.margin.map(Row)
    }

    /// Clear any marked margin row, restoring the plain feasibility solve.
    pub fn clear_margin(&mut self) {
        self.margin = None;
    }

    /// Shrink a column's bounds to `[value, value]`. Sessions provide a scoped
    /// `fix_col` operation when the change must later be reverted.
    ///
    /// # Panics
    /// Panics if `value` is NaN or the column is out of range.
    pub fn fix_col(&mut self, col: Col, value: f64) {
        assert!(!value.is_nan(), "fix_col: NaN value");
        let spec = &mut self.cols[col.index()];
        spec.lb = value;
        spec.ub = value;
    }

    /// Number of columns.
    #[must_use]
    pub fn num_cols(&self) -> usize {
        self.cols.len()
    }

    /// The column handle at `index` (insertion-order-stable), if in range.
    #[must_use]
    pub fn col_at(&self, index: usize) -> Option<Col> {
        (index < self.cols.len()).then_some(Col(index as u32))
    }

    /// The row handle at `index` (insertion-order-stable), if in range.
    #[must_use]
    pub fn row_at(&self, index: usize) -> Option<Row> {
        (index < self.rows.len()).then_some(Row(index as u32))
    }

    /// Number of rows.
    #[must_use]
    pub fn num_rows(&self) -> usize {
        self.rows.len()
    }

    /// Whether this model carries any coefficient/bound whose true value is not
    /// an `f64` (its stored `f64` is a rounded proxy and the truth is in the
    /// side-store). `false` for every all-`f64`-exact model — the entire fast
    /// path is unchanged and byte-identical.
    #[must_use]
    pub(crate) fn has_inexact_coeffs(&self) -> bool {
        self.has_inexact_coeffs
    }

    /// The TRUE rational coefficient of row `row` at column `c`, given its
    /// stored `f64` `a`. Consults the side-store first; falls back to `exact(a)`
    /// (identical to the old behaviour) when there is no override. `row` is a
    /// row index (`Row::index`).
    pub(crate) fn row_coeff_exact(&self, row: usize, c: u32, a: f64) -> BigRational {
        if self.has_inexact_coeffs {
            if let Some(er) = self.exact_rows.get(&(row as u32)) {
                if let Some(v) = er.coeffs.get(&c) {
                    return v.clone();
                }
            }
        }
        exact(a).expect("validated row coefficient")
    }

    /// [`Self::row_coeff_exact`], landing on the inline-small exact rational
    /// representation used by verdict-critical matrix accumulators.
    ///
    /// The side-store lookup is load-bearing: `a` can be only a rounded proxy
    /// for `v`, so the fast `f64` conversion is legal only when no override
    /// exists for this entry.
    pub(crate) fn row_coeff_exact_small(
        &self,
        row: usize,
        c: u32,
        a: f64,
    ) -> ay_lra::rational::Rational {
        if self.has_inexact_coeffs {
            if let Some(er) = self.exact_rows.get(&(row as u32)) {
                if let Some(v) = er.coeffs.get(&c) {
                    return ay_lra::rational::Rational::from_big(v.clone());
                }
            }
        }
        exact_small(a).expect("validated row coefficient")
    }

    /// The TRUE rational lower bound of row `row` (`None` = `-INFINITY`), given
    /// its stored `f64` `lb`. Consults the side-store first.
    pub(crate) fn row_lb_exact(&self, row: usize, lb: f64) -> Option<BigRational> {
        if self.has_inexact_coeffs {
            if let Some(er) = self.exact_rows.get(&(row as u32)) {
                if let Some(v) = &er.lb {
                    return Some(v.clone());
                }
            }
        }
        exact(lb)
    }

    /// [`Self::row_lb_exact`], landing on the inline-small exact rational
    /// representation without bypassing a true-rational side-store override.
    pub(crate) fn row_lb_exact_small(
        &self,
        row: usize,
        lb: f64,
    ) -> Option<ay_lra::rational::Rational> {
        if self.has_inexact_coeffs {
            if let Some(er) = self.exact_rows.get(&(row as u32)) {
                if let Some(v) = &er.lb {
                    return Some(ay_lra::rational::Rational::from_big(v.clone()));
                }
            }
        }
        exact_small(lb)
    }

    /// The TRUE rational upper bound of row `row` (`None` = `+INFINITY`).
    pub(crate) fn row_ub_exact(&self, row: usize, ub: f64) -> Option<BigRational> {
        if self.has_inexact_coeffs {
            if let Some(er) = self.exact_rows.get(&(row as u32)) {
                if let Some(v) = &er.ub {
                    return Some(v.clone());
                }
            }
        }
        exact(ub)
    }

    /// [`Self::row_ub_exact`], landing on the inline-small exact rational
    /// representation without bypassing a true-rational side-store override.
    pub(crate) fn row_ub_exact_small(
        &self,
        row: usize,
        ub: f64,
    ) -> Option<ay_lra::rational::Rational> {
        if self.has_inexact_coeffs {
            if let Some(er) = self.exact_rows.get(&(row as u32)) {
                if let Some(v) = &er.ub {
                    return Some(ay_lra::rational::Rational::from_big(v.clone()));
                }
            }
        }
        exact_small(ub)
    }

    /// The TRUE rational objective coefficient of column `c`, given its stored
    /// `f64` `a`. Consults the side-store first.
    pub(crate) fn obj_coeff_exact_at(&self, c: u32, a: f64) -> BigRational {
        if self.has_inexact_coeffs {
            if let Some(v) = self.exact_obj.get(&c) {
                return v.clone();
            }
        }
        exact(a).expect("validated objective coefficient")
    }

    /// The TRUE rational objective offset. Consults the side-store first.
    pub(crate) fn obj_offset_exact(&self) -> BigRational {
        if self.has_inexact_coeffs {
            if let Some(v) = &self.exact_obj_offset {
                return v.clone();
            }
        }
        exact(self.obj_offset).unwrap_or_else(BigRational::zero)
    }

    /// Record the TRUE rational coefficient of row `row` at column `c` — used by
    /// the MPS reader when a coefficient's `f64` is only a rounded proxy. Sets
    /// [`Self::has_inexact_coeffs`].
    pub(crate) fn record_inexact_row_coeff(&mut self, row: Row, c: u32, value: BigRational) {
        self.has_inexact_coeffs = true;
        self.exact_rows
            .entry(row.0)
            .or_default()
            .coeffs
            .insert(c, value);
    }

    /// Record the TRUE rational lower/upper bound of row `row`.
    pub(crate) fn record_inexact_row_bound(&mut self, row: Row, lower: bool, value: BigRational) {
        self.has_inexact_coeffs = true;
        let er = self.exact_rows.entry(row.0).or_default();
        if lower {
            er.lb = Some(value);
        } else {
            er.ub = Some(value);
        }
    }

    /// Record the TRUE rational objective coefficient of column `c`.
    pub(crate) fn record_inexact_obj_coeff(&mut self, c: u32, value: BigRational) {
        self.has_inexact_coeffs = true;
        self.exact_obj.insert(c, value);
    }

    /// Record the TRUE rational objective offset.
    pub(crate) fn record_inexact_obj_offset(&mut self, value: BigRational) {
        self.has_inexact_coeffs = true;
        self.exact_obj_offset = Some(value);
    }

    /// Recompute the side-store gate after a replacement mutator removes stale
    /// overrides.  Keeping this exact matters for more than speed: several
    /// heuristic lanes deliberately decline all side-store models.
    fn refresh_inexact_flag(&mut self) {
        self.has_inexact_coeffs = !self.exact_obj.is_empty()
            || self.exact_obj_offset.is_some()
            || !self.exact_rows.is_empty();
    }

    /// A column's `(lb, ub)` bounds.
    ///
    /// # Panics
    /// Panics if the column is out of range.
    #[must_use]
    pub fn col_bounds(&self, col: Col) -> (f64, f64) {
        let s = &self.cols[col.index()];
        (s.lb, s.ub)
    }

    /// A column's kind.
    ///
    /// # Panics
    /// Panics if the column is out of range.
    #[must_use]
    pub fn col_kind(&self, col: Col) -> ColKind {
        self.cols[col.index()].kind
    }

    /// A column's objective coefficient.
    ///
    /// # Panics
    /// Panics if the column is out of range.
    #[must_use]
    pub fn obj_coeff(&self, col: Col) -> f64 {
        self.cols[col.index()].obj
    }

    /// The objective direction.
    #[must_use]
    pub fn sense(&self) -> Sense {
        self.sense
    }

    /// The objective offset.
    #[must_use]
    pub fn objective_offset(&self) -> f64 {
        self.obj_offset
    }

    /// Whether an objective was set, however trivial. Sessions optimize when
    /// this holds and answer feasibility when it does not; reading it off the
    /// coefficients instead would make an explicit all-zero objective
    /// indistinguishable from no objective, and the LP and MILP lanes would
    /// then disagree (`Optimal { value: 0 }` against `Feasible`) on the same
    /// model.
    #[must_use]
    pub fn has_objective(&self) -> bool {
        self.has_objective
    }

    /// A row's `(coeffs, lb, ub)`. Coefficients are sorted by column index,
    /// duplicate-free, and zero-free.
    ///
    /// # Panics
    /// Panics if the row is out of range.
    #[must_use]
    pub fn row(&self, row: Row) -> (&[(u32, f64)], f64, f64) {
        let r = &self.rows[row.index()];
        (&r.coeffs, r.lb, r.ub)
    }

    /// Whether any column is integral (Binary).
    #[must_use]
    pub fn has_integrality(&self) -> bool {
        self.cols
            .iter()
            .any(|c| !matches!(c.kind, ColKind::Continuous))
    }

    /// Validate the model for solving: rejects infinite objective
    /// coefficients/offset and NaN anywhere (NaN is already rejected at
    /// construction; this is the session-boundary belt).
    pub(crate) fn validate(&self) -> Result<(), ModelError> {
        for (i, c) in self.cols.iter().enumerate() {
            if c.lb.is_nan() || c.ub.is_nan() || !c.obj.is_finite() {
                return Err(ModelError::InvalidNumber {
                    col: Some(i),
                    row: None,
                });
            }
        }
        for (i, r) in self.rows.iter().enumerate() {
            if r.lb.is_nan() || r.ub.is_nan() || r.coeffs.iter().any(|&(_, a)| !a.is_finite()) {
                return Err(ModelError::InvalidNumber {
                    col: None,
                    row: Some(i),
                });
            }
        }
        if !self.obj_offset.is_finite() {
            return Err(ModelError::InvalidNumber {
                col: None,
                row: None,
            });
        }
        Ok(())
    }

    /// The exact objective value at an exact point (`values[i]` = column `i`).
    ///
    /// # Panics
    /// Panics if `values.len() != num_cols()`.
    #[must_use]
    pub fn objective_value_at(&self, values: &[BigRational]) -> BigRational {
        assert_eq!(
            values.len(),
            self.cols.len(),
            "objective_value_at: wrong arity"
        );
        let mut acc = self.obj_offset_exact();
        for (j, (spec, v)) in self.cols.iter().zip(values).enumerate() {
            // A rounded `f64` obj coeff can be a nonzero true rational stored in
            // the side-store even when `spec.obj == 0.0` is impossible here (a
            // nonzero true coeff never rounds to 0.0 for the magnitudes the
            // reader admits), so the `!= 0.0` fast-skip stays exact: the
            // side-store is only ever populated for columns whose `f64` obj is
            // nonzero.
            if spec.obj != 0.0 {
                acc += self.obj_coeff_exact_at(j as u32, spec.obj) * v;
            }
        }
        acc
    }

    /// Check an exact point against all bounds, rows, and integrality.
    /// Returns the first violation found, or `Ok(())` for a feasible point.
    ///
    /// # Panics
    /// Panics if `values.len() != num_cols()`.
    pub fn check_point(&self, values: &[BigRational]) -> Result<(), PointViolation> {
        use std::sync::atomic::Ordering::Relaxed;
        CHECK_CALLS.fetch_add(1, Relaxed);
        let _t = std::time::Instant::now();
        let out = self.check_point_inner(values);
        CHECK_NANOS.fetch_add(_t.elapsed().as_nanos() as u64, Relaxed);
        out
    }

    fn check_point_inner(&self, values: &[BigRational]) -> Result<(), PointViolation> {
        // A POINT OF THE WRONG LENGTH IS NOT A FEASIBLE POINT — SAY SO, DON'T PANIC.
        //
        // `check_point` decides whether `values` is a feasible point of THIS model, and a vector
        // that does not have one entry per column is unambiguously not one. Returning `Err` is the
        // truthful answer, and every caller already treats `Err` as "reject this witness" — so this
        // can never turn a wrong point into an accepted one. The old `assert_eq!` was a development
        // invariant that fired in production: a primal heuristic (sub-MIP RINS) leaked an
        // LP-augmented vector (`n + m`, slacks included) into `check_point` and crashed the whole
        // solve on nw04 (642 values against 606 columns). A crash is the one outcome worse than a
        // missed heuristic. `debug_assert` keeps the invariant loud in tests, where arity bugs are
        // real bugs to be fixed, without letting one abort a release solve.
        debug_assert_eq!(
            values.len(),
            self.cols.len(),
            "check_point: wrong arity (values {} vs columns {})",
            values.len(),
            self.cols.len(),
        );
        if values.len() != self.cols.len() {
            return Err(PointViolation::Arity);
        }
        // The arithmetic runs on the small-int-fast [`ay_lra::rational::Rational`]
        // (exact big fallback): `BigRational`'s allocating gcd-normalized ops made
        // this check ~8% of a small solve's wall at the rate heuristics ask it.
        // Same numbers, same verdicts.
        use ay_lra::rational::Rational;
        let vals: Vec<Rational> = values
            .iter()
            .map(|v| Rational::from_big(v.clone()))
            .collect();
        for (i, (spec, v)) in self.cols.iter().zip(&vals).enumerate() {
            if let Some(lb) = exact_small(spec.lb) {
                if *v < lb {
                    return Err(PointViolation::ColBound { col: Col(i as u32) });
                }
            }
            if let Some(ub) = exact_small(spec.ub) {
                if *v > ub {
                    return Err(PointViolation::ColBound { col: Col(i as u32) });
                }
            }
            // Both integral kinds are checked here, exactly. A general integer column that
            // was only bound-checked would let a fractional point be certified `Optimal`,
            // which is the one failure this crate does not get to have.
            if spec.kind.is_integral() && !v.is_integer() {
                return Err(PointViolation::Integrality { col: Col(i as u32) });
            }
        }
        for (i, r) in self.rows.iter().enumerate() {
            // The row activity, accumulated as ONE BigInt numerator over a running
            // denominator — the same technique as `solve_sparse` back-substitution.
            // The naive `act += a * x` runs up to five Stein gcds PER TERM at the
            // point's bit-size (num-rational's Mul + AddAssign both normalize), and
            // this loop verifies EVERY incumbent: on the cifar100 w2 model (1.85M
            // nnz, ~3000-bit incumbent rationals) one check_point was 20s of gcd.
            // Fast paths (equal / dividing denominators) are raw integer ops; the
            // slow path gcds the DENOMINATORS only; the bound comparison is done
            // cross-multiplied, so the sum is never reduced at all. Exact: every
            // branch computes the same `Σ a·x`, and `den > 0` throughout (a product
            // of positive denominators), so the comparisons preserve direction.
            let mut num = num_bigint::BigInt::from(0);
            let mut den = num_bigint::BigInt::from(1);
            for &(c, a) in &r.coeffs {
                let x = &values[c as usize];
                if x.is_zero() {
                    continue;
                }
                let av = self.row_coeff_exact(i, c, a);
                let tn = av.numer() * x.numer();
                let td = av.denom() * x.denom();
                if den == td {
                    num += tn;
                } else if (&td % &den).is_zero() {
                    num = &num * (&td / &den) + tn;
                    den = td;
                } else if (&den % &td).is_zero() {
                    num += tn * (&den / &td);
                } else {
                    use num_integer::Integer;
                    let g = den.gcd(&td);
                    let l = &den / &g * &td;
                    num = &num * (&l / &den) + tn * (&l / &td);
                    den = l;
                }
            }
            // act = num/den; bounds are dyadic (or the true rational from the
            // side-store) with positive denominators.
            if let Some(lb) = self.row_lb_exact(i, r.lb) {
                if &num * lb.denom() < lb.numer() * &den {
                    return Err(PointViolation::RowBound { row: Row(i as u32) });
                }
            }
            if let Some(ub) = self.row_ub_exact(i, r.ub) {
                if &num * ub.denom() > ub.numer() * &den {
                    return Err(PointViolation::RowBound { row: Row(i as u32) });
                }
            }
        }
        Ok(())
    }
}

/// A feasibility violation found by [`Model::check_point`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PointViolation {
    /// The point does not have one entry per model column (an internal arity error —
    /// see `check_point_inner`). Treated as "not a feasible point", never accepted.
    Arity,
    /// A column bound is violated.
    ColBound {
        /// The violated column.
        col: Col,
    },
    /// A row bound is violated.
    RowBound {
        /// The violated row.
        row: Row,
    },
    /// A binary column has a non-0/1 value.
    Integrality {
        /// The violating column.
        col: Col,
    },
}

/// The exact rational a finite f64 denotes; `None` for `±INFINITY` (an
/// unbounded side). NaN must be rejected before this point.
/// What the exact point-check costs the search.
pub(crate) static CHECK_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static CHECK_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// `exact`, but landing on the small-int-fast [`ay_lra::rational::Rational`]:
/// the dyadic decomposition drops straight into the inline `i64/i64` variant
/// whenever mantissa and 2^|exp| both fit (every real-world matrix entry), and
/// falls back to the exact big path otherwise. Same number either way.
pub(crate) fn exact_small(f: f64) -> Option<ay_lra::rational::Rational> {
    use ay_lra::rational::Rational;
    debug_assert!(!f.is_nan(), "NaN reached exact_small()");
    if !f.is_finite() {
        return None;
    }
    let bits = f.to_bits();
    let exp_field = ((bits >> 52) & 0x7ff) as i64;
    let frac = bits & ((1u64 << 52) - 1);
    let (mut mantissa, mut exponent) = if exp_field == 0 {
        (frac, -1074i64) // subnormal: no hidden bit
    } else {
        (frac | (1u64 << 52), exp_field - 1075)
    };
    if mantissa == 0 {
        return Some(Rational::new(0, 1)); // ±0.0
    }
    let tz = mantissa.trailing_zeros();
    mantissa >>= tz;
    exponent += i64::from(tz);
    // Odd mantissa against a power of two: coprime by construction, so the
    // Small invariant (reduced, positive denominator) holds with no gcd.
    if exponent >= 0 {
        if i64::from(mantissa.leading_zeros()) > exponent {
            let n = (mantissa as i64) << exponent;
            return Some(Rational::new(if f.is_sign_negative() { -n } else { n }, 1));
        }
    } else if -exponent <= 62 {
        let n = mantissa as i64;
        return Some(Rational::new(
            if f.is_sign_negative() { -n } else { n },
            1i64 << (-exponent),
        ));
    }
    exact(f).map(Rational::from_big)
}

pub(crate) fn exact(f: f64) -> Option<BigRational> {
    debug_assert!(!f.is_nan(), "NaN reached exact()");
    if !f.is_finite() {
        return None;
    }
    // DYADIC FAST PATH. `BigRational::from_float` builds the raw mantissa/2^k pair
    // and hands it to `Ratio::new`, which runs a gcd to reduce — but an f64 is
    // dyadic, so stripping the mantissa's trailing zeros into the exponent leaves
    // an ODD mantissa against a power of two: coprime BY CONSTRUCTION, no gcd to
    // run. `new_raw` then skips the reduce. This function converts every matrix
    // entry the exact lane ever touches (millions per solve on an NN model), and
    // the per-call gcd was the bulk of its cost. Byte-equality with `from_float`
    // over the full float structure (zeros, subnormals, integers, random bit
    // patterns) is pinned by `exact_matches_from_float`.
    let bits = f.to_bits();
    let exp_field = ((bits >> 52) & 0x7ff) as i64;
    let frac = bits & ((1u64 << 52) - 1);
    let (mut mantissa, mut exponent) = if exp_field == 0 {
        (frac, -1074i64) // subnormal: no hidden bit
    } else {
        (frac | (1u64 << 52), exp_field - 1075)
    };
    if mantissa == 0 {
        return Some(BigRational::zero()); // ±0.0
    }
    let tz = mantissa.trailing_zeros();
    mantissa >>= tz;
    exponent += i64::from(tz);
    let mut numer = num_bigint::BigInt::from(mantissa);
    if f.is_sign_negative() {
        numer = -numer;
    }
    Some(if exponent >= 0 {
        BigRational::new_raw(numer << exponent, num_bigint::BigInt::from(1))
    } else {
        // Odd numerator over a power of two: already in lowest terms.
        BigRational::new_raw(numer, num_bigint::BigInt::from(1) << (-exponent))
    })
}

#[cfg(test)]
mod exact_tests {
    use super::{exact, exact_small};
    use num_rational::BigRational;

    /// The dyadic fast path must be BYTE-IDENTICAL to `BigRational::from_float`
    /// (the reference it replaced) across the whole float structure: `exact` feeds
    /// `check_point` and the certificates, so "close" is not a property, equality
    /// is. Cases: zeros (both signs), subnormals (min positive, largest subnormal),
    /// exact integers, powers of two (even raw mantissas), 1/3-style repeating
    /// fractions, f64::MAX/MIN_POSITIVE, and a deterministic sweep of random bit
    /// patterns (non-finite skipped, as both sides decline them).
    #[test]
    fn exact_matches_from_float() {
        let structured: &[f64] = &[
            0.0,
            -0.0,
            1.0,
            -1.0,
            0.5,
            -0.5,
            2.0,
            1e300,
            -1e300,
            1e-300,
            f64::MAX,
            f64::MIN,
            f64::MIN_POSITIVE,
            -f64::MIN_POSITIVE,
            f64::from_bits(1),                  // smallest subnormal
            f64::from_bits(0xF_FFFF_FFFF_FFFF), // largest subnormal
            1.0 / 3.0,
            2.0 / 3.0,
            0.1,
            123_456_789.123_456_79,
            (1u64 << 53) as f64,
            ((1u64 << 53) - 1) as f64,
        ];
        for &f in structured {
            assert_eq!(
                exact(f),
                BigRational::from_float(f),
                "mismatch on structured value {f:e} (bits {:#x})",
                f.to_bits()
            );
            assert_eq!(
                exact_small(f).map(|value| value.to_big()),
                exact(f),
                "small exact mismatch on structured value {f:e} (bits {:#x})",
                f.to_bits()
            );
        }
        assert_eq!(exact(f64::INFINITY), None);
        assert_eq!(exact(f64::NEG_INFINITY), None);
        assert_eq!(exact_small(f64::INFINITY), None);
        assert_eq!(exact_small(f64::NEG_INFINITY), None);

        // Deterministic xorshift sweep over raw bit patterns: exercises random
        // mantissa/exponent combinations including subnormals.
        let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut tested = 0usize;
        while tested < 200_000 {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            let f = f64::from_bits(s);
            if !f.is_finite() {
                continue;
            }
            assert_eq!(
                exact(f),
                BigRational::from_float(f),
                "mismatch on bits {s:#x} ({f:e})"
            );
            assert_eq!(
                exact_small(f).map(|value| value.to_big()),
                exact(f),
                "small exact mismatch on bits {s:#x} ({f:e})"
            );
            tested += 1;
        }
    }
}

#[cfg(test)]
mod check_point_row_tests {
    use super::{Model, PointViolation};
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    /// Exact readers deliberately represent only finite coefficients. Reject
    /// invalid public input at the mutator boundary instead of letting a later
    /// `objective_value_at`/`check_point` panic or silently reinterpret it.
    #[test]
    fn coefficient_mutators_reject_non_finite_values() {
        for bad in [f64::INFINITY, f64::NEG_INFINITY] {
            assert!(std::panic::catch_unwind(|| {
                let mut m = Model::new();
                let x = m.add_col(0.0, 1.0);
                m.add_row(0.0, 1.0, &[(x, bad)]);
            })
            .is_err());
            assert!(std::panic::catch_unwind(|| {
                let mut m = Model::new();
                let x = m.add_col(0.0, 1.0);
                let row = m.add_row(0.0, 1.0, &[(x, 1.0)]);
                m.set_row(row, 0.0, 1.0, &[(x, bad)]);
            })
            .is_err());
            assert!(std::panic::catch_unwind(|| {
                let mut m = Model::new();
                let x = m.add_col(0.0, 1.0);
                m.set_objective(&[(x, bad)], super::Sense::Minimize);
            })
            .is_err());
            assert!(std::panic::catch_unwind(|| {
                let mut m = Model::new();
                m.set_objective_offset(bad);
            })
            .is_err());
        }
    }

    /// Inputs can each be finite while duplicate-row normalization overflows.
    /// Reject the normalized row immediately in both construction paths.
    #[test]
    fn row_mutators_reject_duplicate_sum_overflow() {
        assert!(std::panic::catch_unwind(|| {
            let mut m = Model::new();
            let x = m.add_col(0.0, 1.0);
            m.add_row(0.0, 1.0, &[(x, f64::MAX), (x, f64::MAX)]);
        })
        .is_err());
        assert!(std::panic::catch_unwind(|| {
            let mut m = Model::new();
            let x = m.add_col(0.0, 1.0);
            let row = m.add_row(0.0, 1.0, &[(x, 1.0)]);
            m.set_row(row, 0.0, 1.0, &[(x, f64::MAX), (x, f64::MAX)]);
        })
        .is_err());
    }

    /// The common-denominator row evaluation must agree with the naive exact sum on
    /// points whose term denominators hit ALL FOUR merge branches (equal, den|td,
    /// td|den, coprime) and on both violation directions. Coefficients 0.5/0.25/1.0
    /// are exact dyadics; values with denominators 3, 4, 6, 8 force the branches.
    #[test]
    fn row_activity_exact_across_denominator_branches() {
        let mut m = Model::new();
        let a = m.add_col(-100.0, 100.0);
        let b = m.add_col(-100.0, 100.0);
        let c = m.add_col(-100.0, 100.0);
        let d = m.add_col(-100.0, 100.0);
        // act = 0.5a + 0.25b + 1.0c + 2.0d
        m.add_row(-1.0, 1.0, &[(a, 0.5), (b, 0.25), (c, 1.0), (d, 2.0)]);
        // act = 1/2·(1/3) + 1/4·(1/6) + 1·(1/4) + 2·(3/8)
        //     = 1/6 + 1/24 + 1/4 + 3/4 = 29/24 > 1  → upper violated.
        let over = vec![rat(1, 3), rat(1, 6), rat(1, 4), rat(3, 8)];
        assert!(matches!(
            m.check_point(&over),
            Err(PointViolation::RowBound { .. })
        ));
        // act = 1/6 + 1/24 + 1/4 − 3/4 = −7/24 ∈ [−1, 1] → feasible.
        let inside = vec![rat(1, 3), rat(1, 6), rat(1, 4), rat(-3, 8)];
        assert!(m.check_point(&inside).is_ok());
        // act = −1/6 − 1/24 − 1/4 − 3/4 = −29/24 < −1 → lower violated.
        let under = vec![rat(-1, 3), rat(-1, 6), rat(-1, 4), rat(-3, 8)];
        assert!(matches!(
            m.check_point(&under),
            Err(PointViolation::RowBound { .. })
        ));
        // Exactly ON the bound (act = 1): feasible, no off-by-one in the strict
        // cross-multiplied comparison. 0.5·2 = 1.
        let on = vec![rat(2, 1), rat(0, 1), rat(0, 1), rat(0, 1)];
        assert!(m.check_point(&on).is_ok());
    }

    /// THE SOUNDNESS PROPERTY for inexact coverage: when a coefficient's true
    /// value is not an `f64` (its stored `f64` is a rounded proxy), every
    /// verdict-critical read consults the exact-rational side-store, NEVER the
    /// rounded `f64`. Here the true coefficient is `2^53 + 1` (which rounds DOWN
    /// to `2^53` in `f64`), and a point is chosen that the rounded row would
    /// accept but the TRUE row rejects — check_point and objective_value_at must
    /// answer on the truth, or a rounded coefficient would flip a verdict.
    #[test]
    fn verdict_reads_the_true_rational_not_the_rounded_f64() {
        use num_traits::ToPrimitive;
        let big = BigInt::from((1u64 << 53) + 1); // 2^53 + 1, NOT an f64
        let true_coeff = BigRational::from_integer(big.clone());
        // The nearest f64 is exactly 2^53.
        let rounded = true_coeff.to_f64().expect("finite");
        // Sanity: the f64 really is a rounded proxy for a different rational.
        assert_ne!(
            BigRational::from_float(rounded).expect("finite"),
            true_coeff,
            "test needs a coefficient the f64 cannot hold"
        );

        // Row: (2^53 + 1)·x <= 2^53 + 1, x integer in [0, 2].
        let mut m = Model::new();
        let x = m.add_int_col(0.0, 2.0);
        let row = m.add_row(f64::NEG_INFINITY, rounded, &[(x, rounded)]);
        // Record the truth for the coefficient AND the bound (both 2^53+1).
        m.record_inexact_row_coeff(row, x.0, true_coeff.clone());
        m.record_inexact_row_bound(row, false, true_coeff.clone());
        assert!(m.has_inexact_coeffs());

        // x = 1: TRUE activity 2^53+1 == ub 2^53+1 → feasible.
        assert!(m
            .check_point(&[BigRational::from_integer(1.into())])
            .is_ok());
        // x = 2: TRUE activity 2·(2^53+1) = 2^54+2 > 2^53+1 → INfeasible. A
        // solver reading the rounded coeff would compute 2·2^53 = 2^54 against a
        // rounded ub 2^53 and ALSO reject — so instead pin the discriminating
        // case below where rounding flips the answer.
        assert!(matches!(
            m.check_point(&[BigRational::from_integer(2.into())]),
            Err(PointViolation::RowBound { .. })
        ));

        // The discriminating point: x = (2^53) / (2^53 + 1), just under 1.
        // TRUE activity = (2^53+1)·2^53/(2^53+1) = 2^53 <= ub (2^53+1) → feasible.
        // ROUNDED activity = 2^53 · 2^53/(2^53+1) is a hair under 2^53, also <=
        // rounded ub 2^53 → same verdict, so use the OBJECTIVE gate for the flip.
        //
        // Objective: minimize (2^53+1)·x. At x = 1 the TRUE objective value is
        // exactly 2^53 + 1; a rounded read would report 2^53. Assert the exact
        // value is the TRUE rational, never the rounded one.
        m.set_objective(&[(x, rounded)], super::Sense::Minimize);
        m.record_inexact_obj_coeff(x.0, true_coeff.clone());
        let v = m.objective_value_at(&[BigRational::from_integer(1.into())]);
        assert_eq!(
            v, true_coeff,
            "objective must read the true 2^53+1, not 2^53"
        );
        assert_ne!(
            v,
            BigRational::from_float(rounded).expect("finite"),
            "objective must NOT read the rounded 2^53"
        );
    }

    /// Public replacement mutators must retire parser-owned exact overrides.
    /// Otherwise changing an MPS model's objective would leave value/witness
    /// checks reading the OLD objective from the side-store.
    #[test]
    fn replacement_mutators_clear_stale_exact_overrides() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 2.0);

        m.set_objective(&[(x, 1.0)], super::Sense::Minimize);
        m.record_inexact_obj_coeff(x.0, BigRational::from_integer(7.into()));
        m.set_objective_offset(1.0);
        m.record_inexact_obj_offset(BigRational::from_integer(11.into()));
        assert_eq!(
            m.objective_value_at(&[BigRational::from_integer(2.into())]),
            BigRational::from_integer(25.into())
        );

        m.set_objective(&[(x, 3.0)], super::Sense::Minimize);
        // The offset override is independent and remains until that value is
        // replaced; the old coefficient override is already gone.
        assert_eq!(
            m.objective_value_at(&[BigRational::from_integer(2.into())]),
            BigRational::from_integer(17.into())
        );
        m.set_objective_offset(5.0);
        assert_eq!(
            m.objective_value_at(&[BigRational::from_integer(2.into())]),
            BigRational::from_integer(11.into())
        );
        assert!(!m.has_inexact_coeffs());

        let row = m.add_row(0.0, 1.0, &[(x, 1.0)]);
        m.record_inexact_row_coeff(row, x.0, BigRational::from_integer(9.into()));
        m.set_row(row, 0.0, 2.0, &[(x, 2.0)]);
        assert_eq!(
            m.row_coeff_exact(row.index(), x.0, 2.0),
            BigRational::from_integer(2.into())
        );
        assert!(!m.has_inexact_coeffs());
    }
}
