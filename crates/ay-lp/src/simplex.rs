// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A small revised simplex solver for LP relaxations.
//!
//! This is a Phase 1 implementation sized for the <= 20 variable / <= 20
//! constraint test fixtures. It does not pretend to be competitive with
//! production LP solvers; it exists so that the parser + CLI + branch-and-bound
//! pipeline can be exercised end to end.
//!
//! Approach: tableau-based primal simplex with an explicit phase-I
//! feasibility objective.
//!
//! 1. Normalize variables into nonnegative columns: finite-lower variables use
//!    `x_i = lower_i + y_i`, upper-only variables use `x_i = upper_i - y_i`,
//!    and free variables split as `x_i = x_i^+ - x_i^-`.
//! 2. Add slack variables to convert `<=` to equality, surplus + artificial
//!    to convert `>=` and `=`.
//! 3. Phase I maximizes `-sum(artificials)` to remove artificial variables
//!    without any finite Big-M scale assumption.
//! 4. Phase II maximizes `sum(obj_coef * x)` (for Min, the negated
//!    objective) with artificial columns forbidden from entering.
//! 5. Pivot with Bland's rule until optimal or unbounded.
//!
//! Upper bounds are encoded as extra `<=` rows. This doubles the constraint
//! count for bounded LPs but is the simplest way to keep the tableau uniform.

use crate::error::LpError;
use crate::model::{Problem, RowKind, Sense, Solution, VarKind, Variable};

const EPS: f64 = 1e-9;
const FEAS_TOL: f64 = 1e-6;
const MAX_ITERS: usize = 50_000;

#[derive(Debug, Clone)]
struct VarTransform {
    constant: f64,
    terms: Vec<(usize, f64)>,
}

impl VarTransform {
    fn value(&self, decision_values: &[f64]) -> f64 {
        self.constant
            + self
                .terms
                .iter()
                .map(|&(col, coef)| coef * decision_values[col])
                .sum::<f64>()
    }
}

/// Solves the LP relaxation of `problem`. Integer constraints are ignored.
///
/// # Errors
///
/// Returns [`LpError::Infeasible`], [`LpError::Unbounded`], or
/// [`LpError::IterationLimit`] on failure.
pub fn solve_lp_relaxation(problem: &Problem) -> Result<Solution, LpError> {
    let builder = StandardForm::build(problem)?;
    let mut tableau = builder.into_tableau();
    tableau.run()?;
    let solution = extract_solution(&tableau, problem);
    validate_solution(problem, &solution)?;
    Ok(solution)
}

/// Result of a budgeted LP-relaxation solve (see
/// [`solve_lp_relaxation_budgeted`]).
#[derive(Debug, Clone)]
pub struct LpRelaxation {
    /// A feasible basic solution: the optimum when `optimal` is true,
    /// otherwise the last simplex iterate reached within the budget.
    pub solution: Solution,
    /// True when the simplex reached the optimality criterion; false when
    /// the iteration budget or `should_stop` cut the solve short.
    pub optimal: bool,
}

/// Budgeted/interruptible variant of [`solve_lp_relaxation`]: runs at most
/// `max_iters` pivots and polls `should_stop` at every iteration head.
///
/// On budget exhaustion this returns the best FEASIBLE iterate found so far
/// (`optimal == false`) instead of an error. Primal simplex iterates are
/// basic feasible solutions, so every intermediate tableau is a genuine
/// feasible point of `problem`; for a caller maximizing a dual objective
/// this is exactly the weak-duality truncation-soundness contract (any
/// feasible dual point is a valid bound, just possibly a weaker one).
///
/// # Errors
///
/// Returns [`LpError::Infeasible`] / [`LpError::Unbounded`] as usual. When
/// the budget expires while phase I still has artificial variables basic at a
/// positive level (`>=`/`=` rows not yet satisfied), there is no feasible
/// iterate to return and the call fails with [`LpError::IterationLimit`].
/// Problems whose rows are all `<=` with nonnegative right-hand sides start
/// from the feasible slack basis and can never hit that case.
pub fn solve_lp_relaxation_budgeted(
    problem: &Problem,
    max_iters: usize,
    should_stop: &dyn Fn() -> bool,
) -> Result<LpRelaxation, LpError> {
    let builder = StandardForm::build(problem)?;
    let mut tableau = builder.into_tableau();
    let mut remaining = max_iters;
    if matches!(
        tableau.run_phase1(&mut remaining, should_stop)?,
        RunEnd::Budget
    ) {
        return if tableau.is_infeasible() {
            Err(LpError::IterationLimit)
        } else {
            let solution = extract_solution(&tableau, problem);
            validate_solution(problem, &solution)?;
            Ok(LpRelaxation {
                solution,
                optimal: false,
            })
        };
    }
    let end = tableau.run_phase2(&mut remaining, should_stop)?;
    let solution = extract_solution(&tableau, problem);
    validate_solution(problem, &solution)?;
    Ok(LpRelaxation {
        solution,
        optimal: matches!(end, RunEnd::Optimal),
    })
}

/// Reconstruct source-variable values and recompute the objective on the
/// original (unshifted) values for numerical cleanliness.
fn extract_solution(tableau: &Tableau, problem: &Problem) -> Solution {
    let values = tableau.extract_values();
    let obj = objective_from_values(problem, &values);
    Solution {
        objective: obj,
        values,
    }
}

fn validate_solution(problem: &Problem, solution: &Solution) -> Result<(), LpError> {
    if solution.values.len() != problem.variables.len() {
        return Err(LpError::NumericalFailure(format!(
            "solution has {} values for {} variables",
            solution.values.len(),
            problem.variables.len()
        )));
    }
    if !solution.objective.is_finite() {
        return Err(LpError::NumericalFailure(
            "solution objective is not finite".into(),
        ));
    }
    for (idx, (var, &value)) in problem.variables.iter().zip(&solution.values).enumerate() {
        let (lower, upper) = effective_bounds(var);
        if lower.is_nan() || upper.is_nan() {
            return Err(LpError::NumericalFailure(format!(
                "variable '{}' (index {idx}) has a NaN effective bound",
                var.name
            )));
        }
        if lower.is_infinite() && lower.is_sign_positive() {
            return Err(LpError::NumericalFailure(format!(
                "variable '{}' (index {idx}) has +inf effective lower bound",
                var.name
            )));
        }
        if upper.is_infinite() && upper.is_sign_negative() {
            return Err(LpError::NumericalFailure(format!(
                "variable '{}' (index {idx}) has -inf effective upper bound",
                var.name
            )));
        }
        if lower.is_finite() && upper.is_finite() && upper < lower {
            return Err(LpError::NumericalFailure(format!(
                "variable '{}' (index {idx}) has inconsistent effective bounds",
                var.name
            )));
        }
        if !value.is_finite() {
            return Err(LpError::NumericalFailure(format!(
                "variable '{}' (index {idx}) has non-finite value",
                var.name
            )));
        }
        if lower.is_finite() && violation_below(value, lower) > feasibility_tol(value, lower) {
            return Err(LpError::NumericalFailure(format!(
                "variable '{}' (index {idx}) violates lower bound",
                var.name
            )));
        }
        if upper.is_finite() && violation_above(value, upper) > feasibility_tol(value, upper) {
            return Err(LpError::NumericalFailure(format!(
                "variable '{}' (index {idx}) violates upper bound",
                var.name
            )));
        }
    }

    let expected_objective = objective_from_values(problem, &solution.values);
    if !expected_objective.is_finite() {
        return Err(LpError::NumericalFailure(
            "recomputed solution objective is not finite".into(),
        ));
    }
    if equality_violation(solution.objective, expected_objective)
        > feasibility_tol(solution.objective, expected_objective)
    {
        return Err(LpError::NumericalFailure(format!(
            "solution objective {} does not match reconstructed objective {}",
            solution.objective, expected_objective
        )));
    }

    for (row_idx, constraint) in problem.constraints.iter().enumerate() {
        let mut lhs = 0.0;
        for &(var_idx, coef) in &constraint.coeffs {
            let Some(&value) = solution.values.get(var_idx) else {
                return Err(LpError::NumericalFailure(format!(
                    "constraint '{}' (index {row_idx}) references missing variable index {var_idx}",
                    constraint.name
                )));
            };
            lhs += coef * value;
        }
        if !lhs.is_finite() {
            return Err(LpError::NumericalFailure(format!(
                "constraint '{}' (index {row_idx}) activity is not finite",
                constraint.name
            )));
        }
        let tol = feasibility_tol(lhs, constraint.rhs);
        let ok = match constraint.kind {
            RowKind::Le => violation_above(lhs, constraint.rhs) <= tol,
            RowKind::Ge => violation_below(lhs, constraint.rhs) <= tol,
            RowKind::Eq => equality_violation(lhs, constraint.rhs) <= tol,
        };
        if !ok {
            return Err(LpError::NumericalFailure(format!(
                "constraint '{}' (index {row_idx}) is violated",
                constraint.name
            )));
        }
    }
    Ok(())
}

fn objective_from_values(problem: &Problem, values: &[f64]) -> f64 {
    let mut obj = problem.obj_constant;
    for (var, value) in problem.variables.iter().zip(values) {
        obj += var.obj_coeff * *value;
    }
    obj
}

fn feasibility_tol(a: f64, b: f64) -> f64 {
    FEAS_TOL * (1.0 + a.abs().max(b.abs()))
}

fn violation_above(value: f64, upper: f64) -> f64 {
    if value <= upper {
        0.0
    } else {
        let violation = value - upper;
        if violation.is_finite() {
            violation
        } else {
            f64::INFINITY
        }
    }
}

fn violation_below(value: f64, lower: f64) -> f64 {
    if value >= lower {
        0.0
    } else {
        let violation = lower - value;
        if violation.is_finite() {
            violation
        } else {
            f64::INFINITY
        }
    }
}

fn equality_violation(a: f64, b: f64) -> f64 {
    if a >= b {
        violation_above(a, b)
    } else {
        violation_below(a, b)
    }
}

fn effective_bounds(var: &Variable) -> (f64, f64) {
    match var.kind {
        VarKind::Binary => {
            let lower = if var.lower.is_nan() {
                f64::NAN
            } else {
                var.lower.max(0.0)
            };
            let upper = if var.upper.is_nan() {
                f64::NAN
            } else {
                var.upper.min(1.0)
            };
            (lower, upper)
        }
        VarKind::Continuous | VarKind::Integer => (var.lower, var.upper),
    }
}

fn shift_floor(lower: f64) -> f64 {
    if lower.is_finite() {
        lower
    } else {
        0.0
    }
}

// ----- Standard-form builder -------------------------------------------------

struct StandardForm {
    /// `c` in the maximization problem produced by standardization.
    c: Vec<f64>,
    /// `A` constraint matrix.
    a: Vec<Vec<f64>>,
    /// Right-hand sides (all >= 0 after sign-flipping).
    b: Vec<f64>,
    /// Initial basis: column index for each row.
    basis: Vec<usize>,
    /// Indices of artificial columns (phase I only).
    artificials: Vec<usize>,
    /// Number of nonnegative decision columns introduced by variable
    /// normalization. This can exceed the source variable count when free
    /// variables are split.
    n_decision: usize,
    /// Source-variable reconstruction from nonnegative decision columns.
    transforms: Vec<VarTransform>,
}

impl StandardForm {
    fn build(problem: &Problem) -> Result<Self, LpError> {
        validate_problem(problem)?;
        let (transforms, upper_bound_rows, n_decision) = build_var_transforms(problem)?;
        let mut rows: Vec<(Vec<f64>, RowKind, f64)> = Vec::new();

        // Convert each original constraint by expanding every source variable
        // into nonnegative decision columns.
        for c in &problem.constraints {
            let mut row = vec![0.0; n_decision];
            let mut adjusted_rhs = c.rhs;
            for &(idx, coef) in &c.coeffs {
                let transform = &transforms[idx];
                let shift = checked_mul(
                    coef,
                    transform.constant,
                    format!(
                        "constraint '{}' RHS shift overflows while normalizing variable {}",
                        c.name, idx
                    ),
                )?;
                adjusted_rhs = checked_sub(
                    adjusted_rhs,
                    shift,
                    format!(
                        "constraint '{}' RHS overflows during variable normalization",
                        c.name
                    ),
                )?;
                for &(col, term_coef) in &transform.terms {
                    let term = checked_mul(
                        coef,
                        term_coef,
                        format!(
                            "constraint '{}' coefficient overflows while expanding variable {}",
                            c.name, idx
                        ),
                    )?;
                    row[col] = checked_add(
                        row[col],
                        term,
                        format!(
                            "constraint '{}' coefficient overflows after duplicate accumulation",
                            c.name
                        ),
                    )?;
                }
            }
            rows.push((row, c.kind, adjusted_rhs));
        }

        // Encode finite upper bounds on lower-shifted variables as extra `<=`
        // rows. Upper-only variables use `x = upper - y`, so `y >= 0` already
        // captures the bound and no row is needed.
        for (col, ub_shifted) in upper_bound_rows {
            let mut row = vec![0.0; n_decision];
            row[col] = 1.0;
            rows.push((row, RowKind::Le, ub_shifted));
        }

        // Ensure all b >= 0 by negating rows if needed.
        for (row, kind, rhs) in &mut rows {
            if *rhs < 0.0 {
                for a in row.iter_mut() {
                    *a = -*a;
                }
                *rhs = -*rhs;
                *kind = match *kind {
                    RowKind::Le => RowKind::Ge,
                    RowKind::Ge => RowKind::Le,
                    RowKind::Eq => RowKind::Eq,
                };
            }
        }

        let m = rows.len();

        // Allocate slack / surplus / artificial columns.
        let mut cols_slack: Vec<(usize, f64)> = Vec::new(); // (row_idx, coef)
        let mut cols_surplus: Vec<usize> = Vec::new();
        let mut cols_artif: Vec<usize> = Vec::new();

        for (row_idx, (_, kind, _)) in rows.iter().enumerate() {
            match kind {
                RowKind::Le => cols_slack.push((row_idx, 1.0)),
                RowKind::Ge => {
                    cols_surplus.push(row_idx);
                    cols_artif.push(row_idx);
                }
                RowKind::Eq => cols_artif.push(row_idx),
            }
        }

        let n_total = n_decision + cols_slack.len() + cols_surplus.len() + cols_artif.len();
        let mut a = vec![vec![0.0; n_total]; m];
        let mut b = vec![0.0; m];
        let mut c = vec![0.0; n_total];

        // Objective: maximize +c . x for Max, maximize -c . x for Min. The
        // additive constant introduced by source-variable normalization is
        // irrelevant to pivoting and the final objective is recomputed from
        // reconstructed source values.
        let sense_sign = match problem.sense {
            Sense::Min => -1.0,
            Sense::Max => 1.0,
        };
        for (source_var, transform) in problem.variables.iter().zip(transforms.iter()) {
            for &(col, term_coef) in &transform.terms {
                let term = checked_mul(
                    checked_mul(
                        source_var.obj_coeff,
                        term_coef,
                        format!(
                            "objective coefficient for variable '{}' overflows during normalization",
                            source_var.name
                        ),
                    )?,
                    sense_sign,
                    format!(
                        "objective coefficient for variable '{}' overflows while applying sense",
                        source_var.name
                    ),
                )?;
                c[col] = checked_add(
                    c[col],
                    term,
                    format!(
                        "objective coefficient for variable '{}' overflows after accumulation",
                        source_var.name
                    ),
                )?;
            }
        }

        // Copy original rows.
        for (r, (row, _, rhs)) in rows.iter().enumerate() {
            for (j, val) in row.iter().enumerate() {
                a[r][j] = *val;
            }
            b[r] = *rhs;
        }

        // Slack columns (coefficient +1).
        let mut next = n_decision;
        let mut slack_cols: Vec<usize> = Vec::new();
        for (row_idx, coef) in &cols_slack {
            a[*row_idx][next] = *coef;
            slack_cols.push(next);
            next += 1;
        }

        // Surplus columns (coefficient -1).
        for row_idx in &cols_surplus {
            a[*row_idx][next] = -1.0;
            next += 1;
        }

        // Artificial columns (coefficient +1). They receive their objective
        // only during phase I; phase II forbids them from entering.
        let mut artif_cols: Vec<usize> = Vec::new();
        for row_idx in &cols_artif {
            a[*row_idx][next] = 1.0;
            artif_cols.push(next);
            next += 1;
        }

        // Initial basis: slack if `<=`, artificial for `>=` and `=`.
        let mut basis = vec![0usize; m];
        let mut slack_iter = slack_cols.iter();
        let mut artif_iter = artif_cols.iter();
        for (row_idx, (_, kind, _)) in rows.iter().enumerate() {
            basis[row_idx] = match kind {
                RowKind::Le => *slack_iter.next().expect("slack"),
                RowKind::Ge | RowKind::Eq => *artif_iter.next().expect("artif"),
            };
        }

        Ok(Self {
            c,
            a,
            b,
            basis,
            artificials: artif_cols,
            n_decision,
            transforms,
        })
    }

    fn into_tableau(self) -> Tableau {
        // Basis membership mask, maintained across pivots. Testing
        // `basis.contains(&j)` inside the reduced-cost column loop is an
        // O(m) scan per column (O(m*n) per iteration just for membership);
        // the mask makes it O(1) per column, which is what makes
        // thousand-row/thousand-column problems practical.
        let mut in_basis = vec![false; self.c.len()];
        for &b in &self.basis {
            in_basis[b] = true;
        }
        let mut artificial_col = vec![false; self.c.len()];
        for &col in &self.artificials {
            artificial_col[col] = true;
        }
        Tableau {
            c: self.c,
            a: self.a,
            b: self.b,
            basis: self.basis,
            in_basis,
            artificials: self.artificials,
            artificial_col,
            n_decision: self.n_decision,
            transforms: self.transforms,
        }
    }
}

fn validate_problem(problem: &Problem) -> Result<(), LpError> {
    if !problem.obj_constant.is_finite() {
        return Err(LpError::InvalidInstance(
            "objective constant is not finite".into(),
        ));
    }
    for (idx, var) in problem.variables.iter().enumerate() {
        if !var.obj_coeff.is_finite() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' (index {idx}) has a non-finite objective coefficient",
                var.name
            )));
        }
        if var.lower.is_nan() || var.upper.is_nan() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' (index {idx}) has a NaN bound",
                var.name
            )));
        }
        if var.lower.is_infinite() && var.lower.is_sign_positive() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' (index {idx}) has +inf lower bound",
                var.name
            )));
        }
        if var.upper.is_infinite() && var.upper.is_sign_negative() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' (index {idx}) has -inf upper bound",
                var.name
            )));
        }
    }
    for (row_idx, constraint) in problem.constraints.iter().enumerate() {
        if !constraint.rhs.is_finite() {
            return Err(LpError::InvalidInstance(format!(
                "constraint '{}' (index {row_idx}) has a non-finite RHS",
                constraint.name
            )));
        }
        for &(var_idx, coef) in &constraint.coeffs {
            if var_idx >= problem.variables.len() {
                return Err(LpError::InvalidInstance(format!(
                    "constraint '{}' (index {row_idx}) references missing variable index {var_idx}",
                    constraint.name
                )));
            }
            if !coef.is_finite() {
                return Err(LpError::InvalidInstance(format!(
                    "constraint '{}' (index {row_idx}) has a non-finite coefficient",
                    constraint.name
                )));
            }
        }
    }
    Ok(())
}

fn checked_add(a: f64, b: f64, context: String) -> Result<f64, LpError> {
    finite_standard_value(a + b, context)
}

fn checked_sub(a: f64, b: f64, context: String) -> Result<f64, LpError> {
    finite_standard_value(a - b, context)
}

fn checked_mul(a: f64, b: f64, context: String) -> Result<f64, LpError> {
    finite_standard_value(a * b, context)
}

fn finite_standard_value(value: f64, context: String) -> Result<f64, LpError> {
    if value.is_finite() {
        Ok(value)
    } else {
        Err(LpError::InvalidInstance(context))
    }
}

fn finite_simplex_value(value: f64, context: String) -> Result<f64, LpError> {
    if value.is_finite() {
        Ok(value)
    } else {
        Err(LpError::NumericalFailure(context))
    }
}

fn build_var_transforms(
    problem: &Problem,
) -> Result<(Vec<VarTransform>, Vec<(usize, f64)>, usize), LpError> {
    let mut transforms = Vec::with_capacity(problem.variables.len());
    let mut upper_bound_rows = Vec::new();
    let mut next_col = 0usize;

    for var in &problem.variables {
        let (lower, upper) = effective_bounds(var);
        if lower.is_nan() || upper.is_nan() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' has a NaN bound",
                var.name
            )));
        }
        if lower.is_infinite() && lower.is_sign_positive() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' has +inf lower bound",
                var.name
            )));
        }
        if upper.is_infinite() && upper.is_sign_negative() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' has -inf upper bound",
                var.name
            )));
        }
        if lower.is_finite() && upper.is_finite() && upper < lower {
            return Err(LpError::Infeasible);
        }

        if lower.is_finite() {
            let col = next_col;
            next_col += 1;
            if upper.is_finite() {
                upper_bound_rows.push((
                    col,
                    checked_sub(
                        upper,
                        lower,
                        format!("variable '{}' finite bound width overflows", var.name),
                    )?,
                ));
            }
            transforms.push(VarTransform {
                constant: shift_floor(lower),
                terms: vec![(col, 1.0)],
            });
        } else if upper.is_finite() {
            let col = next_col;
            next_col += 1;
            transforms.push(VarTransform {
                constant: upper,
                terms: vec![(col, -1.0)],
            });
        } else {
            let pos = next_col;
            let neg = next_col + 1;
            next_col += 2;
            transforms.push(VarTransform {
                constant: 0.0,
                terms: vec![(pos, 1.0), (neg, -1.0)],
            });
        }
    }

    Ok((transforms, upper_bound_rows, next_col))
}

// ----- Tableau simplex -------------------------------------------------------

pub(crate) struct Tableau {
    c: Vec<f64>,
    a: Vec<Vec<f64>>,
    b: Vec<f64>,
    basis: Vec<usize>,
    /// `in_basis[j]` iff column `j` appears in `basis` (O(1) membership).
    in_basis: Vec<bool>,
    artificials: Vec<usize>,
    /// `artificial_col[j]` iff column `j` was introduced only for phase I.
    artificial_col: Vec<bool>,
    n_decision: usize,
    transforms: Vec<VarTransform>,
}

/// How a bounded simplex run ended (short of an error).
enum RunEnd {
    /// No entering column: the current basis is optimal.
    Optimal,
    /// The iteration budget or the stop callback cut the run short; the
    /// tableau holds the last (feasible) iterate.
    Budget,
}

impl Tableau {
    fn run(&mut self) -> Result<(), LpError> {
        let mut remaining = MAX_ITERS;
        match self.run_phase1(&mut remaining, &|| false)? {
            RunEnd::Optimal => {}
            RunEnd::Budget => return Err(LpError::IterationLimit),
        }
        match self.run_phase2(&mut remaining, &|| false)? {
            RunEnd::Optimal => Ok(()),
            RunEnd::Budget => Err(LpError::IterationLimit),
        }
    }

    fn run_phase1(
        &mut self,
        remaining: &mut usize,
        should_stop: &dyn Fn() -> bool,
    ) -> Result<RunEnd, LpError> {
        self.validate_well_formed("before phase I")?;
        if self.artificials.is_empty() {
            return Ok(RunEnd::Optimal);
        }
        let original_c = std::mem::take(&mut self.c);
        self.c = vec![0.0; original_c.len()];
        for &col in &self.artificials {
            self.c[col] = -1.0;
        }
        let result = self.run_bounded(remaining, should_stop, false);
        self.c = original_c;
        let end = result?;
        match end {
            RunEnd::Budget => Ok(RunEnd::Budget),
            RunEnd::Optimal if self.is_infeasible() => Err(LpError::Infeasible),
            RunEnd::Optimal => Ok(RunEnd::Optimal),
        }
    }

    fn run_phase2(
        &mut self,
        remaining: &mut usize,
        should_stop: &dyn Fn() -> bool,
    ) -> Result<RunEnd, LpError> {
        self.validate_well_formed("before phase II")?;
        if matches!(
            self.remove_artificial_basics(remaining, should_stop)?,
            RunEnd::Budget
        ) {
            return Ok(RunEnd::Budget);
        }
        self.run_bounded(remaining, should_stop, true)
    }

    fn remove_artificial_basics(
        &mut self,
        remaining: &mut usize,
        should_stop: &dyn Fn() -> bool,
    ) -> Result<RunEnd, LpError> {
        for row in 0..self.basis.len() {
            if should_stop() {
                return Ok(RunEnd::Budget);
            }
            if !self.artificial_col[self.basis[row]] {
                continue;
            }
            if self.b[row].abs() > 1e-6 {
                return Err(LpError::Infeasible);
            }
            let entering = (0..self.c.len()).find(|&col| {
                !self.in_basis[col] && !self.artificial_col[col] && self.a[row][col].abs() > EPS
            });
            if let Some(col) = entering {
                if *remaining == 0 {
                    return Ok(RunEnd::Budget);
                }
                self.pivot(row, col)?;
                *remaining -= 1;
            }
        }
        Ok(RunEnd::Optimal)
    }

    fn run_bounded(
        &mut self,
        remaining: &mut usize,
        should_stop: &dyn Fn() -> bool,
        forbid_artificial_entering: bool,
    ) -> Result<RunEnd, LpError> {
        self.validate_well_formed("before simplex loop")?;
        loop {
            if should_stop() {
                return Ok(RunEnd::Budget);
            }
            // Compute reduced costs = c_j - c_B * B^-1 * A_j. Because the
            // tableau is stored as plain A (not B^-1 * A), we perform Gaussian
            // reduction incrementally: when we pivot, we update A and b so that
            // the basis columns always form the identity within the tableau.
            // Thus the reduced cost is `c_j - sum_i c_{basis[i]} * A[i][j]`.
            let m = self.a.len();
            let n = self.c.len();
            let c_b: Vec<f64> = self.basis.iter().map(|&b| self.c[b]).collect();

            let mut entering = None;
            for j in 0..n {
                if self.in_basis[j] || (forbid_artificial_entering && self.artificial_col[j]) {
                    continue;
                }
                let mut reduced = self.c[j];
                for (i, cb) in c_b.iter().enumerate().take(m) {
                    let priced = finite_simplex_value(
                        cb * self.a[i][j],
                        format!("reduced-cost product for row {i}, column {j} is not finite"),
                    )?;
                    reduced = finite_simplex_value(
                        reduced - priced,
                        format!("reduced cost for column {j} is not finite"),
                    )?;
                }
                if reduced > EPS {
                    entering = Some(j);
                    break;
                }
            }

            let Some(j) = entering else {
                return Ok(RunEnd::Optimal);
            };
            if *remaining == 0 {
                return Ok(RunEnd::Budget);
            }

            // Min-ratio test.
            let mut leaving: Option<usize> = None;
            let mut min_ratio = f64::INFINITY;
            for i in 0..m {
                let aij = self.a[i][j];
                if aij > EPS {
                    let ratio = finite_simplex_value(
                        self.b[i] / aij,
                        format!("ratio test value for row {i}, column {j} is not finite"),
                    )?;
                    let better_ratio = ratio < min_ratio - EPS;
                    let bland_tie = equality_violation(ratio, min_ratio) <= EPS
                        && leaving.map_or(true, |best| self.basis[i] < self.basis[best]);
                    if better_ratio || bland_tie {
                        min_ratio = ratio;
                        leaving = Some(i);
                    }
                }
            }

            let Some(row) = leaving else {
                return Err(LpError::Unbounded);
            };

            self.pivot(row, j)?;
            *remaining -= 1;
        }
    }

    fn pivot(&mut self, row: usize, col: usize) -> Result<(), LpError> {
        if row >= self.a.len() || col >= self.c.len() {
            return Err(LpError::NumericalFailure(format!(
                "pivot index out of range: row {row}, column {col}"
            )));
        }
        self.validate_well_formed("before pivot")?;
        let piv = self.a[row][col];
        if !piv.is_finite() || piv.abs() < EPS {
            return Err(LpError::NumericalFailure(format!(
                "invalid pivot at row {row}, column {col}: {piv}"
            )));
        }
        let n = self.c.len();
        let mut next_a = self.a.clone();
        let mut next_b = self.b.clone();
        for k in 0..n {
            next_a[row][k] = finite_simplex_value(
                self.a[row][k] / piv,
                format!("pivot row {row} column {k} normalization is not finite"),
            )?;
        }
        next_b[row] = finite_simplex_value(
            self.b[row] / piv,
            format!("pivot row {row} RHS normalization is not finite"),
        )?;
        let m = self.a.len();
        for i in 0..m {
            if i == row {
                continue;
            }
            let factor = self.a[i][col];
            if !factor.is_finite() {
                return Err(LpError::NumericalFailure(format!(
                    "pivot elimination factor at row {i}, column {col} is not finite"
                )));
            }
            if factor.abs() < EPS {
                continue;
            }
            for k in 0..n {
                let delta = finite_simplex_value(
                    factor * next_a[row][k],
                    format!("pivot elimination product at row {i}, column {k} is not finite"),
                )?;
                next_a[i][k] = finite_simplex_value(
                    self.a[i][k] - delta,
                    format!("pivot elimination update at row {i}, column {k} is not finite"),
                )?;
            }
            let rhs_delta = finite_simplex_value(
                factor * next_b[row],
                format!("pivot elimination RHS product at row {i} is not finite"),
            )?;
            next_b[i] = finite_simplex_value(
                self.b[i] - rhs_delta,
                format!("pivot elimination RHS update at row {i} is not finite"),
            )?;
        }
        self.a = next_a;
        self.b = next_b;
        self.in_basis[self.basis[row]] = false;
        self.in_basis[col] = true;
        self.basis[row] = col;
        self.validate_well_formed("after pivot")?;
        Ok(())
    }

    fn validate_well_formed(&self, context: &str) -> Result<(), LpError> {
        let m = self.a.len();
        let n = self.c.len();
        if self.b.len() != m || self.basis.len() != m {
            return Err(LpError::NumericalFailure(format!(
                "{context}: tableau row dimensions are inconsistent"
            )));
        }
        if self.in_basis.len() != n || self.artificial_col.len() != n {
            return Err(LpError::NumericalFailure(format!(
                "{context}: tableau column dimensions are inconsistent"
            )));
        }
        if self.n_decision > n {
            return Err(LpError::NumericalFailure(format!(
                "{context}: decision column count exceeds tableau width"
            )));
        }
        if self.c.iter().any(|v| !v.is_finite()) || self.b.iter().any(|v| !v.is_finite()) {
            return Err(LpError::NumericalFailure(format!(
                "{context}: tableau has non-finite objective or RHS entries"
            )));
        }
        for (row, coeffs) in self.a.iter().enumerate() {
            if coeffs.len() != n {
                return Err(LpError::NumericalFailure(format!(
                    "{context}: row {row} has width {}, expected {n}",
                    coeffs.len()
                )));
            }
            if coeffs.iter().any(|v| !v.is_finite()) {
                return Err(LpError::NumericalFailure(format!(
                    "{context}: row {row} has a non-finite coefficient"
                )));
            }
        }

        let mut expected_in_basis = vec![false; n];
        for (row, &col) in self.basis.iter().enumerate() {
            if col >= n {
                return Err(LpError::NumericalFailure(format!(
                    "{context}: basis row {row} references missing column {col}"
                )));
            }
            if expected_in_basis[col] {
                return Err(LpError::NumericalFailure(format!(
                    "{context}: duplicate basis column {col}"
                )));
            }
            expected_in_basis[col] = true;
        }
        if self.in_basis != expected_in_basis {
            return Err(LpError::NumericalFailure(format!(
                "{context}: basis membership cache is stale"
            )));
        }

        let mut expected_artificial = vec![false; n];
        for &col in &self.artificials {
            if col >= n {
                return Err(LpError::NumericalFailure(format!(
                    "{context}: artificial column {col} is out of range"
                )));
            }
            if expected_artificial[col] {
                return Err(LpError::NumericalFailure(format!(
                    "{context}: duplicate artificial column {col}"
                )));
            }
            expected_artificial[col] = true;
        }
        if self.artificial_col != expected_artificial {
            return Err(LpError::NumericalFailure(format!(
                "{context}: artificial-column cache is stale"
            )));
        }

        for (var, transform) in self.transforms.iter().enumerate() {
            if !transform.constant.is_finite() {
                return Err(LpError::NumericalFailure(format!(
                    "{context}: transform {var} has a non-finite constant"
                )));
            }
            for &(col, coef) in &transform.terms {
                if col >= self.n_decision {
                    return Err(LpError::NumericalFailure(format!(
                        "{context}: transform {var} references missing decision column {col}"
                    )));
                }
                if !coef.is_finite() {
                    return Err(LpError::NumericalFailure(format!(
                        "{context}: transform {var} has a non-finite coefficient"
                    )));
                }
            }
        }

        Ok(())
    }

    /// Returns true if any artificial variable remains in the basis with a
    /// strictly positive value, which means phase I could not drive the
    /// artificials to zero. This is the standard infeasibility test.
    pub(crate) fn is_infeasible(&self) -> bool {
        for (i, &b) in self.basis.iter().enumerate() {
            if self.artificials.contains(&b) && self.b[i] > 1e-6 {
                return true;
            }
        }
        false
    }

    fn extract_values(&self) -> Vec<f64> {
        let mut decision_values = vec![0.0; self.n_decision];
        for (i, &col) in self.basis.iter().enumerate() {
            if col < self.n_decision {
                decision_values[col] = self.b[i];
            }
        }
        self.transforms
            .iter()
            .map(|transform| transform.value(&decision_values))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::model::{Constraint, RowKind, Sense, Solution, VarKind, Variable};

    use super::*;

    fn make_problem() -> Problem {
        // min x + y subject to x + y >= 4, x + 3y >= 6, x,y >= 0.
        // Optimal at intersection: 3x + y = 6 - ... solving by hand -> x=3,y=1, obj=4.
        let mut p = Problem::new();
        p.sense = Sense::Min;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: Default::default(),
        });
        p.variables.push(Variable {
            name: "y".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: Default::default(),
        });
        p.constraints.push(Constraint {
            name: "c1".into(),
            kind: RowKind::Ge,
            coeffs: vec![(0, 1.0), (1, 1.0)],
            rhs: 4.0,
        });
        p.constraints.push(Constraint {
            name: "c2".into(),
            kind: RowKind::Ge,
            coeffs: vec![(0, 1.0), (1, 3.0)],
            rhs: 6.0,
        });
        p
    }

    #[test]
    fn test_solve_min_basic() {
        let p = make_problem();
        let sol = solve_lp_relaxation(&p).expect("solve");
        // Optimal: x=3, y=1, obj=4. Accept some numeric slack.
        assert!(
            (sol.objective - 4.0).abs() < 1e-4,
            "obj = {}",
            sol.objective
        );
    }

    #[test]
    fn test_solve_max_le() {
        // max 3x + 2y s.t. x + y <= 4, x <= 2, y <= 3, x,y >= 0
        // Optimal: x=2, y=2, obj=10.
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 3.0,
            lower: 0.0,
            upper: 2.0,
            kind: Default::default(),
        });
        p.variables.push(Variable {
            name: "y".into(),
            obj_coeff: 2.0,
            lower: 0.0,
            upper: 3.0,
            kind: Default::default(),
        });
        p.constraints.push(Constraint {
            name: "c".into(),
            kind: RowKind::Le,
            coeffs: vec![(0, 1.0), (1, 1.0)],
            rhs: 4.0,
        });
        let sol = solve_lp_relaxation(&p).expect("solve");
        assert!(
            (sol.objective - 10.0).abs() < 1e-4,
            "obj = {}",
            sol.objective
        );
    }

    #[test]
    fn test_solve_finite_negative_lower_is_not_double_shifted() {
        let mut p = Problem::new();
        p.sense = Sense::Min;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: -5.0,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        let sol = solve_lp_relaxation(&p).expect("solve");
        assert!(
            (sol.objective + 5.0).abs() < 1e-4,
            "obj = {}",
            sol.objective
        );
        assert!((sol.values[0] + 5.0).abs() < 1e-4, "x = {}", sol.values[0]);
    }

    #[test]
    fn test_solve_free_variable_split() {
        let mut p = Problem::new();
        p.sense = Sense::Min;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: f64::NEG_INFINITY,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "lower".into(),
            kind: RowKind::Ge,
            coeffs: vec![(0, 1.0)],
            rhs: -2.0,
        });
        let sol = solve_lp_relaxation(&p).expect("solve");
        assert!(
            (sol.objective + 2.0).abs() < 1e-4,
            "obj = {}",
            sol.objective
        );
        assert!((sol.values[0] + 2.0).abs() < 1e-4, "x = {}", sol.values[0]);
    }

    #[test]
    fn test_solve_upper_only_variable() {
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: f64::NEG_INFINITY,
            upper: 3.0,
            kind: VarKind::Continuous,
        });
        let sol = solve_lp_relaxation(&p).expect("solve");
        assert!(
            (sol.objective - 3.0).abs() < 1e-4,
            "obj = {}",
            sol.objective
        );
        assert!((sol.values[0] - 3.0).abs() < 1e-4, "x = {}", sol.values[0]);
    }

    #[test]
    fn test_binary_kind_imposes_unit_interval_in_relaxation() {
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: f64::NEG_INFINITY,
            upper: f64::INFINITY,
            kind: VarKind::Binary,
        });

        let sol = solve_lp_relaxation(&p).expect("binary relaxation is bounded by [0, 1]");
        assert!(
            (sol.objective - 1.0).abs() < 1e-9,
            "obj = {}",
            sol.objective
        );
        assert!((sol.values[0] - 1.0).abs() < 1e-9, "x = {}", sol.values[0]);
    }

    #[test]
    fn test_binary_kind_intersects_declared_bounds() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: 2.0,
            upper: f64::INFINITY,
            kind: VarKind::Binary,
        });

        assert!(matches!(solve_lp_relaxation(&p), Err(LpError::Infeasible)));
    }

    #[test]
    fn test_binary_kind_does_not_mask_nan_declared_bounds() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: f64::NAN,
            upper: f64::INFINITY,
            kind: VarKind::Binary,
        });
        assert!(matches!(
            solve_lp_relaxation(&p),
            Err(LpError::InvalidInstance(_))
        ));

        p.variables[0].lower = 0.0;
        p.variables[0].upper = f64::NAN;
        assert!(matches!(
            solve_lp_relaxation_budgeted(&p, MAX_ITERS, &|| false),
            Err(LpError::InvalidInstance(_))
        ));
    }

    #[test]
    fn test_phase_one_is_independent_of_objective_scale() {
        let mut p = Problem::new();
        p.sense = Sense::Min;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1e12,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "lower".into(),
            kind: RowKind::Ge,
            coeffs: vec![(0, 1.0)],
            rhs: 1.0,
        });

        let sol = solve_lp_relaxation(&p).expect("phase I must prove feasibility first");
        assert!((sol.values[0] - 1.0).abs() < 1e-8, "x = {}", sol.values[0]);
        assert!(
            (sol.objective - 1e12).abs() <= 1e3,
            "obj = {}",
            sol.objective
        );
    }

    #[test]
    fn test_phase_two_pivots_zero_artificial_basic_out_before_optimization() {
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "fix".into(),
            kind: RowKind::Eq,
            coeffs: vec![(0, -1.0)],
            rhs: 0.0,
        });

        let sol = solve_lp_relaxation(&p).expect("zero artificial basic must not fake unbounded");
        assert!(sol.objective.abs() < 1e-9, "obj = {}", sol.objective);
        assert!(sol.values[0].abs() < 1e-9, "x = {}", sol.values[0]);

        let truncated =
            solve_lp_relaxation_budgeted(&p, 0, &|| false).expect("initial point is feasible");
        assert!(!truncated.optimal);
        assert!(truncated.solution.values[0].abs() < 1e-9);
    }

    #[test]
    fn test_solution_validation_rejects_infeasible_candidate() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: 10.0,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "lower-row".into(),
            kind: RowKind::Ge,
            coeffs: vec![(0, 1.0)],
            rhs: 2.0,
        });

        let bad = Solution {
            objective: 1.0,
            values: vec![1.0],
        };
        assert!(matches!(
            validate_solution(&p, &bad),
            Err(LpError::NumericalFailure(_))
        ));

        let good = solve_lp_relaxation(&p).expect("solver output validates");
        validate_solution(&p, &good).expect("valid solver output");

        let bad_objective = Solution {
            objective: good.objective + 1.0,
            values: good.values,
        };
        assert!(matches!(
            validate_solution(&p, &bad_objective),
            Err(LpError::NumericalFailure(_))
        ));
    }

    #[test]
    fn test_solution_validation_rejects_malformed_model_references() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: 0.0,
            upper: 1.0,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "missing-var".into(),
            kind: RowKind::Le,
            coeffs: vec![(1, 1.0)],
            rhs: 1.0,
        });

        let candidate = Solution {
            objective: 0.0,
            values: vec![0.0],
        };
        assert!(matches!(
            validate_solution(&p, &candidate),
            Err(LpError::NumericalFailure(_))
        ));
    }

    #[test]
    fn test_solution_validation_rejects_extreme_finite_violation() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: f64::NEG_INFINITY,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "extreme-eq".into(),
            kind: RowKind::Eq,
            coeffs: vec![(0, 1.0)],
            rhs: -f64::MAX,
        });

        let bad = Solution {
            objective: 0.0,
            values: vec![f64::MAX],
        };
        assert!(matches!(
            validate_solution(&p, &bad),
            Err(LpError::NumericalFailure(_))
        ));
    }

    #[test]
    fn test_rejects_non_finite_objective_data() {
        let mut p = Problem::new();
        p.obj_constant = f64::NAN;
        assert!(matches!(
            solve_lp_relaxation(&p),
            Err(LpError::InvalidInstance(_))
        ));

        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: f64::INFINITY,
            lower: 0.0,
            upper: 1.0,
            kind: VarKind::Continuous,
        });
        assert!(matches!(
            solve_lp_relaxation_budgeted(&p, MAX_ITERS, &|| false),
            Err(LpError::InvalidInstance(_))
        ));
    }

    #[test]
    fn test_rejects_malformed_constraint_data_without_panicking() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: 1.0,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "bad-rhs".into(),
            kind: RowKind::Le,
            coeffs: vec![(0, 1.0)],
            rhs: f64::NAN,
        });
        assert!(matches!(
            solve_lp_relaxation(&p),
            Err(LpError::InvalidInstance(_))
        ));

        p.constraints[0] = Constraint {
            name: "bad-coeff".into(),
            kind: RowKind::Le,
            coeffs: vec![(0, f64::NEG_INFINITY)],
            rhs: 1.0,
        };
        assert!(matches!(
            solve_lp_relaxation(&p),
            Err(LpError::InvalidInstance(_))
        ));

        p.constraints[0] = Constraint {
            name: "missing-var".into(),
            kind: RowKind::Le,
            coeffs: vec![(1, 1.0)],
            rhs: 1.0,
        };
        assert!(matches!(
            solve_lp_relaxation_budgeted(&p, MAX_ITERS, &|| false),
            Err(LpError::InvalidInstance(_))
        ));
    }

    #[test]
    fn test_rejects_tiny_inconsistent_variable_bounds() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: 1.0,
            upper: f64::from_bits(1.0f64.to_bits() - 1),
            kind: VarKind::Continuous,
        });

        assert!(matches!(solve_lp_relaxation(&p), Err(LpError::Infeasible)));
    }

    #[test]
    fn test_standardization_rejects_finite_overflow_before_solving() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: -f64::MAX,
            upper: f64::MAX,
            kind: VarKind::Continuous,
        });
        assert!(matches!(
            solve_lp_relaxation(&p),
            Err(LpError::InvalidInstance(_))
        ));

        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: f64::MAX,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "shift-overflow".into(),
            kind: RowKind::Le,
            coeffs: vec![(0, -2.0)],
            rhs: 0.0,
        });
        assert!(matches!(
            solve_lp_relaxation_budgeted(&p, MAX_ITERS, &|| false),
            Err(LpError::InvalidInstance(_))
        ));
    }

    #[test]
    fn test_pivot_arithmetic_overflow_fails_closed() {
        let mut tableau = Tableau {
            c: vec![1.0, 0.0, 0.0, 0.0],
            a: vec![vec![1.0, f64::MAX, 1.0, 0.0], vec![2.0, 0.0, 0.0, 1.0]],
            b: vec![1.0, 1.0],
            basis: vec![2, 3],
            in_basis: vec![false, false, true, true],
            artificials: Vec::new(),
            artificial_col: vec![false; 4],
            n_decision: 2,
            transforms: Vec::new(),
        };
        let a_before = tableau.a.clone();
        let b_before = tableau.b.clone();
        let basis_before = tableau.basis.clone();
        let in_basis_before = tableau.in_basis.clone();

        assert!(matches!(
            tableau.pivot(0, 0),
            Err(LpError::NumericalFailure(_))
        ));
        assert_eq!(tableau.a, a_before, "failed pivot mutated tableau rows");
        assert_eq!(tableau.b, b_before, "failed pivot mutated tableau RHS");
        assert_eq!(tableau.basis, basis_before, "failed pivot mutated basis");
        assert_eq!(
            tableau.in_basis, in_basis_before,
            "failed pivot mutated basis cache"
        );
    }

    #[test]
    fn test_malformed_tableau_fails_closed_before_simplex_loop() {
        let mut tableau = Tableau {
            c: vec![1.0, 0.0],
            a: vec![vec![1.0, 1.0]],
            b: vec![1.0],
            basis: vec![1],
            in_basis: vec![false, false],
            artificials: Vec::new(),
            artificial_col: vec![false; 2],
            n_decision: 1,
            transforms: Vec::new(),
        };
        let mut remaining = 1;

        assert!(matches!(
            tableau.run_bounded(&mut remaining, &|| false, true),
            Err(LpError::NumericalFailure(_))
        ));
    }

    #[test]
    fn test_pivot_rejects_out_of_range_indices_without_panicking() {
        let mut tableau = Tableau {
            c: vec![1.0, 0.0],
            a: vec![vec![1.0, 1.0]],
            b: vec![1.0],
            basis: vec![1],
            in_basis: vec![false, true],
            artificials: Vec::new(),
            artificial_col: vec![false; 2],
            n_decision: 1,
            transforms: Vec::new(),
        };

        assert!(matches!(
            tableau.pivot(1, 0),
            Err(LpError::NumericalFailure(_))
        ));
        assert!(matches!(
            tableau.pivot(0, 2),
            Err(LpError::NumericalFailure(_))
        ));
    }

    #[test]
    fn test_pivot_rejects_stale_basis_cache_before_membership_write() {
        let mut tableau = Tableau {
            c: vec![1.0, 0.0],
            a: vec![vec![1.0, 1.0]],
            b: vec![1.0],
            basis: vec![2],
            in_basis: vec![false, false],
            artificials: Vec::new(),
            artificial_col: vec![false; 2],
            n_decision: 1,
            transforms: Vec::new(),
        };

        assert!(matches!(
            tableau.pivot(0, 0),
            Err(LpError::NumericalFailure(_))
        ));
    }

    #[test]
    fn test_simplex_uses_bland_entering_column_order() {
        let mut tableau = Tableau {
            c: vec![1.0, 2.0, 0.0, 0.0],
            a: vec![vec![1.0, 0.0, 1.0, 0.0], vec![0.0, 1.0, 0.0, 1.0]],
            b: vec![1.0, 1.0],
            basis: vec![2, 3],
            in_basis: vec![false, false, true, true],
            artificials: Vec::new(),
            artificial_col: vec![false; 4],
            n_decision: 2,
            transforms: Vec::new(),
        };
        let mut remaining = 1;

        assert!(matches!(
            tableau.run_bounded(&mut remaining, &|| false, true),
            Ok(RunEnd::Budget)
        ));
        assert_eq!(tableau.basis[0], 0, "column 0 must enter before column 1");
    }

    #[test]
    fn test_simplex_uses_bland_leaving_tie_order() {
        let mut tableau = Tableau {
            c: vec![1.0, 0.0, 0.0, 0.0],
            a: vec![vec![1.0, 0.0, 0.0, 1.0], vec![1.0, 0.0, 1.0, 0.0]],
            b: vec![1.0, 1.0],
            basis: vec![3, 2],
            in_basis: vec![false, false, true, true],
            artificials: Vec::new(),
            artificial_col: vec![false; 4],
            n_decision: 2,
            transforms: Vec::new(),
        };
        let mut remaining = 1;

        let _ = tableau
            .run_bounded(&mut remaining, &|| false, true)
            .expect("one pivot succeeds");
        assert_eq!(
            tableau.basis[1], 0,
            "tied ratio test must leave the smallest-index basic column"
        );
    }

    /// Build a packing LP shaped like the MaxSAT lp-boost dual:
    /// max sum(y) subject to all-`<=` unit-coefficient rows, y >= 0.
    fn packing_problem(rows: &[(Vec<usize>, f64)], n_vars: usize) -> Problem {
        let mut p = Problem::new();
        p.sense = Sense::Max;
        for i in 0..n_vars {
            p.variables.push(Variable {
                name: format!("y{i}"),
                obj_coeff: 1.0,
                lower: 0.0,
                upper: f64::INFINITY,
                kind: VarKind::Continuous,
            });
        }
        for (i, (cols, rhs)) in rows.iter().enumerate() {
            p.constraints.push(Constraint {
                name: format!("r{i}"),
                kind: RowKind::Le,
                coeffs: cols.iter().map(|&c| (c, 1.0)).collect(),
                rhs: *rhs,
            });
        }
        p
    }

    #[test]
    fn test_budgeted_matches_full_solve_on_phase_one_problem() {
        let p = make_problem();
        let r = solve_lp_relaxation_budgeted(&p, MAX_ITERS, &|| false).expect("solve");
        assert!(r.optimal);
        assert!(
            (r.solution.objective - 4.0).abs() < 1e-4,
            "obj = {}",
            r.solution.objective
        );
    }

    #[test]
    fn test_budgeted_zero_iters_le_problem_returns_feasible_iterate() {
        // All-`<=` rows with nonnegative rhs: the slack basis is feasible, so
        // even a zero-iteration run must return a feasible (all-zero) point.
        let p = packing_problem(&[(vec![0, 1], 5.0), (vec![1, 2], 3.0)], 3);
        let r = solve_lp_relaxation_budgeted(&p, 0, &|| false).expect("solve");
        assert!(!r.optimal);
        assert!(r.solution.objective.abs() < 1e-9);
        for v in &r.solution.values {
            assert!(v.abs() < 1e-9);
        }
    }

    #[test]
    fn test_budgeted_zero_iters_phase_one_problem_errors() {
        // `>=` rows need artificials driven out before any iterate is
        // feasible; a zero-iteration budget has no feasible point to return.
        let p = make_problem();
        let r = solve_lp_relaxation_budgeted(&p, 0, &|| false);
        assert!(matches!(r, Err(LpError::IterationLimit)), "got {r:?}");
    }

    #[test]
    fn test_budgeted_should_stop_returns_feasible_iterate() {
        let p = packing_problem(&[(vec![0, 1], 5.0), (vec![1, 2], 3.0)], 3);
        let r = solve_lp_relaxation_budgeted(&p, MAX_ITERS, &|| true).expect("solve");
        assert!(!r.optimal);
        // The truncated objective of a Max problem never exceeds the optimum.
        let opt = solve_lp_relaxation(&p).expect("solve").objective;
        assert!(r.solution.objective <= opt + 1e-9);
    }

    /// Randomized packing LPs: the budgeted entry point with an ample budget
    /// must agree with the one-shot solver, every truncated iterate must be
    /// feasible, and its objective must never exceed the optimum. Also
    /// exercises the in_basis membership mask on non-trivial pivot sequences.
    #[test]
    fn test_budgeted_randomized_packing_agrees_and_truncates_feasibly() {
        let mut state = 0x9E3779B97F4A7C15u64;
        let mut next = move || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state >> 33
        };
        for _case in 0..50 {
            let n_vars = 2 + (next() % 12) as usize;
            let n_rows = 1 + (next() % 12) as usize;
            let mut rows: Vec<(Vec<usize>, f64)> = Vec::new();
            for _ in 0..n_rows {
                let len = 1 + (next() % 4) as usize;
                let mut cols: Vec<usize> = (0..len)
                    .map(|_| (next() % n_vars as u64) as usize)
                    .collect();
                cols.sort_unstable();
                cols.dedup();
                rows.push((cols, (1 + next() % 50) as f64));
            }
            // Every variable must appear in some row or the Max problem is
            // unbounded; pack strays into a fresh row.
            let mut covered = vec![false; n_vars];
            for (cols, _) in &rows {
                for &c in cols {
                    covered[c] = true;
                }
            }
            let strays: Vec<usize> = (0..n_vars).filter(|&v| !covered[v]).collect();
            if !strays.is_empty() {
                rows.push((strays, (1 + next() % 50) as f64));
            }
            let p = packing_problem(&rows, n_vars);

            let full = solve_lp_relaxation(&p).expect("full solve");
            let ample = solve_lp_relaxation_budgeted(&p, MAX_ITERS, &|| false).expect("budgeted");
            assert!(ample.optimal);
            assert!(
                (ample.solution.objective - full.objective).abs() < 1e-6,
                "budgeted {} != full {}",
                ample.solution.objective,
                full.objective
            );

            // Truncate at every prefix length and check feasibility.
            for iters in 0..4 {
                let r = solve_lp_relaxation_budgeted(&p, iters, &|| false).expect("truncated");
                assert!(r.solution.objective <= full.objective + 1e-6);
                for c in &p.constraints {
                    let lhs: f64 = c
                        .coeffs
                        .iter()
                        .map(|&(v, coef)| coef * r.solution.values[v])
                        .sum();
                    assert!(
                        lhs <= c.rhs + 1e-6,
                        "truncated iterate violates row: {lhs} > {}",
                        c.rhs
                    );
                }
                for &v in &r.solution.values {
                    assert!(v >= -1e-9);
                }
            }
        }
    }
}
