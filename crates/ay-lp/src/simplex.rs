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
//! Approach: tableau-based primal simplex with the Big-M method.
//!
//! 1. Normalize variables into nonnegative columns: finite-lower variables use
//!    `x_i = lower_i + y_i`, upper-only variables use `x_i = upper_i - y_i`,
//!    and free variables split as `x_i = x_i^+ - x_i^-`.
//! 2. Add slack variables to convert `<=` to equality, surplus + artificial
//!    to convert `>=` and `=`.
//! 3. Maximize `-M * sum(artificials) + sum(obj_coef * x)` (for Min, we
//!    maximize the negated objective so the tableau always maximizes).
//! 4. Pivot with Bland's rule until optimal or unbounded.
//!
//! Upper bounds are encoded as extra `<=` rows. This doubles the constraint
//! count for bounded LPs but is the simplest way to keep the tableau uniform.

use crate::error::LpError;
use crate::model::{Problem, RowKind, Sense, Solution};

const EPS: f64 = 1e-9;
const BIG_M: f64 = 1e7;
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
    let tableau = builder.into_tableau();
    let tableau = tableau.run()?;
    if tableau.is_infeasible() {
        return Err(LpError::Infeasible);
    }
    Ok(extract_solution(&tableau, problem))
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
/// the budget expires while Big-M artificial variables are still basic at a
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
    let end = tableau.run_bounded(max_iters, should_stop)?;
    if tableau.is_infeasible() {
        // Artificials still basic at a positive level: at optimality this is
        // the standard Big-M infeasibility proof; on budget exhaustion the
        // current iterate is not feasible for the original problem, so there
        // is nothing sound to return.
        return Err(match end {
            RunEnd::Optimal => LpError::Infeasible,
            RunEnd::Budget => LpError::IterationLimit,
        });
    }
    Ok(LpRelaxation {
        solution: extract_solution(&tableau, problem),
        optimal: matches!(end, RunEnd::Optimal),
    })
}

/// Reconstruct source-variable values and recompute the objective on the
/// original (unshifted) values for numerical cleanliness.
fn extract_solution(tableau: &Tableau, problem: &Problem) -> Solution {
    let values = tableau.extract_values();
    let mut obj = problem.obj_constant;
    for (i, v) in problem.variables.iter().enumerate() {
        obj += v.obj_coeff * values[i];
    }
    Solution {
        objective: obj,
        values,
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
    /// Indices of artificial columns (for Big-M).
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
        let (transforms, upper_bound_rows, n_decision) = build_var_transforms(problem)?;
        let mut rows: Vec<(Vec<f64>, RowKind, f64)> = Vec::new();

        // Convert each original constraint by expanding every source variable
        // into nonnegative decision columns.
        for c in &problem.constraints {
            let mut row = vec![0.0; n_decision];
            let mut adjusted_rhs = c.rhs;
            for &(idx, coef) in &c.coeffs {
                let transform = &transforms[idx];
                adjusted_rhs -= coef * transform.constant;
                for &(col, term_coef) in &transform.terms {
                    row[col] += coef * term_coef;
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
            rows.push((row, RowKind::Le, ub_shifted.max(0.0)));
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
                c[col] += source_var.obj_coeff * term_coef * sense_sign;
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

        // Artificial columns (coefficient +1) with Big-M penalty.
        let mut artif_cols: Vec<usize> = Vec::new();
        for row_idx in &cols_artif {
            a[*row_idx][next] = 1.0;
            c[next] = -BIG_M;
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
        Tableau {
            c: self.c,
            a: self.a,
            b: self.b,
            basis: self.basis,
            in_basis,
            artificials: self.artificials,
            n_decision: self.n_decision,
            transforms: self.transforms,
        }
    }
}

fn build_var_transforms(
    problem: &Problem,
) -> Result<(Vec<VarTransform>, Vec<(usize, f64)>, usize), LpError> {
    let mut transforms = Vec::with_capacity(problem.variables.len());
    let mut upper_bound_rows = Vec::new();
    let mut next_col = 0usize;

    for var in &problem.variables {
        if var.lower.is_nan() || var.upper.is_nan() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' has a NaN bound",
                var.name
            )));
        }
        if var.lower.is_infinite() && var.lower.is_sign_positive() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' has +inf lower bound",
                var.name
            )));
        }
        if var.upper.is_infinite() && var.upper.is_sign_negative() {
            return Err(LpError::InvalidInstance(format!(
                "variable '{}' has -inf upper bound",
                var.name
            )));
        }
        if var.lower.is_finite() && var.upper.is_finite() && var.upper < var.lower - EPS {
            return Err(LpError::Infeasible);
        }

        if var.lower.is_finite() {
            let col = next_col;
            next_col += 1;
            if var.upper.is_finite() {
                upper_bound_rows.push((col, var.upper - var.lower));
            }
            transforms.push(VarTransform {
                constant: shift_floor(var.lower),
                terms: vec![(col, 1.0)],
            });
        } else if var.upper.is_finite() {
            let col = next_col;
            next_col += 1;
            transforms.push(VarTransform {
                constant: var.upper,
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
    fn run(mut self) -> Result<Self, LpError> {
        match self.run_bounded(MAX_ITERS, &|| false)? {
            RunEnd::Optimal => Ok(self),
            RunEnd::Budget => Err(LpError::IterationLimit),
        }
    }

    fn run_bounded(
        &mut self,
        max_iters: usize,
        should_stop: &dyn Fn() -> bool,
    ) -> Result<RunEnd, LpError> {
        for _ in 0..max_iters {
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
            let mut best = EPS;
            for j in 0..n {
                if self.in_basis[j] {
                    continue;
                }
                let mut reduced = self.c[j];
                for (i, cb) in c_b.iter().enumerate().take(m) {
                    reduced -= cb * self.a[i][j];
                }
                if reduced > best {
                    best = reduced;
                    entering = Some(j);
                }
            }

            let Some(j) = entering else {
                return Ok(RunEnd::Optimal);
            };

            // Min-ratio test.
            let mut leaving: Option<usize> = None;
            let mut min_ratio = f64::INFINITY;
            for i in 0..m {
                let aij = self.a[i][j];
                if aij > EPS {
                    let ratio = self.b[i] / aij;
                    if ratio < min_ratio - EPS {
                        min_ratio = ratio;
                        leaving = Some(i);
                    }
                }
            }

            let Some(row) = leaving else {
                return Err(LpError::Unbounded);
            };

            self.pivot(row, j);
        }
        Ok(RunEnd::Budget)
    }

    fn pivot(&mut self, row: usize, col: usize) {
        let piv = self.a[row][col];
        let n = self.c.len();
        for k in 0..n {
            self.a[row][k] /= piv;
        }
        self.b[row] /= piv;
        let m = self.a.len();
        for i in 0..m {
            if i == row {
                continue;
            }
            let factor = self.a[i][col];
            if factor.abs() < EPS {
                continue;
            }
            for k in 0..n {
                self.a[i][k] -= factor * self.a[row][k];
            }
            self.b[i] -= factor * self.b[row];
        }
        self.in_basis[self.basis[row]] = false;
        self.in_basis[col] = true;
        self.basis[row] = col;
    }

    /// Returns true if any artificial variable remains in the basis with a
    /// strictly positive value, which means the Big-M tableau could not drive
    /// the artificials to zero. This is the standard infeasibility test.
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
    use crate::model::{Constraint, RowKind, Sense, VarKind, Variable};

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
    fn test_budgeted_matches_full_solve_on_bigm_problem() {
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
    fn test_budgeted_zero_iters_bigm_problem_errors() {
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
