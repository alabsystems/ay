// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An in-process MILP lowering onto ay-dpll's typed `Solver`.
//!
//! Binary columns become 0/1 disjunctions and rows become linear inequalities,
//! built as typed terms rather than serialized text. Arithmetic remains exact
//! end-to-end, and results are returned as typed outcomes. The native
//! branch-and-cut engine is the primary integral-model path; this lowering is
//! an exact fallback behind the same session API.
//!
//! Equality-shaped facts are always asserted as inequality PAIRS (`>=` and
//! `<=`), never `=`: the LRA certificate lane fails closed on
//! equality-justified bounds, so keeping the lowering inequality-only keeps
//! future certificate extraction alive.

use ay_dpll::api::{Logic, ModelValue, SolveResult, Solver, SolverConfig, Term};
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::error::MilpError;
use crate::model::{exact, Col, ColKind, Model, Sense};
use crate::opts::SolveOpts;
use crate::outcome::{Outcome, UnknownReason};

/// The lowered model: a live solver plus the column terms.
pub(crate) struct SmtMilp {
    solver: Solver,
    col_terms: Vec<Term>,
    scope_depth: u32,
    /// Set when the model has a column this lane cannot encode, so both entry points
    /// decline instead of answering about a model that is not the caller's.
    unsupported: Option<UnknownReason>,
}

impl SmtMilp {
    /// Lower `model` into a fresh in-process solver.
    pub(crate) fn new(model: &Model, opts: &SolveOpts) -> Result<Self, MilpError> {
        Self::new_with_binary_values(model, opts, None)
    }

    /// Lower one fixed binary assignment into pure QF_LRA. Omitting
    /// `binary_values` retains the ordinary disjunctive 0/1 encoding used for
    /// feasibility checks.
    // Frame size is dominated by the one-shot embedded-solver construction;
    // boxing it would complicate the API for a function called once per solve.
    #[allow(clippy::large_stack_frames)]
    fn new_with_binary_values(
        model: &Model,
        opts: &SolveOpts,
        binary_values: Option<&[bool]>,
    ) -> Result<Self, MilpError> {
        let mut config = SolverConfig::default();
        if let Some(deadline) = opts.effective_deadline(std::time::Instant::now()) {
            config =
                config.with_timeout(deadline.saturating_duration_since(std::time::Instant::now()));
        }
        let mut solver =
            Solver::try_new_with_config(Logic::QfLra, config).map_err(|e| MilpError::Solver {
                message: e.to_string(),
            })?;
        let mut col_terms = Vec::with_capacity(model.num_cols());
        let mut binary_index = 0;
        for i in 0..model.num_cols() {
            let col = Col(i as u32);
            let x = solver.declare_const(&format!("c{i}"), ay_dpll::api::Sort::Real);
            let (lb, ub) = model.col_bounds(col);
            if let Some(lb) = exact(lb) {
                let bound = rational_term(&mut solver, &lb)?;
                let atom = solver.try_ge(x, bound).map_err(|e| MilpError::Solver {
                    message: e.to_string(),
                })?;
                solver
                    .try_assert_term(atom)
                    .map_err(|e| MilpError::Solver {
                        message: e.to_string(),
                    })?;
            }
            if let Some(ub) = exact(ub) {
                let bound = rational_term(&mut solver, &ub)?;
                let atom = solver.try_le(x, bound).map_err(|e| MilpError::Solver {
                    message: e.to_string(),
                })?;
                solver
                    .try_assert_term(atom)
                    .map_err(|e| MilpError::Solver {
                        message: e.to_string(),
                    })?;
            }
            if matches!(model.col_kind(col), ColKind::Binary) {
                let zero = rational_term(&mut solver, &BigRational::zero())?;
                let one = rational_term(&mut solver, &BigRational::one())?;
                if let Some(values) = binary_values {
                    let value = *values.get(binary_index).ok_or_else(|| MilpError::Session {
                        message: "binary assignment has the wrong arity".to_owned(),
                    })?;
                    let fixed = if value { one } else { zero };
                    // Use an inequality pair, as for equality-shaped rows, so
                    // the pure-LRA optimization/certificate path remains live.
                    let lower = solver.try_ge(x, fixed).map_err(|e| MilpError::Solver {
                        message: e.to_string(),
                    })?;
                    let upper = solver.try_le(x, fixed).map_err(|e| MilpError::Solver {
                        message: e.to_string(),
                    })?;
                    solver
                        .try_assert_term(lower)
                        .map_err(|e| MilpError::Solver {
                            message: e.to_string(),
                        })?;
                    solver
                        .try_assert_term(upper)
                        .map_err(|e| MilpError::Solver {
                            message: e.to_string(),
                        })?;
                } else {
                    let is_zero = solver.try_eq(x, zero).map_err(|e| MilpError::Solver {
                        message: e.to_string(),
                    })?;
                    let is_one = solver.try_eq(x, one).map_err(|e| MilpError::Solver {
                        message: e.to_string(),
                    })?;
                    let disj = solver
                        .try_or(is_zero, is_one)
                        .map_err(|e| MilpError::Solver {
                            message: e.to_string(),
                        })?;
                    solver
                        .try_assert_term(disj)
                        .map_err(|e| MilpError::Solver {
                            message: e.to_string(),
                        })?;
                }
                binary_index += 1;
            }
            col_terms.push(x);
        }
        if let Some(values) = binary_values {
            if values.len() != binary_index {
                return Err(MilpError::Session {
                    message: "binary assignment has the wrong arity".to_owned(),
                });
            }
        }
        let mut lane = Self {
            solver,
            col_terms,
            scope_depth: 0,
            unsupported: unsupported_kind(model),
        };
        for r in 0..model.num_rows() {
            let (coeffs, lb, ub) = model.row(crate::model::Row(r as u32));
            lane.assert_row_facts(coeffs, lb, ub)?;
        }
        Ok(lane)
    }

    /// Assert `lb <= coeffs·x <= ub` as up to two inequality atoms.
    pub(crate) fn assert_row_facts(
        &mut self,
        coeffs: &[(u32, f64)],
        lb: f64,
        ub: f64,
    ) -> Result<(), MilpError> {
        let expr = self.linear_term(coeffs)?;
        if let Some(lb) = exact(lb) {
            let bound = rational_term(&mut self.solver, &lb)?;
            let atom = self
                .solver
                .try_ge(expr, bound)
                .map_err(|e| MilpError::Solver {
                    message: e.to_string(),
                })?;
            self.solver
                .try_assert_term(atom)
                .map_err(|e| MilpError::Solver {
                    message: e.to_string(),
                })?;
        }
        if let Some(ub) = exact(ub) {
            let bound = rational_term(&mut self.solver, &ub)?;
            let atom = self
                .solver
                .try_le(expr, bound)
                .map_err(|e| MilpError::Solver {
                    message: e.to_string(),
                })?;
            self.solver
                .try_assert_term(atom)
                .map_err(|e| MilpError::Solver {
                    message: e.to_string(),
                })?;
        }
        Ok(())
    }

    /// Assert `x_col == value` as an inequality pair at the current scope.
    pub(crate) fn fix_col(&mut self, col: Col, value: f64) -> Result<(), MilpError> {
        self.assert_row_facts(&[(col.0, 1.0)], value, value)
    }

    pub(crate) fn push(&mut self) -> Result<(), MilpError> {
        self.solver.try_push().map_err(|e| MilpError::Solver {
            message: e.to_string(),
        })?;
        self.scope_depth += 1;
        Ok(())
    }

    pub(crate) fn pop(&mut self) -> Result<(), MilpError> {
        if self.scope_depth == 0 {
            return Err(MilpError::Session {
                message: "pop at scope depth 0".to_owned(),
            });
        }
        self.solver.try_pop().map_err(|e| MilpError::Solver {
            message: e.to_string(),
        })?;
        self.scope_depth -= 1;
        Ok(())
    }

    /// Feasibility check (no objective).
    pub(crate) fn check_feasible(&mut self, opts: &SolveOpts) -> Result<Outcome, MilpError> {
        if let Some(reason) = self.unsupported.clone() {
            return Ok(Outcome::Unknown { reason });
        }
        let deadline = opts.effective_deadline(std::time::Instant::now());
        if deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
            return Ok(Outcome::Unknown {
                reason: UnknownReason::Timeout,
            });
        }
        self.solver.set_timeout(
            deadline.map(|limit| limit.saturating_duration_since(std::time::Instant::now())),
        );
        let verdict = self.solver.check_sat();
        match verdict.result() {
            SolveResult::Sat => {
                if verdict.accept_for_consumer().is_err() {
                    // SAT whose model validation did not run is not a verdict
                    // we surface (fail closed).
                    return Ok(Outcome::Unknown {
                        reason: UnknownReason::SolverIncomplete {
                            detail: "sat without validated model".to_owned(),
                        },
                    });
                }
                let model_values = self.extract_values()?;
                Ok(Outcome::Feasible {
                    model_values,
                    incumbent_only: false,
                    dual_bound: None,
                })
            }
            SolveResult::Unsat(_) => Ok(Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            }),
            SolveResult::Unknown => Ok(self.unknown_outcome()),
            _ => Ok(self.unknown_outcome()),
        }
    }

    /// Optimize `coeffs·x` in `sense` (offset handled by the caller).
    /// Objective registration is scoped inside a push/pop so repeated calls
    /// never stack objectives.
    pub(crate) fn optimize(
        &mut self,
        model: &Model,
        opts: &SolveOpts,
        coeffs: &[(u32, f64)],
        sense: Sense,
    ) -> Result<Outcome, MilpError> {
        if let Some(reason) = self.unsupported.clone() {
            let _ = model;
            return Ok(Outcome::Unknown { reason });
        }
        let deadline = opts.effective_deadline(std::time::Instant::now());
        if deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
            return Ok(Outcome::Unknown {
                reason: UnknownReason::Timeout,
            });
        }
        self.solver.set_timeout(
            deadline.map(|limit| limit.saturating_duration_since(std::time::Instant::now())),
        );
        let direct = self.optimize_relaxation(coeffs, sense)?;
        if !matches!(direct, Outcome::Unknown { .. }) {
            self.validate_optimal_outcome(model, coeffs, &direct)?;
            return Ok(direct);
        }

        // A Boolean 0/1 disjunction makes ay-dpll's standalone LRA optimizer
        // inapplicable. Its generic Real fallback is deliberately bounded and
        // may therefore answer unknown. Close that completeness gap at the
        // MILP boundary by exhaustively optimizing each fixed binary branch.
        self.optimize_binary_branches(model, opts, coeffs, sense, deadline)
    }

    /// Optimize one pure-QF_LRA problem. The caller must not use this directly
    /// as a complete MILP procedure when disjunctive binary facts are present.
    fn optimize_relaxation(
        &mut self,
        coeffs: &[(u32, f64)],
        sense: Sense,
    ) -> Result<Outcome, MilpError> {
        let obj = self.linear_term(coeffs)?;
        self.push()?;
        let result = self.optimize_scoped(obj, sense);
        self.pop()?;
        result
    }

    /// Exhaust the relevant 0/1 assignments, optimizing the independent
    /// continuous QF_LRA branch for each assignment. Finite branch optima plus
    /// exhaustive coverage are a complete MILP optimality proof; an unknown
    /// branch keeps the aggregate result unknown.
    fn optimize_binary_branches(
        &self,
        model: &Model,
        opts: &SolveOpts,
        coeffs: &[(u32, f64)],
        sense: Sense,
        deadline: Option<std::time::Instant>,
    ) -> Result<Outcome, MilpError> {
        let binary_cols: Vec<Col> = (0..model.num_cols())
            .map(|i| Col(i as u32))
            .filter(|&col| matches!(model.col_kind(col), ColKind::Binary))
            .collect();

        let mut values = Vec::with_capacity(binary_cols.len());
        let mut branch_positions = Vec::new();
        for (position, &col) in binary_cols.iter().enumerate() {
            let (lb, ub) = model.col_bounds(col);
            let allows_zero = lb <= 0.0 && 0.0 <= ub;
            let allows_one = lb <= 1.0 && 1.0 <= ub;
            if !allows_zero && !allows_one {
                return Ok(Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                });
            }
            values.push(!allows_zero);

            // An unused binary cannot affect feasibility or the objective;
            // fixing its first admissible value avoids an exponential blow-up
            // from routing-only/dummy columns.
            let relevant = coeffs.iter().any(|&(c, _)| c == col.0)
                || (0..model.num_rows()).any(|r| {
                    model
                        .row(crate::model::Row(r as u32))
                        .0
                        .iter()
                        .any(|&(c, _)| c == col.0)
                });
            if relevant && allows_zero && allows_one {
                branch_positions.push(position);
            }
        }

        let max_nodes = crate::exact::Budget::default_iters(model.num_cols() + model.num_rows());
        let mut nodes = 0_u64;
        let mut best: Option<(BigRational, Vec<BigRational>)> = None;
        let mut first_unknown = None;

        loop {
            if nodes >= max_nodes {
                first_unknown.get_or_insert(UnknownReason::IterationLimit);
                break;
            }
            if deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
                first_unknown.get_or_insert(UnknownReason::Timeout);
                break;
            }
            nodes += 1;

            // Preserve one absolute per-check deadline across every branch;
            // otherwise `time_limit` would restart for each fresh solver.
            let mut branch_opts = opts.clone();
            branch_opts.deadline = deadline;
            branch_opts.time_limit = None;
            let mut branch = Self::new_with_binary_values(model, &branch_opts, Some(&values))?;
            match branch.optimize_relaxation(coeffs, sense)? {
                Outcome::Optimal {
                    value,
                    model_values,
                    ..
                } => {
                    self.validate_optimal_point(model, coeffs, &value, &model_values)?;
                    let replace = best.as_ref().is_none_or(|(incumbent, _)| match sense {
                        Sense::Minimize => value < *incumbent,
                        Sense::Maximize => value > *incumbent,
                    });
                    if replace {
                        best = Some((value, model_values));
                    }
                }
                Outcome::Infeasible { .. } => {}
                Outcome::Unbounded => return Ok(Outcome::Unbounded),
                Outcome::Unknown { reason } => {
                    first_unknown.get_or_insert(reason);
                }
                other => {
                    first_unknown.get_or_insert(UnknownReason::SolverIncomplete {
                        detail: format!("unexpected branch outcome: {other:?}"),
                    });
                }
            }

            let mut advanced = false;
            for &position in branch_positions.iter().rev() {
                if values[position] {
                    values[position] = false;
                } else {
                    values[position] = true;
                    advanced = true;
                    break;
                }
            }
            if !advanced {
                break;
            }
        }

        if let Some(reason) = first_unknown {
            return Ok(Outcome::Unknown { reason });
        }
        Ok(match best {
            Some((value, model_values)) => Outcome::Optimal {
                value,
                model_values,
                cert: None,
            },
            None => Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            },
        })
    }

    fn validate_optimal_outcome(
        &self,
        model: &Model,
        coeffs: &[(u32, f64)],
        outcome: &Outcome,
    ) -> Result<(), MilpError> {
        if let Outcome::Optimal {
            value,
            model_values,
            ..
        } = outcome
        {
            self.validate_optimal_point(model, coeffs, value, model_values)?;
        }
        Ok(())
    }

    /// Independently check the adapter boundary: solver model arity,
    /// MILP feasibility/integrality, and attainment of the claimed pure linear
    /// objective. The session layer adds any constant offset afterward.
    fn validate_optimal_point(
        &self,
        model: &Model,
        coeffs: &[(u32, f64)],
        value: &BigRational,
        model_values: &[BigRational],
    ) -> Result<(), MilpError> {
        if model_values.len() != model.num_cols() {
            return Err(MilpError::Solver {
                message: format!(
                    "optimizer model has {} values for {} columns",
                    model_values.len(),
                    model.num_cols()
                ),
            });
        }
        if let Err(violation) = model.check_point(model_values) {
            return Err(MilpError::Solver {
                message: format!("optimizer returned an invalid point: {violation:?}"),
            });
        }
        let mut attained = BigRational::zero();
        for &(col, coefficient) in coeffs {
            attained += exact(coefficient).expect("validated objective coefficient")
                * &model_values[col as usize];
        }
        if attained != *value {
            return Err(MilpError::Solver {
                message: format!(
                    "optimizer model attains {attained}, but reports objective {value}"
                ),
            });
        }
        Ok(())
    }

    fn optimize_scoped(&mut self, obj: Term, sense: Sense) -> Result<Outcome, MilpError> {
        let idx = match sense {
            Sense::Minimize => self.solver.minimize(obj),
            Sense::Maximize => self.solver.maximize(obj),
        };
        let verdict = self.solver.optimize_check();
        match verdict.result() {
            SolveResult::Sat => {
                if verdict.accept_for_consumer().is_err() {
                    return Ok(Outcome::Unknown {
                        reason: UnknownReason::SolverIncomplete {
                            detail: "sat without validated model".to_owned(),
                        },
                    });
                }
                match self.solver.get_objective_value(idx) {
                    Some(ay_dpll::api::ObjectiveValue::Finite(v)) => {
                        let model_values = self.extract_values()?;
                        Ok(Outcome::Optimal {
                            value: v,
                            model_values,
                            cert: None,
                        })
                    }
                    Some(_) => Ok(Outcome::Unbounded),
                    // Post-R1 contract: no proven optimum is `unknown`,
                    // never a crawl position.
                    None => Ok(Outcome::Unknown {
                        reason: UnknownReason::SolverIncomplete {
                            detail: "no proven optimum".to_owned(),
                        },
                    }),
                }
            }
            SolveResult::Unsat(_) => Ok(Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            }),
            SolveResult::Unknown => Ok(self.unknown_outcome()),
            _ => Ok(self.unknown_outcome()),
        }
    }

    fn unknown_outcome(&self) -> Outcome {
        let reason = match self.solver.unknown_reason() {
            Some(r) => map_unknown(&r),
            None => UnknownReason::SolverIncomplete {
                detail: "solver answered unknown".to_owned(),
            },
        };
        Outcome::Unknown { reason }
    }

    fn extract_values(&mut self) -> Result<Vec<BigRational>, MilpError> {
        let mut out = Vec::with_capacity(self.col_terms.len());
        for term in &self.col_terms {
            match self.solver.value(*term) {
                Some(ModelValue::Real(r)) => out.push(r),
                Some(ModelValue::Int(i)) => out.push(BigRational::from_integer(i)),
                other => {
                    return Err(MilpError::Solver {
                        message: format!("model value unavailable: {other:?}"),
                    })
                }
            }
        }
        Ok(out)
    }

    /// Build `Σ coeffs·x` as a term. An empty sum is the constant 0.
    fn linear_term(&mut self, coeffs: &[(u32, f64)]) -> Result<Term, MilpError> {
        let mut parts = Vec::with_capacity(coeffs.len());
        for &(c, a) in coeffs {
            let x = *self
                .col_terms
                .get(c as usize)
                .ok_or_else(|| MilpError::Session {
                    message: format!("column {c} out of range"),
                })?;
            if a == 1.0 {
                parts.push(x);
                continue;
            }
            let a = exact(a).ok_or_else(|| MilpError::Session {
                message: "non-finite coefficient".to_owned(),
            })?;
            let coeff = rational_term(&mut self.solver, &a)?;
            let prod = self
                .solver
                .try_mul(coeff, x)
                .map_err(|e| MilpError::Solver {
                    message: e.to_string(),
                })?;
            parts.push(prod);
        }
        if parts.is_empty() {
            return rational_term(&mut self.solver, &BigRational::zero());
        }
        if parts.len() == 1 {
            return Ok(parts[0]);
        }
        self.solver
            .try_add_many(&parts)
            .map_err(|e| MilpError::Solver {
                message: e.to_string(),
            })
    }
}

/// An exact rational constant term.
fn rational_term(solver: &mut Solver, r: &BigRational) -> Result<Term, MilpError> {
    solver
        .try_rational_const_bigint(r.numer(), r.denom())
        .map_err(|e| MilpError::Solver {
            message: e.to_string(),
        })
}

/// Conservative mapping from ay-dpll's unknown classification.
fn map_unknown(reason: &ay_dpll::UnknownReason) -> UnknownReason {
    match reason {
        ay_dpll::UnknownReason::Timeout => UnknownReason::Timeout,
        ay_dpll::UnknownReason::MemoryLimit | ay_dpll::UnknownReason::ResourceLimit => {
            UnknownReason::MemoryLimit
        }
        ay_dpll::UnknownReason::Interrupted => UnknownReason::Interrupted,
        other => UnknownReason::SolverIncomplete {
            detail: format!("{other:?}"),
        },
    }
}

/// Why this lane cannot take the model, if it cannot.
///
/// The lane models a binary column as the 0/1 disjunction it is and enumerates over those
/// branches; every other column it hands to QF_LRA as a Real. A general integer column has no
/// such encoding here, and handing one to LRA silently DROPS its integrality -- the lane would
/// then report a fractional point as the optimum. Declining is the only honest answer; the
/// native branch-and-bound lane takes these models.
fn unsupported_kind(model: &Model) -> Option<UnknownReason> {
    (0..model.num_cols())
        .map(|i| Col(i as u32))
        .any(|col| matches!(model.col_kind(col), ColKind::Integer))
        .then(|| UnknownReason::SolverIncomplete {
            detail: "the smt lane does not encode general integer columns".to_owned(),
        })
}
