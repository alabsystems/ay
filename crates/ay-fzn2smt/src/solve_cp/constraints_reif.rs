// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Reified constraint translation using Big-M encoding.
//
// For r ↔ (sum(c_i * x_i) ≤ d):
//   Forward:  sum(c_i * x_i) ≤ d + M_fwd * (1 - r)
//   Backward: sum(c_i * x_i) ≥ d + 1 - M_bwd * r
//
// M_fwd = max(sum) - d, M_bwd = d + 1 - min(sum)
// max(sum) = sum(max(c_i*x_i)), min(sum) = sum(min(c_i*x_i))

use crate::error::{Fzn2smtError, Result};
use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::numeric::{encoding_i64, linear_encoding_overflow};
use super::CpContext;

impl CpContext {
    /// Compute exact expression extrema in a wider representation. Returning a
    /// typed error on i128 accumulation overflow is conservative; saturating an
    /// extremum can make a Big-M coefficient too small and admit false models.
    fn linear_extrema(
        &self,
        coeffs: &[i64],
        vars: &[IntVarId],
        context: &str,
    ) -> Result<(i128, i128)> {
        if coeffs.len() != vars.len() {
            return Err(Fzn2smtError::LinearArrayLengthMismatch {
                constraint: context.to_string(),
                coefficients: coeffs.len(),
                variables: vars.len(),
            });
        }

        let mut max_sum = 0i128;
        let mut min_sum = 0i128;
        for (&c, &v) in coeffs.iter().zip(vars.iter()) {
            let (lb, ub) = self.get_var_bounds(v);
            let c = i128::from(c);
            let lb = i128::from(lb);
            let ub = i128::from(ub);
            let (min_term, max_term) = if c >= 0 {
                (c * lb, c * ub)
            } else {
                (c * ub, c * lb)
            };
            min_sum = min_sum
                .checked_add(min_term)
                .ok_or_else(|| linear_encoding_overflow(context))?;
            max_sum = max_sum
                .checked_add(max_term)
                .ok_or_else(|| linear_encoding_overflow(context))?;
        }
        Ok((min_sum, max_sum))
    }

    fn forward_big_m(
        &self,
        coeffs: &[i64],
        vars: &[IntVarId],
        rhs: i64,
        context: &str,
    ) -> Result<(i64, i64)> {
        let (_, max_sum) = self.linear_extrema(coeffs, vars, context)?;
        let rhs = i128::from(rhs);
        let m = max_sum
            .checked_sub(rhs)
            .ok_or_else(|| linear_encoding_overflow(context))?
            .max(0);
        // rhs + M is exactly max(max_sum, rhs), avoiding an unnecessary
        // potentially overflowing addition.
        Ok((
            encoding_i64(m, context)?,
            encoding_i64(max_sum.max(rhs), context)?,
        ))
    }

    fn backward_big_m(
        &self,
        coeffs: &[i64],
        vars: &[IntVarId],
        rhs: i64,
        context: &str,
    ) -> Result<(i64, i64)> {
        let (min_sum, _) = self.linear_extrema(coeffs, vars, context)?;
        let strict_rhs = i128::from(rhs) + 1;
        let m = strict_rhs
            .checked_sub(min_sum)
            .ok_or_else(|| linear_encoding_overflow(context))?
            .max(0);
        Ok((
            encoding_i64(m, context)?,
            encoding_i64(-strict_rhs, context)?,
        ))
    }

    /// Encode r ↔ (sum(c_i * x_i) ≤ d) using Big-M.
    pub(super) fn add_reif_le(
        &mut self,
        coeffs: &[i64],
        vars: &[IntVarId],
        rhs: i64,
        r: IntVarId,
        context: &str,
    ) -> Result<()> {
        let (m_fwd, forward_rhs) = self.forward_big_m(coeffs, vars, rhs, context)?;
        let (m_bwd, backward_rhs) = self.backward_big_m(coeffs, vars, rhs, context)?;
        let neg_coeffs = checked_negated_coefficients(coeffs, context)?;

        // Forward: sum(c_i * x_i) + M_fwd * r ≤ rhs + M_fwd
        // i.e., sum(c_i * x_i) ≤ rhs + M_fwd * (1 - r)
        {
            let mut c = coeffs.to_vec();
            c.push(m_fwd);
            let mut v = vars.to_vec();
            v.push(r);
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: c,
                vars: v,
                rhs: forward_rhs,
            });
        }

        // Backward: -sum(c_i * x_i) - M_bwd * r ≤ -(rhs + 1)
        // i.e., sum(c_i * x_i) ≥ rhs + 1 - M_bwd * r
        // When r=0: sum ≥ rhs + 1 (constraint is violated)
        // When r=1: sum ≥ rhs + 1 - M_bwd (trivially true)
        {
            let mut c = neg_coeffs;
            c.push(-m_bwd);
            let mut v = vars.to_vec();
            v.push(r);
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: c,
                vars: v,
                rhs: backward_rhs,
            });
        }
        Ok(())
    }

    /// Encode r ↔ (sum(c_i * x_i) = d) using Big-M.
    /// Decomposed as: r ↔ (sum ≤ d ∧ sum ≥ d).
    pub(super) fn add_reif_eq(
        &mut self,
        coeffs: &[i64],
        vars: &[IntVarId],
        rhs: i64,
        r: IntVarId,
        context: &str,
    ) -> Result<()> {
        // Validate both orientations before mutating the model.
        let neg_coeffs = checked_negated_coefficients(coeffs, context)?;
        let neg_rhs = rhs
            .checked_neg()
            .ok_or_else(|| linear_encoding_overflow(context))?;
        self.forward_big_m(coeffs, vars, rhs, context)?;
        self.backward_big_m(coeffs, vars, rhs, context)?;
        self.forward_big_m(&neg_coeffs, vars, neg_rhs, context)?;
        self.backward_big_m(&neg_coeffs, vars, neg_rhs, context)?;

        // Introduce two auxiliary booleans: r1 ↔ (sum ≤ d), r2 ↔ (sum ≥ d)
        // Then r = r1 ∧ r2
        let r1 = self.engine.new_bool_var(None);
        let r2 = self.engine.new_bool_var(None);
        self.var_bounds.insert(r1, (0, 1));
        self.var_bounds.insert(r2, (0, 1));

        // r1 ↔ (sum ≤ d)
        self.add_reif_le(coeffs, vars, rhs, r1, context)?;

        // r2 ↔ (-sum ≤ -d) i.e. (sum ≥ d)
        self.add_reif_le(&neg_coeffs, vars, neg_rhs, r2, context)?;

        // r = r1 ∧ r2: r ≤ r1, r ≤ r2, r1 + r2 - r ≤ 1
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![r, r1],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![r, r2],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1, -1],
            vars: vec![r1, r2, r],
            rhs: 1,
        });
        Ok(())
    }

    /// Encode r → (sum(c_i * x_i) ≤ d) (half-reification / implication).
    fn add_imp_le(
        &mut self,
        coeffs: &[i64],
        vars: &[IntVarId],
        rhs: i64,
        r: IntVarId,
        context: &str,
    ) -> Result<()> {
        let (m_fwd, forward_rhs) = self.forward_big_m(coeffs, vars, rhs, context)?;
        let mut c = coeffs.to_vec();
        c.push(m_fwd);
        let mut v = vars.to_vec();
        v.push(r);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: c,
            vars: v,
            rhs: forward_rhs,
        });
        Ok(())
    }

    /// int_eq_reif(a, b, r) etc.
    pub(super) fn translate_int_comparison_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;

        match c.id.as_str() {
            "int_le_reif" | "bool_le_reif" => {
                // r ↔ (a ≤ b) → r ↔ (a - b ≤ 0)
                self.add_reif_le(&[1, -1], &[a, b], 0, r, &c.id)?;
            }
            "int_lt_reif" | "bool_lt_reif" => {
                // r ↔ (a < b) → r ↔ (a - b ≤ -1)
                self.add_reif_le(&[1, -1], &[a, b], -1, r, &c.id)?;
            }
            "int_ge_reif" | "bool_ge_reif" => {
                // r ↔ (a ≥ b) → r ↔ (b - a ≤ 0)
                self.add_reif_le(&[-1, 1], &[a, b], 0, r, &c.id)?;
            }
            "int_gt_reif" | "bool_gt_reif" => {
                // r ↔ (a > b) → r ↔ (b - a ≤ -1)
                self.add_reif_le(&[-1, 1], &[a, b], -1, r, &c.id)?;
            }
            "int_eq_reif" => {
                // r ↔ (a = b) → r ↔ (a - b = 0)
                self.add_reif_eq(&[1, -1], &[a, b], 0, r, &c.id)?;
            }
            "int_ne_reif" => {
                // r ↔ (a ≠ b) → not_r ↔ (a = b), r = 1 - not_r
                let not_r = self.engine.new_bool_var(None);
                self.var_bounds.insert(not_r, (0, 1));
                // not_r = 1 - r
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, 1],
                    vars: vec![r, not_r],
                    rhs: 1,
                });
                self.add_reif_eq(&[1, -1], &[a, b], 0, not_r, &c.id)?;
            }
            _ => return Err(invalid_constraint_route(c, "reified integer comparison")),
        }
        Ok(())
    }

    /// int_lin_le_reif(coeffs, vars, rhs, r) etc.
    pub(super) fn translate_int_linear_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        self.validate_linear_array_lengths(c, coeffs.len(), vars.len())?;
        let rhs = self.resolve_const_int(&c.args[2])?;
        let r = self.resolve_var(&c.args[3])?;

        match c.id.as_str() {
            "int_lin_le_reif" | "bool_lin_le_reif" => {
                self.add_reif_le(&coeffs, &vars, rhs, r, &c.id)?;
            }
            "int_lin_eq_reif" | "bool_lin_eq_reif" => {
                self.add_reif_eq(&coeffs, &vars, rhs, r, &c.id)?;
            }
            _ => return Err(invalid_constraint_route(c, "reified integer linear")),
        }
        Ok(())
    }

    /// bool_eq_reif(a, b, r): r ↔ (a = b)
    pub(super) fn translate_bool_eq_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        self.add_reif_eq(&[1, -1], &[a, b], 0, r, &c.id)?;
        Ok(())
    }

    /// bool_not_reif(a, b, r): r ↔ (a ≠ b)
    /// Decomposed as: not_r ↔ (a = b), r + not_r = 1
    pub(super) fn translate_bool_not_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;

        let not_r = self.engine.new_bool_var(None);
        self.var_bounds.insert(not_r, (0, 1));
        // r + not_r = 1
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, 1],
            vars: vec![r, not_r],
            rhs: 1,
        });
        // not_r ↔ (a = b)
        self.add_reif_eq(&[1, -1], &[a, b], 0, not_r, &c.id)?;
        Ok(())
    }

    /// int_lin_ne_reif(coeffs, vars, rhs, r): r ↔ (sum ≠ rhs)
    /// Decomposed as: not_r ↔ (sum = rhs), r + not_r = 1
    pub(super) fn translate_int_linear_ne_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        self.validate_linear_array_lengths(c, coeffs.len(), vars.len())?;
        let rhs = self.resolve_const_int(&c.args[2])?;
        let r = self.resolve_var(&c.args[3])?;

        let not_r = self.engine.new_bool_var(None);
        self.var_bounds.insert(not_r, (0, 1));
        // r + not_r = 1
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, 1],
            vars: vec![r, not_r],
            rhs: 1,
        });
        // not_r ↔ (sum = rhs)
        self.add_reif_eq(&coeffs, &vars, rhs, not_r, &c.id)?;
        Ok(())
    }

    /// int_lin_ne_imp(coeffs, vars, rhs, r): r → (sum ≠ rhs)
    /// Encoded as: create eq_ind ↔ (sum = rhs), then r + eq_ind ≤ 1
    pub(super) fn translate_int_linear_ne_imp(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        self.validate_linear_array_lengths(c, coeffs.len(), vars.len())?;
        let rhs = self.resolve_const_int(&c.args[2])?;
        let r = self.resolve_var(&c.args[3])?;

        let eq_ind = self.engine.new_bool_var(None);
        self.var_bounds.insert(eq_ind, (0, 1));
        // eq_ind ↔ (sum = rhs)
        self.add_reif_eq(&coeffs, &vars, rhs, eq_ind, &c.id)?;
        // r + eq_ind ≤ 1 (both can't be true: if r=1, sum ≠ rhs)
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1],
            vars: vec![r, eq_ind],
            rhs: 1,
        });
        Ok(())
    }

    /// bool_and_reif(a, b, r): r ↔ (a ∧ b)
    pub(super) fn translate_bool_and_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        // r ≤ a, r ≤ b, a + b - r ≤ 1
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![r, a],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![r, b],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1, -1],
            vars: vec![a, b, r],
            rhs: 1,
        });
        Ok(())
    }

    /// bool_or_reif(a, b, r): r ↔ (a ∨ b)
    pub(super) fn translate_bool_or_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        // a ≤ r, b ≤ r, r - a - b ≤ 0
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![a, r],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![b, r],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -1],
            vars: vec![r, a, b],
            rhs: 0,
        });
        Ok(())
    }

    /// bool_clause_reif(pos, neg, r): r ↔ (pos1 ∨ ... ∨ ¬neg1 ∨ ...)
    pub(super) fn translate_bool_clause_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let pos = self.resolve_var_array(&c.args[0])?;
        let neg = self.resolve_var_array(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        let neg_len = i64::try_from(neg.len()).map_err(|_| linear_encoding_overflow(&c.id))?;

        // The clause is sum(pos) + sum(1-neg) >= 1. With L negative
        // literals, its equivalent <= form is
        // -sum(pos) + sum(neg) <= L - 1.
        let mut coeffs: Vec<i64> = pos.iter().map(|_| -1i64).collect();
        coeffs.extend(neg.iter().map(|_| 1i64));
        let mut vars = pos;
        vars.extend(neg);
        self.add_reif_le(&coeffs, &vars, neg_len - 1, r, &c.id)?;
        Ok(())
    }

    /// Half-reification: r → constraint.
    pub(super) fn translate_int_comparison_imp(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;

        match c.id.as_str() {
            "int_le_imp" | "bool_le_imp" => {
                self.add_imp_le(&[1, -1], &[a, b], 0, r, &c.id)?;
            }
            "int_lt_imp" | "bool_lt_imp" => {
                self.add_imp_le(&[1, -1], &[a, b], -1, r, &c.id)?;
            }
            "int_ge_imp" | "bool_ge_imp" => {
                self.add_imp_le(&[-1, 1], &[a, b], 0, r, &c.id)?;
            }
            "int_gt_imp" | "bool_gt_imp" => {
                self.add_imp_le(&[-1, 1], &[a, b], -1, r, &c.id)?;
            }
            "int_eq_imp" => {
                // r → (a = b): r → (a ≤ b) ∧ r → (a ≥ b)
                self.add_imp_le(&[1, -1], &[a, b], 0, r, &c.id)?;
                self.add_imp_le(&[-1, 1], &[a, b], 0, r, &c.id)?;
            }
            "int_ne_imp" => {
                // Split the disjunction into two activation variables. This
                // avoids the old `2*M-1` formulation, which overflowed even
                // when each individual Big-M coefficient was representable.
                let less = self.engine.new_bool_var(None);
                let greater = self.engine.new_bool_var(None);
                self.var_bounds.insert(less, (0, 1));
                self.var_bounds.insert(greater, (0, 1));
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, 1, -1],
                    vars: vec![less, greater, r],
                    rhs: 0,
                });
                self.add_imp_le(&[1, -1], &[a, b], -1, less, &c.id)?;
                self.add_imp_le(&[-1, 1], &[a, b], -1, greater, &c.id)?;
            }
            _ => {
                return Err(invalid_constraint_route(
                    c,
                    "integer comparison implication",
                ))
            }
        }
        Ok(())
    }

    /// Half-reification for linear constraints.
    pub(super) fn translate_int_linear_imp(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        self.validate_linear_array_lengths(c, coeffs.len(), vars.len())?;
        let rhs = self.resolve_const_int(&c.args[2])?;
        let r = self.resolve_var(&c.args[3])?;

        match c.id.as_str() {
            "int_lin_le_imp" | "bool_lin_le_imp" => {
                self.add_imp_le(&coeffs, &vars, rhs, r, &c.id)?;
            }
            "int_lin_eq_imp" | "bool_lin_eq_imp" => {
                // r → (sum = d): r → (sum ≤ d) ∧ r → (sum ≥ d)
                let neg_coeffs = checked_negated_coefficients(&coeffs, &c.id)?;
                let neg_rhs = rhs
                    .checked_neg()
                    .ok_or_else(|| linear_encoding_overflow(&c.id))?;
                self.add_imp_le(&coeffs, &vars, rhs, r, &c.id)?;
                self.add_imp_le(&neg_coeffs, &vars, neg_rhs, r, &c.id)?;
            }
            _ => return Err(invalid_constraint_route(c, "integer linear implication")),
        }
        Ok(())
    }

    /// bool_lt_reif(a, b, r): r ↔ (a < b), where a,b ∈ {0,1}.
    /// a < b iff a=0 ∧ b=1, so r = (1-a) ∧ b.
    /// Linearized: r ≤ b, r ≤ 1-a, r ≥ b-a.
    pub(super) fn translate_bool_lt_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        // r ≤ b
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![r, b],
            rhs: 0,
        });
        // r ≤ 1 - a → r + a ≤ 1
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1],
            vars: vec![r, a],
            rhs: 1,
        });
        // r ≥ b - a → a + r - b ≥ 0
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1, 1, -1],
            vars: vec![a, r, b],
            rhs: 0,
        });
        Ok(())
    }
}

fn invalid_constraint_route(c: &ConstraintItem, translator: &'static str) -> Fzn2smtError {
    Fzn2smtError::InvalidConstraintRoute {
        constraint: c.id.clone(),
        translator,
    }
}

fn checked_negated_coefficients(coeffs: &[i64], context: &str) -> Result<Vec<i64>> {
    coeffs
        .iter()
        .map(|coefficient| {
            coefficient
                .checked_neg()
                .ok_or_else(|| linear_encoding_overflow(context))
        })
        .collect()
}
