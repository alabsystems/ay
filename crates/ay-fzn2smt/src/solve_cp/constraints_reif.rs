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

use crate::error::Result;
use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::CpContext;

impl CpContext {
    /// Compute Big-M values for a linear expression sum(c_i * x_i) ≤ d.
    /// Returns (M_fwd, M_bwd) where:
    ///   M_fwd = max(sum) - d (for forward implication)
    ///   M_bwd = d + 1 - min(sum) (for backward implication)
    fn compute_big_m(&self, coeffs: &[i64], vars: &[IntVarId], rhs: i64) -> (i64, i64) {
        let mut max_sum: i64 = 0;
        let mut min_sum: i64 = 0;
        for (&c, &v) in coeffs.iter().zip(vars.iter()) {
            let (lb, ub) = self.get_var_bounds(v);
            if c >= 0 {
                max_sum = max_sum.saturating_add(c.saturating_mul(ub));
                min_sum = min_sum.saturating_add(c.saturating_mul(lb));
            } else {
                max_sum = max_sum.saturating_add(c.saturating_mul(lb));
                min_sum = min_sum.saturating_add(c.saturating_mul(ub));
            }
        }
        let m_fwd = (max_sum - rhs).max(0);
        let m_bwd = (rhs + 1 - min_sum).max(0);
        (m_fwd, m_bwd)
    }

    /// Encode r ↔ (sum(c_i * x_i) ≤ d) using Big-M.
    pub(super) fn add_reif_le(&mut self, coeffs: &[i64], vars: &[IntVarId], rhs: i64, r: IntVarId) {
        let (m_fwd, m_bwd) = self.compute_big_m(coeffs, vars, rhs);

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
                rhs: rhs + m_fwd,
            });
        }

        // Backward: -sum(c_i * x_i) - M_bwd * r ≤ -(rhs + 1)
        // i.e., sum(c_i * x_i) ≥ rhs + 1 - M_bwd * r
        // When r=0: sum ≥ rhs + 1 (constraint is violated)
        // When r=1: sum ≥ rhs + 1 - M_bwd (trivially true)
        {
            let mut c: Vec<i64> = coeffs.iter().map(|x| -x).collect();
            c.push(-m_bwd);
            let mut v = vars.to_vec();
            v.push(r);
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: c,
                vars: v,
                rhs: -(rhs + 1),
            });
        }
    }

    /// Encode r ↔ (sum(c_i * x_i) = d) using Big-M.
    /// Decomposed as: r ↔ (sum ≤ d ∧ sum ≥ d).
    pub(super) fn add_reif_eq(&mut self, coeffs: &[i64], vars: &[IntVarId], rhs: i64, r: IntVarId) {
        // Introduce two auxiliary booleans: r1 ↔ (sum ≤ d), r2 ↔ (sum ≥ d)
        // Then r = r1 ∧ r2
        let r1 = self.engine.new_bool_var(None);
        let r2 = self.engine.new_bool_var(None);
        self.var_bounds.insert(r1, (0, 1));
        self.var_bounds.insert(r2, (0, 1));

        // r1 ↔ (sum ≤ d)
        self.add_reif_le(coeffs, vars, rhs, r1);

        // r2 ↔ (-sum ≤ -d) i.e. (sum ≥ d)
        let neg_coeffs: Vec<i64> = coeffs.iter().map(|c| -c).collect();
        self.add_reif_le(&neg_coeffs, vars, -rhs, r2);

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
    }

    /// Encode r → (sum(c_i * x_i) ≤ d) (half-reification / implication).
    fn add_imp_le(&mut self, coeffs: &[i64], vars: &[IntVarId], rhs: i64, r: IntVarId) {
        let (m_fwd, _) = self.compute_big_m(coeffs, vars, rhs);
        let mut c = coeffs.to_vec();
        c.push(m_fwd);
        let mut v = vars.to_vec();
        v.push(r);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: c,
            vars: v,
            rhs: rhs + m_fwd,
        });
    }

    /// int_eq_reif(a, b, r) etc.
    pub(super) fn translate_int_comparison_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;

        match c.id.as_str() {
            "int_le_reif" | "bool_le_reif" => {
                // r ↔ (a ≤ b) → r ↔ (a - b ≤ 0)
                self.add_reif_le(&[1, -1], &[a, b], 0, r);
            }
            "int_lt_reif" | "bool_lt_reif" => {
                // r ↔ (a < b) → r ↔ (a - b ≤ -1)
                self.add_reif_le(&[1, -1], &[a, b], -1, r);
            }
            "int_ge_reif" | "bool_ge_reif" => {
                // r ↔ (a ≥ b) → r ↔ (b - a ≤ 0)
                self.add_reif_le(&[-1, 1], &[a, b], 0, r);
            }
            "int_gt_reif" | "bool_gt_reif" => {
                // r ↔ (a > b) → r ↔ (b - a ≤ -1)
                self.add_reif_le(&[-1, 1], &[a, b], -1, r);
            }
            "int_eq_reif" => {
                // r ↔ (a = b) → r ↔ (a - b = 0)
                self.add_reif_eq(&[1, -1], &[a, b], 0, r);
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
                self.add_reif_eq(&[1, -1], &[a, b], 0, not_r);
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    /// int_lin_le_reif(coeffs, vars, rhs, r) etc.
    pub(super) fn translate_int_linear_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        let rhs = self.resolve_const_int(&c.args[2])?;
        let r = self.resolve_var(&c.args[3])?;

        match c.id.as_str() {
            "int_lin_le_reif" | "bool_lin_le_reif" => {
                self.add_reif_le(&coeffs, &vars, rhs, r);
            }
            "int_lin_eq_reif" | "bool_lin_eq_reif" => {
                self.add_reif_eq(&coeffs, &vars, rhs, r);
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    /// bool_eq_reif(a, b, r): r ↔ (a = b)
    pub(super) fn translate_bool_eq_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;
        self.add_reif_eq(&[1, -1], &[a, b], 0, r);
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
        self.add_reif_eq(&[1, -1], &[a, b], 0, not_r);
        Ok(())
    }

    /// int_lin_ne_reif(coeffs, vars, rhs, r): r ↔ (sum ≠ rhs)
    /// Decomposed as: not_r ↔ (sum = rhs), r + not_r = 1
    pub(super) fn translate_int_linear_ne_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
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
        self.add_reif_eq(&coeffs, &vars, rhs, not_r);
        Ok(())
    }

    /// int_lin_ne_imp(coeffs, vars, rhs, r): r → (sum ≠ rhs)
    /// Encoded as: create eq_ind ↔ (sum = rhs), then r + eq_ind ≤ 1
    pub(super) fn translate_int_linear_ne_imp(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        let rhs = self.resolve_const_int(&c.args[2])?;
        let r = self.resolve_var(&c.args[3])?;

        let eq_ind = self.engine.new_bool_var(None);
        self.var_bounds.insert(eq_ind, (0, 1));
        // eq_ind ↔ (sum = rhs)
        self.add_reif_eq(&coeffs, &vars, rhs, eq_ind);
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
        let neg_len = neg.len() as i64;

        // The clause is: sum(pos) - sum(neg) >= 1 - L
        // Rewrite as: sum(pos) + sum(1-neg) >= 1
        // i.e., sum(pos) - sum(neg) + L >= 1

        // Forward: r → clause holds
        // sum(pos) - sum(neg) >= 1 - L - M*(1-r)
        // Backward: ¬clause → ¬r
        // ¬clause means sum(pos) - sum(neg) < 1 - L, i.e. sum(pos) - sum(neg) <= -L
        // When clause fails: r must be 0

        // Use Big-M reification on the linear form:
        // clause is: sum(pos_i) + sum(1-neg_j) >= 1
        // Rewrite: -sum(pos_i) + sum(neg_j) <= L - 1  (negated ≤ form)
        // So: r ↔ (-sum(pos) + sum(neg) ≤ L - 1) ... no that's wrong direction

        // r ↔ (sum(pos) - sum(neg) >= 1 - L)
        // Rewrite: r ↔ (-sum(pos) + sum(neg) ≤ L - 1)
        let mut coeffs: Vec<i64> = pos.iter().map(|_| -1i64).collect();
        coeffs.extend(neg.iter().map(|_| 1i64));
        let mut vars = pos;
        vars.extend(neg);
        self.add_reif_le(&coeffs, &vars, neg_len - 1, r);
        Ok(())
    }

    /// Half-reification: r → constraint.
    pub(super) fn translate_int_comparison_imp(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        let r = self.resolve_var(&c.args[2])?;

        match c.id.as_str() {
            "int_le_imp" | "bool_le_imp" => self.add_imp_le(&[1, -1], &[a, b], 0, r),
            "int_lt_imp" | "bool_lt_imp" => self.add_imp_le(&[1, -1], &[a, b], -1, r),
            "int_ge_imp" | "bool_ge_imp" => self.add_imp_le(&[-1, 1], &[a, b], 0, r),
            "int_gt_imp" | "bool_gt_imp" => self.add_imp_le(&[-1, 1], &[a, b], -1, r),
            "int_eq_imp" => {
                // r → (a = b): r → (a ≤ b) ∧ r → (a ≥ b)
                self.add_imp_le(&[1, -1], &[a, b], 0, r);
                self.add_imp_le(&[-1, 1], &[a, b], 0, r);
            }
            "int_ne_imp" => {
                // r → (a ≠ b): when r=1, force a < b or a > b.
                // Auxiliary indicator d selects which disjunct:
                //   r=1, d=0: a - b ≤ -1 (a < b)
                //   r=1, d=1: b - a ≤ -1 (a > b)
                //   r=0: unconstrained
                let (a_lb, a_ub) = self.get_var_bounds(a);
                let (b_lb, b_ub) = self.get_var_bounds(b);
                let d = self.engine.new_bool_var(None);
                self.var_bounds.insert(d, (0, 1));

                let m_ab = (a_ub - b_lb + 1).max(1);
                let m_ba = (b_ub - a_lb + 1).max(1);

                // a - b ≤ -1 + m_ab*d + m_ab*(1-r)
                // Rearranged: a - b - m_ab*d + m_ab*r ≤ m_ab - 1
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1, -m_ab, m_ab],
                    vars: vec![a, b, d, r],
                    rhs: m_ab - 1,
                });

                // b - a ≤ -1 + m_ba*(1-d) + m_ba*(1-r)
                // Rearranged: b - a + m_ba*d + m_ba*r ≤ 2*m_ba - 1
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![-1, 1, m_ba, m_ba],
                    vars: vec![a, b, d, r],
                    rhs: 2 * m_ba - 1,
                });
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    /// Half-reification for linear constraints.
    pub(super) fn translate_int_linear_imp(&mut self, c: &ConstraintItem) -> Result<()> {
        let coeffs = self.resolve_const_int_array(&c.args[0])?;
        let vars = self.resolve_var_array(&c.args[1])?;
        let rhs = self.resolve_const_int(&c.args[2])?;
        let r = self.resolve_var(&c.args[3])?;

        match c.id.as_str() {
            "int_lin_le_imp" | "bool_lin_le_imp" => {
                self.add_imp_le(&coeffs, &vars, rhs, r);
            }
            "int_lin_eq_imp" | "bool_lin_eq_imp" => {
                // r → (sum = d): r → (sum ≤ d) ∧ r → (sum ≥ d)
                self.add_imp_le(&coeffs, &vars, rhs, r);
                let neg_coeffs: Vec<i64> = coeffs.iter().map(|x| -x).collect();
                self.add_imp_le(&neg_coeffs, &vars, -rhs, r);
            }
            _ => unreachable!(),
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
