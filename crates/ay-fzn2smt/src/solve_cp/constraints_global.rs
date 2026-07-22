// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Global and set constraint translations for solve-cp.
//
// set_in_reif: reified set membership via Table or reified comparison
// array_int_maximum/minimum: n-ary max/min via Big-M indicator variables

use crate::error::{Fzn2smtError, Result};
use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::{ConstraintItem, Expr};

use super::{materialized_range_len, CpContext};

impl CpContext {
    /// set_in(x, S): x ∈ S
    ///
    /// Constant intervals use bounds; constant sparse sets use a unary table.
    /// When S is a set variable (boolean indicator encoding), we must actively
    /// constrain: the indicator for x's value in S must be 1.
    pub(super) fn translate_set_in(&mut self, c: &ConstraintItem) -> Result<()> {
        // Check if the set argument is a set variable.
        if let Expr::Ident(name) = &c.args[1] {
            if let Some((s_lo, indicators)) = self.set_var_map.get(name).cloned() {
                let x = self.resolve_var(&c.args[0])?;
                // set_in(x, S_var) ≡ set_in_reif(x, S_var, 1)
                let one = self.get_const_var(1);
                return self.set_in_reif_var(x, &indicators, s_lo, one);
            }
        }
        let x = self.resolve_var(&c.args[0])?;
        let set_expr = self.resolve_const_set_expr(&c.args[1]);
        self.enforce_const_set_in(x, &set_expr, "set_in");
        Ok(())
    }

    /// set_in_reif(x, S, r): r ↔ (x ∈ S)
    ///
    /// - Interval S (lo..hi): reified comparison r ↔ (x >= lo ∧ x <= hi)
    /// - Sparse S ({v1,...,vn}): Table constraint on (x, r)
    pub(super) fn translate_set_in_reif(&mut self, c: &ConstraintItem) -> Result<()> {
        let x = self.resolve_var(&c.args[0])?;
        let r = self.resolve_var(&c.args[2])?;

        // Check if the set argument is a set variable (boolean indicator encoding).
        if let Expr::Ident(name) = &c.args[1] {
            if let Some((s_lo, indicators)) = self.set_var_map.get(name).cloned() {
                return self.set_in_reif_var(x, &indicators, s_lo, r);
            }
        }

        // Resolve the set argument: if it's an Ident, look up the parameter value.
        let set_expr = self.resolve_const_set_expr(&c.args[1]);

        match &set_expr {
            Expr::IntRange(lo, hi) => {
                if lo > hi {
                    self.engine.add_constraint(Constraint::LinearEq {
                        coeffs: vec![1],
                        vars: vec![r],
                        rhs: 0,
                    });
                    return Ok(());
                }
                // r ↔ (x >= lo ∧ x <= hi)
                let r1 = if *lo == i64::MIN {
                    self.get_const_var(1)
                } else {
                    let r1 = self.engine.new_bool_var(None);
                    self.var_bounds.insert(r1, (0, 1));
                    // r1 ↔ (x >= lo) → r1 ↔ (-x ≤ -lo)
                    self.add_reif_le(&[-1], &[x], -*lo, r1);
                    r1
                };
                let r2 = if *hi == i64::MAX {
                    self.get_const_var(1)
                } else {
                    let r2 = self.engine.new_bool_var(None);
                    self.var_bounds.insert(r2, (0, 1));
                    // r2 ↔ (x <= hi)
                    self.add_reif_le(&[1], &[x], *hi, r2);
                    r2
                };
                // r = r1 ∧ r2
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
            Expr::SetLit(elems) => {
                let mut set_vals = Vec::with_capacity(elems.len());
                for elem in elems {
                    set_vals.push(self.eval_const_int(elem).ok_or_else(|| {
                        Fzn2smtError::UnsupportedExpression(format!(
                            "set_in_reif: expected a constant set element, got {elem:?}"
                        ))
                    })?);
                }
                set_vals.sort_unstable();
                set_vals.dedup();
                if set_vals.is_empty() {
                    // Empty set literal → r = 0
                    self.engine.add_constraint(Constraint::LinearEq {
                        coeffs: vec![1],
                        vars: vec![r],
                        rhs: 0,
                    });
                } else {
                    let (lb, ub) = self.get_var_bounds(x);
                    let domain_size = i128::from(ub) - i128::from(lb) + 1;
                    if (1..=10_000).contains(&domain_size) {
                        // Small domain: enumerate all (x, r) tuples via Table
                        let set_hash: std::collections::BTreeSet<i64> =
                            set_vals.iter().copied().collect();
                        let mut tuples = Vec::new();
                        for v in lb..=ub {
                            tuples.push(vec![v, i64::from(set_hash.contains(&v))]);
                        }
                        self.engine.add_constraint(Constraint::Table {
                            vars: vec![x, r],
                            tuples,
                        });
                    } else {
                        // Large domain: indicator variables per set element.
                        // b_i ↔ (x = v_i), then r ↔ OR(b_1, ..., b_n).
                        let mut indicators = Vec::with_capacity(set_vals.len());
                        for &val in &set_vals {
                            let bi = self.engine.new_bool_var(None);
                            self.var_bounds.insert(bi, (0, 1));
                            self.add_reif_eq(&[1], &[x], val, bi);
                            indicators.push(bi);
                        }
                        // Forward: r ≥ b_i for each i (any b_i=1 → r=1)
                        for &bi in &indicators {
                            self.engine.add_constraint(Constraint::LinearLe {
                                coeffs: vec![1, -1],
                                vars: vec![bi, r],
                                rhs: 0,
                            });
                        }
                        // Backward: sum(b_i) - r ≥ 0 (all b_i=0 → r=0)
                        let n = indicators.len();
                        let mut coeffs = vec![1i64; n];
                        coeffs.push(-1);
                        let mut vars = indicators;
                        vars.push(r);
                        self.engine.add_constraint(Constraint::LinearGe {
                            coeffs,
                            vars,
                            rhs: 0,
                        });
                    }
                }
            }
            Expr::EmptySet => {
                // x ∈ {} is always false → r = 0
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1],
                    vars: vec![r],
                    rhs: 0,
                });
            }
            _ => {
                self.mark_unsupported("set_in_reif");
            }
        }
        Ok(())
    }

    fn resolve_const_set_expr(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Ident(name) => self.par_sets.get(name).cloned().unwrap_or(expr.clone()),
            other => other.clone(),
        }
    }

    fn enforce_const_set_in(&mut self, x: IntVarId, set_expr: &Expr, unsupported_name: &str) {
        match set_expr {
            Expr::IntRange(lo, hi) => {
                if lo > hi {
                    self.add_false_constraint();
                    return;
                }
                self.engine.add_constraint(Constraint::LinearGe {
                    coeffs: vec![1],
                    vars: vec![x],
                    rhs: *lo,
                });
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1],
                    vars: vec![x],
                    rhs: *hi,
                });
            }
            Expr::SetLit(elems) => {
                let mut set_vals = Vec::with_capacity(elems.len());
                for elem in elems {
                    if let Some(v) = self.eval_const_int(elem) {
                        set_vals.push(v);
                    } else {
                        self.mark_unsupported(unsupported_name);
                        return;
                    }
                }
                set_vals.sort_unstable();
                set_vals.dedup();
                if set_vals.is_empty() {
                    self.add_false_constraint();
                    return;
                }
                let tuples = set_vals.into_iter().map(|v| vec![v]).collect();
                self.engine.add_constraint(Constraint::Table {
                    vars: vec![x],
                    tuples,
                });
            }
            Expr::EmptySet => {
                self.add_false_constraint();
            }
            _ => {
                self.mark_unsupported(unsupported_name);
            }
        }
    }

    fn add_false_constraint(&mut self) {
        let zero = self.get_const_var(0);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1],
            vars: vec![zero],
            rhs: 1,
        });
    }

    /// set_in_reif(x, S_var, r) where S_var is a set variable with indicators.
    ///
    /// Encoding: r ↔ (x ∈ S_var).
    /// If x is constant v: r = indicator_S(v) (or r = 0 if v outside S's range).
    /// If x is variable: use Element constraint over indicators.
    fn set_in_reif_var(
        &mut self,
        x: IntVarId,
        indicators: &[IntVarId],
        s_lo: i64,
        r: IntVarId,
    ) -> Result<()> {
        // Check if x is a known constant.
        let (x_lb, x_ub) = self.get_var_bounds(x);
        if x_lb == x_ub {
            // Constant case: r = indicator(x_lb) or r = 0 if out of range.
            let v = x_lb;
            let idx = usize::try_from(i128::from(v) - i128::from(s_lo)).ok();
            if let Some(&indicator) = idx.and_then(|idx| indicators.get(idx)) {
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![r, indicator],
                    rhs: 0,
                });
            } else {
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1],
                    vars: vec![r],
                    rhs: 0,
                });
            }
            return Ok(());
        }

        // Variable case: use Element constraint.
        // Build indicator table padded with 0 for x's full domain.
        let table_len = materialized_range_len(x_lb, x_ub, "set_in_reif variable domain")?;
        let zero = self.get_const_var(0);
        let table: Vec<IntVarId> = (x_lb..=x_ub)
            .map(|v| {
                usize::try_from(i128::from(v) - i128::from(s_lo))
                    .ok()
                    .and_then(|idx| indicators.get(idx).copied())
                    .unwrap_or(zero)
            })
            .collect();
        debug_assert_eq!(table.len(), table_len);
        let n = i64::try_from(table_len).map_err(|_| {
            Fzn2smtError::UnsupportedExpression(
                "set_in_reif variable domain is too large".to_string(),
            )
        })?;
        let index_0 = self.engine.new_int_var(ay_cp::Domain::new(0, n - 1), None);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, -1],
            vars: vec![x, index_0],
            rhs: x_lb,
        });
        self.engine.add_constraint(Constraint::Element {
            index: index_0,
            array: table,
            result: r,
        });
        Ok(())
    }

    /// array_int_maximum(r, xs): r = max(xs[1], ..., xs[n])
    ///
    /// Big-M linearization with n indicator variables:
    ///   r >= xs[i] for all i (lower bound)
    ///   r <= xs[i] + M*(1-d_i) for all i (d_i=1 → r <= xs[i])
    ///   sum(d_i) >= 1 (at least one indicator active)
    pub(super) fn translate_array_int_maximum(&mut self, c: &ConstraintItem) -> Result<()> {
        let r = self.resolve_var(&c.args[0])?;
        let xs = self.resolve_var_array(&c.args[1])?;
        let r_ub = self.get_var_bounds(r).1;

        for &xi in &xs {
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1, -1],
                vars: vec![r, xi],
                rhs: 0,
            });
        }

        let mut indicators = Vec::with_capacity(xs.len());
        for &xi in &xs {
            let d = self.engine.new_bool_var(None);
            self.var_bounds.insert(d, (0, 1));
            let xi_lb = self.get_var_bounds(xi).0;
            let m = (r_ub - xi_lb).max(1);
            // r <= xs[i] + M*(1-d_i): r - xs[i] + M*d_i ≤ M
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, m],
                vars: vec![r, xi, d],
                rhs: m,
            });
            indicators.push(d);
        }

        let n = indicators.len();
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1i64; n],
            vars: indicators,
            rhs: 1,
        });
        Ok(())
    }

    /// fzn_diffn(x, y, dx, dy): non-overlapping rectangles.
    ///
    /// Rectangle i has origin (x[i], y[i]) and size (dx[i], dy[i]).
    /// No two rectangles may overlap in their interiors.
    pub(super) fn translate_diffn(&mut self, c: &ConstraintItem) -> Result<()> {
        let x = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var_array(&c.args[1])?;
        let dx = self.resolve_var_array(&c.args[2])?;
        let dy = self.resolve_var_array(&c.args[3])?;
        if x.len() != y.len() || x.len() != dx.len() || x.len() != dy.len() {
            return Err(Fzn2smtError::DiffnArrayLengthMismatch {
                x: x.len(),
                y: y.len(),
                dx: dx.len(),
                dy: dy.len(),
            });
        }
        self.engine
            .add_constraint(Constraint::Diffn { x, y, dx, dy });
        Ok(())
    }

    /// array_int_minimum(r, xs): r = min(xs[1], ..., xs[n])
    ///
    /// Big-M linearization with n indicator variables:
    ///   r <= xs[i] for all i (upper bound)
    ///   r >= xs[i] - M*(1-d_i) for all i (d_i=1 → r >= xs[i])
    ///   sum(d_i) >= 1 (at least one indicator active)
    pub(super) fn translate_array_int_minimum(&mut self, c: &ConstraintItem) -> Result<()> {
        let r = self.resolve_var(&c.args[0])?;
        let xs = self.resolve_var_array(&c.args[1])?;
        let r_lb = self.get_var_bounds(r).0;

        for &xi in &xs {
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1],
                vars: vec![r, xi],
                rhs: 0,
            });
        }

        let mut indicators = Vec::with_capacity(xs.len());
        for &xi in &xs {
            let d = self.engine.new_bool_var(None);
            self.var_bounds.insert(d, (0, 1));
            let xi_ub = self.get_var_bounds(xi).1;
            let m = (xi_ub - r_lb).max(1);
            // r >= xs[i] - M*(1-d_i): -r + xs[i] + M*d_i ≤ M
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![-1, 1, m],
                vars: vec![r, xi, d],
                rhs: m,
            });
            indicators.push(d);
        }

        let n = indicators.len();
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1i64; n],
            vars: indicators,
            rhs: 1,
        });
        Ok(())
    }
}
