// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Lexicographic ordering constraint translations for solve-cp.
//
// lex_less_int: strict lexicographic ordering via Big-M chain
// lex_lesseq_int: non-strict lexicographic ordering via Big-M chain

use crate::error::Result;
use ay_cp::propagator::Constraint;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::CpContext;

impl CpContext {
    /// fzn_lex_lesseq_int(xs, ys): xs ≤_lex ys
    ///
    /// Decompose using chained indicator variables with full reification:
    /// - b_0 ↔ (xs[0] == ys[0])
    /// - b_i ↔ (b_{i-1} ∧ xs[i] == ys[i]) for i > 0
    /// - xs[0] <= ys[0] unconditionally
    /// - b_{i-1} = 1 → xs[i] <= ys[i] for i > 0
    ///
    /// Full reification is required: if b_i is only half-reified (b_i=1 → equal),
    /// the solver can set b_i=0 when positions are actually equal, making the
    /// <=  constraint at position i+1 vacuous. This produces false SAT.
    pub(super) fn translate_lex_lesseq_int(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let ys = self.resolve_var_array(&c.args[1])?;
        let n = xs.len().min(ys.len());
        if n == 0 {
            return Ok(());
        }

        // xs[0] <= ys[0]
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![xs[0], ys[0]],
            rhs: 0,
        });

        if n == 1 {
            return Ok(());
        }

        // b_0 ↔ (xs[0] == ys[0]) — full bidirectional reification
        let mut prev_b = self.engine.new_bool_var(None);
        self.var_bounds.insert(prev_b, (0, 1));
        self.add_reif_eq(&[1, -1], &[xs[0], ys[0]], 0, prev_b);

        for i in 1..n {
            let m = {
                let (a_lb, a_ub) = self.get_var_bounds(xs[i]);
                let (b_lb, b_ub) = self.get_var_bounds(ys[i]);
                (a_ub - b_lb).max(b_ub - a_lb).max(1)
            };

            // If prefix was all-equal (prev_b=1), then xs[i] <= ys[i]
            // xs[i] - ys[i] <= M*(1-prev_b)
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, m],
                vars: vec![xs[i], ys[i], prev_b],
                rhs: m,
            });

            if i < n - 1 {
                // eq_i ↔ (xs[i] == ys[i]) — full reification
                let eq_i = self.engine.new_bool_var(None);
                self.var_bounds.insert(eq_i, (0, 1));
                self.add_reif_eq(&[1, -1], &[xs[i], ys[i]], 0, eq_i);

                // new_b ↔ (prev_b ∧ eq_i)
                let new_b = self.engine.new_bool_var(None);
                self.var_bounds.insert(new_b, (0, 1));
                // new_b ≤ prev_b
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![new_b, prev_b],
                    rhs: 0,
                });
                // new_b ≤ eq_i
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![new_b, eq_i],
                    rhs: 0,
                });
                // prev_b + eq_i - new_b ≤ 1 (forces new_b=1 when both are 1)
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, 1, -1],
                    vars: vec![prev_b, eq_i, new_b],
                    rhs: 1,
                });
                prev_b = new_b;
            }
        }
        Ok(())
    }

    /// fzn_lex_less_int(xs, ys): xs <_lex ys
    ///
    /// Decompose as: xs ≤_lex ys AND xs ≠ ys.
    /// The strict part is enforced by requiring at least one position where xs[i] < ys[i]
    /// when the prefix is all-equal.
    ///
    /// Chain indicators use full reification to prevent the solver from
    /// "forgetting" that a prefix is equal. Without full reification,
    /// the encoding can produce false UNSAT when the chain is pessimistic
    /// (setting prev_eq=0 even when positions are equal prevents any d_i=1,
    /// making sum(d_i)>=1 unsatisfiable).
    pub(super) fn translate_lex_less_int(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let ys = self.resolve_var_array(&c.args[1])?;
        let n = xs.len().min(ys.len());
        if n == 0 {
            // Empty arrays: xs <_lex ys is false (empty == empty)
            // Add empty clause to force UNSAT
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![],
                vars: vec![],
                rhs: -1,
            });
            return Ok(());
        }

        let mut d_vars = Vec::with_capacity(n);

        // prev_eq ↔ (xs[0] == ys[0]) — full reification
        let mut prev_eq = self.engine.new_bool_var(None);
        self.var_bounds.insert(prev_eq, (0, 1));
        self.add_reif_eq(&[1, -1], &[xs[0], ys[0]], 0, prev_eq);

        // d0: indicator for xs[0] < ys[0] (half-reif OK for d_i)
        let d0 = self.engine.new_bool_var(None);
        self.var_bounds.insert(d0, (0, 1));
        d_vars.push(d0);

        let m0 = {
            let (a_lb, a_ub) = self.get_var_bounds(xs[0]);
            let (b_lb, b_ub) = self.get_var_bounds(ys[0]);
            (a_ub - b_lb).max(b_ub - a_lb).max(1)
        };

        // d0=1 → xs[0] < ys[0] → xs[0] - ys[0] <= -1 + M*(1-d0)
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, m0 + 1],
            vars: vec![xs[0], ys[0], d0],
            rhs: m0,
        });
        // xs[0] <= ys[0] unconditionally:
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![xs[0], ys[0]],
            rhs: 0,
        });

        for i in 1..n {
            let di = self.engine.new_bool_var(None);
            self.var_bounds.insert(di, (0, 1));
            d_vars.push(di);

            let m = {
                let (a_lb, a_ub) = self.get_var_bounds(xs[i]);
                let (b_lb, b_ub) = self.get_var_bounds(ys[i]);
                (a_ub - b_lb).max(b_ub - a_lb).max(1)
            };

            // di=1 → prev_eq=1 AND xs[i] < ys[i]
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1],
                vars: vec![di, prev_eq],
                rhs: 0,
            });
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, m + 1],
                vars: vec![xs[i], ys[i], di],
                rhs: m,
            });

            // If prefix was all-equal (prev_eq=1), then xs[i] <= ys[i]
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, m],
                vars: vec![xs[i], ys[i], prev_eq],
                rhs: m,
            });

            if i < n - 1 {
                // eq_i ↔ (xs[i] == ys[i]) — full reification
                let eq_i = self.engine.new_bool_var(None);
                self.var_bounds.insert(eq_i, (0, 1));
                self.add_reif_eq(&[1, -1], &[xs[i], ys[i]], 0, eq_i);

                // new_eq ↔ (prev_eq ∧ eq_i)
                let new_eq = self.engine.new_bool_var(None);
                self.var_bounds.insert(new_eq, (0, 1));
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![new_eq, prev_eq],
                    rhs: 0,
                });
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![new_eq, eq_i],
                    rhs: 0,
                });
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, 1, -1],
                    vars: vec![prev_eq, eq_i, new_eq],
                    rhs: 1,
                });
                prev_eq = new_eq;
            }
        }

        // At least one d_i must be 1 (strict inequality somewhere)
        let nd = d_vars.len();
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1i64; nd],
            vars: d_vars,
            rhs: 1,
        });
        Ok(())
    }
}
