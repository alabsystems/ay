// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Lexicographic ordering constraint translations for solve-cp.
//
// lex_less_int: strict lexicographic ordering via Big-M chain
// lex_lesseq_int: non-strict lexicographic ordering via Big-M chain

use crate::error::{Fzn2smtError, Result};
use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
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
            // The empty sequence is a prefix of every sequence. A non-empty
            // sequence cannot be <= an empty sequence.
            if !xs.is_empty() {
                self.add_lex_false_constraint();
            }
            return Ok(());
        }

        let mut prefix_eq = None;
        for i in 0..n {
            if let Some(prefix) = prefix_eq {
                self.add_prefix_le(c, xs[i], ys[i], prefix)?;
            } else {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![xs[i], ys[i]],
                    rhs: 0,
                });
            }

            let equal_here = self.new_reified_equality(xs[i], ys[i], &c.id)?;
            prefix_eq = Some(match prefix_eq {
                Some(prefix) => self.new_bool_and(prefix, equal_here),
                None => equal_here,
            });
        }

        // If ys is the shorter sequence, equality across the common prefix is
        // not enough: the longer xs sequence sorts after its proper prefix.
        if xs.len() > ys.len() {
            if let Some(prefix_eq) = prefix_eq {
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1],
                    vars: vec![prefix_eq],
                    rhs: 0,
                });
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
            // A proper empty prefix is strictly smaller; an empty sequence is
            // not smaller than itself, and a non-empty sequence is not smaller
            // than an empty one.
            if !xs.is_empty() || ys.is_empty() {
                self.add_lex_false_constraint();
            }
            return Ok(());
        }

        let mut d_vars = Vec::with_capacity(n);
        let mut prefix_eq = None;

        for i in 0..n {
            let di = self.engine.new_bool_var(None);
            self.var_bounds.insert(di, (0, 1));
            d_vars.push(di);

            let m = self.forward_difference_big_m(c, xs[i], ys[i], true)?;

            // di=1 selects the first strict inequality. At positions after
            // zero it also requires the complete earlier prefix to be equal.
            if let Some(prefix) = prefix_eq {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![di, prefix],
                    rhs: 0,
                });
            }
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, m + 1],
                vars: vec![xs[i], ys[i], di],
                rhs: m,
            });

            if let Some(prefix) = prefix_eq {
                self.add_prefix_le(c, xs[i], ys[i], prefix)?;
            } else {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![xs[i], ys[i]],
                    rhs: 0,
                });
            }

            let equal_here = self.new_reified_equality(xs[i], ys[i], &c.id)?;
            prefix_eq = Some(match prefix_eq {
                Some(prefix) => self.new_bool_and(prefix, equal_here),
                None => equal_here,
            });
        }

        // A strict difference in the common prefix is sufficient. When xs is
        // shorter, equality throughout that prefix is also sufficient because
        // xs is then a proper prefix of ys.
        let mut acceptance = d_vars;
        if xs.len() < ys.len() {
            if let Some(prefix_eq) = prefix_eq {
                acceptance.push(prefix_eq);
            }
        }
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![1i64; acceptance.len()],
            vars: acceptance,
            rhs: 1,
        });
        Ok(())
    }

    fn add_lex_false_constraint(&mut self) {
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![],
            vars: vec![],
            rhs: -1,
        });
    }

    fn new_reified_equality(
        &mut self,
        left: IntVarId,
        right: IntVarId,
        context: &str,
    ) -> Result<IntVarId> {
        let equal = self.engine.new_bool_var(None);
        self.var_bounds.insert(equal, (0, 1));
        self.add_reif_eq(&[1, -1], &[left, right], 0, equal, context)?;
        Ok(equal)
    }

    fn new_bool_and(&mut self, left: IntVarId, right: IntVarId) -> IntVarId {
        let conjunction = self.engine.new_bool_var(None);
        self.var_bounds.insert(conjunction, (0, 1));
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![conjunction, left],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![conjunction, right],
            rhs: 0,
        });
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, 1, -1],
            vars: vec![left, right, conjunction],
            rhs: 1,
        });
        conjunction
    }

    fn add_prefix_le(
        &mut self,
        c: &ConstraintItem,
        left: IntVarId,
        right: IntVarId,
        prefix_equal: IntVarId,
    ) -> Result<()> {
        let m = self.forward_difference_big_m(c, left, right, false)?;
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, m],
            vars: vec![left, right, prefix_equal],
            rhs: m,
        });
        Ok(())
    }

    /// Largest possible `left - right`, represented without intermediate i64
    /// overflow. Strict encodings need one additional unit in the indicator
    /// coefficient, so that representability is checked here as well.
    fn forward_difference_big_m(
        &self,
        c: &ConstraintItem,
        left: IntVarId,
        right: IntVarId,
        strict: bool,
    ) -> Result<i64> {
        let left_ub = i128::from(self.get_var_bounds(left).1);
        let right_lb = i128::from(self.get_var_bounds(right).0);
        let m = (left_ub - right_lb).max(0);
        let required = m + i128::from(strict);
        if required > i128::from(i64::MAX) {
            return Err(Fzn2smtError::LinearEncodingOverflow {
                constraint: c.id.clone(),
            });
        }
        // `required` fitting proves `m` fits as well.
        Ok(m as i64)
    }
}
