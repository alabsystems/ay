// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Counting constraint translations for solve-cp.
//
// count_eq/leq/geq/lt/gt/neq: counting constraints via reified equality
// global_cardinality: GCC via count decomposition
// nvalue: number of distinct values

use crate::error::{Fzn2smtError, Result};
use ay_cp::propagator::Constraint;
use ay_cp::Domain;
use ay_flatzinc_parser::ast::ConstraintItem;

use super::CpContext;

impl CpContext {
    /// fzn_count_eq(xs, y, c): count(xs[i] == y) = c
    /// Decompose: introduce bool indicator b_i for each xs[i],
    /// b_i = 1 iff xs[i] == y, then sum(b_i) = c.
    pub(super) fn translate_count_eq(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var(&c.args[1])?;
        let count = self.resolve_var(&c.args[2])?;
        let indicators = self.count_eq_indicators(&xs, y)?;
        let n = indicators.len();
        // sum(b_i) = count → sum(b_i) - count = 0
        let mut coeffs = vec![1i64; n];
        coeffs.push(-1);
        let mut vars = indicators;
        vars.push(count);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs,
            vars,
            rhs: 0,
        });
        Ok(())
    }

    /// Build indicator variables: b_i = 1 iff xs[i] == y.
    /// Uses full reified equality via `add_reif_eq` (Big-M both directions).
    pub(super) fn count_eq_indicators(
        &mut self,
        xs: &[ay_cp::variable::IntVarId],
        y: ay_cp::variable::IntVarId,
    ) -> Result<Vec<ay_cp::variable::IntVarId>> {
        let mut indicators = Vec::with_capacity(xs.len());
        for &xi in xs {
            let b = self.engine.new_bool_var(None);
            self.var_bounds.insert(b, (0, 1));
            // b ↔ (xi == y), i.e. b ↔ (xi - y = 0)
            // Full bidirectional reification: b=1 → xi=y AND xi=y → b=1
            self.add_reif_eq(&[1, -1], &[xi, y], 0, b);
            indicators.push(b);
        }
        Ok(indicators)
    }

    /// fzn_count_leq(xs, y, c): c <= count(xs[i] == y), i.e. count >= c.
    ///
    /// MiniZinc semantics: "c is leq the number of occurrences of y in x."
    /// The suffix describes the relationship of c to the count, NOT count to c.
    pub(super) fn translate_count_leq(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var(&c.args[1])?;
        let count = self.resolve_var(&c.args[2])?;
        let indicators = self.count_eq_indicators(&xs, y)?;
        let n = indicators.len();
        // count <= sum(b_i) → -sum(b_i) + count <= 0
        let mut coeffs = vec![-1i64; n];
        coeffs.push(1);
        let mut vars = indicators;
        vars.push(count);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs,
            vars,
            rhs: 0,
        });
        Ok(())
    }

    /// fzn_count_geq(xs, y, c): c >= count(xs[i] == y), i.e. count <= c.
    ///
    /// MiniZinc semantics: "c is geq the number of occurrences of y in x."
    pub(super) fn translate_count_geq(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var(&c.args[1])?;
        let count = self.resolve_var(&c.args[2])?;
        let indicators = self.count_eq_indicators(&xs, y)?;
        let n = indicators.len();
        // sum(b_i) <= count → sum(b_i) - count <= 0
        let mut coeffs = vec![1i64; n];
        coeffs.push(-1);
        let mut vars = indicators;
        vars.push(count);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs,
            vars,
            rhs: 0,
        });
        Ok(())
    }

    /// fzn_count_lt(xs, y, c): c < count(xs[i] == y), i.e. count > c → count >= c+1.
    ///
    /// MiniZinc semantics: "c is strictly less than the number of occurrences of y in x."
    pub(super) fn translate_count_lt(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var(&c.args[1])?;
        let count = self.resolve_var(&c.args[2])?;
        let indicators = self.count_eq_indicators(&xs, y)?;
        let n = indicators.len();
        // count < sum(b_i) → -sum(b_i) + count <= -1
        let mut coeffs = vec![-1i64; n];
        coeffs.push(1);
        let mut vars = indicators;
        vars.push(count);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs,
            vars,
            rhs: -1,
        });
        Ok(())
    }

    /// fzn_count_gt(xs, y, c): c > count(xs[i] == y), i.e. count < c → count <= c-1.
    ///
    /// MiniZinc semantics: "c is strictly greater than the number of occurrences of y in x."
    pub(super) fn translate_count_gt(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var(&c.args[1])?;
        let count = self.resolve_var(&c.args[2])?;
        let indicators = self.count_eq_indicators(&xs, y)?;
        let n = indicators.len();
        // sum(b_i) < count → sum(b_i) - count <= -1
        let mut coeffs = vec![1i64; n];
        coeffs.push(-1);
        let mut vars = indicators;
        vars.push(count);
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs,
            vars,
            rhs: -1,
        });
        Ok(())
    }

    /// fzn_count_neq(xs, y, c): count(xs[i] == y) != c
    /// Decompose as: sum(b_i) != c via AllDifferent on sum variable.
    pub(super) fn translate_count_neq(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let y = self.resolve_var(&c.args[1])?;
        let count = self.resolve_var(&c.args[2])?;
        let indicators = self.count_eq_indicators(&xs, y)?;
        let n = indicators.len();
        // Create auxiliary sum variable
        let sum_var = self.engine.new_int_var(Domain::new(0, n as i64), None);
        self.var_bounds.insert(sum_var, (0, n as i64));
        // sum_var = sum(b_i)
        let mut eq_coeffs = vec![1i64; n];
        eq_coeffs.push(-1);
        let mut eq_vars = indicators;
        eq_vars.push(sum_var);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: eq_coeffs,
            vars: eq_vars,
            rhs: 0,
        });
        // sum_var != count
        self.engine
            .add_constraint(Constraint::AllDifferent(vec![sum_var, count]));
        Ok(())
    }

    // ── Global Cardinality Constraint (GCC) ─────────────────────────

    /// fzn_global_cardinality(xs, cover, counts):
    /// For each i, count(xs[j] == cover[i]) = counts[i].
    ///
    /// Decompose into per-value count constraints.
    pub(super) fn translate_global_cardinality(&mut self, c: &ConstraintItem) -> Result<()> {
        let xs = self.resolve_var_array(&c.args[0])?;
        let cover = self.resolve_const_int_array(&c.args[1])?;
        let counts = self.resolve_var_array(&c.args[2])?;

        if cover.len() != counts.len() {
            return Err(Fzn2smtError::GlobalCardinalityLengthMismatch {
                cover: cover.len(),
                counts: counts.len(),
            });
        }

        for (idx, &val) in cover.iter().enumerate() {
            let count_var = counts[idx];
            let val_var = self.get_const_var(val);

            let indicators = self.count_eq_indicators(&xs, val_var)?;
            let n = indicators.len();
            // sum(b_i) = count_var → sum(b_i) - count_var = 0
            let mut coeffs = vec![1i64; n];
            coeffs.push(-1);
            let mut vars = indicators;
            vars.push(count_var);
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs,
                vars,
                rhs: 0,
            });
        }
        Ok(())
    }

    // ── NValue constraint ───────────────────────────────────────────

    /// fzn_nvalue(n, xs): exactly n distinct values among xs.
    ///
    /// Decompose: for each value v in union of domains, create indicator
    /// "v appears in xs". Then count appearances = n.
    /// Only feasible for small domain unions.
    pub(super) fn translate_nvalue(&mut self, c: &ConstraintItem) -> Result<()> {
        let n_var = self.resolve_var(&c.args[0])?;
        let xs = self.resolve_var_array(&c.args[1])?;

        if xs.is_empty() {
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1],
                vars: vec![n_var],
                rhs: 0,
            });
            return Ok(());
        }

        // Compute union of all domains
        let mut min_val = i64::MAX;
        let mut max_val = i64::MIN;
        for &x in &xs {
            let (lb, ub) = self.get_var_bounds(x);
            min_val = min_val.min(lb);
            max_val = max_val.max(ub);
        }

        let range = max_val - min_val + 1;
        if range > 10_000 || range <= 0 {
            self.mark_unsupported("fzn_nvalue");
            return Ok(());
        }

        // For each possible value v, create indicator "v appears in xs"
        let mut appear_vars = Vec::new();
        for v in min_val..=max_val {
            let appear = self.engine.new_bool_var(None);
            self.var_bounds.insert(appear, (0, 1));
            appear_vars.push(appear);

            // appear=1 iff exists xs[i] == v
            let val_var = self.get_const_var(v);
            let mut bi_vars = Vec::with_capacity(xs.len());
            for &xi in &xs {
                let bi = self.engine.new_bool_var(None);
                self.var_bounds.insert(bi, (0, 1));
                // bi ↔ (xi == v): full bidirectional reification
                self.add_reif_eq(&[1, -1], &[xi, val_var], 0, bi);
                // appear >= bi (if any bi=1, appear must be 1)
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![bi, appear],
                    rhs: 0,
                });
                bi_vars.push(bi);
            }
            // appear <= sum(bi): appear can be 1 only if some element equals v
            // sum(bi) - appear >= 0
            let n_xs = bi_vars.len();
            let mut le_coeffs = vec![1i64; n_xs];
            le_coeffs.push(-1);
            let mut le_vars = bi_vars;
            le_vars.push(appear);
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: le_coeffs,
                vars: le_vars,
                rhs: 0,
            });
        }

        // n_var = sum(appear_vars)
        let na = appear_vars.len();
        let mut coeffs = vec![1i64; na];
        coeffs.push(-1);
        let mut vars = appear_vars;
        vars.push(n_var);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs,
            vars,
            rhs: 0,
        });
        Ok(())
    }
}
