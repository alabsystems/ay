// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// FlatZinc constraint translation to ay-cp Constraint types.

use crate::error::{Fzn2smtError, Result};
use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
use ay_cp::Domain;
use ay_flatzinc_parser::ast::{ConstraintItem, Expr};

use super::CpContext;

impl CpContext {
    pub(super) fn translate_constraint(&mut self, c: &ConstraintItem) -> Result<()> {
        match c.id.as_str() {
            "int_eq" | "int_ne" | "int_lt" | "int_le" | "int_gt" | "int_ge" | "bool_lt"
            | "bool_le" | "bool_gt" | "bool_ge" => {
                self.translate_int_comparison(c)?;
            }
            "int_lin_eq" | "int_lin_le" => {
                self.translate_int_linear(c)?;
            }
            "int_plus" | "int_minus" | "int_negate" => {
                self.translate_int_arithmetic(c)?;
            }
            "bool_eq" | "bool_not" | "bool_and" | "bool_or" | "bool_clause" | "bool2int" => {
                self.translate_boolean(c)?;
            }
            "array_bool_and" | "array_bool_or" => {
                self.translate_array_boolean(c)?;
            }
            "bool_lin_eq" | "bool_lin_le" => {
                self.translate_int_linear(c)?;
            }
            "array_int_element"
            | "array_var_int_element"
            | "array_bool_element"
            | "array_var_bool_element" => {
                self.translate_element(c)?;
            }
            "set_in" => self.translate_set_in(c)?,
            // Set variable constraints (boolean indicator encoding)
            "set_card" => self.translate_set_card(c)?,
            "set_intersect" => self.translate_set_intersect(c)?,
            "set_union" => self.translate_set_union(c)?,
            "set_diff" => self.translate_set_diff(c)?,
            "set_symdiff" => self.translate_set_symdiff(c)?,
            "set_subset" => self.translate_set_subset(c)?,
            "set_superset" => self.translate_set_superset(c)?,
            "set_eq" => self.translate_set_eq(c)?,
            "set_ne" => self.translate_set_ne(c)?,
            "set_lt" => self.translate_set_lt(c)?,
            "set_le" => self.translate_set_le(c)?,
            "array_set_element" => self.translate_array_set_element(c)?,
            "fzn_all_different_int" | "alldifferent" | "alldifferent_int" | "all_different_int" => {
                let vars = self.resolve_var_array(&c.args[0])?;
                self.engine.add_constraint(Constraint::AllDifferent(vars));
            }
            "fzn_table_int" | "table_int" => {
                self.translate_table(c)?;
            }
            "fzn_circuit" | "circuit" => {
                self.translate_circuit(c)?;
            }
            "fzn_cumulative" | "cumulative" => {
                self.translate_cumulative(c)?;
            }
            "fzn_inverse" | "inverse" => {
                self.translate_inverse(c)?;
            }
            "fzn_diffn" | "diffn" => {
                self.translate_diffn(c)?;
            }
            // Reified integer/boolean comparisons
            "int_eq_reif" | "int_ne_reif" | "int_le_reif" | "int_lt_reif" | "int_ge_reif"
            | "int_gt_reif" | "bool_le_reif" | "bool_gt_reif" | "bool_ge_reif" => {
                self.translate_int_comparison_reif(c)?;
            }
            // Reified linear constraints
            "int_lin_le_reif" | "int_lin_eq_reif" | "bool_lin_le_reif" | "bool_lin_eq_reif" => {
                self.translate_int_linear_reif(c)?;
            }
            // Reified linear not-equal
            "int_lin_ne_reif" | "bool_lin_ne_reif" => {
                self.translate_int_linear_ne_reif(c)?;
            }
            // Reified boolean constraints
            "bool_eq_reif" => {
                self.translate_bool_eq_reif(c)?;
            }
            "bool_not_reif" | "bool_ne_reif" => {
                self.translate_bool_not_reif(c)?;
            }
            // Reified boolean comparisons
            "bool_lt_reif" => self.translate_bool_lt_reif(c)?,
            // Reified boolean and/or
            "bool_and_reif" => self.translate_bool_and_reif(c)?,
            "bool_or_reif" => self.translate_bool_or_reif(c)?,
            "bool_clause_reif" => self.translate_bool_clause_reif(c)?,
            // Half-reification (implication)
            "int_le_imp" | "int_lt_imp" | "int_eq_imp" | "int_ne_imp" | "int_ge_imp"
            | "int_gt_imp" | "bool_lt_imp" | "bool_le_imp" | "bool_gt_imp" | "bool_ge_imp" => {
                self.translate_int_comparison_imp(c)?;
            }
            "int_lin_le_imp" | "int_lin_eq_imp" | "bool_lin_le_imp" | "bool_lin_eq_imp" => {
                self.translate_int_linear_imp(c)?;
            }
            // Half-reified linear not-equal
            "int_lin_ne_imp" | "bool_lin_ne_imp" => {
                self.translate_int_linear_ne_imp(c)?;
            }
            "int_times" => self.translate_int_times(c)?,
            "int_abs" => self.translate_int_abs(c)?,
            "int_min" => self.translate_int_min(c)?,
            "int_max" => self.translate_int_max(c)?,
            "int_lin_ne" => self.translate_int_lin_ne(c)?,
            "bool_xor" => self.translate_bool_xor(c)?,
            "int_div" => self.translate_int_div(c)?,
            "int_mod" => self.translate_int_mod(c)?,
            "int_pow" => self.translate_int_pow(c)?,
            // Set membership reification
            "set_in_reif" => self.translate_set_in_reif(c)?,
            "set_eq_reif" => self.translate_set_eq_reif(c)?,
            "set_ne_reif" => self.translate_set_ne_reif(c)?,
            "set_subset_reif" => self.translate_set_subset_reif(c)?,
            "set_superset_reif" => self.translate_set_superset_reif(c)?,
            "set_le_reif" => self.translate_set_le_reif(c)?,
            "set_lt_reif" => self.translate_set_lt_reif(c)?,
            // N-ary max/min
            "array_int_maximum" | "fzn_array_int_maximum" => {
                self.translate_array_int_maximum(c)?;
            }
            "array_int_minimum" | "fzn_array_int_minimum" => {
                self.translate_array_int_minimum(c)?;
            }
            // Counting constraints
            "fzn_count_eq" | "count_eq" => self.translate_count_eq(c)?,
            "fzn_count_leq" | "count_leq" => self.translate_count_leq(c)?,
            "fzn_count_geq" | "count_geq" => self.translate_count_geq(c)?,
            "fzn_count_lt" | "count_lt" => self.translate_count_lt(c)?,
            "fzn_count_gt" | "count_gt" => self.translate_count_gt(c)?,
            "fzn_count_neq" | "count_neq" => self.translate_count_neq(c)?,
            // Lexicographic ordering
            "fzn_lex_lesseq_int" | "lex_lesseq_int" => self.translate_lex_lesseq_int(c)?,
            "fzn_lex_less_int" | "lex_less_int" => self.translate_lex_less_int(c)?,
            // Global cardinality
            "fzn_global_cardinality" | "global_cardinality" => {
                self.translate_global_cardinality(c)?;
            }
            // NValue
            "fzn_nvalue" | "nvalue" => self.translate_nvalue(c)?,
            name if name.ends_with("_reif") || name.ends_with("_imp") => {
                self.mark_unsupported(&c.id);
            }
            _ => {
                self.mark_unsupported(&c.id);
            }
        }
        Ok(())
    }

    fn translate_int_comparison(&mut self, c: &ConstraintItem) -> Result<()> {
        if c.id == "int_eq" && self.translate_fixed_array_access_eq(c)? {
            return Ok(());
        }
        if c.args.iter().any(is_array_access) {
            self.mark_unsupported(&c.id);
            return Ok(());
        }
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;
        match c.id.as_str() {
            "int_eq" => {
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![a, b],
                    rhs: 0,
                });
            }
            "int_ne" => {
                // Use PairwiseNeq(x, y, 0) for a != b: lighter than
                // AllDifferent([a, b]) which creates a bounds propagator.
                self.engine.add_constraint(Constraint::PairwiseNeq {
                    x: a,
                    y: b,
                    offset: 0,
                });
            }
            "int_lt" | "bool_lt" => {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![a, b],
                    rhs: -1,
                });
            }
            "int_le" | "bool_le" => {
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![a, b],
                    rhs: 0,
                });
            }
            "int_gt" | "bool_gt" => {
                self.engine.add_constraint(Constraint::LinearGe {
                    coeffs: vec![1, -1],
                    vars: vec![a, b],
                    rhs: 1,
                });
            }
            "int_ge" | "bool_ge" => {
                self.engine.add_constraint(Constraint::LinearGe {
                    coeffs: vec![1, -1],
                    vars: vec![a, b],
                    rhs: 0,
                });
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn translate_int_linear(&mut self, c: &ConstraintItem) -> Result<()> {
        let mut coeffs = self.resolve_const_int_array(&c.args[0])?;
        let mut vars = self.resolve_var_array(&c.args[1])?;
        // RHS can be a constant or a variable. If variable, move to LHS with coeff -1.
        let rhs = if let Some(k) = self.eval_const_int(&c.args[2]) {
            k
        } else {
            let rhs_var = self.resolve_var(&c.args[2])?;
            coeffs.push(-1);
            vars.push(rhs_var);
            0
        };
        match c.id.as_str() {
            "int_lin_eq" | "bool_lin_eq" => {
                self.engine
                    .add_constraint(Constraint::LinearEq { coeffs, vars, rhs });
            }
            "int_lin_le" | "bool_lin_le" => {
                self.engine
                    .add_constraint(Constraint::LinearLe { coeffs, vars, rhs });
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn translate_int_arithmetic(&mut self, c: &ConstraintItem) -> Result<()> {
        match c.id.as_str() {
            "int_plus" => {
                // a + b = c
                let a = self.resolve_var(&c.args[0])?;
                let b = self.resolve_var(&c.args[1])?;
                let r = self.resolve_var(&c.args[2])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, 1, -1],
                    vars: vec![a, b, r],
                    rhs: 0,
                });
            }
            "int_minus" => {
                // a - b = c
                let a = self.resolve_var(&c.args[0])?;
                let b = self.resolve_var(&c.args[1])?;
                let r = self.resolve_var(&c.args[2])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1, -1],
                    vars: vec![a, b, r],
                    rhs: 0,
                });
            }
            "int_negate" => {
                // b = -a → a + b = 0
                let a = self.resolve_var(&c.args[0])?;
                let b = self.resolve_var(&c.args[1])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, 1],
                    vars: vec![a, b],
                    rhs: 0,
                });
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn translate_boolean(&mut self, c: &ConstraintItem) -> Result<()> {
        match c.id.as_str() {
            "bool_eq" | "bool2int" => {
                let a = self.resolve_var(&c.args[0])?;
                let b = self.resolve_var(&c.args[1])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![a, b],
                    rhs: 0,
                });
            }
            "bool_not" => {
                // not(a) = b → a + b = 1
                let a = self.resolve_var(&c.args[0])?;
                let b = self.resolve_var(&c.args[1])?;
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, 1],
                    vars: vec![a, b],
                    rhs: 1,
                });
            }
            "bool_and" => self.translate_bool_and(c)?,
            "bool_or" => self.translate_bool_or(c)?,
            "bool_clause" => self.translate_bool_clause(c)?,
            _ => unreachable!(),
        }
        Ok(())
    }

    fn translate_bool_and(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;

        if c.args.len() == 2 {
            // 2-arg: assert a AND b (both must be 1).
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1],
                vars: vec![a],
                rhs: 1,
            });
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1],
                vars: vec![b],
                rhs: 1,
            });
            return Ok(());
        }

        // 3-arg: r = a ∧ b: r <= a, r <= b, a + b - r <= 1
        let r = self.resolve_var(&c.args[2])?;
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

    fn translate_bool_or(&mut self, c: &ConstraintItem) -> Result<()> {
        let a = self.resolve_var(&c.args[0])?;
        let b = self.resolve_var(&c.args[1])?;

        if c.args.len() == 2 {
            // 2-arg: assert a OR b (at least one must be 1).
            self.engine.add_constraint(Constraint::LinearGe {
                coeffs: vec![1, 1],
                vars: vec![a, b],
                rhs: 1,
            });
            return Ok(());
        }

        // 3-arg: r = a ∨ b: a <= r, b <= r, r - a - b <= 0
        let r = self.resolve_var(&c.args[2])?;
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

    fn translate_bool_clause(&mut self, c: &ConstraintItem) -> Result<()> {
        // pos1 ∨ ... ∨ posK ∨ ¬neg1 ∨ ... ∨ ¬negL
        // In {0,1}: sum(pos) - sum(neg) >= 1 - L
        let pos = self.resolve_var_array(&c.args[0])?;
        let neg = self.resolve_var_array(&c.args[1])?;
        let neg_len = neg.len() as i64;
        let mut coeffs = vec![1i64; pos.len()];
        coeffs.extend(vec![-1i64; neg.len()]);
        let mut vars = pos;
        vars.extend(neg);
        self.engine.add_constraint(Constraint::LinearGe {
            coeffs,
            vars,
            rhs: 1 - neg_len,
        });
        Ok(())
    }

    fn translate_array_boolean(&mut self, c: &ConstraintItem) -> Result<()> {
        let bools = self.resolve_var_array(&c.args[0])?;
        let result = self.resolve_var(&c.args[1])?;
        let n = bools.len() as i64;

        match c.id.as_str() {
            "array_bool_and" => {
                // r = AND(b1,...,bn): r <= bi for all i, sum(bi) - r <= n-1
                for &b in &bools {
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, -1],
                        vars: vec![result, b],
                        rhs: 0,
                    });
                }
                let mut coeffs = vec![1i64; bools.len()];
                coeffs.push(-1);
                let mut vars = bools;
                vars.push(result);
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs,
                    vars,
                    rhs: n - 1,
                });
            }
            "array_bool_or" => {
                // r = OR(b1,...,bn): bi <= r for all i, r - sum(bi) <= 0
                for &b in &bools {
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, -1],
                        vars: vec![b, result],
                        rhs: 0,
                    });
                }
                let mut coeffs = vec![-1i64; bools.len()];
                coeffs.push(1);
                let mut vars = bools;
                vars.push(result);
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs,
                    vars,
                    rhs: 0,
                });
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn translate_element(&mut self, c: &ConstraintItem) -> Result<()> {
        let index = self.resolve_var(&c.args[0])?;
        let Some((array_lo, array)) = self.resolve_element_array(&c.args[1], index, &c.id)? else {
            return Ok(());
        };
        let result = self.resolve_var(&c.args[2])?;
        if array.is_empty() {
            return Err(Fzn2smtError::ArrayElementEmptyArray {
                constraint: c.id.clone(),
            });
        }
        // ay-cp Element is zero-indexed; named FlatZinc arrays retain their
        // declared lower bound, while inline literals start at one.
        let n = array.len() as i64;
        let index_0 = self.engine.new_int_var(Domain::new(0, n - 1), None);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, -1],
            vars: vec![index, index_0],
            rhs: array_lo,
        });
        self.engine.add_constraint(Constraint::Element {
            index: index_0,
            array,
            result,
        });
        Ok(())
    }

    fn translate_fixed_array_access_eq(&mut self, c: &ConstraintItem) -> Result<bool> {
        let Some((name, index, value)) = self.fixed_array_access_eq_parts(c) else {
            if c.args.iter().any(is_array_access) {
                self.mark_unsupported(&c.id);
                return Ok(true);
            }
            return Ok(false);
        };
        let slot = if let Some(array) = self.array_var_map.get(name) {
            let lo = self.array_var_ranges.get(name).map_or(1, |(lo, _)| *lo);
            let Ok(pos) = usize::try_from(i128::from(index) - i128::from(lo)) else {
                self.mark_unsupported(&c.id);
                return Ok(true);
            };
            let Some(&slot) = array.get(pos) else {
                self.mark_unsupported(&c.id);
                return Ok(true);
            };
            slot
        } else if let Some(array) = self.par_int_arrays.get(name) {
            let lo = self.par_array_ranges.get(name).map_or(1, |(lo, _)| *lo);
            let Ok(pos) = usize::try_from(i128::from(index) - i128::from(lo)) else {
                self.mark_unsupported(&c.id);
                return Ok(true);
            };
            let Some(&parameter_value) = array.get(pos) else {
                self.mark_unsupported(&c.id);
                return Ok(true);
            };
            self.get_const_var(parameter_value)
        } else {
            if self
                .array_var_ranges
                .get(name)
                .is_some_and(|(lo, hi)| index < *lo || index > *hi)
            {
                self.mark_unsupported(&c.id);
                return Ok(true);
            }
            self.materialize_fixed_array_slot(name, index, value)
        };
        let fixed = self.get_const_var(value);
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1, -1],
            vars: vec![slot, fixed],
            rhs: 0,
        });
        Ok(true)
    }

    fn fixed_array_access_eq_parts<'a>(
        &self,
        c: &'a ConstraintItem,
    ) -> Option<(&'a str, i64, i64)> {
        match (&c.args[0], &c.args[1]) {
            (Expr::ArrayAccess(name, index), value) => Some((
                name.as_str(),
                self.eval_const_int(index)?,
                self.eval_const_int(value)?,
            )),
            (value, Expr::ArrayAccess(name, index)) => Some((
                name.as_str(),
                self.eval_const_int(index)?,
                self.eval_const_int(value)?,
            )),
            _ => None,
        }
    }

    fn materialize_fixed_array_slot(&mut self, name: &str, index: i64, value: i64) -> IntVarId {
        let key = fixed_array_slot_key(name, index);
        if let Some(&id) = self.var_map.get(&key) {
            return id;
        }
        let id = self
            .engine
            .new_int_var(Domain::singleton(value), Some(&key));
        self.var_map.insert(key, id);
        self.var_bounds.insert(id, (value, value));
        id
    }

    fn resolve_element_array(
        &mut self,
        expr: &Expr,
        index: IntVarId,
        constraint: &str,
    ) -> Result<Option<(i64, Vec<IntVarId>)>> {
        if let Ok((lo, _, array)) = self.resolve_var_array_with_bounds(expr) {
            return Ok(Some((lo, array)));
        }
        if constraint != "array_var_int_element" {
            self.mark_unsupported(constraint);
            return Ok(None);
        }
        let Expr::Ident(name) = expr else {
            self.mark_unsupported(constraint);
            return Ok(None);
        };
        let (index_lo, index_hi) = self
            .array_var_ranges
            .get(name)
            .copied()
            .unwrap_or_else(|| self.get_var_bounds(index));
        let Ok(array_len) = usize::try_from(i128::from(index_hi) - i128::from(index_lo) + 1) else {
            self.mark_unsupported(constraint);
            return Ok(None);
        };
        if array_len == 0 || array_len > 10_000 {
            self.mark_unsupported(constraint);
            return Ok(None);
        }

        let mut array = Vec::with_capacity(array_len);
        for pos in index_lo..=index_hi {
            let key = fixed_array_slot_key(name, pos);
            let Some(&slot) = self.var_map.get(&key) else {
                self.mark_unsupported(constraint);
                return Ok(None);
            };
            let (lo, hi) = self.get_var_bounds(slot);
            if lo != hi {
                self.mark_unsupported(constraint);
                return Ok(None);
            }
            array.push(slot);
        }
        self.array_var_map.insert(name.clone(), array.clone());
        if !self.register_fixed_array_output(name, &array) {
            self.mark_unsupported(constraint);
            return Ok(None);
        }
        Ok(Some((index_lo, array)))
    }

    fn register_fixed_array_output(&mut self, name: &str, array: &[IntVarId]) -> bool {
        let mut ok = true;
        for output in &mut self.output_vars {
            if output.fzn_name != name
                || !output.is_array
                || !output.var_ids.is_empty()
                || !output.set_var_names.is_empty()
            {
                continue;
            }
            if output.array_range.is_some_and(|(lo, hi)| {
                hi < lo
                    || usize::try_from(i128::from(hi) - i128::from(lo) + 1).ok()
                        != Some(array.len())
            }) {
                ok = false;
                continue;
            }
            output.var_ids = array.to_vec();
        }
        ok
    }

    fn translate_table(&mut self, c: &ConstraintItem) -> Result<()> {
        let vars = self.resolve_var_array(&c.args[0])?;
        let flat = self.resolve_const_int_array(&c.args[1])?;
        let arity = vars.len();
        if arity > 0 {
            if flat.len() % arity != 0 {
                return Err(Fzn2smtError::TableTupleLengthMismatch {
                    values: flat.len(),
                    arity,
                });
            }
            let tuples: Vec<Vec<i64>> = flat.chunks(arity).map(<[i64]>::to_vec).collect();
            self.engine
                .add_constraint(Constraint::Table { vars, tuples });
        }
        Ok(())
    }

    fn translate_cumulative(&mut self, c: &ConstraintItem) -> Result<()> {
        let starts = self.resolve_var_array(&c.args[0])?;
        // Durations and demands may be variable (e.g., yumi-dynamic benchmark).
        // Use resolve_var_array which handles both constant and variable arrays.
        let durations = self.resolve_var_array(&c.args[1])?;
        let demands = self.resolve_var_array(&c.args[2])?;
        if starts.len() != durations.len() || starts.len() != demands.len() {
            return Err(Fzn2smtError::CumulativeArrayLengthMismatch {
                starts: starts.len(),
                durations: durations.len(),
                resources: demands.len(),
            });
        }
        let capacity = self.resolve_const_int(&c.args[3])?;
        self.engine.add_constraint(Constraint::Cumulative {
            starts,
            durations,
            demands,
            capacity,
        });
        Ok(())
    }
}

fn fixed_array_slot_key(name: &str, index: i64) -> String {
    format!("{name}[{index}]")
}

fn is_array_access(expr: &Expr) -> bool {
    matches!(expr, Expr::ArrayAccess(_, _))
}
