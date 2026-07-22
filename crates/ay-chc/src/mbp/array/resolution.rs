// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Mbp {
    /// Project out a single array-sorted variable from the implicant.
    /// Entry point called from `theory.rs` for `ChcSort::Array`.
    pub(in crate::mbp) fn project_array_var(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        let (result, _fresh) = self.project_array_var_with_fresh(var, with_var, without_var, model);
        result
    }

    /// Project out an array variable and return fresh variable model values.
    ///
    /// Like `project_array_var`, but also returns `(ChcVar, SmtValue)` pairs
    /// for each fresh `__mbp_sel_*` / `__mbp_arr_*` variable created during
    /// projection. The caller registers these in the model so downstream
    /// phases (FM projection, Ackermannization) can evaluate expressions
    /// containing them.
    ///
    /// Matches Z3 `mbp_arrays.cpp:194-195` and `:922-923` where fresh
    /// variables are immediately registered in the model at creation time.
    pub(in crate::mbp) fn project_array_var_with_fresh(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> (Vec<Literal>, Vec<(ChcVar, SmtValue)>) {
        let mut fresh_vars = Vec::new();
        let ChcSort::Array(idx_sort, val_sort) = &var.sort else {
            return (without_var, fresh_vars);
        };

        // Phase 1: Equality resolution.
        let (with_var, extra_lits) =
            self.array_resolve_equalities(var, with_var, model, &mut fresh_vars);
        let mut result = without_var;
        result.extend(extra_lits);

        if with_var.is_empty() {
            return (result, fresh_vars);
        }

        // Phase 2+3: Select factoring + Ackermannization.
        let (remaining, select_lits) = self.array_factor_and_ackermannize(
            var,
            with_var,
            model,
            idx_sort,
            val_sort,
            &mut fresh_vars,
        );
        result.extend(select_lits);

        // Drop remaining literals that still mention the array variable (sound
        // over-approximation for non-select/non-equality contexts).
        for lit in remaining {
            if !lit.atom.contains_var_name(&var.name) {
                result.push(lit);
            }
        }
        (result, fresh_vars)
    }

    /// Phase 1: Resolve array equalities to substitute `var` away.
    /// Ref: `reference/z3/src/qe/mbp/mbp_arrays.cpp:59-537`.
    pub(in crate::mbp) fn array_resolve_equalities(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
        fresh_vars: &mut Vec<(ChcVar, SmtValue)>,
    ) -> (Vec<Literal>, Vec<Literal>) {
        let mut extra = Vec::new();
        let mut equality_indices: Vec<(usize, u32)> = with_var
            .iter()
            .enumerate()
            .filter(|(_, lit)| lit.positive)
            .map(|(i, lit)| (i, self.store_nesting_depth(&lit.atom, var)))
            .collect();
        equality_indices.sort_by_key(|(_, depth)| *depth);

        for (i, _depth) in equality_indices {
            let atom = with_var[i].atom.clone();
            if let Some(subst_term) =
                self.find_array_equality_subst(var, &atom, model, &mut extra, fresh_vars)
            {
                let mut remaining = Vec::new();
                for (j, other_lit) in with_var.into_iter().enumerate() {
                    if j == i {
                        continue;
                    }
                    let new_atom = other_lit
                        .atom
                        .substitute(&[(var.clone(), subst_term.clone())]);
                    let simplified = new_atom.simplify_constants();
                    if simplified == ChcExpr::Bool(true) {
                        continue;
                    }
                    if simplified.contains_var_name(&var.name) {
                        remaining.push(Literal::new(simplified, other_lit.positive));
                    } else {
                        self.push_normalized_array_literal(
                            &mut extra,
                            Literal::new(simplified, other_lit.positive),
                            model,
                        );
                    }
                }
                let extra = self.normalize_array_literals(extra, model);
                return (remaining, extra);
            }
        }
        (with_var, self.normalize_array_literals(extra, model))
    }

    /// Extract a substitution for `var` from an equality: `var = t`, `t = var`,
    /// or `store(var, i, v) = t` (inverted).
    pub(in crate::mbp) fn find_array_equality_subst(
        &self,
        var: &ChcVar,
        atom: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        extra: &mut Vec<Literal>,
        fresh_vars: &mut Vec<(ChcVar, SmtValue)>,
    ) -> Option<ChcExpr> {
        let ChcExpr::Op(ChcOp::Eq, args) = atom else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (&args[0], &args[1]);

        if self.is_var_expr(lhs, var) {
            return Some(rhs.as_ref().clone());
        }
        if self.is_var_expr(rhs, var) {
            return Some(lhs.as_ref().clone());
        }
        // Try inverting store chains on either side.
        if let Some(t) = self.invert_store_equality(var, lhs, rhs, model, extra, fresh_vars) {
            return Some(t);
        }
        self.invert_store_equality(var, rhs, lhs, model, extra, fresh_vars)
    }

    /// Invert `store(...store(var, i1, v1)..., in, vn) = other` to get a
    /// substitution for `var`.  Adds side constraints `select(other, ik) = vk`.
    /// Ref: `reference/z3/src/qe/mbp/mbp_arrays.cpp:245-380`.
    pub(in crate::mbp) fn invert_store_equality(
        &self,
        var: &ChcVar,
        store_side: &Arc<ChcExpr>,
        other_side: &Arc<ChcExpr>,
        model: &FxHashMap<String, SmtValue>,
        extra: &mut Vec<Literal>,
        fresh_vars: &mut Vec<(ChcVar, SmtValue)>,
    ) -> Option<ChcExpr> {
        let mut peq = PartialArrayEq {
            lhs: store_side.as_ref().clone(),
            rhs: other_side.as_ref().clone(),
            diff_indices: Vec::new(),
        };

        loop {
            if !self.has_stores_on(&peq.lhs, var) {
                if self.has_stores_on(&peq.rhs, var) {
                    std::mem::swap(&mut peq.lhs, &mut peq.rhs);
                }
            }

            match &peq.lhs {
                ChcExpr::Var(v) if v == var => break,
                ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                    let arr0 = args[0].as_ref().clone();
                    let idx = args[1].as_ref().clone();
                    let stored_val = args[2].as_ref().clone();
                    let (matching_diff, idx_diseq) =
                        self.classify_peq_index(&idx, &peq.diff_indices, model)?;

                    if let Some((diff_idx, needs_eq_lit)) = matching_diff {
                        if needs_eq_lit {
                            extra.push(Literal::new(ChcExpr::eq(idx, diff_idx), true));
                        }
                        peq.lhs = arr0;
                    } else {
                        extra.extend(idx_diseq);
                        extra.push(Literal::new(
                            ChcExpr::eq(ChcExpr::select(peq.rhs.clone(), idx.clone()), stored_val),
                            true,
                        ));
                        peq.diff_indices.push(idx);
                        peq.lhs = arr0;
                    }
                }
                _ if peq.lhs == peq.rhs => return None,
                _ => return None,
            }
        }

        if peq.rhs.contains_var_name(&var.name) {
            return None;
        }

        let mut subst_term = peq.rhs;
        let arr_model_val = model.get(&var.name);
        for (k, diff_idx) in peq.diff_indices.iter().enumerate() {
            let val_sort = self.select_sort(&var.sort);
            let fresh_var = ChcVar {
                name: format!("__mbp_arr_{}_{}", var.name, k),
                sort: val_sort,
            };
            // Register fresh var with model value (Z3 mbp_arrays.cpp:194-195).
            if let Some(arr_val) = arr_model_val {
                if let Some(idx_val) = self.eval_smt_value(diff_idx, model) {
                    if let Some(elem_val) = eval_array_select(arr_val, &idx_val) {
                        fresh_vars.push((fresh_var.clone(), elem_val));
                    }
                }
            }
            subst_term = ChcExpr::store(subst_term, diff_idx.clone(), ChcExpr::Var(fresh_var));
        }
        Some(subst_term)
    }
}
