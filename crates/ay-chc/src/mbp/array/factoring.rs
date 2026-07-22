// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Mbp {
    /// Phase 2+3: Factor selects into fresh scalars, then Ackermannize.
    /// Ref: `reference/z3/src/qe/mbp/mbp_arrays.cpp:544-1040`.
    pub(in crate::mbp) fn array_factor_and_ackermannize(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
        idx_sort: &ChcSort,
        val_sort: &ChcSort,
        fresh_vars: &mut Vec<(ChcVar, SmtValue)>,
    ) -> (Vec<Literal>, Vec<Literal>) {
        let mut select_occurrences: Vec<SelectOccurrence> = Vec::new();
        let mut fresh_counter = 0u32;
        let mut select_subst: Vec<(ChcExpr, ChcExpr)> = Vec::new();

        for lit in &with_var {
            self.collect_selects(
                &lit.atom,
                var,
                model,
                idx_sort,
                val_sort,
                &mut select_occurrences,
                &mut fresh_counter,
                &mut select_subst,
                fresh_vars,
            );
        }

        let mut remaining = Vec::new();
        let mut new_constraints: Vec<Literal> = Vec::new();

        for lit in with_var {
            let new_atom = if select_subst.is_empty() {
                lit.atom
            } else {
                lit.atom.substitute_expr_pairs(&select_subst)
            };
            let mut side_constraints = Vec::new();
            let reduced = self
                .reduce_select_store_with_conditions(&new_atom, model, &mut side_constraints)
                .simplify_constants();
            new_constraints.extend(self.normalize_array_literals(side_constraints, model));
            if reduced == ChcExpr::Bool(true) {
                continue;
            }
            if reduced.contains_var_name(&var.name) {
                remaining.push(Literal::new(reduced, lit.positive));
            } else {
                new_constraints.push(Literal::new(reduced, lit.positive));
            }
        }

        // Phase 3: Ackermannization — add disequality constraints between
        // distinct index equivalence classes.
        new_constraints.extend(self.ackermannize_selects(&select_occurrences));
        (remaining, new_constraints)
    }

    pub(in crate::mbp) fn store_nesting_depth(&self, expr: &ChcExpr, var: &ChcVar) -> u32 {
        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return u32::MAX;
        };
        if args.len() != 2 {
            return u32::MAX;
        }

        let lhs_depth = Self::store_chain_depth(&args[0], var);
        let rhs_depth = Self::store_chain_depth(&args[1], var);
        match (lhs_depth, rhs_depth) {
            (Some(_), Some(_)) => 0,
            (Some(depth), None) | (None, Some(depth)) => depth.saturating_add(1),
            (None, None) => u32::MAX,
        }
    }

    pub(in crate::mbp) fn store_chain_depth(expr: &ChcExpr, var: &ChcVar) -> Option<u32> {
        match expr {
            ChcExpr::Var(v) if v == var => Some(0),
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                Self::store_chain_depth(&args[0], var).map(|depth| depth.saturating_add(1))
            }
            _ => None,
        }
    }

    pub(in crate::mbp) fn has_stores_on(&self, expr: &ChcExpr, var: &ChcVar) -> bool {
        Self::store_chain_depth(expr, var).is_some()
    }

    pub(in crate::mbp) fn classify_peq_index(
        &self,
        idx: &ChcExpr,
        diff_indices: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(Option<(ChcExpr, bool)>, Vec<Literal>)> {
        let mut idx_diseq = Vec::new();
        let idx_val = self.eval_smt_value(idx, model);

        for diff_idx in diff_indices {
            if idx == diff_idx {
                return Some((Some((diff_idx.clone(), false)), idx_diseq));
            }

            let diff_val = self.eval_smt_value(diff_idx, model);
            match (&idx_val, &diff_val) {
                (Some(lhs), Some(rhs)) if lhs == rhs => {
                    return Some((Some((diff_idx.clone(), true)), idx_diseq));
                }
                (Some(_), Some(_)) => {
                    idx_diseq.push(Literal::new(
                        ChcExpr::ne(idx.clone(), diff_idx.clone()),
                        true,
                    ));
                }
                _ => return None,
            }
        }

        Some((None, idx_diseq))
    }

    pub(in crate::mbp) fn normalize_array_literals(
        &self,
        literals: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        let mut normalized = Vec::new();
        for lit in literals {
            self.push_normalized_array_literal(&mut normalized, lit, model);
        }
        normalized
    }

    pub(in crate::mbp) fn push_normalized_array_literal(
        &self,
        out: &mut Vec<Literal>,
        lit: Literal,
        model: &FxHashMap<String, SmtValue>,
    ) {
        let mut side_constraints = Vec::new();
        let reduced = self
            .reduce_select_store_with_conditions(&lit.atom, model, &mut side_constraints)
            .simplify_constants();
        for side in side_constraints {
            let simplified = side.atom.simplify_constants();
            if simplified != ChcExpr::Bool(true) {
                out.push(Literal::new(simplified, side.positive));
            }
        }
        if reduced != ChcExpr::Bool(true) {
            out.push(Literal::new(reduced, lit.positive));
        }
    }

    /// Recursively collect `select(var, idx)` and create fresh replacements.
    fn collect_selects(
        &self,
        expr: &ChcExpr,
        var: &ChcVar,
        model: &FxHashMap<String, SmtValue>,
        idx_sort: &ChcSort,
        val_sort: &ChcSort,
        occurrences: &mut Vec<SelectOccurrence>,
        counter: &mut u32,
        subst: &mut Vec<(ChcExpr, ChcExpr)>,
        fresh_vars: &mut Vec<(ChcVar, SmtValue)>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                if self.is_var_expr(&args[0], var) {
                    // Recurse into the index expression first — it may itself
                    // contain `select(var, ...)` (e.g. `select(a, select(a, 0))`).
                    // Without this, nested selects in the index position are missed.
                    self.collect_selects(
                        &args[1],
                        var,
                        model,
                        idx_sort,
                        val_sort,
                        occurrences,
                        counter,
                        subst,
                        fresh_vars,
                    );
                    let idx = args[1].as_ref();
                    let idx_val = self.eval_smt_value(idx, model);
                    // Pre-compute model value for fresh var registration
                    // (Z3 mbp_arrays.cpp:922-923).
                    let fresh_model_val = idx_val.as_ref().and_then(|ival| {
                        model
                            .get(&var.name)
                            .and_then(|arr_val| eval_array_select(arr_val, ival))
                    });
                    // Deduplicate by index model value when available, falling
                    // back to syntactic equality when both are unevaluable.
                    // This avoids unsound false merges (#6096) while still
                    // merging genuinely identical index expressions.
                    let fresh = if let Some(ref val) = idx_val {
                        // Both must evaluate to the same value to merge.
                        occurrences
                            .iter()
                            .find(|o| o.index_model_value.as_ref() == Some(val))
                            .map(|e| e.fresh_var.clone())
                    } else {
                        // Unevaluable: merge only with syntactically identical
                        // unevaluable indices to avoid `ne(x, x)` tautological
                        // falsity in Ackermannization.
                        occurrences
                            .iter()
                            .find(|o| o.index_model_value.is_none() && o.index == *idx)
                            .map(|e| e.fresh_var.clone())
                    };
                    let fresh = fresh.unwrap_or_else(|| {
                        let fv = ChcVar {
                            name: format!("__mbp_sel_{}_{}", var.name, counter),
                            sort: val_sort.clone(),
                        };
                        *counter += 1;
                        // Register model value for new fresh var.
                        if let Some(elem_val) = fresh_model_val {
                            fresh_vars.push((fv.clone(), elem_val));
                        }
                        occurrences.push(SelectOccurrence {
                            index: idx.clone(),
                            fresh_var: fv.clone(),
                            index_model_value: idx_val,
                        });
                        fv
                    });
                    subst.push((
                        ChcExpr::select(ChcExpr::Var(var.clone()), idx.clone()),
                        ChcExpr::Var(fresh),
                    ));
                    return;
                }
                for a in args {
                    self.collect_selects(
                        a,
                        var,
                        model,
                        idx_sort,
                        val_sort,
                        occurrences,
                        counter,
                        subst,
                        fresh_vars,
                    );
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    self.collect_selects(
                        a,
                        var,
                        model,
                        idx_sort,
                        val_sort,
                        occurrences,
                        counter,
                        subst,
                        fresh_vars,
                    );
                }
            }
            ChcExpr::ConstArray(_, val) => {
                self.collect_selects(
                    val,
                    var,
                    model,
                    idx_sort,
                    val_sort,
                    occurrences,
                    counter,
                    subst,
                    fresh_vars,
                );
            }
            _ => {}
        }
    }

    /// Phase 3: Ackermannization — add ordering constraints between distinct
    /// index equivalence classes.
    ///
    /// Z3's approach (reference/z3/src/qe/mbp/mbp_arrays.cpp): sort index
    /// classes by their model value and emit strict inequality chains
    /// `idx_0 < idx_1 < ... < idx_n`. This is stronger than all-pairs
    /// disequality because it also constrains relative ordering.
    ///
    /// For indices with unknown model values, we fall back to pairwise
    /// disequality constraints (#6096).
    fn ackermannize_selects(&self, occurrences: &[SelectOccurrence]) -> Vec<Literal> {
        if occurrences.len() <= 1 {
            return Vec::new();
        }

        // Partition into evaluable (known model value) and unevaluable.
        let mut evaluable: Vec<&SelectOccurrence> = Vec::new();
        let mut unevaluable: Vec<&SelectOccurrence> = Vec::new();
        for occ in occurrences {
            if occ.index_model_value.is_some() {
                evaluable.push(occ);
            } else {
                unevaluable.push(occ);
            }
        }

        let mut lits = Vec::new();

        // Sort evaluable indices by model value and emit ordering chain.
        if evaluable.len() >= 2 {
            // Determine the index sort for choosing the right comparison operator.
            let idx_sort = occurrences[0].index.sort();
            let is_bv = matches!(idx_sort, ChcSort::BitVec(_));

            evaluable.sort_by(|a, b| {
                Self::cmp_smt_values(
                    a.index_model_value
                        .as_ref()
                        .expect("invariant: evaluable partition guarantees Some"),
                    b.index_model_value
                        .as_ref()
                        .expect("invariant: evaluable partition guarantees Some"),
                )
            });

            // Emit chain: idx_0 < idx_1 < ... < idx_n
            for window in evaluable.windows(2) {
                let left = window[0];
                let right = window[1];
                // Skip if same model value (shouldn't happen since collect_selects
                // deduplicates by model value, but be defensive).
                if left.index_model_value == right.index_model_value {
                    continue;
                }
                let constraint = if is_bv {
                    // Use bvult for unsigned BV ordering
                    ChcExpr::Op(
                        ChcOp::BvULt,
                        vec![Arc::new(left.index.clone()), Arc::new(right.index.clone())],
                    )
                } else {
                    // Use < for Int ordering
                    ChcExpr::lt(left.index.clone(), right.index.clone())
                };
                lits.push(Literal::new(constraint, true));
            }
        }

        // For unevaluable indices, add pairwise disequality constraints
        // against all other indices (both evaluable and unevaluable).
        for uneval in &unevaluable {
            for occ in occurrences {
                if std::ptr::eq(*uneval, occ) {
                    continue;
                }
                // Only emit one direction to avoid duplicates between unevaluable pairs.
                if std::ptr::addr_of!(**uneval) < std::ptr::addr_of!(*occ)
                    || occ.index_model_value.is_some()
                {
                    lits.push(Literal::new(
                        ChcExpr::ne(uneval.index.clone(), occ.index.clone()),
                        true,
                    ));
                }
            }
        }

        lits
    }
}
