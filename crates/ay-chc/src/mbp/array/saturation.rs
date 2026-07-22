// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Mbp {
    /// Pre-projection saturation: add model-true array axioms for the current
    /// implicant.
    ///
    /// This historically only saturated array disequalities. For #6047 we also
    /// add read-over-write branch facts for shared `select(store(...), idx)`
    /// terms so the subsequent MBP passes can see the index guards explicitly.
    ///
    /// For each positive `select(store(a, i, v), j)` occurrence:
    /// - if `M(i) == M(j)`, add `i = j`
    /// - if `M(i) != M(j)`, add `i != j` and
    ///   `select(store(a, i, v), j) = select(a, j)`
    ///
    /// For each `a != b` literal where both sides are array-sorted and have
    /// known model values, find a witnessing index `k` where
    /// `M(select(a, k)) != M(select(b, k))` and add `select(a, k) != select(b, k)`.
    ///
    /// Ref: Z3 `mbp_arrays.cpp:1228-1272` (saturate).
    pub(in crate::mbp) fn saturate_array_disequalities(
        &self,
        implicant: &mut Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) {
        let mut new_lits: Vec<Literal> = Vec::new();
        let mut pending_atoms: Vec<ChcExpr> = implicant
            .iter()
            .filter(|lit| lit.positive)
            .map(|lit| lit.atom.clone())
            .collect();
        let mut seen_store_selects: Vec<ChcExpr> = Vec::new();

        let mut cursor = 0;
        while cursor < pending_atoms.len() {
            let atom = pending_atoms[cursor].clone();
            cursor += 1;

            let mut store_selects = Vec::new();
            Self::collect_store_select_terms(&atom, &mut store_selects);
            for (select_term, base_array, store_idx, select_idx) in store_selects {
                if seen_store_selects.contains(&select_term) {
                    continue;
                }
                seen_store_selects.push(select_term.clone());

                for lit in self.saturate_store_select_term(
                    &select_term,
                    &base_array,
                    &store_idx,
                    &select_idx,
                    model,
                ) {
                    if Self::contains_literal(implicant, &lit)
                        || Self::contains_literal(&new_lits, &lit)
                    {
                        continue;
                    }
                    pending_atoms.push(lit.atom.clone());
                    new_lits.push(lit);
                }
            }
        }

        for lit in implicant.iter() {
            if !lit.positive {
                continue;
            }
            let ChcExpr::Op(ChcOp::Ne, args) = &lit.atom else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            // Check both sides are array-sorted.
            let lhs_sort = args[0].sort();
            let ChcSort::Array(idx_sort, val_sort) = &lhs_sort else {
                continue;
            };
            // Get model values for both sides.
            let lhs_val = self.eval_array_model(&args[0], model);
            let rhs_val = self.eval_array_model(&args[1], model);
            let (Some(lhs_arr), Some(rhs_arr)) = (lhs_val, rhs_val) else {
                continue;
            };
            // Find a witnessing index where the arrays differ.
            if let Some(witness_idx) =
                Self::find_witnessing_index(&lhs_arr, &rhs_arr, idx_sort, val_sort)
            {
                let witness = Literal::new(
                    ChcExpr::ne(
                        ChcExpr::select(args[0].as_ref().clone(), witness_idx.clone()),
                        ChcExpr::select(args[1].as_ref().clone(), witness_idx),
                    ),
                    true,
                );
                if !Self::contains_literal(implicant, &witness)
                    && !Self::contains_literal(&new_lits, &witness)
                {
                    new_lits.push(witness);
                }
            }
        }
        implicant.extend(new_lits);
    }

    pub(in crate::mbp) fn collect_store_select_terms(
        expr: &ChcExpr,
        out: &mut Vec<(ChcExpr, ChcExpr, ChcExpr, ChcExpr)>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                if let ChcExpr::Op(ChcOp::Store, store_args) = args[0].as_ref() {
                    if store_args.len() == 3 {
                        out.push((
                            expr.clone(),
                            store_args[0].as_ref().clone(),
                            store_args[1].as_ref().clone(),
                            args[1].as_ref().clone(),
                        ));
                    }
                }
                for arg in args {
                    Self::collect_store_select_terms(arg, out);
                }
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::collect_store_select_terms(arg, out);
                }
            }
            ChcExpr::ConstArray(_, val) => Self::collect_store_select_terms(val, out),
            _ => {}
        }
    }

    pub(in crate::mbp) fn saturate_store_select_term(
        &self,
        select_term: &ChcExpr,
        base_array: &ChcExpr,
        store_idx: &ChcExpr,
        select_idx: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        let Some(store_idx_val) = self.eval_smt_value(store_idx, model) else {
            return Vec::new();
        };
        let Some(select_idx_val) = self.eval_smt_value(select_idx, model) else {
            return Vec::new();
        };

        let mut result = Vec::new();
        if store_idx_val == select_idx_val {
            let eq = ChcExpr::eq(store_idx.clone(), select_idx.clone()).simplify_constants();
            if eq != ChcExpr::Bool(true) {
                result.push(Literal::new(eq, true));
            }
        } else {
            let ne = ChcExpr::ne(store_idx.clone(), select_idx.clone()).simplify_constants();
            if ne != ChcExpr::Bool(true) {
                result.push(Literal::new(ne, true));
            }

            let passthrough = ChcExpr::eq(
                select_term.clone(),
                ChcExpr::select(base_array.clone(), select_idx.clone()),
            )
            .simplify_constants();
            if passthrough != ChcExpr::Bool(true) {
                result.push(Literal::new(passthrough, true));
            }
        }
        result
    }

    pub(in crate::mbp) fn contains_literal(literals: &[Literal], candidate: &Literal) -> bool {
        literals
            .iter()
            .any(|lit| lit.positive == candidate.positive && lit.atom == candidate.atom)
    }
}
