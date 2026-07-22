// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cube extraction from SMT models.
//!
//! Functions for building cubes (conjunctive state descriptions) from SMT
//! solver models. Extracted from core.rs for file size management.
//!
//! Submodules:
//! - `mbp`: Model-based projection (MBP) cube extraction strategies.

use super::{cube, Arc, ChcExpr, ChcSort, ChcVar, FxHashMap, PdrSolver, PredicateId, SmtValue};

mod mbp;

impl PdrSolver {
    /// Build a concrete cube over canonical vars for a predicate, using `model` values for `args`.
    /// Array-sorted variables generate `select(arr, idx) = val` constraints from model entries.
    ///
    /// #8660: When property_array_indices has entries for this predicate, only emit array
    /// select constraints for property-relevant indices (dramatically reducing cube size).
    /// When the property doesn't use arrays at all, skip array selects entirely.
    pub(in crate::pdr::solver) fn cube_from_model(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }

        // #8660: Check if the property is purely scalar (no array ops).
        // If so, skip all array select constraints — they're not needed.
        let skip_array_selects =
            self.uses_arrays && !self.property_array_indices.property_uses_arrays;

        // #8660: Check if we have property-directed indices for this predicate.
        let has_property_indices = self.property_array_indices.has_indices_for(pred);

        let mut conjuncts = Vec::with_capacity(args.len());
        for (param_pos, (canon, arg)) in vars.iter().zip(args.iter()).enumerate() {
            if matches!(canon.sort, ChcSort::Array(_, _)) {
                // #8660: Skip array selects entirely when property is purely scalar
                if skip_array_selects {
                    continue;
                }

                // #8660: When we have property indices, only emit selects for those indices
                if has_property_indices {
                    let property_indices = self.property_array_indices.indices_for(pred, param_pos);
                    if !property_indices.is_empty() {
                        let array_model_val = match arg {
                            ChcExpr::Var(v) => model.get(&v.name),
                            _ => None,
                        };
                        if let Some(select_conjuncts) = Self::array_select_constraints_for_indices(
                            canon,
                            array_model_val,
                            property_indices,
                        ) {
                            conjuncts.extend(select_conjuncts);
                        }
                        continue;
                    }
                    // No property indices for this array param — skip it
                    continue;
                }

                // Fallback: no property indices available, use all model entries
                let array_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(select_conjuncts) =
                    Self::array_select_constraints_from_model(canon, array_model_val)
                {
                    conjuncts.extend(select_conjuncts);
                }
                continue;
            }
            if matches!(canon.sort, ChcSort::Datatype { .. }) {
                let dt_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(dt_conjuncts) = Self::dt_constraints_from_model(canon, dt_model_val) {
                    conjuncts.extend(dt_conjuncts);
                }
                continue;
            }
            let value = Self::cube_scalar_value_expr(arg, &canon.sort, model)?;
            match (&canon.sort, value) {
                (ChcSort::Bool, ChcExpr::Bool(true)) => conjuncts.push(ChcExpr::var(canon.clone())),
                (ChcSort::Bool, ChcExpr::Bool(false)) => {
                    conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                }
                (_, v) => conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), v)),
            }
        }
        if conjuncts.is_empty() {
            return None;
        }
        Some(ChcExpr::and_all(conjuncts))
    }

    /// Build array select constraints for ONLY the specified property-relevant indices (#8660).
    ///
    /// Instead of emitting `select(arr, idx) = val` for every model entry, only emit
    /// constraints for the indices that appear in the property clause. This produces
    /// much smaller cubes for multi-array problems.
    pub(in crate::pdr) fn array_select_constraints_for_indices(
        canon: &ChcVar,
        model_val: Option<&SmtValue>,
        property_indices: &[ChcExpr],
    ) -> Option<Vec<ChcExpr>> {
        let ChcSort::Array(ref idx_sort, ref val_sort) = canon.sort else {
            return None;
        };
        let model_val = model_val?;

        match model_val {
            SmtValue::ConstArray(default) => {
                // For const arrays, the value at any index is the default.
                // Emit select constraints for each property index.
                let default_expr = Self::smt_value_to_scalar_expr(default, val_sort)?;
                let mut conjuncts = Vec::with_capacity(property_indices.len());
                for idx in property_indices {
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::select(ChcExpr::var(canon.clone()), idx.clone()),
                        default_expr.clone(),
                    ));
                }
                if conjuncts.is_empty() {
                    None
                } else {
                    Some(conjuncts)
                }
            }
            SmtValue::ArrayMap {
                default, entries, ..
            } => {
                let default_expr = Self::smt_value_to_scalar_expr(default, val_sort);
                let mut conjuncts = Vec::with_capacity(property_indices.len());

                for prop_idx in property_indices {
                    // Try to find this index in the model entries
                    let val_expr = entries
                        .iter()
                        .find_map(|(idx_val, elem_val)| {
                            let idx_expr = Self::smt_value_to_scalar_expr(idx_val, idx_sort)?;
                            if &idx_expr == prop_idx {
                                Self::smt_value_to_scalar_expr(elem_val, val_sort)
                            } else {
                                None
                            }
                        })
                        .or_else(|| default_expr.clone());

                    if let Some(val) = val_expr {
                        conjuncts.push(ChcExpr::eq(
                            ChcExpr::select(ChcExpr::var(canon.clone()), prop_idx.clone()),
                            val,
                        ));
                    }
                }

                if conjuncts.is_empty() {
                    None
                } else {
                    Some(conjuncts)
                }
            }
            _ => None,
        }
    }

    /// #6047: Convert an array model value to constraints over array contents.
    pub(in crate::pdr) fn array_select_constraints_from_model(
        canon: &ChcVar,
        model_val: Option<&SmtValue>,
    ) -> Option<Vec<ChcExpr>> {
        let ChcSort::Array(ref idx_sort, ref val_sort) = canon.sort else {
            return None;
        };
        let model_val = model_val?;
        match model_val {
            SmtValue::ConstArray(default) => {
                let default_expr = Self::smt_value_to_scalar_expr(default, val_sort)?;
                let const_arr = ChcExpr::ConstArray(*idx_sort.clone(), Arc::new(default_expr));
                Some(vec![ChcExpr::eq(ChcExpr::var(canon.clone()), const_arr)])
            }
            SmtValue::ArrayMap {
                default, entries, ..
            } => {
                if entries.is_empty() {
                    let default_expr = Self::smt_value_to_scalar_expr(default, val_sort)?;
                    let const_arr = ChcExpr::ConstArray(*idx_sort.clone(), Arc::new(default_expr));
                    return Some(vec![ChcExpr::eq(ChcExpr::var(canon.clone()), const_arr)]);
                }
                let mut conjuncts = Vec::with_capacity(entries.len());
                for (idx_val, elem_val) in entries {
                    let idx_expr = Self::smt_value_to_scalar_expr(idx_val, idx_sort)?;
                    let val_expr = Self::smt_value_to_scalar_expr(elem_val, val_sort)?;
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::select(ChcExpr::var(canon.clone()), idx_expr),
                        val_expr,
                    ));
                }
                Some(conjuncts)
            }
            _ => None,
        }
    }

    fn smt_value_to_scalar_expr(val: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
        match (val, sort) {
            (SmtValue::Int(n), ChcSort::Int | ChcSort::Real) => Some(ChcExpr::int(*n)),
            // Beyond-i128 witness: exact Horner encoding (never wraps).
            (SmtValue::BigInt(b), ChcSort::Int) => Some(ChcExpr::from_bigint(b.as_ref().clone())),
            (SmtValue::Real(r), ChcSort::Real) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64().unwrap_or(0);
                let d = r.denom().to_i64().unwrap_or(1);
                Some(ChcExpr::Real(n, d))
            }
            (SmtValue::Bool(b), ChcSort::Bool) => Some(ChcExpr::Bool(*b)),
            (SmtValue::BitVec(v, w), ChcSort::BitVec(_)) => Some(ChcExpr::BitVec(*v, *w)),
            _ => None,
        }
    }

    fn cube_scalar_value_expr(
        arg: &ChcExpr,
        sort: &ChcSort,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        cube::value_expr_from_model(arg, model).or_else(|| {
            let value = crate::expr::evaluate_expr(arg, model)?;
            Self::smt_value_to_scalar_expr(&value, sort)
        })
    }

    fn dt_constraints_from_model(
        canon: &ChcVar,
        model_val: Option<&SmtValue>,
    ) -> Option<Vec<ChcExpr>> {
        let model_val = model_val?;
        match model_val {
            SmtValue::Datatype(ctor, fields) => {
                let field_exprs: Vec<Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_any_expr(f).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?;
                let ctor_app = ChcExpr::FuncApp(ctor.clone(), canon.sort.clone(), field_exprs);
                let mut conjuncts = vec![ChcExpr::eq(ChcExpr::var(canon.clone()), ctor_app)];
                if let ChcSort::Datatype { constructors, .. } = &canon.sort {
                    if let Some(constructor) = constructors.iter().find(|c| c.name == *ctor) {
                        for (selector, field) in constructor.selectors.iter().zip(fields.iter()) {
                            let field_expr = Self::smt_value_to_scalar_expr(field, &selector.sort)
                                .or_else(|| Self::smt_value_to_any_expr(field))?;
                            conjuncts.push(ChcExpr::eq(
                                ChcExpr::FuncApp(
                                    selector.name.clone(),
                                    selector.sort.clone(),
                                    vec![Arc::new(ChcExpr::var(canon.clone()))],
                                ),
                                field_expr,
                            ));
                        }
                    }
                }
                Some(conjuncts)
            }
            SmtValue::Opaque(name) => {
                let ctor_app = ChcExpr::FuncApp(name.clone(), canon.sort.clone(), vec![]);
                Some(vec![ChcExpr::eq(ChcExpr::var(canon.clone()), ctor_app)])
            }
            _ => None,
        }
    }

    fn smt_value_to_any_expr(val: &SmtValue) -> Option<ChcExpr> {
        match val {
            SmtValue::Int(n) => Some(ChcExpr::int(*n)),
            // Beyond-i128 witness: exact Horner encoding (never wraps).
            SmtValue::BigInt(b) => Some(ChcExpr::from_bigint(b.as_ref().clone())),
            SmtValue::Bool(b) => Some(ChcExpr::Bool(*b)),
            SmtValue::BitVec(v, w) => Some(ChcExpr::BitVec(*v, *w)),
            SmtValue::Real(r) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64().unwrap_or(0);
                let d = r.denom().to_i64().unwrap_or(1);
                Some(ChcExpr::Real(n, d))
            }
            SmtValue::Datatype(ctor, fields) => {
                let field_exprs: Vec<Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_any_expr(f).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?;
                Some(ChcExpr::FuncApp(
                    ctor.clone(),
                    ChcSort::Uninterpreted(ctor.clone()),
                    field_exprs,
                ))
            }
            SmtValue::Opaque(name) => Some(ChcExpr::FuncApp(
                name.clone(),
                ChcSort::Uninterpreted(name.clone()),
                vec![],
            )),
            _ => None,
        }
    }

    /// Extract a cube, prioritizing constraint extraction when model is empty.
    pub(in crate::pdr::solver) fn cube_from_model_or_constraints(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let mut augmented = model.clone();
        cube::augment_model_from_equalities(constraint, &mut augmented);
        self.cube_from_model(pred, args, &augmented)
            .or_else(|| self.cube_from_equalities(pred, args, constraint))
            .or_else(|| self.cube_from_model_partial(pred, args, &augmented))
    }

    /// Build a best-effort partial cube, skipping variables that can't be evaluated.
    pub(super) fn cube_from_model_partial(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let mut conjuncts = Vec::with_capacity(args.len());
        for (canon, arg) in vars.iter().zip(args.iter()) {
            if matches!(canon.sort, ChcSort::Array(_, _)) {
                let array_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(select_conjuncts) =
                    Self::array_select_constraints_from_model(canon, array_model_val)
                {
                    conjuncts.extend(select_conjuncts);
                }
                continue;
            }
            if matches!(canon.sort, ChcSort::Datatype { .. }) {
                let dt_model_val = match arg {
                    ChcExpr::Var(v) => model.get(&v.name),
                    _ => None,
                };
                if let Some(dt_conjuncts) = Self::dt_constraints_from_model(canon, dt_model_val) {
                    conjuncts.extend(dt_conjuncts);
                }
                continue;
            }
            let value = match Self::cube_scalar_value_expr(arg, &canon.sort, model) {
                Some(v) => v,
                None => continue,
            };
            match (&canon.sort, value) {
                (ChcSort::Bool, ChcExpr::Bool(true)) => conjuncts.push(ChcExpr::var(canon.clone())),
                (ChcSort::Bool, ChcExpr::Bool(false)) => {
                    conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                }
                (_, v) => conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), v)),
            }
        }
        if conjuncts.is_empty() {
            return None;
        }
        Some(ChcExpr::and_all(conjuncts))
    }

    /// Compute a predecessor cube using MBP (unified entry point).
    pub(in crate::pdr::solver) fn cube_with_mbp(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let point_cube = self.cube_from_model_or_constraints(pred, args, constraint, model);
        if model.is_empty() || !self.config.use_mbp {
            return point_cube;
        }
        let Some(inputs) = self.prepare_cube_mbp_inputs(pred, args, constraint, model) else {
            return point_cube;
        };
        if !Self::should_attempt_cube_mbp(&inputs) {
            return point_cube;
        }
        let mbp_cube = self.cube_from_model_mbp_with_inputs(pred, args, constraint, model, inputs);
        mbp_cube.or(point_cube)
    }

    /// Array-aware predecessor cube for the blocking / reachability loop.
    ///
    /// Mem-track fix: when the safety property itself reasons about array cells
    /// (e.g. the model-checker-consumer Mem-track shape whose query is `not(select obj_valid
    /// k)`), keep the property-relevant `select(arr, idx) = val` literals in the
    /// cube. The previous unconditional `cube_from_model_scalar_only` preference
    /// dropped *every* array literal; with a live scalar counter in the
    /// predicate it still returned a non-empty cube (`i = c`) that never
    /// captured `select(obj_valid, 0) = true`, so PDR generalized over the
    /// counter alone and diverged — the portfolio then exhausted to `unknown`
    /// and model-checker-consumer downgraded its precise Mem track to a weaker Reg track.
    ///
    /// Only property-relevant indices are materialised (via `cube_from_model`'s
    /// #8660 property-directed path), so this stays cheap for wide byte-array
    /// problems, and it is gated on `property_uses_arrays` so array problems
    /// with a purely scalar property keep the cheaper scalar-only cube.
    pub(in crate::pdr::solver) fn cube_from_model_array_aware(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        if self.property_array_indices.property_uses_arrays {
            self.cube_from_model(pred, args, model)
                .or_else(|| self.cube_from_model_scalar_only(pred, args, model))
                .or_else(|| self.cube_with_mbp(pred, args, constraint, model))
        } else {
            self.cube_from_model_scalar_only(pred, args, model)
                .or_else(|| self.cube_with_mbp(pred, args, constraint, model))
        }
    }

    /// Build a scalar-only cube that skips array-sorted variables (#8660).
    ///
    /// For problems with >=2 array parameters, the full cube contains expensive
    /// `select(arr, idx) = val` constraints. This method extracts only the scalar
    /// (Int, Bool, BitVec) portion of the cube, which is cheaper to reason about
    /// during generalization and often sufficient for blocking.
    ///
    /// Returns None if no scalar constraints can be extracted.
    pub(in crate::pdr::solver) fn cube_from_model_scalar_only(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let mut conjuncts = Vec::with_capacity(args.len());
        for (canon, arg) in vars.iter().zip(args.iter()) {
            // Skip array and datatype sorts entirely
            if matches!(canon.sort, ChcSort::Array(_, _) | ChcSort::Datatype { .. }) {
                continue;
            }
            let value = match Self::cube_scalar_value_expr(arg, &canon.sort, model) {
                Some(v) => v,
                None => continue,
            };
            match (&canon.sort, value) {
                (ChcSort::Bool, ChcExpr::Bool(true)) => conjuncts.push(ChcExpr::var(canon.clone())),
                (ChcSort::Bool, ChcExpr::Bool(false)) => {
                    conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                }
                (_, v) => conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), v)),
            }
        }
        if conjuncts.is_empty() {
            return None;
        }
        Some(ChcExpr::and_all(conjuncts))
    }

    /// Extract a cube from equality constraints in a formula.
    pub(in crate::pdr::solver) fn cube_from_equalities(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let mut expr_model = FxHashMap::default();
        cube::extract_equalities_from_formula(constraint, &mut expr_model);
        let mut conjuncts = Vec::with_capacity(args.len());
        for (canon, arg) in vars.iter().zip(args.iter()) {
            if matches!(canon.sort, ChcSort::Array(_, _) | ChcSort::Datatype { .. }) {
                continue;
            }
            match arg {
                ChcExpr::Var(v) => {
                    let value = expr_model.get(&v.name)?;
                    let value_expr = Self::smt_value_to_scalar_expr(value, &canon.sort)?;
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), value_expr));
                }
                ChcExpr::Int(n) => {
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(*n)));
                }
                ChcExpr::Bool(b) => {
                    if *b {
                        conjuncts.push(ChcExpr::var(canon.clone()));
                    } else {
                        conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                    }
                }
                expr => {
                    let value = crate::expr::evaluate_expr(expr, &expr_model)?;
                    let value_expr = Self::smt_value_to_scalar_expr(&value, &canon.sort)?;
                    match (&canon.sort, value_expr) {
                        (ChcSort::Bool, ChcExpr::Bool(true)) => {
                            conjuncts.push(ChcExpr::var(canon.clone()));
                        }
                        (ChcSort::Bool, ChcExpr::Bool(false)) => {
                            conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                        }
                        (_, v) => {
                            conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), v));
                        }
                    }
                }
            }
        }
        Some(ChcExpr::and_all(conjuncts))
    }

    #[cfg(test)]
    pub(in crate::pdr::solver) fn extract_integer_only_cube(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let mut conjuncts = Vec::new();
        for (canon, arg) in vars.iter().zip(args.iter()) {
            if matches!(canon.sort, ChcSort::Array(_, _)) {
                continue;
            }
            match arg {
                ChcExpr::Var(v) => {
                    if matches!(v.sort, ChcSort::Array(_, _)) {
                        continue;
                    }
                    if let Some(SmtValue::Int(value)) = model.get(&v.name) {
                        conjuncts.push(ChcExpr::eq(
                            ChcExpr::var(canon.clone()),
                            ChcExpr::int(*value),
                        ));
                    } else if let Some(SmtValue::BigInt(value)) = model.get(&v.name) {
                        // Beyond-i128 witness: exact Horner encoding, so
                        // reachability propagation through the cube stays
                        // precise (never wrapped, never dropped).
                        conjuncts.push(ChcExpr::eq(
                            ChcExpr::var(canon.clone()),
                            ChcExpr::from_bigint(value.as_ref().clone()),
                        ));
                    } else if let Some(SmtValue::Bool(value)) = model.get(&v.name) {
                        if *value {
                            conjuncts.push(ChcExpr::var(canon.clone()));
                        } else {
                            conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                        }
                    } else {
                        return None;
                    }
                }
                ChcExpr::Int(n) => {
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(*n)));
                }
                ChcExpr::Bool(b) => {
                    if *b {
                        conjuncts.push(ChcExpr::var(canon.clone()));
                    } else {
                        conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                    }
                }
                _ => {
                    if let Some(v) = cube::value_expr_from_model(arg, model) {
                        match v {
                            ChcExpr::Int(n) => {
                                conjuncts.push(ChcExpr::eq(
                                    ChcExpr::var(canon.clone()),
                                    ChcExpr::int(n),
                                ));
                            }
                            ChcExpr::Bool(b) => {
                                if b {
                                    conjuncts.push(ChcExpr::var(canon.clone()));
                                } else {
                                    conjuncts.push(ChcExpr::not(ChcExpr::var(canon.clone())));
                                }
                            }
                            _ => return None,
                        }
                    } else {
                        return None;
                    }
                }
            }
        }
        if conjuncts.is_empty() {
            Some(ChcExpr::Bool(true))
        } else {
            Some(ChcExpr::and_all(conjuncts))
        }
    }

    /// Extract equalities from a formula and populate an SMT model.
    pub(in crate::pdr) fn extract_equalities_from_formula(
        expr: &ChcExpr,
        model: &mut FxHashMap<String, SmtValue>,
    ) {
        cube::extract_equalities_from_formula(expr, model);
    }
}
