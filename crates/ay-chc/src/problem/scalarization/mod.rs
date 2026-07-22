// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl ChcProblem {
    pub fn try_scalarize_int_indexed_const_array_selects(&mut self) {
        let _ = self.try_scalarize_int_indexed_const_array_selects_with_map();
    }

    pub(crate) fn try_scalarize_int_indexed_const_array_selects_with_map(
        &mut self,
    ) -> Option<ArrayScalarizationMap> {
        let mut index_map: FxHashMap<ChcSort, FxHashSet<ConstIndex>> = FxHashMap::default();
        let mut symbolic_sorts: FxHashSet<ChcSort> = FxHashSet::default();
        for clause in &self.clauses {
            if let Some(c) = &clause.body.constraint {
                Self::collect_const_array_select_indices(c, &mut index_map);
                Self::collect_symbolic_select_key_sorts(c, &mut symbolic_sorts);
            }
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    Self::collect_const_array_select_indices(arg, &mut index_map);
                    Self::collect_symbolic_select_key_sorts(arg, &mut symbolic_sorts);
                }
            }
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    Self::collect_const_array_select_indices(arg, &mut index_map);
                    Self::collect_symbolic_select_key_sorts(arg, &mut symbolic_sorts);
                }
            }
        }

        index_map.retain(|k, _| matches!(k, ChcSort::Int) && !symbolic_sorts.contains(k));
        if index_map.is_empty() {
            return None;
        }
        Some(self.apply_scalarization(index_map))
    }

    pub fn try_scalarize_property_directed(&mut self) {
        let _ = self.try_scalarize_property_directed_with_map();
    }

    pub(crate) fn try_scalarize_property_directed_with_map(
        &mut self,
    ) -> Option<ArrayScalarizationMap> {
        let mut index_map: FxHashMap<ChcSort, FxHashSet<ConstIndex>> = FxHashMap::default();
        for clause in self.clauses.iter().filter(|c| c.is_query()) {
            if let Some(c) = &clause.body.constraint {
                Self::collect_const_array_select_indices(c, &mut index_map);
            }
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    Self::collect_const_array_select_indices(arg, &mut index_map);
                }
            }
        }

        if index_map.is_empty() {
            return None;
        }

        let mut symbolic_sorts: FxHashSet<ChcSort> = FxHashSet::default();
        for clause in &self.clauses {
            if let Some(c) = &clause.body.constraint {
                Self::collect_symbolic_select_key_sorts(c, &mut symbolic_sorts);
            }
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    Self::collect_symbolic_select_key_sorts(arg, &mut symbolic_sorts);
                }
            }
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    Self::collect_symbolic_select_key_sorts(arg, &mut symbolic_sorts);
                }
            }
        }

        index_map.retain(|k, _| !symbolic_sorts.contains(k));
        if index_map.is_empty() {
            return None;
        }
        Some(self.apply_scalarization(index_map))
    }

    pub fn try_scalarize_const_array_selects(&mut self) {
        let _ = self.try_scalarize_const_array_selects_with_map();
    }

    pub(crate) fn try_scalarize_const_array_selects_with_map(
        &mut self,
    ) -> Option<ArrayScalarizationMap> {
        self.try_scalarize_const_array_selects_with_extra_indices_with_map(&[])
    }

    pub(crate) fn try_scalarize_const_array_selects_with_extra_indices_with_map(
        &mut self,
        extra_indices: &[(ChcSort, ChcExpr)],
    ) -> Option<ArrayScalarizationMap> {
        self.try_scalarize_const_array_selects_with_extra_indices_impl(extra_indices, true)
    }

    /// Scalarize finite constant array keys even when the same array key sort
    /// also appears in symbolic selects/stores.
    ///
    /// This is an abstraction route, not a standalone proof rule: callers must
    /// validate any translated SAFE model on the original CHC before accepting
    /// it. Keeping these keys is useful for Solidity/Quic3-style formulas where
    /// literal event keys such as calldata bytes coexist with symbolic array
    /// loop keys.
    pub(crate) fn try_scalarize_const_array_selects_allow_symbolic_keys_with_map(
        &mut self,
        extra_indices: &[(ChcSort, ChcExpr)],
    ) -> Option<ArrayScalarizationMap> {
        self.try_scalarize_const_array_selects_with_extra_indices_impl(extra_indices, false)
    }

    pub(crate) fn has_const_array_scalarization_candidates_allow_symbolic_keys(&self) -> bool {
        let mut index_map: FxHashMap<ChcSort, FxHashSet<ConstIndex>> = FxHashMap::default();
        for clause in &self.clauses {
            if let Some(c) = &clause.body.constraint {
                Self::collect_const_array_select_indices(c, &mut index_map);
            }
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    Self::collect_const_array_select_indices(arg, &mut index_map);
                }
            }
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    Self::collect_const_array_select_indices(arg, &mut index_map);
                }
            }
        }

        !index_map.is_empty()
    }

    pub(crate) fn rewrite_clause_local_constant_aliases_for_array_scalarization(
        &mut self,
    ) -> usize {
        let mut rewritten_aliases = 0usize;
        for clause in &mut self.clauses {
            let Some(constraint) = clause.body.constraint.as_ref() else {
                continue;
            };
            let aliases = Self::collect_clause_local_constant_aliases(constraint);
            if aliases.is_empty() {
                continue;
            }

            if let Some(constraint) = &mut clause.body.constraint {
                *constraint = constraint
                    .substitute_name_map(&aliases)
                    .simplify_array_ops()
                    .simplify_constants();
            }
            for (_, args) in &mut clause.body.predicates {
                for arg in args {
                    *arg = arg
                        .substitute_name_map(&aliases)
                        .simplify_array_ops()
                        .simplify_constants();
                }
            }
            if let ClauseHead::Predicate(_, args) = &mut clause.head {
                for arg in args {
                    *arg = arg
                        .substitute_name_map(&aliases)
                        .simplify_array_ops()
                        .simplify_constants();
                }
            }
            rewritten_aliases += aliases.len();
        }
        rewritten_aliases
    }

    fn collect_clause_local_constant_aliases(constraint: &ChcExpr) -> FxHashMap<String, ChcExpr> {
        let conjuncts = constraint.collect_conjuncts();
        let mut aliases: FxHashMap<String, ChcExpr> = FxHashMap::default();
        for _ in 0..8 {
            let mut changed = false;
            for conjunct in &conjuncts {
                let simplified = conjunct
                    .substitute_name_map(&aliases)
                    .simplify_array_ops()
                    .simplify_constants();
                let Some((var, value)) = Self::clause_local_constant_alias(&simplified) else {
                    continue;
                };
                if !Self::literal_matches_sort(&value, &var.sort) {
                    continue;
                }
                match aliases.get(&var.name) {
                    Some(current) if current == &value => {}
                    Some(_) => {}
                    None => {
                        aliases.insert(var.name.clone(), value);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        aliases
    }

    fn clause_local_constant_alias(expr: &ChcExpr) -> Option<(ChcVar, ChcExpr)> {
        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        Self::oriented_clause_local_constant_alias(args[0].as_ref(), args[1].as_ref()).or_else(
            || Self::oriented_clause_local_constant_alias(args[1].as_ref(), args[0].as_ref()),
        )
    }

    fn oriented_clause_local_constant_alias(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
    ) -> Option<(ChcVar, ChcExpr)> {
        let ChcExpr::Var(var) = lhs else {
            return None;
        };
        Self::literal_expr(rhs).map(|value| (var.clone(), value))
    }

    fn literal_expr(expr: &ChcExpr) -> Option<ChcExpr> {
        match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
                Some(expr.clone())
            }
            _ => None,
        }
    }

    fn literal_matches_sort(value: &ChcExpr, sort: &ChcSort) -> bool {
        match (value, sort) {
            (ChcExpr::Bool(_), ChcSort::Bool)
            | (ChcExpr::Int(_), ChcSort::Int)
            | (ChcExpr::Real(_, _), ChcSort::Real) => true,
            (ChcExpr::BitVec(_, width), ChcSort::BitVec(sort_width)) => width == sort_width,
            _ => false,
        }
    }

    fn try_scalarize_const_array_selects_with_extra_indices_impl(
        &mut self,
        extra_indices: &[(ChcSort, ChcExpr)],
        drop_symbolic_key_sorts: bool,
    ) -> Option<ArrayScalarizationMap> {
        let mut index_map: FxHashMap<ChcSort, FxHashSet<ConstIndex>> = FxHashMap::default();
        let mut symbolic_sorts: FxHashSet<ChcSort> = FxHashSet::default();
        for clause in &self.clauses {
            if let Some(c) = &clause.body.constraint {
                Self::collect_const_array_select_indices(c, &mut index_map);
                Self::collect_symbolic_select_key_sorts(c, &mut symbolic_sorts);
            }
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    Self::collect_const_array_select_indices(arg, &mut index_map);
                    Self::collect_symbolic_select_key_sorts(arg, &mut symbolic_sorts);
                }
            }
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    Self::collect_const_array_select_indices(arg, &mut index_map);
                    Self::collect_symbolic_select_key_sorts(arg, &mut symbolic_sorts);
                }
            }
        }

        if drop_symbolic_key_sorts {
            index_map.retain(|k, _| !symbolic_sorts.contains(k));
        }
        for (key_sort, index) in extra_indices {
            if let Some(const_index) = Self::try_eval_const_index(index)
                .and_then(|const_index| const_index.coerce_to_sort(key_sort))
            {
                index_map
                    .entry(key_sort.clone())
                    .or_default()
                    .insert(const_index);
            }
        }
        if index_map.is_empty() {
            return None;
        }
        Some(self.apply_scalarization(index_map))
    }

    fn apply_scalarization(
        &mut self,
        index_map: FxHashMap<ChcSort, FxHashSet<ConstIndex>>,
    ) -> ArrayScalarizationMap {
        let sorted_index_map: FxHashMap<ChcSort, Vec<ConstIndex>> = index_map
            .into_iter()
            .map(|(k, set)| {
                let mut v: Vec<ConstIndex> = set.into_iter().collect();
                v.sort();
                (k, v)
            })
            .collect();

        let old_predicates = self.predicates.clone();
        let mut pred_args: FxHashMap<PredicateId, Vec<ArrayScalarizedArg>> = FxHashMap::default();
        for pred in &mut self.predicates {
            let mut new_sorts = Vec::new();
            let mut arg_map = Vec::new();
            for (arg_idx, sort) in pred.arg_sorts.iter().enumerate() {
                if Self::is_scalarizable_array_sort(sort) {
                    let key_sort = Self::array_key_sort(sort).expect("checked above");
                    let val_sort = Self::array_value_sort(sort).expect("checked above");
                    if let Some(indices) = sorted_index_map.get(key_sort) {
                        if indices.is_empty() {
                            new_sorts.push(sort.clone());
                            arg_map.push(ArrayScalarizedArg::Original(arg_idx));
                        } else {
                            for idx in indices {
                                new_sorts.push(val_sort.clone());
                                arg_map.push(ArrayScalarizedArg::Select {
                                    original_arg: arg_idx,
                                    index: idx.to_expr(),
                                });
                            }
                        }
                    } else {
                        new_sorts.push(sort.clone());
                        arg_map.push(ArrayScalarizedArg::Original(arg_idx));
                    }
                } else {
                    new_sorts.push(sort.clone());
                    arg_map.push(ArrayScalarizedArg::Original(arg_idx));
                }
            }
            pred.arg_sorts = new_sorts;
            pred_args.insert(pred.id, arg_map);
        }

        let mut new_clauses = Vec::with_capacity(self.clauses.len());
        for clause in &self.clauses {
            let mut new_body_preds = Vec::with_capacity(clause.body.predicates.len());
            for (pred_id, args) in &clause.body.predicates {
                let old_pred = &old_predicates[pred_id.index()];
                let new_args = Self::scalarize_pred_args(old_pred, args, &sorted_index_map);
                new_body_preds.push((*pred_id, new_args));
            }

            let new_constraint = clause
                .body
                .constraint
                .as_ref()
                .map(|c| Self::scalarize_constraint(c, &sorted_index_map));

            let new_body = ClauseBody::new(new_body_preds, new_constraint);
            let new_head = match &clause.head {
                ClauseHead::Predicate(pred_id, args) => {
                    let old_pred = &old_predicates[pred_id.index()];
                    let new_args = Self::scalarize_pred_args(old_pred, args, &sorted_index_map);
                    ClauseHead::Predicate(*pred_id, new_args)
                }
                ClauseHead::False => ClauseHead::False,
            };
            new_clauses.push(HornClause::new(new_body, new_head));
        }

        self.clauses = new_clauses;
        ArrayScalarizationMap {
            original_predicates: old_predicates,
            pred_args,
        }
    }

    fn is_scalarizable_array_sort(sort: &ChcSort) -> bool {
        matches!(sort, ChcSort::Array(k, v)
            if matches!(**k, ChcSort::Int | ChcSort::BitVec(_))
            && matches!(**v, ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_)))
    }

    fn array_key_sort(sort: &ChcSort) -> Option<&ChcSort> {
        match sort {
            ChcSort::Array(k, _) => Some(k),
            _ => None,
        }
    }

    fn array_value_sort(sort: &ChcSort) -> Option<&ChcSort> {
        match sort {
            ChcSort::Array(_, v) => Some(v),
            _ => None,
        }
    }

    fn try_eval_const_index(expr: &ChcExpr) -> Option<ConstIndex> {
        match expr {
            ChcExpr::Int(k) => Some(ConstIndex::Int(*k)),
            ChcExpr::BitVec(v, w) => Some(ConstIndex::BitVec(*v, *w)),
            ChcExpr::Op(ChcOp::BvConcat, args) if args.len() == 2 => {
                let hi = Self::try_eval_const_index(&args[0])?;
                let lo = Self::try_eval_const_index(&args[1])?;
                match (hi, lo) {
                    (ConstIndex::BitVec(a, wa), ConstIndex::BitVec(b, wb)) => {
                        let result = (a << wb) | b;
                        Some(ConstIndex::BitVec(result & bv_mask(wa + wb), wa + wb))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::BvExtract(hi, lo), args) if args.len() == 1 => {
                let inner = Self::try_eval_const_index(&args[0])?;
                match inner {
                    ConstIndex::BitVec(v, _w) => {
                        let width = hi - lo + 1;
                        let result = (v >> lo) & bv_mask(width);
                        Some(ConstIndex::BitVec(result, width))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::BvZeroExtend(n), args) if args.len() == 1 => {
                Self::try_eval_const_index(&args[0]).map(|ci| match ci {
                    ConstIndex::BitVec(v, w) => ConstIndex::BitVec(v, w + n),
                    other => other,
                })
            }
            _ => None,
        }
    }

    fn collect_const_array_select_indices(
        expr: &ChcExpr,
        index_map: &mut FxHashMap<ChcSort, FxHashSet<ConstIndex>>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                let arr_sort = args[0].sort();
                if Self::is_scalarizable_array_sort(&arr_sort) {
                    if let Some(ci) = Self::try_eval_const_index(&args[1]) {
                        let key_sort = Self::array_key_sort(&arr_sort)
                            .expect("checked above")
                            .clone();
                        if let Some(ci) = ci.coerce_to_sort(&key_sort) {
                            index_map.entry(key_sort).or_default().insert(ci);
                        }
                    }
                }
                for a in args {
                    Self::collect_const_array_select_indices(a, index_map);
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_const_array_select_indices(a, index_map);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    Self::collect_const_array_select_indices(a, index_map);
                }
            }
            ChcExpr::ConstArray(_ks, val) => {
                Self::collect_const_array_select_indices(val, index_map);
            }
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Real(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        });
    }

    fn collect_symbolic_select_key_sorts(expr: &ChcExpr, symbolic_sorts: &mut FxHashSet<ChcSort>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                let arr_sort = args[0].sort();
                if Self::is_scalarizable_array_sort(&arr_sort)
                    && Self::try_eval_const_index(&args[1]).is_none()
                {
                    let key_sort = Self::array_key_sort(&arr_sort)
                        .expect("checked above")
                        .clone();
                    symbolic_sorts.insert(key_sort);
                }
                for a in args {
                    Self::collect_symbolic_select_key_sorts(a, symbolic_sorts);
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_symbolic_select_key_sorts(a, symbolic_sorts);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    Self::collect_symbolic_select_key_sorts(a, symbolic_sorts);
                }
            }
            ChcExpr::ConstArray(_ks, val) => {
                Self::collect_symbolic_select_key_sorts(val, symbolic_sorts);
            }
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Real(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        });
    }

    fn scalarize_pred_args(
        pred: &Predicate,
        args: &[ChcExpr],
        index_map: &FxHashMap<ChcSort, Vec<ConstIndex>>,
    ) -> Vec<ChcExpr> {
        let mut out = Vec::new();
        for (arg, sort) in args.iter().zip(pred.arg_sorts.iter()) {
            if Self::is_scalarizable_array_sort(sort) {
                let key_sort = Self::array_key_sort(sort).expect("checked above");
                if let Some(indices) = index_map.get(key_sort) {
                    if indices.is_empty() {
                        out.push(Self::scalarize_expr(arg, index_map));
                    } else {
                        for idx in indices {
                            out.push(Self::scalar_value_at_index(arg, idx, sort));
                        }
                    }
                } else {
                    out.push(Self::scalarize_expr(arg, index_map));
                }
            } else {
                out.push(Self::scalarize_expr(arg, index_map));
            }
        }
        // Fold the constant `ite((= k k), val, base@k)` guards that
        // `scalar_value_at_index` emits for a `store(_, k, val)` argument at a
        // tracked index. Without this the scalarized init head keeps
        // `(ite (= bv0 bv0) true v@0)` instead of `true`, which makes PDR's
        // init analysis believe the cell could take the free `else` value
        // (`v@0`) at init — it then generalizes a spurious `v@0 OR i>=1`
        // disjunction that is not self-inductive and diverges on the Mem-track
        // store-in-head-arg shape. Simplification only rewrites content, not the
        // positional arg↦ArrayScalarizedArg mapping, so back-translation is
        // unaffected.
        for e in &mut out {
            *e = e.clone().simplify_array_ops().simplify_constants();
        }
        out
    }

    fn scalar_var_for_array(array_var: &ChcVar, index: &ConstIndex) -> ChcVar {
        let val_sort = match &array_var.sort {
            ChcSort::Array(_, v) => (**v).clone(),
            _ => ChcSort::Int,
        };
        ChcVar::new(
            format!("{}__sel_{}", array_var.name, index.suffix()),
            val_sort,
        )
    }

    fn scalar_value_at_index(
        array_expr: &ChcExpr,
        index: &ConstIndex,
        array_sort: &ChcSort,
    ) -> ChcExpr {
        crate::expr::maybe_grow_expr_stack(|| match array_expr {
            ChcExpr::Var(v) if Self::is_scalarizable_array_sort(&v.sort) => {
                ChcExpr::Var(Self::scalar_var_for_array(v, index))
            }
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                let cond = ChcExpr::eq(args[1].as_ref().clone(), index.to_expr());
                let then_ = args[2].as_ref().clone();
                let else_ = Self::scalar_value_at_index(&args[0], index, array_sort);
                ChcExpr::ite(cond, then_, else_)
            }
            ChcExpr::ConstArray(_ks, val) => (**val).clone(),
            _ => ChcExpr::select(array_expr.clone(), index.to_expr()),
        })
    }

    fn scalarize_expr(expr: &ChcExpr, index_map: &FxHashMap<ChcSort, Vec<ConstIndex>>) -> ChcExpr {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
                expr.clone()
            }
            ChcExpr::Var(_) => expr.clone(),
            ChcExpr::PredicateApp(name, id, args) => {
                let new_args = args
                    .iter()
                    .map(|a| Arc::new(Self::scalarize_expr(a, index_map)))
                    .collect();
                ChcExpr::PredicateApp(name.clone(), *id, new_args)
            }
            ChcExpr::FuncApp(name, sort, args) => {
                let new_args = args
                    .iter()
                    .map(|a| Arc::new(Self::scalarize_expr(a, index_map)))
                    .collect();
                ChcExpr::FuncApp(name.clone(), sort.clone(), new_args)
            }
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                let arr_sort = args[0].sort();
                if Self::is_scalarizable_array_sort(&arr_sort) {
                    if let Some(ci) = Self::try_eval_const_index(&args[1]).and_then(|ci| {
                        ci.coerce_to_sort(Self::array_key_sort(&arr_sort).expect("checked above"))
                    }) {
                        let key_sort = Self::array_key_sort(&arr_sort).expect("checked above");
                        if index_map
                            .get(key_sort)
                            .is_some_and(|indices| indices.contains(&ci))
                        {
                            return Self::scalar_value_at_index(&args[0], &ci, &arr_sort);
                        }
                    }
                }
                let new_args = args
                    .iter()
                    .map(|a| Arc::new(Self::scalarize_expr(a, index_map)))
                    .collect();
                ChcExpr::Op(ChcOp::Select, new_args)
            }
            ChcExpr::Op(op, args) => {
                let new_args = args
                    .iter()
                    .map(|a| Arc::new(Self::scalarize_expr(a, index_map)))
                    .collect();
                ChcExpr::Op(*op, new_args)
            }
            ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => expr.clone(),
            ChcExpr::ConstArray(ks, val) => {
                ChcExpr::ConstArray(ks.clone(), Arc::new(Self::scalarize_expr(val, index_map)))
            }
        })
    }

    fn scalarize_constraint(
        constraint: &ChcExpr,
        index_map: &FxHashMap<ChcSort, Vec<ConstIndex>>,
    ) -> ChcExpr {
        let mut conjuncts = Vec::new();
        constraint.collect_conjuncts_into(&mut conjuncts);

        let mut out = Vec::new();
        for c in &conjuncts {
            if let Some(expanded) = Self::scalarize_store_equality(c, index_map) {
                out.extend(expanded);
            } else {
                out.push(Self::scalarize_expr(c, index_map));
            }
        }

        // Fold constant `ite`/`select(store ...)` guards introduced by
        // scalarizing `select(store(_, k, v), k)` and store-equality expansion,
        // so the scalarized body constraint is clean (e.g. `true` rather than
        // `(select (store v bv0 true) bv0)`). See `scalarize_pred_args`.
        ChcExpr::and_all(out)
            .simplify_array_ops()
            .simplify_constants()
    }

    fn scalarize_store_equality(
        conjunct: &ChcExpr,
        index_map: &FxHashMap<ChcSort, Vec<ConstIndex>>,
    ) -> Option<Vec<ChcExpr>> {
        let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        fn as_array_var(e: &ChcExpr) -> Option<&ChcVar> {
            match e {
                ChcExpr::Var(v) if ChcProblem::is_scalarizable_array_sort(&v.sort) => Some(v),
                _ => None,
            }
        }

        fn as_store(e: &ChcExpr) -> Option<(&ChcExpr, &ChcExpr, &ChcExpr)> {
            match e {
                ChcExpr::Op(ChcOp::Store, a) if a.len() == 3 => Some((&a[0], &a[1], &a[2])),
                _ => None,
            }
        }

        let (next_arr, store_base, store_idx, store_val) = if let (Some(lhs), Some((b, i, v))) =
            (as_array_var(&args[0]), as_store(&args[1]))
        {
            (lhs, b, i, v)
        } else if let (Some(rhs), Some((b, i, v))) = (as_array_var(&args[1]), as_store(&args[0])) {
            (rhs, b, i, v)
        } else {
            return None;
        };

        let base_sort = store_base.sort();
        if !Self::is_scalarizable_array_sort(&base_sort) {
            return None;
        }

        let key_sort = Self::array_key_sort(&base_sort)?;
        let indices = index_map.get(key_sort)?;
        if indices.is_empty() {
            return None;
        }

        let idx_expr = Self::scalarize_expr(store_idx, index_map);
        let val_expr = Self::scalarize_expr(store_val, index_map);

        let mut out = Vec::new();
        for k in indices {
            let next_k = ChcExpr::Var(Self::scalar_var_for_array(next_arr, k));
            let base_k = Self::scalar_value_at_index(store_base, k, &base_sort);
            out.push(ChcExpr::or(
                ChcExpr::not(ChcExpr::eq(idx_expr.clone(), k.to_expr())),
                ChcExpr::eq(next_k.clone(), val_expr.clone()),
            ));
            out.push(ChcExpr::or(
                ChcExpr::eq(idx_expr.clone(), k.to_expr()),
                ChcExpr::eq(next_k, base_k),
            ));
        }
        Some(out)
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
