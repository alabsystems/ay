// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression tree rewriting: substitution, renaming, and disequality replacement.

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcVar, MAX_EXPR_RECURSION_DEPTH,
    MAX_PREPROCESSING_NODES,
};

impl ChcExpr {
    /// Rebuild this expression by applying a transform to each direct child node.
    ///
    /// Returns `self.clone()` (cheap shallow clone) when no child was modified,
    /// avoiding O(n) tree reconstruction (#3665).
    pub(crate) fn map_children_with<F>(&self, mut map_child: F) -> Self
    where
        F: FnMut(&Self) -> Self,
    {
        match self {
            Self::Bool(_)
            | Self::Int(_)
            | Self::Real(_, _)
            | Self::BitVec(_, _)
            | Self::Var(_)
            | Self::ConstArrayMarker(_)
            | Self::IsTesterMarker(_) => self.clone(),
            Self::Op(op, args) => {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| Arc::new(map_child(arg.as_ref())))
                    .collect();
                if args
                    .iter()
                    .zip(new_args.iter())
                    .all(|(old, new)| old.as_ref() == new.as_ref())
                {
                    self.clone()
                } else {
                    Self::Op(*op, new_args)
                }
            }
            Self::PredicateApp(name, id, args) => {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| Arc::new(map_child(arg.as_ref())))
                    .collect();
                if args
                    .iter()
                    .zip(new_args.iter())
                    .all(|(old, new)| old.as_ref() == new.as_ref())
                {
                    self.clone()
                } else {
                    Self::PredicateApp(name.clone(), *id, new_args)
                }
            }
            Self::FuncApp(name, sort, args) => {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| Arc::new(map_child(arg.as_ref())))
                    .collect();
                if args
                    .iter()
                    .zip(new_args.iter())
                    .all(|(old, new)| old.as_ref() == new.as_ref())
                {
                    self.clone()
                } else {
                    Self::FuncApp(name.clone(), sort.clone(), new_args)
                }
            }
            Self::ConstArray(ks, val) => {
                let new_val = Arc::new(map_child(val.as_ref()));
                if val.as_ref() == new_val.as_ref() {
                    self.clone()
                } else {
                    Self::ConstArray(ks.clone(), new_val)
                }
            }
        }
    }

    /// Substitute variables in the expression
    pub fn substitute(&self, subst: &[(ChcVar, Self)]) -> Self {
        if subst.is_empty() {
            return self.clone();
        }
        let map: FxHashMap<&ChcVar, &Self> = subst.iter().map(|(v, e)| (v, e)).collect();
        self.substitute_map(&map)
    }

    /// Substitute variables using a pre-built map (O(1) lookup per variable).
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn substitute_map(&self, map: &FxHashMap<&ChcVar, &Self>) -> Self {
        self.substitute_with_lookup(&|v| map.get(v).map(|e| (*e).clone()))
    }

    /// Variable substitution that PRESERVES structural sharing — for SMT-LIB
    /// `let` expansion (#9074).
    ///
    /// Unlike the `substitute_*` family, each bound value is inserted as a
    /// shared `Arc` clone (a refcount bump) rather than deep-cloned at every
    /// occurrence, and shared input subtrees are visited once via an
    /// `Arc`-pointer memo. This keeps nested-`let` expansion LINEAR (the result
    /// is a DAG) instead of exploding into an exponential tree of distinct
    /// `Arc`s — which otherwise blows up parse-time `simplify_constants` and
    /// every later tree walk (eq/hash/drop/canonicalization) on heavily
    /// `let`-nested inputs (e.g. sally/oral_messages: one transition over 145
    /// vars built by deeply nested `let`s).
    ///
    /// Semantically identical to `substitute_map`: each `Var(v)` with `v` in
    /// `map` becomes `map[v]` (no re-substitution of the inserted value, i.e.
    /// parallel-`let` semantics), all other nodes are structurally unchanged.
    /// It carries NO node budget, so — unlike the budgeted `substitute_*` paths,
    /// which can bail mid-tree and leave bound vars dangling on huge inputs — it
    /// ALWAYS completes the substitution. Depth is handled by
    /// `maybe_grow_expr_stack`; `let` bodies have source-bounded depth.
    pub(crate) fn substitute_let_shared(
        body: &Arc<Self>,
        map: &FxHashMap<&ChcVar, Arc<Self>>,
    ) -> Arc<Self> {
        if map.is_empty() {
            return Arc::clone(body);
        }
        let mut memo: FxHashMap<*const Self, Arc<Self>> = FxHashMap::default();
        Self::subst_shared_inner(body, map, &mut memo)
    }

    fn subst_shared_inner(
        node: &Arc<Self>,
        map: &FxHashMap<&ChcVar, Arc<Self>>,
        memo: &mut FxHashMap<*const Self, Arc<Self>>,
    ) -> Arc<Self> {
        // Var is the only leaf that can change; handle before the memo so even a
        // singly-referenced var shares the (already-`Arc`) bound value.
        if let Self::Var(v) = node.as_ref() {
            return match map.get(v) {
                Some(value) => Arc::clone(value),
                None => Arc::clone(node),
            };
        }
        // Shared input subtree reached again → reuse the prior result. Pointers
        // are stable: every subtree of `body` stays alive for this call.
        let key = Arc::as_ptr(node);
        if let Some(cached) = memo.get(&key) {
            return Arc::clone(cached);
        }
        let result = maybe_grow_expr_stack(|| match node.as_ref() {
            Self::Op(op, args) => {
                let new_args: Vec<Arc<Self>> = args
                    .iter()
                    .map(|a| Self::subst_shared_inner(a, map, memo))
                    .collect();
                if new_args
                    .iter()
                    .zip(args.iter())
                    .all(|(n, o)| Arc::ptr_eq(n, o))
                {
                    Arc::clone(node)
                } else {
                    Arc::new(Self::Op(*op, new_args))
                }
            }
            Self::PredicateApp(name, id, args) => {
                let new_args: Vec<Arc<Self>> = args
                    .iter()
                    .map(|a| Self::subst_shared_inner(a, map, memo))
                    .collect();
                if new_args
                    .iter()
                    .zip(args.iter())
                    .all(|(n, o)| Arc::ptr_eq(n, o))
                {
                    Arc::clone(node)
                } else {
                    Arc::new(Self::PredicateApp(name.clone(), *id, new_args))
                }
            }
            Self::FuncApp(name, sort, args) => {
                let new_args: Vec<Arc<Self>> = args
                    .iter()
                    .map(|a| Self::subst_shared_inner(a, map, memo))
                    .collect();
                if new_args
                    .iter()
                    .zip(args.iter())
                    .all(|(n, o)| Arc::ptr_eq(n, o))
                {
                    Arc::clone(node)
                } else {
                    Arc::new(Self::FuncApp(name.clone(), sort.clone(), new_args))
                }
            }
            Self::ConstArray(ks, val) => {
                let new_val = Self::subst_shared_inner(val, map, memo);
                if Arc::ptr_eq(&new_val, val) {
                    Arc::clone(node)
                } else {
                    Arc::new(Self::ConstArray(ks.clone(), new_val))
                }
            }
            // Leaves other than Var (handled above): nothing to substitute.
            _ => Arc::clone(node),
        });
        memo.insert(key, Arc::clone(&result));
        result
    }

    /// Substitute variables by variable name (O(1) lookup per variable name).
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn substitute_name_map(&self, map: &FxHashMap<String, Self>) -> Self {
        if map.is_empty() {
            return self.clone();
        }
        self.substitute_with_lookup(&|v| map.get(&v.name).cloned())
    }

    /// Rename variables by name, preserving sorts (#3577).
    /// Maps old variable names to new variable names. Variables not in the map
    /// are left unchanged. If the expression tree exceeds 1M nodes, returns
    /// `self` unchanged.
    pub(crate) fn rename_vars(&self, map: &FxHashMap<String, String>) -> Self {
        if map.is_empty() {
            return self.clone();
        }
        self.substitute_with_lookup(&|v| {
            map.get(&v.name)
                .map(|new_name| Self::var(ChcVar::new(new_name, v.sort.clone())))
        })
    }

    /// Substitute sub-expressions by structural equality (#3577).
    /// Each `(from, to)` pair replaces occurrences of `from` with `to`.
    /// Matching is checked at each node before recursing into children.
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged.
    pub(crate) fn substitute_expr_pairs(&self, pairs: &[(Self, Self)]) -> Self {
        if pairs.is_empty() {
            return self.clone();
        }
        use std::cell::Cell;
        let budget = Cell::new(MAX_PREPROCESSING_NODES);
        Self::subst_expr_inner(self, &budget, 0, pairs).unwrap_or_else(|| self.clone())
    }

    fn subst_expr_inner(
        expr: &Self,
        budget: &std::cell::Cell<usize>,
        depth: usize,
        pairs: &[(Self, Self)],
    ) -> Option<Self> {
        maybe_grow_expr_stack(|| {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return None;
            }
            let remaining = budget.get();
            if remaining == 0 {
                return None;
            }
            budget.set(remaining - 1);

            // Check whole-expression matches before recursing
            for (from, to) in pairs {
                if expr == from {
                    return Some(to.clone());
                }
            }

            Some(match expr {
                Self::Bool(_)
                | Self::Int(_)
                | Self::Real(_, _)
                | Self::BitVec(_, _)
                | Self::Var(_)
                | Self::ConstArrayMarker(_)
                | Self::IsTesterMarker(_) => expr.clone(),
                Self::Op(op, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(
                                Self::subst_expr_inner(a, budget, depth + 1, pairs)
                                    .unwrap_or_else(|| a.as_ref().clone()),
                            )
                        })
                        .collect();
                    if args
                        .iter()
                        .zip(new_args.iter())
                        .all(|(old, new)| old.as_ref() == new.as_ref())
                    {
                        expr.clone()
                    } else {
                        Self::Op(*op, new_args)
                    }
                }
                Self::PredicateApp(name, id, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(
                                Self::subst_expr_inner(a, budget, depth + 1, pairs)
                                    .unwrap_or_else(|| a.as_ref().clone()),
                            )
                        })
                        .collect();
                    if args
                        .iter()
                        .zip(new_args.iter())
                        .all(|(old, new)| old.as_ref() == new.as_ref())
                    {
                        expr.clone()
                    } else {
                        Self::PredicateApp(name.clone(), *id, new_args)
                    }
                }
                Self::FuncApp(name, sort, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(
                                Self::subst_expr_inner(a, budget, depth + 1, pairs)
                                    .unwrap_or_else(|| a.as_ref().clone()),
                            )
                        })
                        .collect();
                    if args
                        .iter()
                        .zip(new_args.iter())
                        .all(|(old, new)| old.as_ref() == new.as_ref())
                    {
                        expr.clone()
                    } else {
                        Self::FuncApp(name.clone(), sort.clone(), new_args)
                    }
                }
                Self::ConstArray(ks, val) => {
                    let new_val = Arc::new(
                        Self::subst_expr_inner(val, budget, depth + 1, pairs)
                            .unwrap_or_else(|| val.as_ref().clone()),
                    );
                    if val.as_ref() == new_val.as_ref() {
                        expr.clone()
                    } else {
                        Self::ConstArray(ks.clone(), new_val)
                    }
                }
            })
        })
    }

    pub(crate) fn substitute_with_lookup<F>(&self, lookup: &F) -> Self
    where
        F: Fn(&ChcVar) -> Option<Self>,
    {
        use std::cell::Cell;
        let budget = Cell::new(MAX_PREPROCESSING_NODES);
        // `Arc`-pointer memo so shared input subtrees (a DAG, as produced by
        // nested-`let` expansion or a prior substitution) are substituted ONCE
        // and reused, instead of being re-walked and deep-cloned into a distinct
        // tree at every reference — the same structural-sharing fix
        // `substitute_let_shared` applies, now for the budgeted
        // `substitute_map`/`substitute_name_map`/`rename_vars` family that
        // dominates BMC transition-building and PDR frame rewriting. The result
        // also PRESERVES `Arc` sharing (a DAG out, not an exploded tree), so the
        // downstream eq/hash/drop/simplify walks stay linear too.
        let mut memo: FxHashMap<*const Self, Arc<Self>> = FxHashMap::default();
        // Wrap in an `Arc` so the root joins the memoized recursion. This is a
        // shallow clone (child `Arc`s are shared, refcount-bumped); the only
        // fresh node is the root itself, so intra-input sharing is fully kept.
        let root = Arc::new(self.clone());
        match Self::subst_inner(&root, &budget, 0, lookup, &mut memo) {
            Some(result) => Arc::try_unwrap(result).unwrap_or_else(|arc| (*arc).clone()),
            None => self.clone(),
        }
    }

    /// Memoized, sharing-preserving variable substitution (see
    /// `substitute_with_lookup`). Returns `None` only when the per-call node
    /// budget or recursion-depth cap is hit AT THIS node; callers substitute the
    /// original (unchanged) child in that case and continue — a local best-effort
    /// bail identical to the prior behavior, but reached far less often because
    /// shared subtrees no longer each re-spend the budget.
    fn subst_inner<F>(
        node: &Arc<Self>,
        budget: &std::cell::Cell<usize>,
        depth: usize,
        lookup: &F,
        memo: &mut FxHashMap<*const Self, Arc<Self>>,
    ) -> Option<Arc<Self>>
    where
        F: Fn(&ChcVar) -> Option<Self>,
    {
        // `Var` is the only leaf that can change; handle before the memo so the
        // substituted value is shared without a per-occurrence tree walk.
        if let Self::Var(v) = node.as_ref() {
            return Some(match lookup(v) {
                Some(value) => Arc::new(value),
                None => Arc::clone(node),
            });
        }
        // Shared input subtree reached again → reuse the prior substituted result.
        // Pointers are stable: every subtree of the borrowed root stays alive for
        // this call, and freshly-built nodes are never used as keys.
        let key = Arc::as_ptr(node);
        if let Some(cached) = memo.get(&key) {
            return Some(Arc::clone(cached));
        }
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        let remaining = budget.get();
        if remaining == 0 {
            return None;
        }
        budget.set(remaining - 1);

        let result = maybe_grow_expr_stack(|| match node.as_ref() {
            Self::Op(op, args) => {
                let mut changed = false;
                let mut new_args: Vec<Arc<Self>> = Vec::with_capacity(args.len());
                for a in args {
                    let n = Self::subst_inner(a, budget, depth + 1, lookup, memo)
                        .unwrap_or_else(|| Arc::clone(a));
                    changed |= !Arc::ptr_eq(&n, a);
                    new_args.push(n);
                }
                if changed {
                    Arc::new(Self::Op(*op, new_args))
                } else {
                    Arc::clone(node)
                }
            }
            Self::PredicateApp(name, id, args) => {
                let mut changed = false;
                let mut new_args: Vec<Arc<Self>> = Vec::with_capacity(args.len());
                for a in args {
                    let n = Self::subst_inner(a, budget, depth + 1, lookup, memo)
                        .unwrap_or_else(|| Arc::clone(a));
                    changed |= !Arc::ptr_eq(&n, a);
                    new_args.push(n);
                }
                if changed {
                    Arc::new(Self::PredicateApp(name.clone(), *id, new_args))
                } else {
                    Arc::clone(node)
                }
            }
            Self::FuncApp(name, sort, args) => {
                let mut changed = false;
                let mut new_args: Vec<Arc<Self>> = Vec::with_capacity(args.len());
                for a in args {
                    let n = Self::subst_inner(a, budget, depth + 1, lookup, memo)
                        .unwrap_or_else(|| Arc::clone(a));
                    changed |= !Arc::ptr_eq(&n, a);
                    new_args.push(n);
                }
                if changed {
                    Arc::new(Self::FuncApp(name.clone(), sort.clone(), new_args))
                } else {
                    Arc::clone(node)
                }
            }
            Self::ConstArray(ks, val) => {
                let new_val = Self::subst_inner(val, budget, depth + 1, lookup, memo)
                    .unwrap_or_else(|| Arc::clone(val));
                if Arc::ptr_eq(&new_val, val) {
                    Arc::clone(node)
                } else {
                    Arc::new(Self::ConstArray(ks.clone(), new_val))
                }
            }
            // Non-`Var` leaves (Bool/Int/Real/BitVec/markers): nothing to
            // substitute. `Var` was handled before the memo above.
            _ => Arc::clone(node),
        });
        memo.insert(key, Arc::clone(&result));
        Some(result)
    }

    /// Replace a disequality (not (= lhs rhs)) with a replacement expression.
    ///
    /// This is used for disequality splitting: (not (= a b)) -> (< a b) or (> a b).
    pub(crate) fn replace_diseq(
        &self,
        target_lhs: &Self,
        target_rhs: &Self,
        replacement: Self,
    ) -> Self {
        fn replace_diseq_inner(
            expr: &ChcExpr,
            depth: usize,
            target_lhs: &ChcExpr,
            target_rhs: &ChcExpr,
            replacement: &ChcExpr,
        ) -> ChcExpr {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return expr.clone();
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                        if eq_args.len() == 2 {
                            let lhs = &*eq_args[0];
                            let rhs = &*eq_args[1];
                            if (lhs == target_lhs && rhs == target_rhs)
                                || (lhs == target_rhs && rhs == target_lhs)
                            {
                                return replacement.clone();
                            }
                        }
                    }
                    let new_inner = Arc::new(replace_diseq_inner(
                        args[0].as_ref(),
                        depth + 1,
                        target_lhs,
                        target_rhs,
                        replacement,
                    ));
                    if args[0].as_ref() == new_inner.as_ref() {
                        expr.clone()
                    } else {
                        ChcExpr::Op(ChcOp::Not, vec![new_inner])
                    }
                }
                ChcExpr::Op(op, args) => {
                    let new_args: Vec<_> = args
                        .iter()
                        .map(|a| {
                            Arc::new(replace_diseq_inner(
                                a.as_ref(),
                                depth + 1,
                                target_lhs,
                                target_rhs,
                                replacement,
                            ))
                        })
                        .collect();
                    if args
                        .iter()
                        .zip(new_args.iter())
                        .all(|(old, new)| old.as_ref() == new.as_ref())
                    {
                        expr.clone()
                    } else {
                        ChcExpr::Op(*op, new_args)
                    }
                }
                _ => expr.clone(),
            })
        }

        replace_diseq_inner(self, 0, target_lhs, target_rhs, &replacement)
    }
}
