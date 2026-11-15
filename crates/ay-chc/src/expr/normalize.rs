// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression normalization passes (negation rewriting, strict comparison elimination).

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::intern::arc as mk_arc;
use super::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, MAX_EXPR_RECURSION_DEPTH,
    MAX_PREPROCESSING_NODES,
};

/// Rebuild `node` with `new` children, or return `node` itself when every
/// child is the same `Arc` (keeps the input's sharing).
fn rebuild_with(node: &Arc<ChcExpr>, new: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    let old = super::dag::children(node);
    if old.len() == new.len() && old.iter().zip(&new).all(|(a, b)| Arc::ptr_eq(a, b)) {
        return Arc::clone(node);
    }
    match (node.as_ref(), new.as_slice()) {
        (ChcExpr::Op(op, _), _) => Arc::new(ChcExpr::Op(*op, new)),
        (ChcExpr::PredicateApp(name, id, _), _) => {
            Arc::new(ChcExpr::PredicateApp(name.clone(), *id, new))
        }
        (ChcExpr::FuncApp(name, sort, _), _) => {
            Arc::new(ChcExpr::FuncApp(name.clone(), sort.clone(), new))
        }
        (ChcExpr::ConstArray(sort, _), [value]) => {
            Arc::new(ChcExpr::ConstArray(sort.clone(), Arc::clone(value)))
        }
        (ChcExpr::ArrayLambda(lambda), _) => {
            Arc::new(ChcExpr::ArrayLambda(lambda.with_captures(new)))
        }
        // Leaves have no children to rebuild.
        _ => Arc::clone(node),
    }
}

/// Pointer-keyed memo that also PINS each key (holds its `Arc`), so keys made
/// for freshly built nodes can never be reused by a later allocation within
/// one top-level call.
type PinnedMemo = FxHashMap<*const ChcExpr, (Arc<ChcExpr>, Arc<ChcExpr>)>;

/// `normalize_strict_int_comparisons` over distinct nodes (WP-F F0b). Same
/// local rewrite as the tree walk; the node budget counts distinct nodes, and
/// on exhaustion the input is returned unchanged (as the tree walk does).
pub(super) struct StrictDag {
    memo: PinnedMemo,
    budget: usize,
}

impl StrictDag {
    pub(super) fn run(expr: &ChcExpr) -> ChcExpr {
        let mut me = Self {
            memo: FxHashMap::default(),
            budget: MAX_PREPROCESSING_NODES,
        };
        let root = Arc::new(expr.clone());
        match me.node(&root) {
            Some(out) => Arc::unwrap_or_clone(out),
            None => expr.clone(),
        }
    }

    fn node(&mut self, node: &Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
        let kids = super::dag::children(node);
        if kids.is_empty() {
            return Some(Arc::clone(node));
        }
        let key = Arc::as_ptr(node);
        if let Some((_, done)) = self.memo.get(&key) {
            return Some(Arc::clone(done));
        }
        if self.budget == 0 {
            return None;
        }
        self.budget -= 1;
        let out = maybe_grow_expr_stack(|| -> Option<Arc<ChcExpr>> {
            match node.as_ref() {
                ChcExpr::Op(op, args) if args.len() == 2 => {
                    let a = self.node(&args[0])?;
                    let b = self.node(&args[1])?;
                    let is_int = |e: &ChcExpr| matches!(e.sort(), ChcSort::Int);
                    let int_ab = is_int(&a) && is_int(&b);
                    let bin = |op: ChcOp, x: Arc<ChcExpr>, y: Arc<ChcExpr>| {
                        Arc::new(ChcExpr::Op(op, vec![x, y]))
                    };
                    let plus_one = |x: Arc<ChcExpr>| {
                        Arc::new(ChcExpr::Op(ChcOp::Add, vec![x, mk_arc(ChcExpr::Int(1))]))
                    };
                    Some(match (op, a.as_ref(), b.as_ref()) {
                        (ChcOp::Lt, _, ChcExpr::Int(c)) if int_ab => match c.checked_sub(1) {
                            Some(c1) => bin(ChcOp::Le, a, mk_arc(ChcExpr::Int(c1))),
                            None => bin(ChcOp::Lt, a, b),
                        },
                        (ChcOp::Lt, ChcExpr::Int(c), _) if int_ab => match c.checked_add(1) {
                            Some(c1) => bin(ChcOp::Ge, b, mk_arc(ChcExpr::Int(c1))),
                            None => bin(ChcOp::Lt, a, b),
                        },
                        (ChcOp::Lt, _, _) if int_ab => bin(ChcOp::Le, plus_one(a), b),
                        (ChcOp::Gt, _, ChcExpr::Int(c)) if int_ab => match c.checked_add(1) {
                            Some(c1) => bin(ChcOp::Ge, a, mk_arc(ChcExpr::Int(c1))),
                            None => bin(ChcOp::Gt, a, b),
                        },
                        (ChcOp::Gt, ChcExpr::Int(c), _) if int_ab => match c.checked_sub(1) {
                            Some(c1) => bin(ChcOp::Le, b, mk_arc(ChcExpr::Int(c1))),
                            None => bin(ChcOp::Gt, a, b),
                        },
                        (ChcOp::Gt, _, _) if int_ab => bin(ChcOp::Ge, a, plus_one(b)),
                        _ => rebuild_with(node, vec![a, b]),
                    })
                }
                _ => {
                    let mut new = Vec::with_capacity(kids.len());
                    for child in kids {
                        new.push(self.node(child)?);
                    }
                    Some(rebuild_with(node, new))
                }
            }
        })?;
        self.memo.insert(key, (Arc::clone(node), Arc::clone(&out)));
        Some(out)
    }
}

/// `normalize_negations` over distinct nodes (WP-F F0b).
///
/// `norm(e)` is the tree walk's `normalize_inner(e)`; `neg(z)` is its
/// `normalize_inner(not(z))` for the De Morgan children. Both are memoised by
/// node (pinned: `neg` and double negation reach freshly built nodes). The
/// tree walk's "inner unchanged, skip rebuild" checks only avoid an
/// allocation — both of its branches are structurally equal — so they are
/// replaced by pointer checks. On budget exhaustion the input is returned
/// unchanged, which the tree walk also does for its root.
pub(super) struct NegationsDag {
    norm_memo: PinnedMemo,
    neg_memo: PinnedMemo,
    budget: usize,
}

impl NegationsDag {
    pub(super) fn run(expr: &ChcExpr) -> ChcExpr {
        let mut me = Self {
            norm_memo: FxHashMap::default(),
            neg_memo: FxHashMap::default(),
            budget: 1_000_000,
        };
        let root = Arc::new(expr.clone());
        match me.norm(&root) {
            Some(out) => Arc::unwrap_or_clone(out),
            None => expr.clone(),
        }
    }

    fn tick(&mut self) -> Option<()> {
        if self.budget == 0 {
            return None;
        }
        self.budget -= 1;
        Some(())
    }

    fn norm(&mut self, node: &Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
        let kids = super::dag::children(node);
        if kids.is_empty() {
            return Some(Arc::clone(node));
        }
        let key = Arc::as_ptr(node);
        if let Some((_, done)) = self.norm_memo.get(&key) {
            return Some(Arc::clone(done));
        }
        self.tick()?;
        let out = maybe_grow_expr_stack(|| -> Option<Arc<ChcExpr>> {
            match node.as_ref() {
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    let inner = self.norm(&args[0])?;
                    self.not_of(&args[0], inner)
                }
                _ => {
                    let mut new = Vec::with_capacity(kids.len());
                    for child in kids {
                        new.push(self.norm(child)?);
                    }
                    Some(rebuild_with(node, new))
                }
            }
        })?;
        self.norm_memo
            .insert(key, (Arc::clone(node), Arc::clone(&out)));
        Some(out)
    }

    /// The tree walk's `normalize_inner(not(z))`: `not(z)` strips a double
    /// negation, otherwise it is `Not(z)`, whose normalization is
    /// `not_of(z, norm(z))`.
    fn neg(&mut self, z: &Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
        if let ChcExpr::Op(ChcOp::Not, w) = z.as_ref() {
            if w.len() == 1 {
                return self.norm(&w[0]);
            }
        }
        let key = Arc::as_ptr(z);
        if let Some((_, done)) = self.neg_memo.get(&key) {
            return Some(Arc::clone(done));
        }
        self.tick()?;
        let inner = self.norm(z)?;
        let out = self.not_of(z, inner)?;
        self.neg_memo.insert(key, (Arc::clone(z), Arc::clone(&out)));
        Some(out)
    }

    /// Normalization of `Not(x)` given `inner = norm(x)`.
    fn not_of(&mut self, x: &Arc<ChcExpr>, inner: Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
        maybe_grow_expr_stack(|| -> Option<Arc<ChcExpr>> {
            Some(match inner.as_ref() {
                ChcExpr::Bool(b) => mk_arc(ChcExpr::Bool(!b)),
                ChcExpr::Op(ChcOp::Not, inner_args) if inner_args.len() == 1 => {
                    self.norm(&inner_args[0])?
                }
                ChcExpr::Op(op @ (ChcOp::And | ChcOp::Or), inner_args) => {
                    let mut parts = Vec::with_capacity(inner_args.len());
                    for child in inner_args {
                        parts.push(self.neg(child)?);
                    }
                    let (flipped, empty) = if *op == ChcOp::And {
                        (ChcOp::Or, false)
                    } else {
                        (ChcOp::And, true)
                    };
                    match parts.len() {
                        0 => mk_arc(ChcExpr::Bool(empty)),
                        1 => parts.swap_remove(0),
                        _ => Arc::new(ChcExpr::Op(flipped, parts)),
                    }
                }
                ChcExpr::Op(op, inner_args) if inner_args.len() == 2 => {
                    let a = Arc::clone(&inner_args[0]);
                    let b = Arc::clone(&inner_args[1]);
                    let flipped = match op {
                        ChcOp::Eq | ChcOp::Iff => Some(ChcOp::Ne),
                        ChcOp::Ne => Some(ChcOp::Eq),
                        ChcOp::Lt => Some(ChcOp::Ge),
                        ChcOp::Le => Some(ChcOp::Gt),
                        ChcOp::Gt => Some(ChcOp::Le),
                        ChcOp::Ge => Some(ChcOp::Lt),
                        _ => None,
                    };
                    match flipped {
                        Some(f) => Arc::new(ChcExpr::Op(f, vec![a, b])),
                        None => Self::not_node(x, inner),
                    }
                }
                _ => Self::not_node(x, inner),
            })
        })
    }

    /// `Not(inner)`, reusing the input's `Not(x)` shape when `inner` is `x`.
    fn not_node(x: &Arc<ChcExpr>, inner: Arc<ChcExpr>) -> Arc<ChcExpr> {
        let child = if Arc::ptr_eq(x, &inner) {
            Arc::clone(x)
        } else {
            inner
        };
        Arc::new(ChcExpr::Op(ChcOp::Not, vec![child]))
    }
}

impl ChcExpr {
    /// Normalize negations by rewriting `not` applied to comparisons into equivalent operators.
    ///
    /// This keeps formulas in a form that the CHC SMT backend can treat as theory atoms, avoiding
    /// expensive DPLL(T) splitting on Boolean structure like `(not (<= ...))`.
    ///
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2771).
    /// Unnormalized negations are still semantically correct, just less efficient.
    pub(crate) fn normalize_negations(&self) -> Self {
        // Shared DAGs (WP-F F0b): rewrite each distinct node once. Exact
        // whenever the tree walk below could not truncate (its recursion runs
        // at most two levels per input edge, hence the halved cap).
        if super::dag::prefer_dag_walk(self, MAX_EXPR_RECURSION_DEPTH / 2) {
            return NegationsDag::run(self);
        }
        self.normalize_negations_tree()
    }

    /// The per-path (tree) form of [`Self::normalize_negations`].
    pub(super) fn normalize_negations_tree(&self) -> Self {
        use std::cell::Cell;

        /// Budget for normalize_negations traversal (#2771).
        const MAX_NORMALIZE_NODES: usize = 1_000_000;

        let budget = Cell::new(MAX_NORMALIZE_NODES);

        fn normalize_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                        let inner = normalize_inner(&args[0], budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        match inner {
                            ChcExpr::Bool(b) => ChcExpr::Bool(!b),
                            ChcExpr::Op(ChcOp::Not, ref inner_args) if inner_args.len() == 1 => {
                                normalize_inner(&inner_args[0], budget, depth + 1)
                                    .unwrap_or_else(|| inner_args[0].as_ref().clone())
                            }
                            ChcExpr::Op(ChcOp::And, ref inner_args) => {
                                // De Morgan: NOT(AND(a,b,...)) → OR(NOT(a), NOT(b), ...)
                                // Distributing NOT here avoids mk_not's De Morgan in the
                                // TermStore, which creates complex boolean structure that
                                // triggers incorrect UNSAT in the SAT solver (#5376).
                                let children: Vec<ChcExpr> = inner_args
                                    .iter()
                                    .map(|child| {
                                        let not_child = ChcExpr::not(child.as_ref().clone());
                                        normalize_inner(&not_child, budget, depth + 1)
                                            .unwrap_or(not_child)
                                    })
                                    .collect();
                                ChcExpr::or_vec(children)
                            }
                            ChcExpr::Op(ChcOp::Or, ref inner_args) => {
                                // De Morgan: NOT(OR(a,b,...)) → AND(NOT(a), NOT(b), ...)
                                let children: Vec<ChcExpr> = inner_args
                                    .iter()
                                    .map(|child| {
                                        let not_child = ChcExpr::not(child.as_ref().clone());
                                        normalize_inner(&not_child, budget, depth + 1)
                                            .unwrap_or(not_child)
                                    })
                                    .collect();
                                ChcExpr::and_vec(children)
                            }
                            ChcExpr::Op(op, ref inner_args) if inner_args.len() == 2 => {
                                let a = inner_args[0].as_ref().clone();
                                let b = inner_args[1].as_ref().clone();
                                match op {
                                    ChcOp::Eq | ChcOp::Iff => ChcExpr::ne(a, b),
                                    ChcOp::Ne => ChcExpr::eq(a, b),
                                    ChcOp::Lt => ChcExpr::ge(a, b),
                                    ChcOp::Le => ChcExpr::gt(a, b),
                                    ChcOp::Gt => ChcExpr::le(a, b),
                                    ChcOp::Ge => ChcExpr::lt(a, b),
                                    _ => {
                                        // Skip rebuild when inner is unchanged (#3665)
                                        if args[0].as_ref() == &ChcExpr::Op(op, inner_args.clone())
                                        {
                                            expr.clone()
                                        } else {
                                            ChcExpr::not(ChcExpr::Op(op, inner_args.clone()))
                                        }
                                    }
                                }
                            }
                            ref other if args[0].as_ref() == other => {
                                // Inner unchanged, skip rebuild (#3665)
                                expr.clone()
                            }
                            other => ChcExpr::not(other),
                        }
                    }
                    _ => expr.map_children_with(|child| {
                        normalize_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        normalize_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }

    /// Rewrite strict integer comparisons with constant bounds into equivalent non-strict forms.
    ///
    /// For Ints:
    /// - `x < c`  <=>  `x <= c-1`
    /// - `x > c`  <=>  `x >= c+1`
    /// - `c < x`  <=>  `x >= c+1`
    /// - `c > x`  <=>  `x <= c-1`
    pub(crate) fn normalize_strict_int_comparisons(&self) -> Self {
        // Shared DAGs (WP-F F0b): a pure bottom-up rewrite, memoised per node.
        if super::dag::prefer_dag_walk(self, MAX_EXPR_RECURSION_DEPTH) {
            return StrictDag::run(self);
        }
        self.normalize_strict_int_comparisons_tree()
    }

    /// The per-path (tree) form of [`Self::normalize_strict_int_comparisons`].
    pub(super) fn normalize_strict_int_comparisons_tree(&self) -> Self {
        use std::cell::Cell;

        let budget = Cell::new(MAX_PREPROCESSING_NODES);

        fn normalize_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Op(op, args) if args.len() == 2 => {
                        let a = normalize_inner(&args[0], budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        let b = normalize_inner(&args[1], budget, depth + 1)
                            .unwrap_or_else(|| args[1].as_ref().clone());

                        let is_int = |e: &ChcExpr| matches!(e.sort(), ChcSort::Int);

                        match op {
                            ChcOp::Lt if is_int(&a) && is_int(&b) => match (&a, &b) {
                                (_, ChcExpr::Int(c)) => {
                                    if let Some(c1) = c.checked_sub(1) {
                                        ChcExpr::le(a.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::lt(a.clone(), b.clone())
                                    }
                                }
                                (ChcExpr::Int(c), _) => {
                                    if let Some(c1) = c.checked_add(1) {
                                        ChcExpr::ge(b.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::lt(a.clone(), b.clone())
                                    }
                                }
                                _ => ChcExpr::le(ChcExpr::add(a, ChcExpr::Int(1)), b),
                            },
                            ChcOp::Gt if is_int(&a) && is_int(&b) => match (&a, &b) {
                                (_, ChcExpr::Int(c)) => {
                                    if let Some(c1) = c.checked_add(1) {
                                        ChcExpr::ge(a.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::gt(a.clone(), b.clone())
                                    }
                                }
                                (ChcExpr::Int(c), _) => {
                                    if let Some(c1) = c.checked_sub(1) {
                                        ChcExpr::le(b.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::gt(a.clone(), b.clone())
                                    }
                                }
                                _ => ChcExpr::ge(a, ChcExpr::add(b, ChcExpr::Int(1))),
                            },
                            _ => {
                                // Skip rebuild when children are unchanged (#3665)
                                if args[0].as_ref() == &a && args[1].as_ref() == &b {
                                    expr.clone()
                                } else {
                                    ChcExpr::Op(*op, vec![Arc::new(a), Arc::new(b)])
                                }
                            }
                        }
                    }
                    _ => expr.map_children_with(|child| {
                        normalize_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        normalize_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }
}
