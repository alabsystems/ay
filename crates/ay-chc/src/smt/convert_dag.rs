// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `convert_expr` entry point with a per-call node memo (WP-F F0c).

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::TermId;

use super::context::SmtContext;
use crate::{ChcExpr, ChcVar};

/// Inner children [`SmtContext::convert_expr`] converts as a plain tree walk
/// before it starts memoising by node address (keeps small conversions
/// allocation-free).
const CONVERT_PLAIN_CHILDREN: usize = 1024;

/// Per-top-level-call conversion state.
pub(super) struct ConvertCx {
    plain_children_left: usize,
    pub(super) bindings: FxHashMap<ChcVar, TermId>,
    /// Child node address -> converted term. Valid only within one top-level
    /// `convert_expr` call, while the borrowed root keeps every node alive.
    memo: Option<FxHashMap<usize, TermId>>,
}

impl ConvertCx {
    pub(super) fn scoped(bindings: FxHashMap<ChcVar, TermId>) -> Self {
        Self {
            plain_children_left: CONVERT_PLAIN_CHILDREN,
            memo: None,
            bindings,
        }
    }
}

impl SmtContext {
    pub fn convert_expr(&mut self, expr: &ChcExpr) -> TermId {
        let mut cx = ConvertCx {
            plain_children_left: CONVERT_PLAIN_CHILDREN,
            memo: None,
            bindings: FxHashMap::default(),
        };
        self.convert_node(expr, &mut cx)
    }

    /// [`Self::convert_expr`] without the node memo (differential tests).
    #[cfg(test)]
    pub(crate) fn convert_expr_unmemoised(&mut self, expr: &ChcExpr) -> TermId {
        let mut cx = ConvertCx {
            plain_children_left: usize::MAX,
            memo: None,
            bindings: FxHashMap::default(),
        };
        self.convert_node(expr, &mut cx)
    }

    pub(super) fn convert_node(&mut self, expr: &ChcExpr, cx: &mut ConvertCx) -> TermId {
        // Guard against stack overflow on deep expression trees (e.g., from PDKind
        // iterations building deep conjunctions). Uses stacker to grow onto heap
        // when the thread stack runs low — matching the protection in expr.rs
        // traversals (#2759).
        crate::expr::maybe_grow_expr_stack(|| self.convert_expr_inner(expr, cx))
    }

    /// Convert one `Arc` child, memoised per node address once
    /// [`CONVERT_PLAIN_CHILDREN`] children have been converted in this call
    /// (WP-F F0c).
    ///
    /// Sound and exact: the input root is borrowed for the whole top-level
    /// `convert_expr` call, so every child address denotes one live node; and
    /// converting a node is a deterministic function of its structure (the
    /// `TermStore` hash-conses, and the variable / predicate-application maps
    /// return the term they minted the first time), so a memo hit returns the
    /// very `TermId` a re-conversion would. The only observable difference is
    /// the node budget: `conversion_node_count` now counts DISTINCT nodes, so
    /// `MAX_CONVERSION_NODES` bounds the DAG a query shares rather than its tree
    /// expansion. A conversion that ran out of budget is never memoised (the
    /// whole conversion is discarded by the caller anyway).
    pub(super) fn convert_children(
        &mut self,
        args: &[Arc<ChcExpr>],
        cx: &mut ConvertCx,
    ) -> Vec<TermId> {
        args.iter().map(|a| self.convert_child(a, cx)).collect()
    }

    pub(super) fn convert_child(&mut self, child: &Arc<ChcExpr>, cx: &mut ConvertCx) -> TermId {
        let is_leaf = matches!(
            child.as_ref(),
            ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
        );
        if is_leaf {
            return self.convert_node(child, cx);
        }
        if cx.plain_children_left > 0 {
            cx.plain_children_left -= 1;
            return self.convert_node(child, cx);
        }
        let key = Arc::as_ptr(child) as usize;
        if let Some(&term) = cx.memo.as_ref().and_then(|memo| memo.get(&key)) {
            return term;
        }
        let term = self.convert_node(child, cx);
        if !self.conversion_budget_exceeded {
            cx.memo
                .get_or_insert_with(Default::default)
                .insert(key, term);
        }
        term
    }
}
