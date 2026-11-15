// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DAG-linear counting and SMT-LIB printing of `ChcExpr`.
//!
//! Workstream D, Rung 1 (CHC-COMP 2026; the development design notes
//! DESIGN_lra_interp_tpa.md` §4.1, interface contract **C-P2**).
//! **Owner after the day-1 skeleton: WP-D1-P** (proof substrate). The
//! implementation shipped with the skeleton, written by WP-D1-M, because the
//! executor adapter's Search-lane scripts (bridge item D-1, WP-D1-M) print
//! through it before WP-D1-P starts.
//!
//! `ChcExpr` children are `Arc`s, and substitution and `let` expansion keep
//! that sharing, so a k-step unrolling of a transition relation is a small DAG
//! whose tree expansion can be orders of magnitude larger
//! (`om1_with_relays_general_4_6_agreement`: a 1.09 MB let-expanded k=1 query).
//! Both functions here visit each distinct node (pointer identity) once.
//!
//! Semantics contract: for every root, the text emitted by
//! [`write_asserts_dag`] denotes the same formula as
//! `(assert <InvariantModel::expr_to_smtlib(root)>)`. With no node referenced
//! twice inside a root it is byte-identical to that text; otherwise each
//! compound node referenced at least twice inside the root is bound once by a
//! `let`. `let` binds in parallel, so bindings are emitted level by level
//! (a binding only references bindings of strictly lower levels), and the
//! nesting depth is the number of levels, not the number of bindings.
//! Binder names are `<prefix><n>` with prefix `_d`, lengthened with `_` until
//! no symbol of the root starts with it, so a binder can never capture a
//! variable, function or predicate name of the formula.

#![expect(
    dead_code,
    reason = "Workstream D day-1 skeleton: WP-D1-M (executor adapter) and WP-D1-P (proof scripts) wires these items; remove when used"
)]

use crate::pdr::model::InvariantModel;
use crate::smt::executor_adapter::{quote_symbol, sort_to_smtlib};
use crate::{ChcExpr, ChcOp, ChcSort};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::borrow::Cow;
use std::fmt::Write as _;
use std::sync::Arc;

/// Resource caps for one DAG walk.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DagCaps {
    /// Maximum number of distinct nodes (pointer identity) visited.
    pub(crate) max_unique_nodes: usize,
    /// Maximum root-to-leaf path length, in edges (a root alone has depth 0).
    pub(crate) max_depth: usize,
}

/// What one walk saw.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct DagStats {
    /// Distinct nodes visited (for [`write_asserts_dag`]: summed per root).
    pub(crate) unique_nodes: usize,
    /// Distinct compound nodes referenced at least twice (the `let`-bound
    /// nodes for [`write_asserts_dag`]).
    pub(crate) shared_nodes: usize,
    /// Longest root-to-leaf path, in edges.
    pub(crate) max_depth: usize,
}

/// Why a walk refused its input. The caller keeps its previous behaviour
/// (for printing: the tree printer).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DagError {
    /// More distinct nodes than `DagCaps::max_unique_nodes`.
    UniqueNodeCap,
    /// A root-to-leaf path longer than `DagCaps::max_depth`.
    DepthCap,
    /// A node that has no SMT-LIB surface (internal parser markers).
    Unsupported(&'static str),
}

impl std::fmt::Display for DagError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UniqueNodeCap => write!(f, "DAG unique-node cap exceeded"),
            Self::DepthCap => write!(f, "DAG depth cap exceeded"),
            Self::Unsupported(what) => write!(f, "unsupported DAG node: {what}"),
        }
    }
}

/// Counts distinct `Arc` nodes (pointer memo) reachable from `roots`; never
/// walks a shared subtree twice.
pub(crate) fn count_dag(roots: &[&ChcExpr], caps: DagCaps) -> Result<DagStats, DagError> {
    let mut walk = DagWalk::default();
    for root in roots {
        walk.visit_root(root, caps)?;
    }
    walk.checked_stats(roots, caps)
}

/// Appends one `(assert …)` per root; every node referenced ≥ 2 times inside
/// that root is bound once by a `let` (see the module docs for the naming and
/// level rules). Semantics equal `InvariantModel::expr_to_smtlib`.
///
/// On `Err`, `out` is left unchanged.
pub(crate) fn write_asserts_dag(
    out: &mut String,
    roots: &[&ChcExpr],
    caps: DagCaps,
) -> Result<DagStats, DagError> {
    let mut text = String::new();
    let mut total = DagStats::default();
    let mut remaining = caps.max_unique_nodes;
    for root in roots {
        let mut walk = DagWalk::default();
        walk.visit_root(
            root,
            DagCaps {
                max_unique_nodes: remaining,
                max_depth: caps.max_depth,
            },
        )?;
        let stats = walk.checked_stats(
            &[root],
            DagCaps {
                max_unique_nodes: remaining,
                max_depth: caps.max_depth,
            },
        )?;
        remaining = remaining.saturating_sub(stats.unique_nodes);
        total.unique_nodes += stats.unique_nodes;
        total.shared_nodes += stats.shared_nodes;
        total.max_depth = total.max_depth.max(stats.max_depth);
        walk.write_assert(&mut text, root)?;
    }
    out.push_str(&text);
    Ok(total)
}

/// Direct children of a node, in printing order.
fn children(expr: &ChcExpr) -> &[Arc<ChcExpr>] {
    match expr {
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args
        }
        ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
        ChcExpr::ArrayLambda(lambda) => lambda.captures(),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => &[],
    }
}

/// Includes a lambda's immutable code without adding it to the enclosing
/// let-binding scope. Captures retain their ordinary child order; code is last.
fn semantic_child(expr: &ChcExpr, index: usize) -> Option<&ChcExpr> {
    let ordinary = children(expr);
    if let Some(child) = ordinary.get(index) {
        return Some(child.as_ref());
    }
    match expr {
        ChcExpr::ArrayLambda(lambda) if index == ordinary.len() => Some(lambda.body()),
        _ => None,
    }
}

/// Complete resource census, with one height per distinct semantic node. This
/// extra walk is needed only when the binding walk encountered a lambda. A
/// shared body can occur at different depths, so a memo hit checks its full
/// previously computed height at the new incoming edge.
fn semantic_resources(roots: &[&ChcExpr], caps: DagCaps) -> Result<(usize, usize), DagError> {
    let mut heights: FxHashMap<usize, usize> = FxHashMap::default();
    let mut max_depth = 0;
    for root in roots {
        if let Some(&height) = heights.get(&node_key(root)) {
            if height > caps.max_depth {
                return Err(DagError::DepthCap);
            }
            max_depth = max_depth.max(height);
            continue;
        }
        if heights.len() >= caps.max_unique_nodes {
            return Err(DagError::UniqueNodeCap);
        }
        heights.insert(node_key(root), 0);
        let mut stack = vec![(*root, 0usize)];
        while let Some((node, next_child)) = stack.last_mut() {
            let node = *node;
            if let Some(child) = semantic_child(node, *next_child) {
                *next_child += 1;
                let depth = stack.len();
                if depth > caps.max_depth {
                    return Err(DagError::DepthCap);
                }
                if let Some(&height) = heights.get(&node_key(child)) {
                    if depth.saturating_add(height) > caps.max_depth {
                        return Err(DagError::DepthCap);
                    }
                } else {
                    if heights.len() >= caps.max_unique_nodes {
                        return Err(DagError::UniqueNodeCap);
                    }
                    heights.insert(node_key(child), 0);
                    stack.push((child, 0));
                }
            } else {
                stack.pop();
                let mut height = 0;
                let mut index = 0;
                while let Some(child) = semantic_child(node, index) {
                    height = height.max(heights[&node_key(child)].saturating_add(1));
                    index += 1;
                }
                heights.insert(node_key(node), height);
            }
        }
        max_depth = max_depth.max(heights[&node_key(root)]);
    }
    Ok((heights.len(), max_depth))
}

fn node_key(expr: &ChcExpr) -> usize {
    std::ptr::from_ref(expr) as usize
}

#[derive(Clone, Copy, Debug, Default)]
struct NodeInfo {
    /// Occurrences as a child (plus one per root occurrence).
    refs: u32,
    /// Longest path below this node, in edges (final once the node is done).
    height: u32,
    /// Highest binding level referenced by this node's printed body.
    body_level: u32,
    /// Binding level (1-based) if this node is let-bound, else 0.
    level: u32,
    /// Binder index if this node is let-bound.
    binder: u32,
}

/// One memoised post-order walk over a set of roots.
#[derive(Default)]
struct DagWalk<'a> {
    info: FxHashMap<usize, NodeInfo>,
    /// Distinct nodes, children before parents.
    post_order: Vec<&'a ChcExpr>,
    max_depth: usize,
    has_array_lambda: bool,
}

impl<'a> DagWalk<'a> {
    fn visit_root(&mut self, root: &'a ChcExpr, caps: DagCaps) -> Result<(), DagError> {
        if let Some(info) = self.info.get_mut(&node_key(root)) {
            info.refs = info.refs.saturating_add(1);
            return Ok(());
        }
        self.enter(root, 0, caps)?;
        let mut stack: Vec<(&'a ChcExpr, usize)> = vec![(root, 0)];
        loop {
            let Some(top) = stack.last_mut() else {
                break;
            };
            let node: &'a ChcExpr = top.0;
            let kids = children(node);
            if top.1 < kids.len() {
                let child: &'a ChcExpr = kids[top.1].as_ref();
                top.1 += 1;
                // Stack holds the path root..parent; the child sits one below.
                let child_depth = stack.len();
                if let Some(info) = self.info.get_mut(&node_key(child)) {
                    info.refs = info.refs.saturating_add(1);
                    if child_depth.saturating_add(info.height as usize) > caps.max_depth {
                        return Err(DagError::DepthCap);
                    }
                } else {
                    self.enter(child, child_depth, caps)?;
                    stack.push((child, 0));
                }
            } else {
                stack.pop();
                self.leave(node);
            }
        }
        let height = self.info.get(&node_key(root)).map_or(0, |i| i.height) as usize;
        self.max_depth = self.max_depth.max(height);
        Ok(())
    }

    fn enter(&mut self, node: &'a ChcExpr, depth: usize, caps: DagCaps) -> Result<(), DagError> {
        if depth > caps.max_depth {
            return Err(DagError::DepthCap);
        }
        if matches!(
            node,
            ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_)
        ) {
            return Err(DagError::Unsupported("internal parser marker"));
        }
        if self.info.len() >= caps.max_unique_nodes {
            return Err(DagError::UniqueNodeCap);
        }
        self.has_array_lambda |= matches!(node, ChcExpr::ArrayLambda(_));
        self.info.insert(
            node_key(node),
            NodeInfo {
                refs: 1,
                ..NodeInfo::default()
            },
        );
        Ok(())
    }

    /// Post-order completion: children are final, so height is final.
    fn leave(&mut self, node: &'a ChcExpr) {
        let height = children(node)
            .iter()
            .filter_map(|child| self.info.get(&node_key(child)))
            .map(|info| info.height.saturating_add(1))
            .max()
            .unwrap_or(0);
        if let Some(info) = self.info.get_mut(&node_key(node)) {
            info.height = height;
        }
        self.post_order.push(node);
    }

    fn is_shared(expr: &ChcExpr, info: &NodeInfo) -> bool {
        info.refs >= 2 && !children(expr).is_empty()
    }

    /// The binding walk deliberately treats closed lambda code as a separate
    /// scope. Resource accounting must still cover every node that it emits.
    fn checked_stats(&self, roots: &[&ChcExpr], caps: DagCaps) -> Result<DagStats, DagError> {
        let mut stats = self.stats();
        if self.has_array_lambda {
            let (unique_nodes, max_depth) = semantic_resources(roots, caps)?;
            stats.unique_nodes = unique_nodes;
            stats.max_depth = max_depth;
        }
        Ok(stats)
    }

    fn stats(&self) -> DagStats {
        let shared_nodes = self
            .post_order
            .iter()
            .filter(|node| {
                self.info
                    .get(&node_key(node))
                    .is_some_and(|info| Self::is_shared(node, info))
            })
            .count();
        DagStats {
            unique_nodes: self.post_order.len(),
            shared_nodes,
            max_depth: self.max_depth,
        }
    }

    /// Assign binding levels and binder indices, pick a capture-free prefix
    /// and print `(assert …)` for the single root this walk covered.
    fn write_assert(&mut self, out: &mut String, root: &ChcExpr) -> Result<(), DagError> {
        let mut levels: Vec<Vec<&'a ChcExpr>> = Vec::new();
        let mut binder = 0u32;
        for index in 0..self.post_order.len() {
            let node = self.post_order[index];
            let body_level = children(node)
                .iter()
                .filter_map(|child| self.info.get(&node_key(child)))
                .map(|info| {
                    if info.level > 0 {
                        info.level
                    } else {
                        info.body_level
                    }
                })
                .max()
                .unwrap_or(0);
            let Some(info) = self.info.get_mut(&node_key(node)) else {
                continue;
            };
            info.body_level = body_level;
            if Self::is_shared(node, info) {
                info.level = body_level + 1;
                info.binder = binder;
                binder += 1;
                let slot = info.level as usize - 1;
                if levels.len() <= slot {
                    levels.resize_with(slot + 1, Vec::new);
                }
                levels[slot].push(node);
            }
        }
        let prefix = self.binder_prefix();
        out.push_str("(assert ");
        let mut opened = 0usize;
        for level in &levels {
            if level.is_empty() {
                continue;
            }
            out.push_str("(let (");
            for (i, node) in level.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                let index = self.info.get(&node_key(node)).map_or(0, |i| i.binder);
                let _ = write!(out, "({prefix}{index} ");
                self.write_body(out, node, &prefix)?;
                out.push(')');
            }
            out.push_str(") ");
            opened += 1;
        }
        self.write_term(out, root, &prefix)?;
        for _ in 0..opened {
            out.push(')');
        }
        out.push_str(")\n");
        Ok(())
    }

    /// `_d`, lengthened with `_` until no symbol of the walked formula starts
    /// with it.
    fn binder_prefix(&self) -> String {
        let mut prefix = String::from("_d");
        let symbols: Vec<&str> = self
            .post_order
            .iter()
            .filter_map(|node| match node {
                ChcExpr::Var(var) => Some(var.name.as_str()),
                ChcExpr::PredicateApp(name, _, _) | ChcExpr::FuncApp(name, _, _) => {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();
        while symbols.iter().any(|symbol| symbol.starts_with(&prefix))
            || self.post_order.iter().any(|node| matches!(node, ChcExpr::ArrayLambda(lambda) if lambda.code_uses_prefix(&prefix)))
        {
            prefix.push('_');
        }
        prefix
    }

    /// A reference to `node` from a parent: its binder if let-bound, else its
    /// body.
    fn write_term(&self, out: &mut String, node: &ChcExpr, prefix: &str) -> Result<(), DagError> {
        match self.info.get(&node_key(node)) {
            Some(info) if info.level > 0 => {
                let _ = write!(out, "{prefix}{}", info.binder);
                Ok(())
            }
            _ => self.write_body(out, node, prefix),
        }
    }

    /// The node itself, exactly as `InvariantModel::expr_to_smtlib` prints
    /// it, with let-bound children replaced by their binders.
    fn write_body(&self, out: &mut String, node: &ChcExpr, prefix: &str) -> Result<(), DagError> {
        crate::expr::maybe_grow_expr_stack(|| match node {
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_) => {
                out.push_str(&InvariantModel::expr_to_smtlib(node));
                Ok(())
            }
            ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => {
                Err(DagError::Unsupported("internal parser marker"))
            }
            ChcExpr::PredicateApp(name, _, args) => {
                self.write_app(out, &quote_symbol(name), args, prefix)
            }
            ChcExpr::FuncApp(name, sort, args) => {
                let head = match sort {
                    ChcSort::Uninterpreted(sort_name)
                    | ChcSort::Datatype {
                        name: sort_name, ..
                    } => {
                        format!("(as {} {})", quote_symbol(name), quote_symbol(sort_name))
                    }
                    _ => quote_symbol(name),
                };
                self.write_app(out, &head, args, prefix)
            }
            ChcExpr::Op(op, args) => {
                out.push('(');
                out.push_str(&op_head(op));
                for arg in args {
                    out.push(' ');
                    self.write_term(out, arg, prefix)?;
                }
                out.push(')');
                Ok(())
            }
            ChcExpr::ArrayLambda(lambda) => {
                let mut captures = Vec::new();
                for value in lambda.captures() {
                    let mut text = String::new();
                    self.write_term(&mut text, value, prefix)?;
                    captures.push(text);
                }
                out.push_str(
                    &lambda.render(&captures, &InvariantModel::expr_to_smtlib(lambda.body())),
                );
                Ok(())
            }
            ChcExpr::ConstArray(key_sort, value) => {
                let _ = write!(
                    out,
                    "((as const (Array {} {})) ",
                    sort_to_smtlib(key_sort),
                    sort_to_smtlib(&value.sort())
                );
                self.write_term(out, value, prefix)?;
                out.push(')');
                Ok(())
            }
        })
    }

    fn write_app(
        &self,
        out: &mut String,
        head: &str,
        args: &[Arc<ChcExpr>],
        prefix: &str,
    ) -> Result<(), DagError> {
        if args.is_empty() {
            out.push_str(head);
            return Ok(());
        }
        out.push('(');
        out.push_str(head);
        for arg in args {
            out.push(' ');
            self.write_term(out, arg, prefix)?;
        }
        out.push(')');
        Ok(())
    }
}

/// The operator head `InvariantModel::expr_to_smtlib` prints (indexed
/// bit-vector operators as `(_ name params)`).
fn op_head(op: &ChcOp) -> Cow<'static, str> {
    let name = match op {
        ChcOp::Not => "not",
        ChcOp::And => "and",
        ChcOp::Or => "or",
        ChcOp::Implies => "=>",
        ChcOp::Iff | ChcOp::Eq => "=",
        ChcOp::Add => "+",
        ChcOp::Sub | ChcOp::Neg => "-",
        ChcOp::Mul => "*",
        ChcOp::Div => "div",
        ChcOp::Mod => "mod",
        ChcOp::Ne => "distinct",
        ChcOp::Lt => "<",
        ChcOp::Le => "<=",
        ChcOp::Gt => ">",
        ChcOp::Ge => ">=",
        ChcOp::Ite => "ite",
        ChcOp::Select => "select",
        ChcOp::Store => "store",
        ChcOp::BvAdd => "bvadd",
        ChcOp::BvSub => "bvsub",
        ChcOp::BvMul => "bvmul",
        ChcOp::BvUDiv => "bvudiv",
        ChcOp::BvURem => "bvurem",
        ChcOp::BvSDiv => "bvsdiv",
        ChcOp::BvSRem => "bvsrem",
        ChcOp::BvSMod => "bvsmod",
        ChcOp::BvAnd => "bvand",
        ChcOp::BvOr => "bvor",
        ChcOp::BvXor => "bvxor",
        ChcOp::BvNand => "bvnand",
        ChcOp::BvNor => "bvnor",
        ChcOp::BvXnor => "bvxnor",
        ChcOp::BvNot => "bvnot",
        ChcOp::BvNeg => "bvneg",
        ChcOp::BvShl => "bvshl",
        ChcOp::BvLShr => "bvlshr",
        ChcOp::BvAShr => "bvashr",
        ChcOp::BvULt => "bvult",
        ChcOp::BvULe => "bvule",
        ChcOp::BvUGt => "bvugt",
        ChcOp::BvUGe => "bvuge",
        ChcOp::BvSLt => "bvslt",
        ChcOp::BvSLe => "bvsle",
        ChcOp::BvSGt => "bvsgt",
        ChcOp::BvSGe => "bvsge",
        ChcOp::BvComp => "bvcomp",
        ChcOp::BvConcat => "concat",
        ChcOp::Bv2Nat => "bv2nat",
        ChcOp::BvExtract(hi, lo) => return Cow::Owned(format!("(_ extract {hi} {lo})")),
        ChcOp::BvZeroExtend(n) => return Cow::Owned(format!("(_ zero_extend {n})")),
        ChcOp::BvSignExtend(n) => return Cow::Owned(format!("(_ sign_extend {n})")),
        ChcOp::BvRotateLeft(n) => return Cow::Owned(format!("(_ rotate_left {n})")),
        ChcOp::BvRotateRight(n) => return Cow::Owned(format!("(_ rotate_right {n})")),
        ChcOp::BvRepeat(n) => return Cow::Owned(format!("(_ repeat {n})")),
        ChcOp::Int2Bv(w) => return Cow::Owned(format!("(_ int2bv {w})")),
    };
    Cow::Borrowed(name)
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "dag_smtlib_tests.rs"]
mod tests;
