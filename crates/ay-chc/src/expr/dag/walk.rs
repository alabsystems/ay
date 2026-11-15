// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DAG walks that reproduce tree walks exactly (WP-F F0b/F0d): distinct-node
//! preorder walks, memoised subtree predicates, depth and size measures.

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{children, has_children};
use crate::expr::ChcExpr;

/// Whether some root-to-node path of `root` has at least `limit` edges,
/// computed on the DAG (each distinct node's height is computed once).
///
/// A tree walk that stops at depth `limit` truncates exactly when this is
/// true; callers use it to decide whether a DAG walk reproduces the tree
/// walk's result.
pub(crate) fn longest_path_at_least(root: &ChcExpr, limit: usize) -> bool {
    fn height(
        node: &ChcExpr,
        depth: usize,
        limit: usize,
        memo: &mut FxHashMap<*const ChcExpr, usize>,
    ) -> Option<usize> {
        // `None` = a path of length >= limit exists (abort).
        if depth >= limit {
            return None;
        }
        if !has_children(node) {
            return Some(0);
        }
        let key = node as *const ChcExpr;
        if let Some(h) = memo.get(&key) {
            return (depth + h < limit).then_some(*h);
        }
        let mut max_child = 0usize;
        let mut aborted = false;
        crate::expr::maybe_grow_expr_stack(|| {
            for child in children(node) {
                match height(child, depth + 1, limit, memo) {
                    Some(h) => max_child = max_child.max(h),
                    None => {
                        aborted = true;
                        break;
                    }
                }
            }
        });
        if aborted {
            return None;
        }
        let h = max_child + 1;
        if depth + h >= limit {
            return None;
        }
        memo.insert(key, h);
        Some(h)
    }
    let mut memo = FxHashMap::default();
    height(root, 0, limit, &mut memo).is_none()
}

/// What a [`walk_distinct_preorder`] visitor wants next.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Step {
    /// Visit this node's children.
    Descend,
    /// Do not visit this node's children.
    Skip,
    /// End the whole walk.
    Stop,
}

/// Node pops [`walk_distinct_preorder`] makes before it starts skipping
/// already-visited shared nodes (keeps small walks free of hashing).
const WALK_PLAIN_POPS: usize = 512;

/// Walk `root` in the preorder of a recursive tree walk, but visit a shared
/// inner node (same `Arc`) only on its FIRST occurrence. Returns `false` if the
/// visitor stopped the walk.
///
/// Exact replacement for a tree walk with no depth cut-off whose per-node
/// effect is idempotent and whose decision to descend depends only on the node
/// (set insertion, max, boolean or): the first occurrence already visited the
/// node's whole subtree, so a repeat would change nothing — and the first
/// occurrences come in the same order as in the tree walk (duplicates are
/// rejected when popped, not when pushed, so a node reached earlier through a
/// deeper path is still visited at that earlier point).
pub(crate) fn walk_distinct_preorder(
    root: &ChcExpr,
    mut visit: impl FnMut(&ChcExpr) -> Step,
) -> bool {
    let mut seen: ay_core::kani_compat::DetHashSet<*const ChcExpr> = Default::default();
    let mut plain_pops = WALK_PLAIN_POPS;
    let mut stack: Vec<&ChcExpr> = vec![root];
    while let Some(node) = stack.pop() {
        if has_children(node) {
            if plain_pops > 0 {
                plain_pops -= 1;
            } else if !seen.insert(node as *const ChcExpr) {
                continue;
            }
        }
        match visit(node) {
            Step::Stop => return false,
            Step::Skip => {}
            Step::Descend => {
                for child in children(node).iter().rev() {
                    stack.push(child);
                }
            }
        }
    }
    true
}

/// Whether every node of `root` satisfies the node-local check `ok` (children
/// are checked as nodes of their own). Exact replacement for a recursive
/// `ok(node) && children.all(..)` walk with no depth cut-off: a conjunction
/// over nodes does not depend on how often a shared node is reached.
pub(crate) fn all_distinct(root: &ChcExpr, mut ok: impl FnMut(&ChcExpr) -> bool) -> bool {
    walk_distinct_preorder(
        root,
        |node| if ok(node) { Step::Descend } else { Step::Stop },
    )
}

/// DAG form of a tree walk `walk(n, d) = d >= cap || hit(n) || (descend(n)
/// && any(walk(child, d + 1)))` that answers `true` when it reaches depth
/// `cap`. `None` means the input is small: run the tree walk.
///
/// Exact provided every inner node the walk does not descend into is a hit
/// (true of every caller): then a root-to-node path of `cap` edges forces
/// `true` — the walk either follows it to the cut-off or meets a hit on it —
/// and otherwise the answer is an OR over the distinct nodes it reaches.
pub(crate) fn any_node_or_deep(
    root: &ChcExpr,
    cap: usize,
    mut hit: impl FnMut(&ChcExpr) -> bool,
    descend: impl Fn(&ChcExpr) -> bool,
) -> Option<bool> {
    if !tree_size_at_least(root, DAG_WALK_MIN_TREE) {
        return None;
    }
    if longest_path_at_least(root, cap) {
        return Some(true);
    }
    let mut found = false;
    walk_distinct_preorder(root, |node| {
        if hit(node) {
            found = true;
            Step::Stop
        } else if descend(node) {
            Step::Descend
        } else {
            Step::Skip
        }
    });
    Some(found)
}

/// Whether `root` has at least `limit` nodes counted the way the memoised
/// `convert_expr` counts them: each distinct inner node once, each leaf once
/// per distinct parent edge. The DAG counterpart of a `node_count` guard that
/// protects the conversion budget (WP-F F0d).
pub(crate) fn dag_size_at_least(root: &ChcExpr, limit: usize) -> bool {
    let mut count = 0usize;
    let completed = walk_distinct_preorder(root, |_| {
        count += 1;
        if count >= limit {
            Step::Stop
        } else {
            Step::Descend
        }
    });
    !completed || count >= limit
}

/// `format!("{value:?}")` cut after `max_bytes` bytes, in time proportional to
/// `max_bytes`: the writer refuses further output, and the derived `Debug`
/// builders stop descending once a write failed. Verbose diagnostics use it so
/// a shared DAG is never printed as its (exponential) tree (WP-F F0d).
pub(crate) fn debug_prefix<T: std::fmt::Debug + ?Sized>(value: &T, max_bytes: usize) -> String {
    struct Capped {
        out: String,
        left: usize,
        truncated: bool,
    }
    impl std::fmt::Write for Capped {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            if s.len() <= self.left {
                self.out.push_str(s);
                self.left -= s.len();
                return Ok(());
            }
            let mut end = self.left;
            while !s.is_char_boundary(end) {
                end -= 1;
            }
            self.out.push_str(&s[..end]);
            self.left = 0;
            self.truncated = true;
            Err(std::fmt::Error)
        }
    }
    let mut w = Capped {
        out: String::new(),
        left: max_bytes,
        truncated: false,
    };
    let _ = std::fmt::write(&mut w, format_args!("{value:?}"));
    if w.truncated {
        w.out.push_str("…[truncated]");
    }
    w.out
}

/// Whether `a` is a shallow copy of `b`: the same variant with equal node
/// data and pointer-identical `Arc` children. Implies `a == b` structurally.
pub(crate) fn shallow_same(a: &ChcExpr, b: &ChcExpr) -> bool {
    let same_children = |x: &[Arc<ChcExpr>], y: &[Arc<ChcExpr>]| {
        x.len() == y.len() && x.iter().zip(y).all(|(p, q)| Arc::ptr_eq(p, q))
    };
    match (a, b) {
        (ChcExpr::Op(ao, aa), ChcExpr::Op(bo, ba)) => ao == bo && same_children(aa, ba),
        (ChcExpr::PredicateApp(an, ai, aa), ChcExpr::PredicateApp(bn, bi, ba)) => {
            ai == bi && an == bn && same_children(aa, ba)
        }
        (ChcExpr::FuncApp(an, asort, aa), ChcExpr::FuncApp(bn, bsort, ba)) => {
            an == bn && asort == bsort && same_children(aa, ba)
        }
        (ChcExpr::ConstArray(asort, av), ChcExpr::ConstArray(bsort, bv)) => {
            asort == bsort && Arc::ptr_eq(av, bv)
        }
        (a, b) if !has_children(a) && !has_children(b) => a == b,
        _ => false,
    }
}

/// [`SubtreeAny`] restricted to the nodes a walk descends through: `holds(n)`
/// is `pred(n) || (descend(n) && any child holds)`, memoised per distinct node.
pub(crate) struct SubtreeAnyVia<P: Fn(&ChcExpr) -> bool, D: Fn(&ChcExpr) -> bool> {
    pred: P,
    descend: D,
    memo: FxHashMap<*const ChcExpr, bool>,
}

impl<P: Fn(&ChcExpr) -> bool, D: Fn(&ChcExpr) -> bool> SubtreeAnyVia<P, D> {
    pub(crate) fn new(pred: P, descend: D) -> Self {
        Self {
            pred,
            descend,
            memo: FxHashMap::default(),
        }
    }

    /// Callers keep every queried node alive for the lifetime of `self`.
    pub(crate) fn holds(&mut self, node: &ChcExpr) -> bool {
        if (self.pred)(node) {
            return true;
        }
        if !(self.descend)(node) || !has_children(node) {
            return false;
        }
        let key = node as *const ChcExpr;
        if let Some(&known) = self.memo.get(&key) {
            return known;
        }
        let result =
            crate::expr::maybe_grow_expr_stack(|| children(node).iter().any(|c| self.holds(c)));
        self.memo.insert(key, result);
        result
    }
}

/// Tree nodes a walk must reach before it is worth switching to its DAG form
/// ([`prefer_dag_walk`]).
pub(crate) const DAG_WALK_MIN_TREE: usize = 4096;

/// Whether `root`'s tree expansion has at least `limit` nodes (bounded,
/// allocation-light count; stops as soon as `limit` is reached).
pub(crate) fn tree_size_at_least(root: &ChcExpr, limit: usize) -> bool {
    let mut count = 0usize;
    let mut stack: Vec<&ChcExpr> = vec![root];
    while let Some(node) = stack.pop() {
        count += 1;
        if count >= limit {
            return true;
        }
        stack.extend(children(node).iter().map(AsRef::as_ref));
    }
    false
}

/// Whether a depth-capped tree walk over `root` should run in its DAG form:
/// the tree is large ([`DAG_WALK_MIN_TREE`]) and no root-to-node path reaches
/// `depth_cap`, so the tree walk would never have truncated and the DAG form
/// computes exactly its result.
pub(crate) fn prefer_dag_walk(root: &ChcExpr, depth_cap: usize) -> bool {
    tree_size_at_least(root, DAG_WALK_MIN_TREE) && !longest_path_at_least(root, depth_cap)
}

/// Memoised "does this node's subtree contain a node satisfying `pred`" over
/// the distinct nodes of one borrowed root (no depth cut-off).
pub(crate) struct SubtreeAny<P: Fn(&ChcExpr) -> bool> {
    pred: P,
    memo: FxHashMap<*const ChcExpr, bool>,
}

impl<P: Fn(&ChcExpr) -> bool> SubtreeAny<P> {
    pub(crate) fn new(pred: P) -> Self {
        Self {
            pred,
            memo: FxHashMap::default(),
        }
    }

    /// Callers keep every queried node alive for the lifetime of `self`.
    pub(crate) fn holds(&mut self, node: &ChcExpr) -> bool {
        if (self.pred)(node) {
            return true;
        }
        if !has_children(node) {
            return false;
        }
        let key = node as *const ChcExpr;
        if let Some(&known) = self.memo.get(&key) {
            return known;
        }
        let result =
            crate::expr::maybe_grow_expr_stack(|| children(node).iter().any(|c| self.holds(c)));
        self.memo.insert(key, result);
        result
    }
}

/// Number of distinct nodes (by `Arc` identity; the root counts once) and the
/// saturating tree size of `root`. Tests and diagnostics only.
#[cfg(test)]
pub(crate) fn dag_and_tree_size(root: &ChcExpr) -> (usize, u128) {
    let mut memo = FxHashMap::default();
    let (tree, _) = tree_stats(root, &mut memo);
    (memo.len(), tree)
}

/// Saturating tree size and height (edges on the longest root-to-node path)
/// of `root`, computed per distinct node — the numbers a tree walk would
/// count, in time linear in the DAG.
pub(crate) fn tree_size_and_height(root: &ChcExpr) -> (u128, usize) {
    tree_stats(root, &mut FxHashMap::default())
}

/// Tree size (saturating) and height per distinct node, memoised by address
/// (every node stays alive: the root is borrowed for the whole walk).
fn tree_stats(
    node: &ChcExpr,
    memo: &mut FxHashMap<*const ChcExpr, (u128, usize)>,
) -> (u128, usize) {
    let key = node as *const ChcExpr;
    if let Some(&known) = memo.get(&key) {
        return known;
    }
    let mut size: u128 = 1;
    let mut height = 0usize;
    crate::expr::maybe_grow_expr_stack(|| {
        for child in children(node) {
            let (child_size, child_height) = tree_stats(child, memo);
            size = size.saturating_add(child_size);
            height = height.max(child_height + 1);
        }
    });
    memo.insert(key, (size, height));
    (size, height)
}
