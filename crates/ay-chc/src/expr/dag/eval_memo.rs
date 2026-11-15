// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-thread memo for model evaluation over shared DAGs (WP-F).
//!
//! The model evaluators (`expr::evaluate_expr`, `Mbp::eval_bool`,
//! `Mbp::eval_arith`, `Mbp::eval_generic`) recurse once per incoming edge, so
//! evaluating a shared transition relation costs its tree size (measured:
//! PDKIND's projection spent its whole run in `eval_bool` on `bist_cell`, and
//! the process died of `memout` on 11 of 20 front-end blow-up instances).
//!
//! Every evaluator call goes through [`memoised`]. Evaluations run inside a
//! SCOPE — an explicit [`EvalScope`] entered by an MBP entry point over the
//! roots it will evaluate, or, absent one, the outermost evaluator call on the
//! thread — that records one model. When a scope opens, and only then, its
//! roots are in hand: a bounded per-occurrence pre-walk ([`worth_indexing`],
//! at most [`PLAIN_VISITS`] node pops) decides whether the roots are both
//! large and shared, and if so every distinct inner node of their DAGs is
//! indexed with its height right there. Small expressions pay at most their
//! own size in extra pops; large unshared trees are evaluated plainly, as
//! before. Ordinary indexed nodes memoise by (node, evaluator) under the
//! scope's model. Lambda-bearing nodes additionally retain one exact entry
//! depth, since instantiation can reach the depth limit.
//!
//! ## Why the memo is exact
//! The evaluators are pure functions of (node, model) except for one thing:
//! `ExprDepthGuard` answers `None` past [`MAX_EXPR_RECURSION_DEPTH`] frames.
//! Ordinary nodes reuse values only when the current frame cannot reach that
//! limit (`current depth + FRAMES_PER_EDGE × height + slack < MAX`). Lambda
//! instantiation adds bound code plus capture/index depth, which this syntactic
//! height does not bound. Lambda-bearing nodes therefore key reuse by the exact
//! entry depth as well as node, evaluator and model. One active depth retains
//! the four evaluator values; a different depth clears all four. Both paths
//! return exactly what the plain walk returns, including a depth-limited miss.
//!
//! ## Why an address key is sound
//! Only nodes reachable from the scope's roots are indexed, and the index is
//! built from the roots' live borrows: an [`EvalScope<'a>`] holds those
//! borrows for its whole lifetime, and an outermost call's root is borrowed
//! for the whole call. The memo dies with the scope, so an indexed address
//! is never consulted after its node could have been freed. Any temporary
//! expression an evaluator builds on the fly is not in the index and is
//! evaluated plainly (its shared children still hit). No raw pointer is ever
//! dereferenced: addresses are keys, never read through.

use std::cell::{Cell, RefCell};
use std::marker::PhantomData;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::{children, has_children};
use crate::expr::{current_expr_depth, maybe_grow_expr_stack, ChcExpr, MAX_EXPR_RECURSION_DEPTH};
use crate::SmtValue;

/// Node pops of the pre-walk before an expression counts as large. Small
/// expressions (most evaluator calls) finish the pre-walk within it and stay
/// unindexed.
const PLAIN_VISITS: usize = 4096;

/// Pre-walk pops before it starts counting distinct nodes (keeps small walks
/// free of hashing); the sharing ratio is measured on the pops after it.
const PREWALK_HASH_AFTER: usize = 512;

/// Upper bound on distinct inner nodes the memo indexes (about 200 bytes
/// each); larger DAGs are evaluated plainly (the lane memory guard bounds a
/// blow-up there).
const MAX_MEMO_NODES: usize = 1 << 21;

/// `maybe_grow_expr_stack` frames one DAG edge may cost an evaluator. Every
/// evaluator takes one frame per node and `eval_generic` none; the bound is
/// twice that, so an off-by-one in this accounting can only make the memo
/// decline a node, never memoise a depth-truncated result.
const FRAMES_PER_EDGE: usize = 2;

/// Frames kept in reserve below the recursion limit.
const FRAME_SLACK: usize = 8;

/// Which evaluator a memoised value belongs to.
#[derive(Clone, Copy)]
pub(crate) enum EvalKind {
    Canonical = 0,
    MbpBool = 1,
    MbpArith = 2,
    MbpGeneric = 3,
}

/// A memoised evaluator result.
#[derive(Clone)]
pub(crate) enum EvalValue {
    Bool(Option<bool>),
    Int(Option<i128>),
    Value(Option<SmtValue>),
}

struct NodeSlot {
    /// Longest syntactic path through ordinary children, in edges.
    height: usize,
    /// Instantiation can add capture/index depth beyond the syntactic height.
    lambda_dependent: bool,
    /// One active depth only: changing it invalidates all evaluator kinds.
    memo_depth: Option<usize>,
    /// One slot per [`EvalKind`].
    values: [Option<EvalValue>; 4],
}

/// Distinct inner nodes of the scope's roots -> height and memoised values.
type Memo = FxHashMap<usize, NodeSlot>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scope {
    /// No scope: the next evaluator call at nesting 0 opens a `Call` scope.
    None,
    /// Opened by the outermost evaluator call over its argument.
    Call,
    /// Opened by [`EvalScope::enter`] over the roots it was given.
    Explicit,
}

thread_local! {
    static NESTING: Cell<usize> = const { Cell::new(0) };
    static SCOPE: Cell<Scope> = const { Cell::new(Scope::None) };
    static MODEL: Cell<usize> = const { Cell::new(0) };
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static MEMO: RefCell<Option<Memo>> = const { RefCell::new(None) };
    #[cfg(test)]
    static DISABLED: Cell<bool> = const { Cell::new(false) };
}

fn model_key(model: &FxHashMap<String, SmtValue>) -> usize {
    model as *const FxHashMap<String, SmtValue> as usize
}

fn address(node: &ChcExpr) -> usize {
    node as *const ChcExpr as usize
}

/// Open a scope of `kind` over `roots` under `model`, indexing the roots'
/// DAGs when they are worth it. `roots` are live borrows: this is the only
/// place the index is built.
fn open_scope(kind: Scope, model: &FxHashMap<String, SmtValue>, roots: &[&ChcExpr]) {
    SCOPE.with(|s| s.set(kind));
    MODEL.with(|m| m.set(model_key(model)));
    ACTIVE.with(|a| a.set(false));
    if worth_indexing(roots) {
        if let Some(memo) = index(roots) {
            MEMO.with(|m| *m.borrow_mut() = Some(memo));
            ACTIVE.with(|a| a.set(true));
        }
    }
}

fn close_scope() {
    SCOPE.with(|s| s.set(Scope::None));
    ACTIVE.with(|a| a.set(false));
    MEMO.with(|m| m.borrow_mut().take());
}

/// Whether `roots` are both large (more than [`PLAIN_VISITS`] tree nodes)
/// and shared (fewer than half as many distinct inner nodes as pops among
/// the pops after [`PREWALK_HASH_AFTER`]). A per-occurrence walk bounded by
/// `PLAIN_VISITS` pops; its pending stack is capped at the same bound, which
/// cannot change the "large" verdict (a full stack already holds that many
/// unvisited tree nodes).
fn worth_indexing(roots: &[&ChcExpr]) -> bool {
    let mut stack: Vec<&ChcExpr> = roots
        .iter()
        .copied()
        .filter(|root| has_children(root))
        .take(PLAIN_VISITS)
        .collect();
    let mut pops = 0usize;
    let mut distinct: FxHashSet<usize> = FxHashSet::default();
    while let Some(node) = stack.pop() {
        pops += 1;
        if pops > PLAIN_VISITS {
            return distinct.len() * 2 <= PLAIN_VISITS - PREWALK_HASH_AFTER;
        }
        if pops > PREWALK_HASH_AFTER {
            distinct.insert(address(node));
        }
        for child in children(node) {
            if has_children(child) && stack.len() < PLAIN_VISITS {
                stack.push(child);
            }
        }
    }
    false
}

/// Index every distinct inner node reachable from `roots` with its height —
/// unless a root's DAG is deeper than the recursion limit or larger than
/// [`MAX_MEMO_NODES`], in which case evaluation stays plain.
fn index(roots: &[&ChcExpr]) -> Option<Memo> {
    let mut memo = Memo::default();
    for root in roots {
        height(root, MAX_EXPR_RECURSION_DEPTH, &mut memo)?;
    }
    Some(memo)
}

/// Height of `node` (edges to its farthest leaf), indexing every distinct
/// inner node below it. `None` when some path has at least `remaining` edges
/// or the index would exceed [`MAX_MEMO_NODES`].
fn height(node: &ChcExpr, remaining: usize, memo: &mut Memo) -> Option<usize> {
    if !has_children(node) {
        return Some(0);
    }
    if remaining == 0 {
        return None;
    }
    let key = address(node);
    if let Some(slot) = memo.get(&key) {
        return (slot.height < remaining).then_some(slot.height);
    }
    if memo.len() >= MAX_MEMO_NODES {
        return None;
    }
    let mut max_child = 0usize;
    let mut aborted = false;
    maybe_grow_expr_stack(|| {
        for child in children(node) {
            match height(child, remaining - 1, memo) {
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
    if h >= remaining {
        return None;
    }
    let lambda_dependent = matches!(node, ChcExpr::ArrayLambda(_))
        || children(node).iter().any(|child| {
            memo.get(&address(child))
                .is_some_and(|slot| slot.lambda_dependent)
        });
    memo.insert(
        key,
        NodeSlot {
            height: h,
            lambda_dependent,
            memo_depth: None,
            values: Default::default(),
        },
    );
    Some(h)
}

/// One memo scope over `roots` under one model, for every evaluator call made
/// while it is alive on this thread (MBP's implicant extraction and MBQI term
/// search evaluate thousands of nodes of one formula under one model).
///
/// A scope requested while another is open, or from inside an evaluator, is a
/// no-op: the open scope keeps serving (its index may not cover the new
/// roots; those nodes are then evaluated plainly, which is still exact).
pub(crate) struct EvalScope<'a> {
    owns: bool,
    _roots: PhantomData<&'a ChcExpr>,
}

impl<'a> EvalScope<'a> {
    /// Enter a scope over `roots`, indexing their DAGs now if they are worth
    /// it. The roots and the model are borrowed for the scope's lifetime,
    /// which is what keeps every indexed node alive.
    pub(crate) fn enter(
        roots: impl IntoIterator<Item = &'a ChcExpr>,
        model: &'a FxHashMap<String, SmtValue>,
    ) -> Self {
        let free = NESTING.with(Cell::get) == 0 && SCOPE.with(Cell::get) == Scope::None;
        if !free {
            return Self {
                owns: false,
                _roots: PhantomData,
            };
        }
        let roots: Vec<&ChcExpr> = roots.into_iter().collect();
        open_scope(Scope::Explicit, model, &roots);
        Self {
            owns: true,
            _roots: PhantomData,
        }
    }
}

impl Drop for EvalScope<'_> {
    fn drop(&mut self) {
        if self.owns {
            close_scope();
        }
    }
}

/// Bracket for one evaluator call: the outermost call on a thread without a
/// scope opens a `Call` scope over its argument (indexed now, while the
/// argument is borrowed) and closes it when it returns.
struct EvalCall {
    owns_scope: bool,
}

impl EvalCall {
    fn enter(node: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Self {
        let nesting = NESTING.with(|n| {
            let depth = n.get();
            n.set(depth + 1);
            depth
        });
        if nesting == 0 && SCOPE.with(Cell::get) == Scope::None {
            open_scope(Scope::Call, model, &[node]);
            return Self { owns_scope: true };
        }
        Self { owns_scope: false }
    }
}

impl Drop for EvalCall {
    fn drop(&mut self) {
        NESTING.with(|n| n.set(n.get().saturating_sub(1)));
        if self.owns_scope {
            close_scope();
        }
    }
}

/// Height of an indexed node, if the memo is active and covers it.
fn indexed_profile(key: usize) -> Option<(usize, bool)> {
    MEMO.with(|m| {
        m.borrow()
            .as_ref()?
            .get(&key)
            .map(|slot| (slot.height, slot.lambda_dependent))
    })
}

fn lookup(key: usize, kind: EvalKind) -> Option<EvalValue> {
    MEMO.with(|m| m.borrow().as_ref()?.get(&key)?.values[kind as usize].clone())
}

fn store(key: usize, kind: EvalKind, value: EvalValue) {
    MEMO.with(|m| {
        if let Some(slot) = m.borrow_mut().as_mut().and_then(|memo| memo.get_mut(&key)) {
            slot.values[kind as usize] = Some(value);
        }
    });
}

/// Lambda-bearing nodes have a pure result at one exact entry depth, even
/// when instantiating their closed code reaches the existing depth refusal.
/// One active depth bounds memory while allowing repeated same-depth reads.
fn lookup_at_depth(key: usize, kind: EvalKind, depth: usize) -> Option<EvalValue> {
    MEMO.with(|m| {
        let borrowed = m.borrow();
        let slot = borrowed.as_ref()?.get(&key)?;
        (slot.memo_depth == Some(depth))
            .then(|| slot.values[kind as usize].clone())
            .flatten()
    })
}

fn store_at_depth(key: usize, kind: EvalKind, depth: usize, value: EvalValue) {
    MEMO.with(|m| {
        if let Some(slot) = m.borrow_mut().as_mut().and_then(|memo| memo.get_mut(&key)) {
            if slot.memo_depth != Some(depth) {
                slot.values = Default::default();
                slot.memo_depth = Some(depth);
            }
            slot.values[kind as usize] = Some(value);
        }
    });
}

/// Run evaluator `eval` for `node` under `model` through the memo: a hit
/// returns the stored value and a miss evaluates. Ordinary nodes are stored
/// only when their static height excludes a depth refusal. Lambda-bearing
/// nodes store at the exact entry depth, including a possible refusal; changing
/// that depth clears all evaluator slots. `wrap`/`unwrap` move values through
/// [`EvalValue`]. Leaves are evaluated directly.
#[inline]
pub(crate) fn memoised<T: Clone>(
    node: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    kind: EvalKind,
    wrap: fn(T) -> EvalValue,
    unwrap: fn(EvalValue) -> Option<T>,
    eval: impl FnOnce() -> T,
) -> T {
    if !has_children(node) {
        return eval();
    }
    #[cfg(test)]
    if DISABLED.with(Cell::get) {
        return eval();
    }
    let _call = EvalCall::enter(node, model);
    if !ACTIVE.with(Cell::get) || MODEL.with(Cell::get) != model_key(model) {
        return eval();
    }
    let key = address(node);
    let Some((height, lambda_dependent)) = indexed_profile(key) else {
        return eval();
    };
    if lambda_dependent {
        let depth = current_expr_depth();
        if let Some(value) = lookup_at_depth(key, kind, depth).and_then(unwrap) {
            return value;
        }
        let value = eval();
        store_at_depth(key, kind, depth, wrap(value.clone()));
        return value;
    }
    if current_expr_depth() + FRAMES_PER_EDGE * height + FRAME_SLACK >= MAX_EXPR_RECURSION_DEPTH {
        return eval();
    }
    if let Some(value) = lookup(key, kind).and_then(unwrap) {
        return value;
    }
    let value = eval();
    store(key, kind, wrap(value.clone()));
    value
}

/// Run `f` with every evaluator on this thread evaluating plainly (the
/// reference for the differential tests).
#[cfg(test)]
pub(crate) fn with_memo_disabled<R>(f: impl FnOnce() -> R) -> R {
    let previous = DISABLED.with(|d| d.replace(true));
    let result = f();
    DISABLED.with(|d| d.set(previous));
    result
}

/// Whether a memo is active on this thread right now (tests).
#[cfg(test)]
pub(crate) fn memo_active() -> bool {
    ACTIVE.with(Cell::get)
}

/// Wrappers for the three result shapes.
pub(crate) fn wrap_bool(v: Option<bool>) -> EvalValue {
    EvalValue::Bool(v)
}
pub(crate) fn unwrap_bool(v: EvalValue) -> Option<Option<bool>> {
    match v {
        EvalValue::Bool(b) => Some(b),
        _ => None,
    }
}
pub(crate) fn wrap_int(v: Option<i128>) -> EvalValue {
    EvalValue::Int(v)
}
pub(crate) fn unwrap_int(v: EvalValue) -> Option<Option<i128>> {
    match v {
        EvalValue::Int(n) => Some(n),
        _ => None,
    }
}
pub(crate) fn wrap_value(v: Option<SmtValue>) -> EvalValue {
    EvalValue::Value(v)
}
pub(crate) fn unwrap_value(v: EvalValue) -> Option<Option<SmtValue>> {
    match v {
        EvalValue::Value(x) => Some(x),
        _ => None,
    }
}

#[cfg(test)]
#[path = "eval_memo_tests.rs"]
mod tests;
