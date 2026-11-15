// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural `PartialEq`/`Eq` and `Hash` for [`ChcExpr`] (WP-F F0a).
//!
//! Children are shared `Arc`s, so an expression is a DAG whose tree expansion
//! can be exponentially larger; both impls stay linear in the distinct nodes
//! while returning exactly the structural answer (and, for expressions of at
//! most [`HASH_EXACT_CHILD_VISITS`] descendants, exactly the former derived
//! hash).

use std::hash::{Hash, Hasher};
use std::sync::Arc;

use super::ChcExpr;

/// Child visits that `==` makes as a plain recursive walk before it starts
/// memoising proven-equal `(left, right)` node pairs. Below this the walk is
/// exactly the old one; above it every distinct pair is compared once, which
/// makes comparing two pointer-distinct copies of a shared DAG linear in the
/// DAG instead of the tree.
const EQ_PLAIN_CHILD_VISITS: usize = 4096;

/// Child nodes that `Hash` streams exactly as the former `#[derive(Hash)]`
/// did before it writes the remaining children as one 64-bit structural
/// digest each ([`super::dag::structural_digest`]).
///
/// Every expression with at most this many descendants therefore hashes to
/// the SAME value as under the derive (so hash-map iteration orders of
/// ordinary queries are unchanged); a larger one costs O(budget + distinct
/// nodes) instead of O(tree). Consistency with `==` is unaffected: the stream
/// is a deterministic function of structure (the preorder position where the
/// budget runs out is itself structural).
pub(crate) const HASH_EXACT_CHILD_VISITS: usize = 4096;

impl PartialEq for ChcExpr {
    /// Structural equality with an `Arc::ptr_eq` fast path on children
    /// (#9077, fast-core P1) and a pair memo for shared DAGs (WP-F F0a).
    ///
    /// Returns *exactly* structural equality: for every child pair `(x, y)`
    /// it evaluates `Arc::ptr_eq(x, y) || x == y` (`ptr_eq ⟹ same allocation
    /// ⟹ structurally equal`), and once [`EQ_PLAIN_CHILD_VISITS`] child
    /// comparisons have been made it also skips a pair already PROVEN equal in
    /// this call. A pair is only recorded after its comparison returned `true`,
    /// and every node stays alive for the whole call (both roots are
    /// borrowed), so a recorded address pair always denotes the same two nodes.
    ///
    /// NOTE: `Real(n, d)` compares structurally (numerator AND denominator),
    /// identical to the derive — `1/2` and `2/4` are NOT equal here.
    fn eq(&self, other: &Self) -> bool {
        if std::ptr::eq(self, other) {
            return true;
        }
        let mut cx = EqCx {
            plain_visits_left: EQ_PLAIN_CHILD_VISITS,
            proven: None,
        };
        eq_node(self, other, &mut cx)
    }
}

impl Eq for ChcExpr {}

struct EqCx {
    plain_visits_left: usize,
    proven: Option<ay_core::kani_compat::DetHashSet<(usize, usize)>>,
}

fn eq_node(a: &ChcExpr, b: &ChcExpr, cx: &mut EqCx) -> bool {
    match (a, b) {
        (ChcExpr::Bool(a), ChcExpr::Bool(b)) => a == b,
        (ChcExpr::Int(a), ChcExpr::Int(b)) => a == b,
        (ChcExpr::Real(an, ad), ChcExpr::Real(bn, bd)) => an == bn && ad == bd,
        (ChcExpr::BitVec(av, aw), ChcExpr::BitVec(bv, bw)) => av == bv && aw == bw,
        (ChcExpr::Var(a), ChcExpr::Var(b)) => a == b,
        (ChcExpr::Op(ao, aa), ChcExpr::Op(bo, ba)) => ao == bo && children_eq(aa, ba, cx),
        (ChcExpr::PredicateApp(an, ai, aa), ChcExpr::PredicateApp(bn, bi, ba)) => {
            ai == bi && an == bn && children_eq(aa, ba, cx)
        }
        (ChcExpr::FuncApp(an, asort, aa), ChcExpr::FuncApp(bn, bsort, ba)) => {
            an == bn && asort == bsort && children_eq(aa, ba, cx)
        }
        (ChcExpr::ConstArrayMarker(a), ChcExpr::ConstArrayMarker(b)) => a == b,
        (ChcExpr::IsTesterMarker(a), ChcExpr::IsTesterMarker(b)) => a == b,
        (ChcExpr::ConstArray(asort, av), ChcExpr::ConstArray(bsort, bv)) => {
            asort == bsort && child_eq(av, bv, cx)
        }
        (ChcExpr::ArrayLambda(a), ChcExpr::ArrayLambda(b)) => {
            a.binder() == b.binder()
                && a.formals() == b.formals()
                && a.sort() == b.sort()
                && child_eq(a.body(), b.body(), cx)
                && children_eq(a.captures(), b.captures(), cx)
        }
        _ => false,
    }
}

/// Compare child slices with a per-element `Arc::ptr_eq` short-circuit before
/// the structural recursion. Same result as `aa == ba` on the slices.
#[inline]
fn children_eq(aa: &[Arc<ChcExpr>], ba: &[Arc<ChcExpr>], cx: &mut EqCx) -> bool {
    aa.len() == ba.len() && aa.iter().zip(ba.iter()).all(|(x, y)| child_eq(x, y, cx))
}

#[inline]
fn child_eq(x: &Arc<ChcExpr>, y: &Arc<ChcExpr>, cx: &mut EqCx) -> bool {
    if Arc::ptr_eq(x, y) {
        return true;
    }
    if cx.plain_visits_left > 0 {
        cx.plain_visits_left -= 1;
        return eq_node(x, y, cx);
    }
    let key = (Arc::as_ptr(x) as usize, Arc::as_ptr(y) as usize);
    if cx
        .proven
        .as_ref()
        .is_some_and(|proven| proven.contains(&key))
    {
        return true;
    }
    let equal = super::maybe_grow_expr_stack(|| eq_node(x, y, cx));
    if equal {
        cx.proven.get_or_insert_with(Default::default).insert(key);
    }
    equal
}

impl Hash for ChcExpr {
    /// Structural hash (WP-F F0a). For expressions with at most
    /// [`HASH_EXACT_CHILD_VISITS`] descendants this writes exactly the byte
    /// stream the former `#[derive(Hash)]` wrote (discriminant, fields, and for
    /// each child vector its length followed by each child). Past that budget
    /// each remaining child is written as its structural digest, so hashing a
    /// shared DAG is linear in its distinct nodes.
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut exact_visits_left = HASH_EXACT_CHILD_VISITS;
        hash_node(self, state, &mut exact_visits_left);
    }
}

fn hash_node<H: Hasher>(node: &ChcExpr, state: &mut H, exact_visits_left: &mut usize) {
    std::mem::discriminant(node).hash(state);
    match node {
        ChcExpr::Bool(b) => b.hash(state),
        ChcExpr::Int(n) => n.hash(state),
        ChcExpr::Real(n, d) => {
            n.hash(state);
            d.hash(state);
        }
        ChcExpr::BitVec(v, w) => {
            v.hash(state);
            w.hash(state);
        }
        ChcExpr::Var(v) => v.hash(state),
        ChcExpr::Op(op, args) => {
            op.hash(state);
            hash_children(args, state, exact_visits_left);
        }
        ChcExpr::PredicateApp(name, id, args) => {
            name.hash(state);
            id.hash(state);
            hash_children(args, state, exact_visits_left);
        }
        ChcExpr::FuncApp(name, sort, args) => {
            name.hash(state);
            sort.hash(state);
            hash_children(args, state, exact_visits_left);
        }
        ChcExpr::ArrayLambda(lambda) => {
            lambda.binder().hash(state);
            lambda.formals().hash(state);
            lambda.sort().hash(state);
            hash_child(lambda.body(), state, exact_visits_left);
            hash_children(lambda.captures(), state, exact_visits_left);
        }
        ChcExpr::ConstArrayMarker(sort) => sort.hash(state),
        ChcExpr::IsTesterMarker(name) => name.hash(state),
        ChcExpr::ConstArray(sort, value) => {
            sort.hash(state);
            hash_child(value, state, exact_visits_left);
        }
    }
}

/// `Vec<Arc<ChcExpr>>`'s derived hash: the length prefix (`write_usize`, the
/// default `write_length_prefix`), then each element.
#[inline]
fn hash_children<H: Hasher>(args: &[Arc<ChcExpr>], state: &mut H, exact_visits_left: &mut usize) {
    state.write_usize(args.len());
    for arg in args {
        hash_child(arg, state, exact_visits_left);
    }
}

#[inline]
fn hash_child<H: Hasher>(child: &Arc<ChcExpr>, state: &mut H, exact_visits_left: &mut usize) {
    if *exact_visits_left > 0 {
        *exact_visits_left -= 1;
        hash_node(child, state, exact_visits_left);
    } else {
        state.write_u64(super::dag::structural_digest(child));
    }
}
