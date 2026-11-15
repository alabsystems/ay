// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared reference walks and generators for the WP-F DAG tests: verbatim
//! copies of the pre-F0 tree walks (`reference_*`), a field-for-field mirror of
//! the former derived `Hash`, and random / exponentially shared DAG builders.

use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use ay_core::kani_compat::DetHashSet;

use super::*;
use crate::expr::{ChcOp, ChcSort, ChcVar, ExprFeatures, MAX_EXPR_RECURSION_DEPTH};
use crate::PredicateId;

// ---------------------------------------------------------------------------
// Reference implementations (the pre-F0 tree walks, verbatim in behaviour)
// ---------------------------------------------------------------------------

/// Field-for-field mirror of `ChcExpr` with the DERIVED `Hash` the type had
/// before F0a. Hashing a mirror reproduces the old byte stream exactly.
#[derive(Hash)]
pub(super) enum MirrorExpr {
    Bool(bool),
    Int(i128),
    Real(i64, i64),
    BitVec(u128, u32),
    Var(ChcVar),
    Op(ChcOp, Vec<Arc<Self>>),
    PredicateApp(String, PredicateId, Vec<Arc<Self>>),
    FuncApp(String, ChcSort, Vec<Arc<Self>>),
    ConstArrayMarker(ChcSort),
    IsTesterMarker(String),
    ConstArray(ChcSort, Arc<Self>),
    ArrayLambda(ChcVar, Vec<ChcVar>, ChcSort, Arc<Self>, Vec<Arc<Self>>),
}

pub(super) fn mirror(expr: &ChcExpr) -> MirrorExpr {
    let kids = |args: &[Arc<ChcExpr>]| args.iter().map(|a| Arc::new(mirror(a))).collect();
    match expr {
        ChcExpr::ArrayLambda(lambda) => MirrorExpr::ArrayLambda(
            lambda.binder().clone(),
            lambda.formals().to_vec(),
            lambda.sort(),
            Arc::new(mirror(lambda.body())),
            kids(lambda.captures()),
        ),
        ChcExpr::Bool(b) => MirrorExpr::Bool(*b),
        ChcExpr::Int(n) => MirrorExpr::Int(*n),
        ChcExpr::Real(n, d) => MirrorExpr::Real(*n, *d),
        ChcExpr::BitVec(v, w) => MirrorExpr::BitVec(*v, *w),
        ChcExpr::Var(v) => MirrorExpr::Var(v.clone()),
        ChcExpr::Op(op, args) => MirrorExpr::Op(*op, kids(args)),
        ChcExpr::PredicateApp(n, id, args) => MirrorExpr::PredicateApp(n.clone(), *id, kids(args)),
        ChcExpr::FuncApp(n, s, args) => MirrorExpr::FuncApp(n.clone(), s.clone(), kids(args)),
        ChcExpr::ConstArrayMarker(s) => MirrorExpr::ConstArrayMarker(s.clone()),
        ChcExpr::IsTesterMarker(n) => MirrorExpr::IsTesterMarker(n.clone()),
        ChcExpr::ConstArray(s, v) => MirrorExpr::ConstArray(s.clone(), Arc::new(mirror(v))),
    }
}

/// Records the exact byte stream a `Hash` impl writes.
#[derive(Default)]
pub(super) struct Recorder(pub(super) Vec<u8>);

impl Hasher for Recorder {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }
}

pub(super) fn hash_with<T: Hash + ?Sized, H: Hasher>(value: &T, mut h: H) -> u64 {
    value.hash(&mut h);
    h.finish()
}

pub(super) fn reference_vars(expr: &ChcExpr) -> Vec<ChcVar> {
    fn go(e: &ChcExpr, seen: &mut DetHashSet<ChcVar>, out: &mut Vec<ChcVar>, depth: usize) {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return;
        }
        match e {
            ChcExpr::Var(v) => {
                if seen.insert(v.clone()) {
                    out.push(v.clone());
                }
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    go(a, seen, out, depth + 1);
                }
            }
            ChcExpr::ConstArray(_, v) => go(v, seen, out, depth + 1),
            ChcExpr::ArrayLambda(lambda) => {
                for value in lambda.captures() {
                    go(value, seen, out, depth + 1);
                }
            }
            _ => {}
        }
    }
    let mut seen = DetHashSet::default();
    let mut out = Vec::new();
    go(expr, &mut seen, &mut out, 0);
    out
}

pub(super) fn features_tuple(f: &ExprFeatures) -> [bool; 9] {
    [
        f.has_array_ops,
        f.has_bv,
        f.has_uf_apps,
        f.has_dt,
        f.has_mixed_sort_eq,
        f.has_ite,
        f.has_mod_or_div,
        f.has_negation,
        f.has_strict_int_comparison,
    ]
}

/// The pre-F0 `scan_features` tree walk (flags only; the production call
/// then applies the same closure, so it is applied here too).
pub(super) fn reference_scan(expr: &ChcExpr) -> [bool; 9] {
    fn inner(e: &ChcExpr, f: &mut ExprFeatures, depth: usize) {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            f.has_array_ops = true;
            f.has_bv = true;
            f.has_uf_apps = true;
            f.has_dt = true;
            f.has_mixed_sort_eq = true;
            f.has_ite = true;
            f.has_mod_or_div = true;
            f.has_negation = true;
            f.has_strict_int_comparison = true;
            return;
        }
        if features_tuple(f).iter().all(|b| *b) {
            return;
        }
        match e {
            ChcExpr::Var(v) => {
                if matches!(v.sort, ChcSort::Array(_, _)) {
                    f.has_array_ops = true;
                }
                if matches!(v.sort, ChcSort::BitVec(_)) {
                    f.has_bv = true;
                }
            }
            ChcExpr::BitVec(..) => f.has_bv = true,
            ChcExpr::Op(op, args) => {
                match op {
                    ChcOp::Ite => {
                        f.has_ite = true;
                        if args.len() == 3 {
                            let t = args[1].sort();
                            let el = args[2].sort();
                            if t == el && matches!(t, ChcSort::Int | ChcSort::Real) {
                                f.has_negation = true;
                            }
                        }
                    }
                    ChcOp::Mod | ChcOp::Div => f.has_mod_or_div = true,
                    ChcOp::Not => f.has_negation = true,
                    ChcOp::Lt | ChcOp::Gt => f.has_strict_int_comparison = true,
                    ChcOp::Eq if args.len() == 2 => {
                        let s0 = args[0].sort();
                        let s1 = args[1].sort();
                        if (s0 == ChcSort::Bool) != (s1 == ChcSort::Bool)
                            && (matches!(s0, ChcSort::Int | ChcSort::Real)
                                || matches!(s1, ChcSort::Int | ChcSort::Real))
                        {
                            f.has_mixed_sort_eq = true;
                        }
                    }
                    _ => {}
                }
                for a in args {
                    inner(a, f, depth + 1);
                }
            }
            _ => {}
        }
    }
    let mut f = ExprFeatures::default();
    inner(expr, &mut f, 0);
    // close_under_preprocessing, as in production
    if f.has_mixed_sort_eq {
        f.has_ite = true;
        f.has_negation = true;
    }
    if f.has_mod_or_div || f.has_negation {
        f.has_strict_int_comparison = true;
    }
    features_tuple(&f)
}

/// The pre-F0 `and_all` / `or_all` (owned clones, fresh `Arc` per element).
pub(super) fn reference_connective(op: ChcOp, parts: Vec<ChcExpr>) -> ChcExpr {
    let (unit, zero) = if op == ChcOp::And {
        (true, false)
    } else {
        (false, true)
    };
    let mut out: Vec<Arc<ChcExpr>> = Vec::new();
    let mut seen: Vec<ChcExpr> = Vec::new();
    let mut pending: VecDeque<ChcExpr> = parts.into_iter().collect();
    while let Some(expr) = pending.pop_front() {
        match expr {
            ChcExpr::Bool(b) if b == unit => {}
            ChcExpr::Bool(b) if b == zero => return ChcExpr::Bool(zero),
            ChcExpr::Op(o, ref args) if o == op => {
                for arg in args.iter().rev() {
                    pending.push_front(arg.as_ref().clone());
                }
            }
            other => {
                if !seen.iter().any(|s| reference_eq(s, &other)) {
                    seen.push(other.clone());
                    out.push(Arc::new(other));
                }
            }
        }
    }
    match out.len() {
        0 => ChcExpr::Bool(unit),
        1 => (*out.pop().unwrap()).clone(),
        _ => ChcExpr::Op(op, out),
    }
}

/// Plain structural equality (no pointer shortcuts, no memo).
pub(super) fn reference_eq(a: &ChcExpr, b: &ChcExpr) -> bool {
    match (a, b) {
        (ChcExpr::Op(ao, aa), ChcExpr::Op(bo, ba)) => {
            ao == bo && aa.len() == ba.len() && aa.iter().zip(ba).all(|(x, y)| reference_eq(x, y))
        }
        (ChcExpr::Op(..), _) | (_, ChcExpr::Op(..)) => false,
        _ => mirror_bytes(a) == mirror_bytes(b),
    }
}

pub(super) fn mirror_bytes(e: &ChcExpr) -> Vec<u8> {
    let mut r = Recorder::default();
    mirror(e).hash(&mut r);
    r.0
}

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

pub(crate) struct Rng(pub(crate) u64);

impl Rng {
    pub(crate) fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    pub(crate) fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

pub(crate) fn leaf(rng: &mut Rng) -> ChcExpr {
    match rng.below(6) {
        0 => ChcExpr::Int(rng.below(5) as i128 - 2),
        1 => ChcExpr::Real(rng.below(3) as i64, 1 + rng.below(2) as i64),
        2 => ChcExpr::Bool(rng.below(2) == 0),
        3 => ChcExpr::var(ChcVar::new(format!("b{}", rng.below(4)), ChcSort::Bool)),
        4 => ChcExpr::var(ChcVar::new(format!("r{}", rng.below(6)), ChcSort::Real)),
        _ => ChcExpr::var(ChcVar::new(format!("i{}", rng.below(6)), ChcSort::Int)),
    }
}

/// A random DAG of `n` inner nodes; each node draws children from the pool
/// of earlier nodes, so sharing (and tree blow-up) is common. A child is only
/// drawn from the pool while the new node's tree size stays within
/// `tree_cap`, so reference tree walks remain feasible when needed.
pub(crate) fn random_dag(seed: u64, n: usize, tree_cap: u128) -> ChcExpr {
    let mut rng = Rng(seed | 1);
    let mut pool: Vec<(Arc<ChcExpr>, u128)> =
        (0..8).map(|_| (Arc::new(leaf(&mut rng)), 1)).collect();
    let ops = [
        ChcOp::Add,
        ChcOp::Ite,
        ChcOp::Eq,
        ChcOp::Le,
        ChcOp::Lt,
        ChcOp::And,
        ChcOp::Or,
        ChcOp::Not,
        ChcOp::Mul,
    ];
    for _ in 0..n {
        let op = ops[rng.below(ops.len())];
        let arity = match op {
            ChcOp::Not => 1,
            ChcOp::Ite => 3,
            ChcOp::And | ChcOp::Or | ChcOp::Add => 2 + rng.below(3),
            _ => 2,
        };
        let mut size: u128 = 1;
        let mut args: Vec<Arc<ChcExpr>> = Vec::with_capacity(arity);
        for slot in 0..arity {
            // favour recent nodes: deeper, more shared
            let lo = pool.len().saturating_sub(6);
            let (cand, cand_size) = pool[lo + rng.below(pool.len() - lo)].clone();
            // Keep one node of room for every slot still to fill (each takes at
            // least a leaf), so the finished node never exceeds `tree_cap`.
            let reserve = (arity - slot - 1) as u128;
            if rng.below(5) != 0
                && size.saturating_add(cand_size).saturating_add(reserve) <= tree_cap
            {
                size = size.saturating_add(cand_size);
                args.push(cand);
            } else {
                size += 1;
                args.push(Arc::new(leaf(&mut rng)));
            }
        }
        pool.push((Arc::new(ChcExpr::Op(op, args)), size));
    }
    pool.last().unwrap().0.as_ref().clone()
}

/// `x_{k+1} = ite(c_k, x_k + 1, x_k)` — every level references the previous
/// one twice, so the tree has ~2^k nodes while the DAG has ~4k.
pub(crate) fn ite_chain(k: usize, tag: &str) -> Arc<ChcExpr> {
    let mut x = Arc::new(ChcExpr::var(ChcVar::new(format!("{tag}x0"), ChcSort::Real)));
    for i in 0..k {
        let c = Arc::new(ChcExpr::var(ChcVar::new(
            format!("{tag}c{i}"),
            ChcSort::Bool,
        )));
        let plus = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&x), Arc::new(ChcExpr::Real(1, 1))],
        ));
        x = Arc::new(ChcExpr::Op(ChcOp::Ite, vec![c, plus, x]));
    }
    x
}

pub(super) fn tree_size(e: &ChcExpr) -> u128 {
    dag_and_tree_size(e).1
}
