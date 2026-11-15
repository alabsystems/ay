// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Substitution and constant folding for [`super::solve_eqs`]: exact
//! rational arithmetic, Boolean structure and `ite`s, over a DAG memoised on
//! node identity.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use super::MAX_VISITS;
use crate::expr::{maybe_grow_expr_stack, MAX_EXPR_RECURSION_DEPTH};
use crate::{ChcExpr, ChcOp, ChcVar};

/// A numeric constant.
#[derive(Clone, Debug, PartialEq)]
enum Num {
    Int(i128),
    Real(BigRational),
}

fn num_of(e: &ChcExpr) -> Option<Num> {
    match e {
        ChcExpr::Int(n) => Some(Num::Int(*n)),
        ChcExpr::Real(n, d) if *d != 0 => Some(Num::Real(BigRational::new(
            BigInt::from(*n),
            BigInt::from(*d),
        ))),
        _ => None,
    }
}

fn num_expr(n: &Num) -> Option<ChcExpr> {
    match n {
        Num::Int(i) => Some(ChcExpr::Int(*i)),
        Num::Real(r) => {
            let num = r.numer().to_i64()?;
            let den = r.denom().to_i64()?;
            Some(ChcExpr::Real(num, den))
        }
    }
}

/// Compare two constants of the same kind.
fn num_cmp(a: &Num, b: &Num) -> Option<std::cmp::Ordering> {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => Some(x.cmp(y)),
        (Num::Real(x), Num::Real(y)) => Some(x.cmp(y)),
        _ => None,
    }
}

fn num_add(a: &Num, b: &Num) -> Option<Num> {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => x.checked_add(*y).map(Num::Int),
        (Num::Real(x), Num::Real(y)) => Some(Num::Real(x + y)),
        _ => None,
    }
}

fn num_mul(a: &Num, b: &Num) -> Option<Num> {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => x.checked_mul(*y).map(Num::Int),
        (Num::Real(x), Num::Real(y)) => Some(Num::Real(x * y)),
        _ => None,
    }
}

fn num_neg(a: &Num) -> Option<Num> {
    match a {
        Num::Int(x) => x.checked_neg().map(Num::Int),
        Num::Real(x) => Some(Num::Real(-x)),
    }
}

fn num_is_zero(a: &Num) -> bool {
    match a {
        Num::Int(x) => *x == 0,
        Num::Real(x) => x.is_zero(),
    }
}

fn num_is_one(a: &Num) -> bool {
    match a {
        Num::Int(x) => *x == 1,
        Num::Real(x) => x.is_one(),
    }
}

type Memo = FxHashMap<*const ChcExpr, Arc<ChcExpr>>;

/// Substitute-and-simplify over a DAG, memoised on node identity. The memo
/// is valid for one definition map: callers use a fresh simplifier whenever
/// the map may have grown (or accept stale, under-substituted results, see
/// [`solve_eqs`]).
#[derive(Default)]
pub(super) struct Simplifier {
    memo: Memo,
}

impl Simplifier {
    /// The simplified form of `e` under `defs` (the very same `Arc` when
    /// nothing changed), or `None` when the budget or the recursion depth ran
    /// out.
    pub(super) fn simp(
        &mut self,
        defs: &FxHashMap<ChcVar, Arc<ChcExpr>>,
        visits: &mut usize,
        e: &Arc<ChcExpr>,
        depth: usize,
    ) -> Option<Arc<ChcExpr>> {
        let key = Arc::as_ptr(e);
        if let Some(done) = self.memo.get(&key) {
            return Some(Arc::clone(done));
        }
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        *visits += 1;
        if *visits > MAX_VISITS {
            return None;
        }
        let result = maybe_grow_expr_stack(|| self.simp_node(defs, visits, e, depth))?;
        self.memo.insert(key, Arc::clone(&result));
        Some(result)
    }

    fn simp_node(
        &mut self,
        defs: &FxHashMap<ChcVar, Arc<ChcExpr>>,
        visits: &mut usize,
        e: &Arc<ChcExpr>,
        depth: usize,
    ) -> Option<Arc<ChcExpr>> {
        match e.as_ref() {
            ChcExpr::Var(v) => Some(defs.get(v).map_or_else(|| Arc::clone(e), Arc::clone)),
            ChcExpr::Op(op, args) => {
                let mut new_args = Vec::with_capacity(args.len());
                let mut changed = false;
                for a in args {
                    let s = self.simp(defs, visits, a, depth + 1)?;
                    changed |= !Arc::ptr_eq(&s, a);
                    new_args.push(s);
                }
                Some(fold(*op, &new_args).unwrap_or_else(|| {
                    if changed {
                        Arc::new(ChcExpr::Op(*op, new_args))
                    } else {
                        Arc::clone(e)
                    }
                }))
            }
            _ => Some(Arc::clone(e)),
        }
    }
}

fn bool_arc(b: bool) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Bool(b))
}

fn is_bool_const(e: &ChcExpr) -> Option<bool> {
    match e {
        ChcExpr::Bool(b) => Some(*b),
        _ => None,
    }
}

/// Structural identity cheap enough for a fold: the same node, or the same
/// variable / constant.
fn same_leaf(a: &Arc<ChcExpr>, b: &Arc<ChcExpr>) -> bool {
    if Arc::ptr_eq(a, b) {
        return true;
    }
    match (a.as_ref(), b.as_ref()) {
        (ChcExpr::Var(x), ChcExpr::Var(y)) => x == y,
        (ChcExpr::Bool(x), ChcExpr::Bool(y)) => x == y,
        _ => match (num_of(a), num_of(b)) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        },
    }
}

fn negate(e: &Arc<ChcExpr>) -> Arc<ChcExpr> {
    match e.as_ref() {
        ChcExpr::Bool(b) => bool_arc(!b),
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => Arc::clone(&args[0]),
        _ => Arc::new(ChcExpr::Op(ChcOp::Not, vec![Arc::clone(e)])),
    }
}

fn mk_and(args: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    fold(ChcOp::And, &args).unwrap_or_else(|| Arc::new(ChcExpr::Op(ChcOp::And, args)))
}

fn mk_or(args: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    fold(ChcOp::Or, &args).unwrap_or_else(|| Arc::new(ChcExpr::Op(ChcOp::Or, args)))
}

/// The folded form of `op(args)` (arguments already simplified), or `None`
/// when no rule applies.
fn fold(op: ChcOp, args: &[Arc<ChcExpr>]) -> Option<Arc<ChcExpr>> {
    match op {
        ChcOp::Not if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Bool(b) => Some(bool_arc(!b)),
            ChcExpr::Op(ChcOp::Not, inner) if inner.len() == 1 => Some(Arc::clone(&inner[0])),
            _ => None,
        },
        ChcOp::And | ChcOp::Or => fold_junction(op, args),
        ChcOp::Implies if args.len() == 2 => {
            match (is_bool_const(&args[0]), is_bool_const(&args[1])) {
                (Some(false), _) | (_, Some(true)) => Some(bool_arc(true)),
                (Some(true), _) => Some(Arc::clone(&args[1])),
                (_, Some(false)) => Some(negate(&args[0])),
                _ => None,
            }
        }
        ChcOp::Iff if args.len() == 2 => fold_bool_eq(&args[0], &args[1]),
        ChcOp::Ite if args.len() == 3 => fold_ite(&args[0], &args[1], &args[2]),
        ChcOp::Eq if args.len() == 2 => {
            if let (Some(a), Some(b)) = (num_of(&args[0]), num_of(&args[1])) {
                return num_cmp(&a, &b).map(|o| bool_arc(o.is_eq()));
            }
            if same_leaf(&args[0], &args[1]) {
                return Some(bool_arc(true));
            }
            fold_bool_eq(&args[0], &args[1])
        }
        ChcOp::Ne if args.len() == 2 => {
            if let (Some(a), Some(b)) = (num_of(&args[0]), num_of(&args[1])) {
                return num_cmp(&a, &b).map(|o| bool_arc(!o.is_eq()));
            }
            if same_leaf(&args[0], &args[1]) {
                return Some(bool_arc(false));
            }
            fold_bool_eq(&args[0], &args[1]).map(|eq| negate(&eq))
        }
        ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge if args.len() == 2 => {
            fold_order(op, &args[0], &args[1])
        }
        ChcOp::Add => fold_add(args),
        ChcOp::Mul => fold_mul(args),
        ChcOp::Neg if args.len() == 1 => {
            let n = num_of(&args[0])?;
            num_expr(&num_neg(&n)?).map(Arc::new)
        }
        ChcOp::Sub if args.len() >= 2 => {
            let mut acc = num_of(&args[0])?;
            for a in &args[1..] {
                acc = num_add(&acc, &num_neg(&num_of(a)?)?)?;
            }
            num_expr(&acc).map(Arc::new)
        }
        _ => None,
    }
}

/// `and` / `or` with constants absorbed, nested same-op arguments flattened
/// one level (arguments are already folded) and repeated nodes dropped.
fn fold_junction(op: ChcOp, args: &[Arc<ChcExpr>]) -> Option<Arc<ChcExpr>> {
    let is_and = op == ChcOp::And;
    let absorbing = !is_and;
    let mut kept: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
    let mut seen: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut changed = false;
    for a in args {
        match a.as_ref() {
            ChcExpr::Bool(b) if *b == absorbing => return Some(bool_arc(absorbing)),
            ChcExpr::Bool(_) => changed = true,
            ChcExpr::Op(inner, inner_args) if *inner == op => {
                // Arguments are already folded, so a nested `op` has
                // no nested `op` of its own: one level suffices.
                changed = true;
                for ia in inner_args {
                    if seen.insert(Arc::as_ptr(ia)) {
                        kept.push(Arc::clone(ia));
                    }
                }
            }
            _ => {
                if seen.insert(Arc::as_ptr(a)) {
                    kept.push(Arc::clone(a));
                } else {
                    changed = true;
                }
            }
        }
    }
    match kept.len() {
        0 => Some(bool_arc(is_and)),
        1 => kept.pop(),
        _ if changed => Some(Arc::new(ChcExpr::Op(op, kept))),
        _ => None,
    }
}

/// `<`, `<=`, `>`, `>=` on two constants, or on one node twice.
fn fold_order(op: ChcOp, a: &Arc<ChcExpr>, b: &Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
    if let (Some(a), Some(b)) = (num_of(a), num_of(b)) {
        let o = num_cmp(&a, &b)?;
        let holds = match op {
            ChcOp::Lt => o.is_lt(),
            ChcOp::Le => o.is_le(),
            ChcOp::Gt => o.is_gt(),
            _ => o.is_ge(),
        };
        return Some(bool_arc(holds));
    }
    if same_leaf(a, b) {
        return Some(bool_arc(matches!(op, ChcOp::Le | ChcOp::Ge)));
    }
    None
}

/// `a = b` over Bool when one side is a constant.
fn fold_bool_eq(a: &Arc<ChcExpr>, b: &Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
    match (is_bool_const(a), is_bool_const(b)) {
        (Some(x), Some(y)) => Some(bool_arc(x == y)),
        (Some(true), None) => Some(Arc::clone(b)),
        (None, Some(true)) => Some(Arc::clone(a)),
        (Some(false), None) => Some(negate(b)),
        (None, Some(false)) => Some(negate(a)),
        (None, None) => None,
    }
}

fn fold_ite(c: &Arc<ChcExpr>, t: &Arc<ChcExpr>, e: &Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
    if let Some(b) = is_bool_const(c) {
        return Some(Arc::clone(if b { t } else { e }));
    }
    if same_leaf(t, e) {
        return Some(Arc::clone(t));
    }
    match (is_bool_const(t), is_bool_const(e)) {
        (Some(true), Some(false)) => Some(Arc::clone(c)),
        (Some(false), Some(true)) => Some(negate(c)),
        (Some(true), None) => Some(mk_or(vec![Arc::clone(c), Arc::clone(e)])),
        (Some(false), None) => Some(mk_and(vec![negate(c), Arc::clone(e)])),
        (None, Some(true)) => Some(mk_or(vec![negate(c), Arc::clone(t)])),
        (None, Some(false)) => Some(mk_and(vec![Arc::clone(c), Arc::clone(t)])),
        _ => None,
    }
}

/// Sum the constant addends; drop a zero sum. `None` when nothing changes.
fn fold_add(args: &[Arc<ChcExpr>]) -> Option<Arc<ChcExpr>> {
    let mut sum: Option<Num> = None;
    let mut consts = 0usize;
    let mut rest: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
    for a in args {
        match num_of(a) {
            Some(n) => {
                consts += 1;
                sum = Some(match sum {
                    None => n,
                    Some(s) => num_add(&s, &n)?,
                });
            }
            None => rest.push(Arc::clone(a)),
        }
    }
    let sum = sum?;
    if rest.is_empty() {
        return num_expr(&sum).map(Arc::new);
    }
    let drop_sum = num_is_zero(&sum);
    if consts == 1 && !drop_sum {
        return None;
    }
    if !drop_sum {
        rest.push(Arc::new(num_expr(&sum)?));
    }
    if rest.len() == 1 {
        return rest.pop();
    }
    Some(Arc::new(ChcExpr::Op(ChcOp::Add, rest)))
}

/// Multiply the constant factors; a zero product is zero, a unit product
/// disappears. `None` when nothing changes.
fn fold_mul(args: &[Arc<ChcExpr>]) -> Option<Arc<ChcExpr>> {
    let mut prod: Option<Num> = None;
    let mut consts = 0usize;
    let mut rest: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
    for a in args {
        match num_of(a) {
            Some(n) => {
                consts += 1;
                prod = Some(match prod {
                    None => n,
                    Some(p) => num_mul(&p, &n)?,
                });
            }
            None => rest.push(Arc::clone(a)),
        }
    }
    let prod = prod?;
    if rest.is_empty() || num_is_zero(&prod) {
        return num_expr(&prod).map(Arc::new);
    }
    let drop_prod = num_is_one(&prod);
    if consts == 1 && !drop_prod {
        return None;
    }
    if !drop_prod {
        rest.insert(0, Arc::new(num_expr(&prod)?));
    }
    if rest.len() == 1 {
        return rest.pop();
    }
    Some(Arc::new(ChcExpr::Op(ChcOp::Mul, rest)))
}
