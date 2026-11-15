// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keys, conversion memo, conjunct split and eligibility (design §2.6;
//! contract C5; owner WP-3 / C).
//!
//! The structural key is PRIMARY (design F18: `and_all`/`and_vec` rebuild Arcs,
//! so pointer identity mostly misses); the pointer key is a pre-check cache. On
//! a structural hit the stored Arc is compared with `==` (`Arc::ptr_eq` fast
//! path) before reuse — a collision falls back to fresh encoding, never to a
//! wrong reuse.
//!
//! Normalisation: each conjunct goes through
//! `SmtContext::preprocess_incremental_assumption(expr, ns)` with a namespace
//! derived from the STRUCTURAL key (not a counter, not the pointer) so
//! re-encounters produce identical auxiliaries; auxiliary names are stripped
//! from returned models. (The namespace rule itself is applied by
//! `HornSmt::assert_with_origin`, `mod.rs`; the memo sees the normalised Arc.)

use std::hash::{Hash, Hasher};
use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::{Sort, TermId};
use rustc_hash::FxHasher;

use super::{TheoryKind, UnknownReason, UnsupportedKind};
use crate::expr::{maybe_grow_expr_stack, MAX_EXPR_RECURSION_DEPTH};
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcOp, ChcSort};

/// Seeds of the two FxHash passes behind `ConjunctKey::Structural`. Two
/// independent 64-bit passes plus the node count make an accidental collision
/// of two distinct live conjuncts practically impossible; the `==`
/// confirmation on every structural hit makes it harmless when it happens.
const KEY_SEED_1: usize = 0x9E37_79B9_7F4A_7C15;
const KEY_SEED_2: usize = 0xC2B2_AE3D_27D4_EB4F;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ConjunctKey {
    /// Two seeded FxHash passes over the derived `Hash` + node count.
    Structural { h1: u64, h2: u64, nodes: u32 },
}

/// Which rung's eligibility rules apply (§2.6: Rung 1 rejects `mod`/`div` and
/// Int vars under `TheoryKind::Lra`; Rung 2 admits `mod`/`div` through
/// per-conjunct `eliminate_mod()`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rung {
    Rung1,
    Rung2,
}

/// `split_conjuncts` met `Bool(false)`: the query is trivially UNSAT and never
/// touches the solver (the router answers `SmtResult::Unsat` directly).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TriviallyFalse;

#[derive(Default)]
pub(crate) struct ConvertMemo {
    /// Arc retained => the address is never reused while the entry lives.
    by_ptr: FxHashMap<usize, (Arc<ChcExpr>, ConjunctKey, TermId)>,
    /// The Arc is kept so a structural hit is confirmed with `==` before the
    /// term is reused (a key collision falls through to a fresh conversion).
    by_key: FxHashMap<ConjunctKey, (Arc<ChcExpr>, TermId)>,
    pub(crate) hits_ptr: u64,
    pub(crate) hits_struct: u64,
    pub(crate) misses: u64,
}

impl ConvertMemo {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Structural key: two seeded FxHash passes over the derived (structural)
    /// `Hash` plus the node count. Pure function of the expression's structure —
    /// never of its allocation — so `and_all`/`and_vec` rebuilds (F18) key
    /// identically.
    pub(crate) fn key_of(e: &ChcExpr) -> ConjunctKey {
        let mut hasher1 = FxHasher::with_seed(KEY_SEED_1);
        e.hash(&mut hasher1);
        let mut hasher2 = FxHasher::with_seed(KEY_SEED_2);
        e.hash(&mut hasher2);
        ConjunctKey::Structural {
            h1: hasher1.finish(),
            h2: hasher2.finish(),
            nodes: node_count(e),
        }
    }

    /// ptr hit -> struct hit -> `own.reset_conversion_budget(); own.convert_expr(e)`.
    /// The budget sentinel path returns `mk_bool(true)` and MUST NOT be
    /// memoised: on `own.conversion_budget_exceeded()` return
    /// `Err(Unsupported(ConversionBudget))`. Budget is reset per conjunct
    /// (the counter is cumulative and sticky otherwise, B-sound M3). A
    /// non-Bool result (an ill-typed conjunct the converter could not repair)
    /// is `Err(Unsupported(IllTyped))` and is not memoised either.
    pub(crate) fn convert(
        &mut self,
        own: &mut SmtContext,
        e: &Arc<ChcExpr>,
    ) -> Result<(ConjunctKey, TermId), UnknownReason> {
        let ptr = Arc::as_ptr(e) as usize;
        if let Some((_, key, term)) = self.by_ptr.get(&ptr) {
            self.hits_ptr += 1;
            return Ok((*key, *term));
        }
        let key = Self::key_of(e);
        if let Some((stored, term)) = self.by_key.get(&key) {
            // `==` has the `Arc::ptr_eq` fast path on children (types.rs);
            // a collision (different expr, same key) falls through.
            if **stored == **e {
                self.hits_struct += 1;
                let term = *term;
                self.by_ptr.insert(ptr, (Arc::clone(e), key, term));
                return Ok((key, term));
            }
        }
        self.misses += 1;
        own.reset_conversion_budget();
        let term = own.convert_expr(e);
        if own.conversion_budget_exceeded() {
            // The sentinel `true` would WEAKEN the conjunct: never memoised,
            // never asserted.
            return Err(UnknownReason::Unsupported(
                UnsupportedKind::ConversionBudget,
            ));
        }
        if own.terms.sort(term) != &Sort::Bool {
            return Err(UnknownReason::Unsupported(UnsupportedKind::IllTyped));
        }
        self.by_key.insert(key, (Arc::clone(e), term));
        self.by_ptr.insert(ptr, (Arc::clone(e), key, term));
        Ok((key, term))
    }

    pub(crate) fn clear(&mut self) {
        self.by_ptr.clear();
        self.by_key.clear();
    }

    /// Number of distinct conjuncts memoised (tests / board).
    pub(crate) fn len(&self) -> usize {
        self.by_key.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.by_key.is_empty()
    }
}

/// Node count of the expression tree (saturating at `u32::MAX`; a tree deeper
/// than `MAX_EXPR_RECURSION_DEPTH` counts its remaining subtree as one node —
/// the same depth bail-out the other walks use, and such a conjunct is
/// rejected by `eligible` anyway).
fn node_count(e: &ChcExpr) -> u32 {
    fn inner(e: &ChcExpr, depth: usize, acc: &mut u32) {
        *acc = acc.saturating_add(1);
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return;
        }
        maybe_grow_expr_stack(|| match e {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    inner(a, depth + 1, acc);
                }
            }
            ChcExpr::ConstArray(_, val) => inner(val, depth + 1, acc),
            _ => {}
        });
    }
    let mut acc = 0u32;
    inner(e, 0, &mut acc);
    acc
}

/// Flatten `Op(And, args)` recursively into its `Arc` children; a non-And root
/// is wrapped once; `Bool(true)` dropped; `Bool(false)` => `TriviallyFalse`.
/// Mirrors `ChcExpr::conjuncts()` but keeps the Arcs (so the pointer pre-check
/// of the memo and `Assertion::expr` see the caller's allocation). Beyond
/// `MAX_EXPR_RECURSION_DEPTH` a nested `And` is kept whole as one conjunct
/// (still a sound conjunct; `eligible` decides whether it is encodable).
pub(crate) fn split_conjuncts(root: &ChcExpr) -> Result<Vec<Arc<ChcExpr>>, TriviallyFalse> {
    fn push(
        e: &Arc<ChcExpr>,
        out: &mut Vec<Arc<ChcExpr>>,
        depth: usize,
    ) -> Result<(), TriviallyFalse> {
        match &**e {
            ChcExpr::Bool(true) => Ok(()),
            ChcExpr::Bool(false) => Err(TriviallyFalse),
            ChcExpr::Op(ChcOp::And, args) if depth < MAX_EXPR_RECURSION_DEPTH => {
                maybe_grow_expr_stack(|| {
                    for a in args {
                        push(a, out, depth + 1)?;
                    }
                    Ok(())
                })
            }
            _ => {
                out.push(Arc::clone(e));
                Ok(())
            }
        }
    }

    let mut out = Vec::new();
    match root {
        ChcExpr::Bool(true) => {}
        ChcExpr::Bool(false) => return Err(TriviallyFalse),
        ChcExpr::Op(ChcOp::And, args) => {
            for a in args {
                push(a, &mut out, 1)?;
            }
        }
        other => out.push(Arc::new(other.clone())),
    }
    Ok(out)
}

/// Eligibility from `ChcExpr::scan_features()`: reject `has_array_ops | has_bv |
/// has_uf_apps | has_dt | has_mixed_sort_eq`, `contains_nonlinear_mul()`,
/// PredicateApp / FuncApp / ConstArray / quantifier nodes; Rung 1 also rejects
/// `has_mod_or_div`; Int vars are rejected while `TheoryKind::Lra` (Rung 1).
/// Checked BEFORE conversion so nothing is asserted for a rejected query.
///
/// Beyond the design's list, the walk rejects what the legacy converter would
/// silently WEAKEN instead of refusing (`convert.rs`: `Not`/`And`/`Or`/
/// `Implies`/`Iff` over a non-Bool operand, an `Ite` with mismatched branch
/// sorts, a non-Bool conjunct root, uninterpreted-sorted vars, parser markers)
/// as `IllTyped`/`Shape` — the session must never assert a weaker formula
/// than the caller's (INV-S3 covers SAT only; UNSAT has no such net).
///
/// Kinds: sorts outside the theory (arrays, BV, DT, uninterpreted, Int under
/// `Lra`) => `Sort`; predicate/function applications, constant arrays,
/// markers, nonlinear products and (Rung 1) `mod`/`div` => `Shape`; mixed-sort
/// equalities and the weakening cases => `IllTyped`.
pub(crate) fn eligible(e: &ChcExpr, kind: TheoryKind, rung: Rung) -> Result<(), UnsupportedKind> {
    let features = e.scan_features();
    if features.has_array_ops || features.has_bv || features.has_dt {
        return Err(UnsupportedKind::Sort);
    }
    if features.has_uf_apps {
        return Err(UnsupportedKind::Shape);
    }
    if features.has_mixed_sort_eq {
        return Err(UnsupportedKind::IllTyped);
    }
    if rung == Rung::Rung1 && features.has_mod_or_div {
        return Err(UnsupportedKind::Shape);
    }
    if e.contains_nonlinear_mul() {
        return Err(UnsupportedKind::Shape);
    }
    if e.sort() != ChcSort::Bool {
        return Err(UnsupportedKind::IllTyped);
    }
    walk_eligible(e, kind, rung, 0)
}

/// Equal sorts, or both numeric: the converter promotes an Int operand next to
/// a Real one with `to_real` (`convert.rs` `coerce_int_bv_pair`), which folds
/// an Int CONSTANT to a rational — `(= x 0)` with Real `x` is well-typed here.
/// (An Int VARIABLE under `Lra` is still rejected by the `Var` arm.)
fn same_or_numeric(a: &ChcSort, b: &ChcSort) -> bool {
    a == b
        || (matches!(a, ChcSort::Int | ChcSort::Real) && matches!(b, ChcSort::Int | ChcSort::Real))
}

/// The node-kind / sort walk `scan_features` does not cover: predicate
/// applications, parser markers, constant arrays, uninterpreted-sorted and
/// (under `Lra`) Int-sorted variables, and the operand-sort checks of the Bool
/// connectives and `Ite`. Depth-bounded like every other expression walk.
fn walk_eligible(
    e: &ChcExpr,
    kind: TheoryKind,
    rung: Rung,
    depth: usize,
) -> Result<(), UnsupportedKind> {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return Err(UnsupportedKind::Shape);
    }
    maybe_grow_expr_stack(|| match e {
        ChcExpr::ArrayLambda(_) => Err(UnsupportedKind::Shape),
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) => Ok(()),
        ChcExpr::BitVec(_, _) => Err(UnsupportedKind::Sort),
        ChcExpr::Var(v) => match &v.sort {
            ChcSort::Bool | ChcSort::Real => Ok(()),
            ChcSort::Int => match kind {
                TheoryKind::Lia => Ok(()),
                TheoryKind::Lra => Err(UnsupportedKind::Sort),
            },
            ChcSort::BitVec(_)
            | ChcSort::Array(_, _)
            | ChcSort::Uninterpreted(_)
            | ChcSort::Datatype { .. } => Err(UnsupportedKind::Sort),
        },
        ChcExpr::PredicateApp(_, _, _)
        | ChcExpr::FuncApp(_, _, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => Err(UnsupportedKind::Shape),
        ChcExpr::Op(op, args) => {
            match op {
                ChcOp::Not | ChcOp::And | ChcOp::Or | ChcOp::Implies | ChcOp::Iff => {
                    // The converter turns a non-Bool operand into `true` (a
                    // weakening) or trips the ill-typed sentinel; refuse here.
                    if args.iter().any(|a| a.sort() != ChcSort::Bool) {
                        return Err(UnsupportedKind::IllTyped);
                    }
                }
                ChcOp::Ite => {
                    if args.len() != 3
                        || args[0].sort() != ChcSort::Bool
                        || !same_or_numeric(&args[1].sort(), &args[2].sort())
                    {
                        return Err(UnsupportedKind::IllTyped);
                    }
                }
                ChcOp::Eq | ChcOp::Ne => {
                    if args.len() != 2 || !same_or_numeric(&args[0].sort(), &args[1].sort()) {
                        return Err(UnsupportedKind::IllTyped);
                    }
                }
                ChcOp::Mod | ChcOp::Div if rung == Rung::Rung1 => {
                    return Err(UnsupportedKind::Shape);
                }
                ChcOp::Select | ChcOp::Store => return Err(UnsupportedKind::Sort),
                ChcOp::Lt
                | ChcOp::Le
                | ChcOp::Gt
                | ChcOp::Ge
                | ChcOp::Add
                | ChcOp::Sub
                | ChcOp::Mul
                | ChcOp::Neg
                | ChcOp::Mod
                | ChcOp::Div => {}
                // Every remaining operator is a bit-vector operator.
                _ => return Err(UnsupportedKind::Sort),
            }
            for a in args {
                walk_eligible(a, kind, rung, depth + 1)?;
            }
            Ok(())
        }
    })
}
