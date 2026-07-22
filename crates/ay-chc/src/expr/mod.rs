// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression types for CHC formulas

// These constructors build AST nodes, not perform operations.
// Implementing std::ops traits would be semantically incorrect.
#![allow(clippy::should_implement_trait)]

mod eliminate;
pub(crate) mod evaluate;
pub(crate) mod intern;
pub(crate) mod jit_bridge;
mod methods;
mod normalize;
mod simplify;
mod types;

pub use types::{ChcDtConstructor, ChcDtSelector, ChcExpr, ChcOp, ChcSort, ChcVar};

#[cfg(test)]
#[path = "tests/mod.rs"]
mod expr_tests;

pub(crate) use evaluate::{eval_array_select, eval_int_big, evaluate_expr};
pub(crate) use methods::ExprFeatures;

#[cfg(test)]
use crate::PredicateId;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_rational::Rational64;

/// (#3121) Linear term decomposition for tautological equality elimination.
/// Used by `simplify_linear_equalities` to detect `(= A B)` where A-B=0.
#[derive(Default)]
pub(crate) struct LinearTermsProd {
    coeffs: FxHashMap<String, i128>,
    constant: i128,
}

// ---------------------------------------------------------------------------
// Generic linear expression walker (#3669, #3719)
// ---------------------------------------------------------------------------

/// Coefficient type for linear expression parsing.
///
/// Abstracts over `i64` (with overflow-checked arithmetic) and `Rational64`
/// so that the expression-walking logic is written once.
///
/// i128-lockstep: the multiplier channel is `i128` (the `ChcExpr::Int` width);
/// impls narrow fail-closed (`None` when the product leaves their own range —
/// the walker then declines to decompose, never truncates).
pub(crate) trait LinearCoeff: Copy {
    fn checked_neg(self) -> Option<Self>;
    fn checked_mul_i128(self, n: i128) -> Option<Self>;
}

#[allow(clippy::use_self)] // Self::checked_neg would recurse into the trait method
impl LinearCoeff for i128 {
    fn checked_neg(self) -> Option<Self> {
        i128::checked_neg(self)
    }
    fn checked_mul_i128(self, n: i128) -> Option<Self> {
        self.checked_mul(n)
    }
}

#[allow(clippy::use_self)] // Self::checked_neg would recurse into the trait method
impl LinearCoeff for i64 {
    fn checked_neg(self) -> Option<Self> {
        i64::checked_neg(self)
    }
    fn checked_mul_i128(self, n: i128) -> Option<Self> {
        // i128-lockstep: exact product, fail-closed narrowing back to i64.
        i64::try_from(i128::from(self).checked_mul(n)?).ok()
    }
}

fn checked_rational64_neg(r: Rational64) -> Option<Rational64> {
    let numer = (*r.numer()).checked_neg()?;
    Some(Rational64::new(numer, *r.denom()))
}

fn checked_rational64_mul_i128(r: Rational64, n: i128) -> Option<Rational64> {
    let numer = i128::from(*r.numer()).checked_mul(n)?;
    let numer_i64 = i64::try_from(numer).ok()?;
    Some(Rational64::new(numer_i64, *r.denom()))
}

#[allow(clippy::use_self)] // Rational64 constructor, not a Self alias
impl LinearCoeff for Rational64 {
    fn checked_neg(self) -> Option<Self> {
        checked_rational64_neg(self)
    }
    fn checked_mul_i128(self, n: i128) -> Option<Self> {
        checked_rational64_mul_i128(self, n)
    }
}

/// Extract an integer constant from a possibly `Neg`-wrapped `Int` node.
fn extract_int_constant(expr: &ChcExpr) -> Option<i128> {
    match expr {
        ChcExpr::Int(n) => Some(*n),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            if let ChcExpr::Int(n) = args[0].as_ref() {
                n.checked_neg()
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Try to strip a BvToInt ITE wrapper, returning the inner linear expression.
///
/// Recognizes two patterns produced by BvToInt:
/// - bvadd: `ite(sum < 2^w, sum, sum - 2^w)` -> `sum`
/// - bvsub: `ite(diff >= 0, diff, diff + 2^w)` -> `diff`
fn strip_bv_to_int_ite<'a>(args: &'a [std::sync::Arc<ChcExpr>]) -> Option<&'a ChcExpr> {
    // Pattern: ite(sum < 2^w, sum, sum - 2^w) -- bvadd
    if let ChcExpr::Op(ChcOp::Lt, cond_args) = &*args[0] {
        if cond_args.len() == 2 {
            if let ChcExpr::Int(bound) = &*cond_args[1] {
                if *bound > 0 && (*bound & (*bound - 1)) == 0 && *cond_args[0] == *args[1] {
                    if let ChcExpr::Op(ChcOp::Sub, sub_args) = &*args[2] {
                        if sub_args.len() == 2
                            && *cond_args[0] == *sub_args[0]
                            && *sub_args[1] == ChcExpr::Int(*bound)
                        {
                            return Some(&cond_args[0]);
                        }
                    }
                }
            }
        }
    }
    // Pattern: ite(diff >= 0, diff, diff + 2^w) -- bvsub
    if let ChcExpr::Op(ChcOp::Ge, cond_args) = &*args[0] {
        if cond_args.len() == 2 && *cond_args[1] == ChcExpr::Int(0) && *cond_args[0] == *args[1] {
            if let ChcExpr::Op(ChcOp::Add, add_args) = &*args[2] {
                if add_args.len() == 2 && *cond_args[0] == *add_args[0] {
                    if let ChcExpr::Int(bound) = &*add_args[1] {
                        if *bound > 0 && (*bound & (*bound - 1)) == 0 {
                            return Some(&cond_args[0]);
                        }
                    }
                }
            }
        }
    }
    None
}

/// Walk a linear integer expression, invoking callbacks for leaf nodes.
///
/// Decomposes `Add`, `Sub`, `Neg`, and `Mul`-by-constant into a sum of
/// scaled variables and a constant offset.  Returns `None` when any
/// sub-expression is non-linear or when checked arithmetic overflows.
///
/// Callers supply:
/// - `on_int(mult, n)` — called for each `Int(n)` leaf with accumulated scale
/// - `on_var(mult, var)` — called for each `Var(v)` leaf with accumulated scale
///
/// The `on_var` callback decides whether to filter by sort (e.g. Int-only).
pub(crate) fn walk_linear_expr<C: LinearCoeff>(
    expr: &ChcExpr,
    mult: C,
    on_int: &mut impl FnMut(C, i128) -> Option<()>,
    on_var: &mut impl FnMut(C, &ChcVar) -> Option<()>,
) -> Option<()> {
    maybe_grow_expr_stack(|| {
        ExprDepthGuard::check()?;
        match expr {
            ChcExpr::Int(n) => on_int(mult, *n),
            ChcExpr::Var(v) => on_var(mult, v),
            ChcExpr::Op(ChcOp::Add, args) => {
                for arg in args {
                    walk_linear_expr(arg, mult, on_int, on_var)?;
                }
                Some(())
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                walk_linear_expr(&args[0], mult, on_int, on_var)?;
                let neg_mult = mult.checked_neg()?;
                for arg in &args[1..] {
                    walk_linear_expr(arg, neg_mult, on_int, on_var)?;
                }
                Some(())
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                walk_linear_expr(&args[0], mult.checked_neg()?, on_int, on_var)
            }
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                // Try both sides for the constant factor, including Neg(Int(c)).
                let (c, other) = if let Some(c) = extract_int_constant(args[0].as_ref()) {
                    (c, args[1].as_ref())
                } else if let Some(c) = extract_int_constant(args[1].as_ref()) {
                    (c, args[0].as_ref())
                } else {
                    return None;
                };
                walk_linear_expr(other, mult.checked_mul_i128(c)?, on_int, on_var)
            }
            // BvToInt bvadd wrapping: ite(sum < 2^w, sum, sum - 2^w) (#7931)
            // BvToInt bvsub wrapping: ite(diff >= 0, diff, diff + 2^w)
            // See through the modular guard to the inner linear expression.
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                if let Some(inner) = strip_bv_to_int_ite(args) {
                    walk_linear_expr(inner, mult, on_int, on_var)
                } else {
                    None
                }
            }
            // BvToInt mod wrapping: mod(expr, 2^w) -> walk expr (#7931)
            ChcExpr::Op(ChcOp::Mod, args)
                if args.len() == 2
                    && matches!(&*args[1], ChcExpr::Int(b) if *b > 0 && (*b & (*b - 1)) == 0) =>
            {
                walk_linear_expr(&args[0], mult, on_int, on_var)
            }
            _ => None,
        }
    })
}

/// Red zone for stacker: in debug builds, closure frames are 1-2KB each
/// (no inlining, debug symbols), so 32KB may be insufficient at depth 10K.
/// Use 128KB in debug mode for safety (#3164).
const EXPR_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};
const EXPR_STACK_SIZE: usize = 2 * 1024 * 1024;

/// SMT-LIB Euclidean division for i128: `a = b * q + r` where `0 <= r < |b|`.
///
/// Returns `None` on division by zero or overflow (`i128::MIN / -1`).
pub(crate) fn smt_euclid_div(a: i128, b: i128) -> Option<i128> {
    a.checked_div_euclid(b)
}

/// SMT-LIB Euclidean remainder for i128: always non-negative, `0 <= r < |b|`.
///
/// Returns `None` on division by zero or overflow (`i128::MIN % -1`).
pub(crate) fn smt_euclid_mod(a: i128, b: i128) -> Option<i128> {
    a.checked_rem_euclid(b)
}

/// Node budget for expression preprocessing traversals (#2774, #2771).
/// Used by: simplify_constants, normalize_strict_int_comparisons,
/// eliminate_ite, eliminate_mod, substitute_map, rename_internal_aux_vars (smt.rs).
/// (normalize_negations has its own MAX_NORMALIZE_NODES constant.)
/// Each function independently limits its traversal to this many nodes.
/// On exhaustion, the function returns the original expression unchanged —
/// semantically correct, just unoptimized.
pub(crate) const MAX_PREPROCESSING_NODES: usize = 1_000_000;

/// Maximum recursion depth for expression tree traversals (#2988, #3031).
/// Depth limit for `ExprDepthGuard::check()` bail-out. Call sites that return
/// `Option<T>` use this to stop recursing on expressions deeper than typical
/// solver outputs. `maybe_grow_expr_stack` itself always uses stacker (#3079).
pub(crate) const MAX_EXPR_RECURSION_DEPTH: usize = 500;

/// Grow the stack for deep expression recursion, with automatic depth tracking (#3031).
///
/// Always delegates to `stacker::maybe_grow` which allocates heap segments on
/// demand (only when the red zone is hit). Stacker overhead is bounded by
/// actual stack usage, not by recursion depth — a depth-10000 tree with small
/// frames reuses segments and allocates far less than `depth * EXPR_STACK_SIZE`.
///
/// The depth counter is incremented per call for `ExprDepthGuard::check()`.
#[inline]
pub(crate) fn maybe_grow_expr_stack<T>(f: impl FnOnce() -> T) -> T {
    EXPR_DEPTH.with(|d| {
        let depth = d.get();
        d.set(depth.saturating_add(1));
        let result = stacker::maybe_grow(EXPR_STACK_RED_ZONE, EXPR_STACK_SIZE, f);
        d.set(depth);
        result
    })
}

thread_local! {
    static EXPR_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Current expression recursion depth (for testing).
#[cfg(test)]
fn expr_depth() -> usize {
    EXPR_DEPTH.with(std::cell::Cell::get)
}

/// Walk an expression tree, calling `visitor` for each comparison bound found.
///
/// Descends through `And` conjunctions. When `descend_or` is true, also descends
/// through `Or` disjunctions. When `handle_negation` is true, `Not(Le(a,b))` is
/// converted to `Gt(a,b)`, etc.
///
/// For each comparison `Le/Lt/Ge/Gt` with exactly 2 arguments, calls
/// `visitor(left, op, right)` with the raw operands. The caller interprets
/// whether `left`/`right` are variables, constants, or complex expressions.
///
/// Shared traversal for `init_analysis::extract_bounds_recursive`,
/// `bounds_recurrence::extract_bounds_recursive`, and similar (#3786).
pub(crate) fn walk_comparison_bounds(
    expr: &ChcExpr,
    descend_or: bool,
    handle_negation: bool,
    visitor: &mut impl FnMut(&ChcExpr, ChcOp, &ChcExpr),
) {
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::And, args) => {
            for arg in args {
                walk_comparison_bounds(arg, descend_or, handle_negation, visitor);
            }
        }
        ChcExpr::Op(ChcOp::Or, args) if descend_or => {
            for arg in args {
                walk_comparison_bounds(arg, descend_or, handle_negation, visitor);
            }
        }
        ChcExpr::Op(op @ (ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt), args)
            if args.len() == 2 =>
        {
            visitor(args[0].as_ref(), *op, args[1].as_ref());
        }
        ChcExpr::Op(ChcOp::Not, args) if handle_negation && args.len() == 1 => {
            if let ChcExpr::Op(op @ (ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt), inner) =
                args[0].as_ref()
            {
                if inner.len() == 2 {
                    let flipped = match op {
                        ChcOp::Le => ChcOp::Gt,
                        ChcOp::Lt => ChcOp::Ge,
                        ChcOp::Ge => ChcOp::Lt,
                        ChcOp::Gt => ChcOp::Le,
                        _ => return, // #6091: defensive
                    };
                    visitor(inner[0].as_ref(), flipped, inner[1].as_ref());
                }
            }
        }
        _ => {}
    });
}

/// Depth limit check for expression recursion (#3031).
///
/// Use `ExprDepthGuard::check()?` inside `maybe_grow_expr_stack` closures that
/// return `Option<T>` and need to bail out at the depth limit. Most call sites
/// do NOT need this — `maybe_grow_expr_stack` already caps stacker heap growth.
/// Use this only when the algorithm itself must stop recursing (e.g., evaluation
/// that returns `None` on indeterminate input).
///
/// Does NOT modify the depth counter — `maybe_grow_expr_stack` handles that.
pub(crate) struct ExprDepthGuard;

impl ExprDepthGuard {
    /// Check if depth limit is reached. Returns `None` if at limit.
    /// Does not modify the depth counter.
    #[inline]
    pub(crate) fn check() -> Option<Self> {
        EXPR_DEPTH.with(|d| {
            if d.get() >= MAX_EXPR_RECURSION_DEPTH {
                None
            } else {
                Some(Self)
            }
        })
    }
}
