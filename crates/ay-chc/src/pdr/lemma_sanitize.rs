// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lemma sanitization at frame admission (#task-18 crash class).
//!
//! PDR on the reve/llreve/rust-horn family accumulates GIANT compound lemmas
//! whose `Or` nodes contain trivially-false atoms (e.g. `(>= x (+ x 1))`) and
//! whose `And` nodes contain trivially-true conjuncts. The bloat eventually
//! kills `push_lemmas` (SIGSEGV/SIGBUS). This module performs an EXACT
//! simplification pass at lemma admission:
//!
//! - `false ∨ X ≡ X` — drop trivially-false disjuncts inside `Or`
//! - `true ∧ X ≡ X` — drop trivially-true conjuncts inside `And`
//! - collapse empty/singleton connectives, fold `Not` over constants
//!
//! Triviality detection uses a small LINEAR DIFFERENCE evaluator over Int
//! atoms (`<`, `<=`, `>`, `>=`, `=`, `!=`): normalize `lhs - rhs` into a
//! coefficient map over variables plus a constant by walking `+`, `-`, `Neg`,
//! `*const`, `Int`, `Var` — bailing on ANY other shape. Only when every
//! variable coefficient cancels to zero is the atom decided, by comparing the
//! residual constant against 0 per the operator.
//!
//! EXACTNESS RULE: an atom is only rewritten when it is PROVABLY constant
//! under this evaluator; anything else stays untouched. Every rewrite is a
//! semantic equivalence, so sanitization is sound by construction.
//!
//! Kill-switch: `AY_PDR_LEMMA_SANITIZE=0` disables (default ON).

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::expr::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, ChcVar, MAX_EXPR_RECURSION_DEPTH,
};

/// Soft node-count cap for admitted lemmas. Exceeding it only logs a warning
/// in this increment (observability, not enforcement).
pub(crate) const LEMMA_NODE_SOFT_CAP: usize = 50_000;

/// Kill-switch: `AY_PDR_LEMMA_SANITIZE=0` disables sanitization (default ON).
pub(crate) fn lemma_sanitize_enabled() -> bool {
    // B27: CLI-owned (--chc-no-pdr-lemma-sanitize); env retired.
    crate::ab_switches::get().pdr_lemma_sanitize
}

/// Testable core of the kill-switch parse: only the literal "0" disables.
#[cfg(test)]
fn lemma_sanitize_enabled_for(value: Option<&str>) -> bool {
    !matches!(value, Some("0"))
}

/// Sanitize a lemma formula. Returns the (possibly identical) sanitized expr.
///
/// Exact simplification only — the result is semantically equivalent to the
/// input. When nothing is rewritten the input is returned structurally
/// unchanged (Arc-sharing preserved).
#[cfg_attr(not(test), allow(dead_code))] // test-facing wrapper over sanitize_lemma_opt
pub(crate) fn sanitize_lemma(expr: &ChcExpr) -> ChcExpr {
    sanitize_lemma_opt(expr).unwrap_or_else(|| expr.clone())
}

/// Like [`sanitize_lemma`] but returns `None` when the formula is already
/// clean (no rewrite applied), letting callers skip hash recomputation.
pub(crate) fn sanitize_lemma_opt(expr: &ChcExpr) -> Option<ChcExpr> {
    let rewritten = sanitize_rec(expr, 0)?;
    // Constant-fold the rewritten formula via the existing exact simplifier.
    // Only runs on CHANGED lemmas, so already-clean lemmas stay structurally
    // untouched (no-op guarantee).
    Some(rewritten.simplify_constants())
}

/// Recursive sanitization over the Boolean skeleton (`And`/`Or`/`Not`).
/// Returns `None` when the subtree is unchanged.
fn sanitize_rec(expr: &ChcExpr, depth: usize) -> Option<ChcExpr> {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(op @ (ChcOp::And | ChcOp::Or), args) => {
            let is_and = matches!(op, ChcOp::And);
            let mut changed = false;
            let mut new_args: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
            for arg in args {
                let child = match sanitize_rec(arg, depth + 1) {
                    Some(c) => {
                        changed = true;
                        Arc::new(c)
                    }
                    None => Arc::clone(arg),
                };
                match child.as_ref() {
                    // Absorbing element: false ∧ X ≡ false; true ∨ X ≡ true.
                    ChcExpr::Bool(b) if *b != is_and => {
                        return Some(ChcExpr::Bool(!is_and));
                    }
                    // Identity element: true ∧ X ≡ X; false ∨ X ≡ X — drop.
                    ChcExpr::Bool(_) => {
                        changed = true;
                    }
                    _ => new_args.push(child),
                }
            }
            if !changed {
                return None;
            }
            Some(match new_args.len() {
                // Empty connective collapses to its identity element.
                0 => ChcExpr::Bool(is_and),
                1 => new_args.swap_remove(0).as_ref().clone(),
                _ => ChcExpr::Op(*op, new_args),
            })
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            match sanitize_rec(&args[0], depth + 1) {
                Some(ChcExpr::Bool(b)) => Some(ChcExpr::Bool(!b)),
                Some(c) => Some(ChcExpr::not(c)),
                // Fold a pre-existing constant under Not even when the child
                // itself needed no rewriting.
                None => match args[0].as_ref() {
                    ChcExpr::Bool(b) => Some(ChcExpr::Bool(!*b)),
                    _ => None,
                },
            }
        }
        ChcExpr::Op(
            op @ (ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge | ChcOp::Eq | ChcOp::Ne),
            args,
        ) if args.len() == 2 => atom_trivial_truth(*op, &args[0], &args[1]).map(ChcExpr::Bool),
        _ => None,
    })
}

/// Decide an Int comparison atom that is PROVABLY constant under the linear
/// difference evaluator. Returns `None` unless `lhs - rhs` normalizes to a
/// pure constant (all variable coefficients cancel to zero).
fn atom_trivial_truth(op: ChcOp, lhs: &ChcExpr, rhs: &ChcExpr) -> Option<bool> {
    let mut coeffs: FxHashMap<ChcVar, i128> = FxHashMap::default();
    let mut constant: i128 = 0;
    accumulate_linear(lhs, 1, &mut coeffs, &mut constant, 0)?;
    accumulate_linear(rhs, -1, &mut coeffs, &mut constant, 0)?;
    if coeffs.values().any(|&c| c != 0) {
        return None;
    }
    // lhs - rhs == constant; decide `lhs OP rhs` as `constant OP 0`.
    Some(match op {
        ChcOp::Lt => constant < 0,
        ChcOp::Le => constant <= 0,
        ChcOp::Gt => constant > 0,
        ChcOp::Ge => constant >= 0,
        ChcOp::Eq => constant == 0,
        ChcOp::Ne => constant != 0,
        _ => return None,
    })
}

/// Strict linear walker: accumulate `mult * expr` into `(coeffs, constant)`.
///
/// Handles ONLY `Int`, Int-sorted `Var`, `+`, `-` (n-ary), unary `Neg`, and
/// `*` by an integer constant. Anything else — including the BvToInt
/// ITE/Mod see-throughs that `walk_linear_expr` permits — returns `None`
/// (atom not provably constant). All arithmetic is checked `i128`.
fn accumulate_linear(
    expr: &ChcExpr,
    mult: i128,
    coeffs: &mut FxHashMap<ChcVar, i128>,
    constant: &mut i128,
    depth: usize,
) -> Option<()> {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Int(n) => {
            *constant = constant.checked_add(mult.checked_mul(i128::from(*n))?)?;
            Some(())
        }
        ChcExpr::Var(v) if matches!(v.sort, ChcSort::Int) => {
            let entry = coeffs.entry(v.clone()).or_insert(0);
            *entry = entry.checked_add(mult)?;
            Some(())
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            for arg in args {
                accumulate_linear(arg, mult, coeffs, constant, depth + 1)?;
            }
            Some(())
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            accumulate_linear(&args[0], mult, coeffs, constant, depth + 1)?;
            let neg = mult.checked_neg()?;
            for arg in &args[1..] {
                accumulate_linear(arg, neg, coeffs, constant, depth + 1)?;
            }
            Some(())
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            accumulate_linear(&args[0], mult.checked_neg()?, coeffs, constant, depth + 1)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            let (c, other) = match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Int(c), other) => (*c, other),
                (other, ChcExpr::Int(c)) => (*c, other),
                _ => return None,
            };
            accumulate_linear(
                other,
                mult.checked_mul(i128::from(c))?,
                coeffs,
                constant,
                depth + 1,
            )
        }
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ivar(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    fn bvar(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
    }

    // --- linear triviality evaluator ---

    #[test]
    fn ge_x_x_plus_1_is_false() {
        // (>= x (+ x 1)) => x - (x+1) = -1 => -1 >= 0 => FALSE
        let x = ivar("x");
        let atom = ChcExpr::ge(x.clone(), ChcExpr::add(x, ChcExpr::int(1)));
        assert_eq!(sanitize_lemma(&atom), ChcExpr::Bool(false));
    }

    #[test]
    fn le_a_minus_1a_le_neg2_is_false() {
        // (<= (- a (* 1 a)) -2) => 0 <= -2 => FALSE
        let a = ivar("a");
        let lhs = ChcExpr::sub(a.clone(), ChcExpr::mul(ChcExpr::int(1), a));
        let atom = ChcExpr::le(lhs, ChcExpr::int(-2));
        assert_eq!(sanitize_lemma(&atom), ChcExpr::Bool(false));
    }

    #[test]
    fn ge_x_x_is_true() {
        let x = ivar("x");
        let atom = ChcExpr::ge(x.clone(), x);
        assert_eq!(sanitize_lemma(&atom), ChcExpr::Bool(true));
    }

    #[test]
    fn eq_and_ne_constant_difference() {
        let x = ivar("x");
        // (= (+ x 1) (+ 1 x)) => 0 = 0 => TRUE
        let eq = ChcExpr::eq(
            ChcExpr::add(x.clone(), ChcExpr::int(1)),
            ChcExpr::add(ChcExpr::int(1), x.clone()),
        );
        assert_eq!(sanitize_lemma(&eq), ChcExpr::Bool(true));
        // (= x (+ x 1)) => -1 = 0 => FALSE
        let ne = ChcExpr::eq(x.clone(), ChcExpr::add(x, ChcExpr::int(1)));
        assert_eq!(sanitize_lemma(&ne), ChcExpr::Bool(false));
    }

    #[test]
    fn nonlinear_atom_untouched() {
        // (>= (* x x) 0) — true over Int, but NOT decidable by the linear
        // evaluator; must stay untouched per the exactness rule.
        let x = ivar("x");
        let atom = ChcExpr::ge(ChcExpr::mul(x.clone(), x), ChcExpr::int(0));
        assert_eq!(sanitize_lemma(&atom), atom);
    }

    #[test]
    fn non_constant_atom_untouched() {
        // (>= x 0) depends on x — untouched.
        let atom = ChcExpr::ge(ivar("x"), ChcExpr::int(0));
        assert_eq!(sanitize_lemma(&atom), atom);
    }

    #[test]
    fn unknown_shape_untouched() {
        // Bool-sorted equality: the walker bails on non-Int leaves.
        let atom = ChcExpr::eq(bvar("p"), bvar("p"));
        assert_eq!(sanitize_lemma(&atom), atom);
    }

    // --- sanitize_lemma shape tests ---

    #[test]
    fn or_drops_trivially_false_disjunct() {
        // (or (>= x (+ x 1)) (> y 0)) => (> y 0)  [singleton collapse]
        let x = ivar("x");
        let keep = ChcExpr::gt(ivar("y"), ChcExpr::int(0));
        let lemma = ChcExpr::or(
            ChcExpr::ge(x.clone(), ChcExpr::add(x, ChcExpr::int(1))),
            keep.clone(),
        );
        assert_eq!(sanitize_lemma(&lemma), keep);
    }

    #[test]
    fn or_keeps_multiple_survivors() {
        let x = ivar("x");
        let k1 = ChcExpr::gt(ivar("y"), ChcExpr::int(0));
        let k2 = ChcExpr::lt(ivar("z"), ChcExpr::int(5));
        let lemma = ChcExpr::or_vec(vec![
            k1.clone(),
            ChcExpr::ge(x.clone(), ChcExpr::add(x, ChcExpr::int(1))),
            k2.clone(),
        ]);
        assert_eq!(sanitize_lemma(&lemma), ChcExpr::or(k1, k2));
    }

    #[test]
    fn and_drops_trivially_true_conjunct() {
        // (and (>= x x) (> y 0)) => (> y 0)
        let x = ivar("x");
        let keep = ChcExpr::gt(ivar("y"), ChcExpr::int(0));
        let lemma = ChcExpr::and(ChcExpr::ge(x.clone(), x), keep.clone());
        assert_eq!(sanitize_lemma(&lemma), keep);
    }

    #[test]
    fn nested_or_inside_and() {
        // (and (or FALSE_ATOM (> y 0)) TRUE_ATOM) => (> y 0)
        let x = ivar("x");
        let keep = ChcExpr::gt(ivar("y"), ChcExpr::int(0));
        let false_atom = ChcExpr::ge(x.clone(), ChcExpr::add(x.clone(), ChcExpr::int(1)));
        let true_atom = ChcExpr::ge(x.clone(), x);
        let lemma = ChcExpr::and(ChcExpr::or(false_atom, keep.clone()), true_atom);
        assert_eq!(sanitize_lemma(&lemma), keep);
    }

    #[test]
    fn or_of_all_false_collapses_to_false() {
        let x = ivar("x");
        let f1 = ChcExpr::ge(x.clone(), ChcExpr::add(x.clone(), ChcExpr::int(1)));
        let f2 = ChcExpr::gt(ChcExpr::int(0), ChcExpr::int(3));
        let lemma = ChcExpr::or(f1, f2);
        assert_eq!(sanitize_lemma(&lemma), ChcExpr::Bool(false));
        // Dually, true disjunct absorbs the whole Or.
        let t = ChcExpr::ge(x.clone(), x);
        let lemma2 = ChcExpr::or(ChcExpr::gt(ivar("y"), ChcExpr::int(0)), t);
        assert_eq!(sanitize_lemma(&lemma2), ChcExpr::Bool(true));
    }

    #[test]
    fn not_over_decided_atom_folds() {
        // (not (>= x x)) => (not true) => false
        let x = ivar("x");
        let lemma = ChcExpr::not(ChcExpr::ge(x.clone(), x));
        assert_eq!(sanitize_lemma(&lemma), ChcExpr::Bool(false));
    }

    #[test]
    fn noop_on_clean_lemma() {
        // Already-clean lemma: structurally equal result, and the opt API
        // reports "unchanged".
        let lemma = ChcExpr::or(
            ChcExpr::ge(ivar("x"), ChcExpr::int(0)),
            ChcExpr::and(
                ChcExpr::lt(ivar("y"), ivar("z")),
                ChcExpr::eq(ivar("w"), ChcExpr::int(7)),
            ),
        );
        assert!(sanitize_lemma_opt(&lemma).is_none());
        assert_eq!(sanitize_lemma(&lemma), lemma);
    }

    #[test]
    fn kill_switch_parse() {
        assert!(lemma_sanitize_enabled_for(None));
        assert!(lemma_sanitize_enabled_for(Some("1")));
        assert!(lemma_sanitize_enabled_for(Some("")));
        assert!(!lemma_sanitize_enabled_for(Some("0")));
    }

    #[test]
    fn overflow_bails_untouched() {
        // i64::MAX * 3 overflows the i64 atom range but not i128; a genuine
        // i128 overflow must bail. Build (>= (* BIG (* BIG x)) 0)-ish shape
        // via nested constant Muls so checked_mul fails.
        let x = ivar("x");
        let big = ChcExpr::int(i64::MAX);
        let inner = ChcExpr::mul(big.clone(), x);
        let nested = ChcExpr::mul(
            big.clone(),
            ChcExpr::mul(big.clone(), ChcExpr::mul(big, inner)),
        );
        let atom = ChcExpr::ge(nested.clone(), nested);
        // lhs == rhs structurally; coefficients would cancel, but the walker
        // overflows first and must leave the atom untouched.
        assert_eq!(sanitize_lemma(&atom), atom);
    }
}
