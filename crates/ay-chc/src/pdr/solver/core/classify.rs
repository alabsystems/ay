// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Problem and expression classification functions.
//!
//! Pure-LIA and integer-arithmetic classification for clause surfaces,
//! canonical variable filtering, and per-predicate prop_solver management.

use super::{ChcExpr, ChcOp, ChcSort, ChcVar, Frame, FxHashSet, PredicateId};

/// Filter a formula to only keep conjuncts that reference canonical vars.
pub(in crate::pdr::solver) fn filter_to_canonical_vars(
    formula: &ChcExpr,
    canonical_vars: &[ChcVar],
) -> ChcExpr {
    let names: FxHashSet<&str> = canonical_vars.iter().map(|cv| cv.name.as_str()).collect();
    filter_to_canonical_vars_inner(formula, &names)
}

fn filter_to_canonical_vars_inner(formula: &ChcExpr, canonical_names: &FxHashSet<&str>) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| match formula {
        ChcExpr::Op(ChcOp::And, args) => {
            let filtered: Vec<ChcExpr> = args
                .iter()
                .map(|a| filter_to_canonical_vars_inner(a, canonical_names))
                .filter(|e| *e != ChcExpr::Bool(true))
                .collect();
            ChcExpr::and_all(filtered)
        }
        _ => {
            let vars = formula.vars();
            let all_canonical = vars
                .iter()
                .all(|v| canonical_names.contains(v.name.as_str()));
            if all_canonical || vars.is_empty() {
                formula.clone()
            } else {
                ChcExpr::Bool(true)
            }
        }
    })
}

/// Get or create a per-predicate prop_solver with full lemma backfill (#6358).
///
/// Free function for split-borrow compatibility: takes `prop_solvers` and `frames`
/// as separate arguments so the caller can hold other `PdrSolver` field borrows
/// (e.g., `self.problem.clauses()`) without conflicting.
///
/// Uses `LruSolverMap` for bounded memory (#6554). When the map is at capacity,
/// the least-recently-used solver is evicted and will be recreated on demand.
pub(in crate::pdr::solver) fn ensure_prop_solver_split<'a>(
    prop_solvers: &'a mut super::super::caches::LruSolverMap<
        PredicateId,
        super::super::prop_solver::PredicatePropSolver,
    >,
    frames: &[Frame],
    pred: PredicateId,
) -> &'a mut super::super::prop_solver::PredicatePropSolver {
    prop_solvers.get_or_insert_with(pred, || {
        let mut ps = super::super::prop_solver::PredicatePropSolver::new();
        ps.finalize();
        // Backfill: assert all existing frame lemmas for this predicate.
        for (level, frame) in frames.iter().enumerate() {
            for lemma in &frame.lemmas {
                if lemma.predicate == pred {
                    ps.assert_lemma_at_level(&lemma.formula, level);
                }
            }
        }
        ps
    })
}

pub(super) fn sort_is_pure_lia(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::Real)
}

pub(super) fn op_is_pure_lia(op: &ChcOp) -> bool {
    matches!(
        op,
        ChcOp::Not
            | ChcOp::And
            | ChcOp::Or
            | ChcOp::Implies
            | ChcOp::Iff
            | ChcOp::Add
            | ChcOp::Sub
            | ChcOp::Mul
            | ChcOp::Neg
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
    )
}

pub(super) fn expr_is_pure_lia(expr: &ChcExpr) -> bool {
    // scan_features walks the ENTIRE subtree once — O(n).
    // If any non-LIA feature is found anywhere in the tree, reject early.
    let features = expr.scan_features();
    if features.has_ite || features.has_mod_or_div || features.has_array_ops || features.has_uf_apps
    {
        return false;
    }
    // Features confirmed clean for the whole subtree. Now check op/sort
    // compatibility without re-scanning (avoids O(n²) repeated walks).
    expr_is_pure_lia_structural(expr)
}

/// Structural LIA check: verifies every op and variable sort is LIA-compatible.
/// Assumes scan_features() was already called on the root and rejected non-LIA
/// features (ITE, mod/div, arrays, UF). This function only checks op/sort, never
/// re-calls scan_features, making the total cost O(n) instead of O(n²).
fn expr_is_pure_lia_structural(expr: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) => true,
        ChcExpr::BitVec(_, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => false,
        ChcExpr::Var(v) => sort_is_pure_lia(&v.sort),
        ChcExpr::Op(op, args) => {
            op_is_pure_lia(op) && args.iter().all(|arg| expr_is_pure_lia_structural(arg))
        }
        ChcExpr::PredicateApp(_, _, args) => {
            args.iter().all(|arg| expr_is_pure_lia_structural(arg))
        }
        ChcExpr::FuncApp(_, sort, args) => {
            sort_is_pure_lia(sort) && args.iter().all(|arg| expr_is_pure_lia_structural(arg))
        }
    })
}

pub(super) fn clause_is_pure_lia(clause: &crate::HornClause) -> bool {
    clause.body.constraint.iter().all(expr_is_pure_lia)
        && clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter())
            .all(expr_is_pure_lia)
        && match &clause.head {
            crate::ClauseHead::Predicate(_, args) => args.iter().all(expr_is_pure_lia),
            crate::ClauseHead::False => true,
        }
}

pub(super) fn clause_has_ite(clause: &crate::HornClause) -> bool {
    clause
        .body
        .constraint
        .iter()
        .any(|expr| expr.scan_features().has_ite)
        || clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter())
            .any(|expr| expr.scan_features().has_ite)
        || match &clause.head {
            crate::ClauseHead::Predicate(_, args) => {
                args.iter().any(|expr| expr.scan_features().has_ite)
            }
            crate::ClauseHead::False => false,
        }
}

/// Check whether an expression is integer arithmetic (LIA + ITE + mod/div).
/// Allows `ite` and `mod`/`div` over integers but still rejects BV, arrays, and UF.
/// This is a weaker condition than `expr_is_pure_lia` — problems classified as
/// `problem_is_integer_arithmetic = true` can use incremental PDR (#5970).
pub(super) fn expr_is_integer_arithmetic(expr: &ChcExpr) -> bool {
    // scan_features walks the ENTIRE subtree once — O(n).
    let features = expr.scan_features();
    // Reject BV/arrays/UF — these cause incremental incompleteness
    if features.has_array_ops || features.has_uf_apps {
        return false;
    }
    // Allow ITE and mod/div — standard integer operations handled by the
    // incremental SMT context via boolean reasoning and theory lemmas.
    // Delegate to structural check to avoid O(n²) repeated scan_features.
    expr_is_integer_arithmetic_structural(expr)
}

/// Structural integer-arithmetic check: LIA ops + ITE + mod/div allowed.
/// Assumes scan_features() was already called on the root and rejected
/// arrays/UF. Only checks op/sort compatibility — never re-calls scan_features.
fn expr_is_integer_arithmetic_structural(expr: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) => true,
        ChcExpr::BitVec(_, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => false,
        ChcExpr::Var(v) => sort_is_pure_lia(&v.sort),
        ChcExpr::Op(op, args) => {
            (op_is_pure_lia(op) || matches!(op, ChcOp::Ite | ChcOp::Mod | ChcOp::Div))
                && args
                    .iter()
                    .all(|arg| expr_is_integer_arithmetic_structural(arg))
        }
        ChcExpr::PredicateApp(_, _, args) => args
            .iter()
            .all(|arg| expr_is_integer_arithmetic_structural(arg)),
        ChcExpr::FuncApp(_, sort, args) => {
            sort_is_pure_lia(sort)
                && args
                    .iter()
                    .all(|arg| expr_is_integer_arithmetic_structural(arg))
        }
    })
}

pub(super) fn clause_is_integer_arithmetic(clause: &crate::HornClause) -> bool {
    clause
        .body
        .constraint
        .iter()
        .all(expr_is_integer_arithmetic)
        && clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter())
            .all(expr_is_integer_arithmetic)
        && match &clause.head {
            crate::ClauseHead::Predicate(_, args) => args.iter().all(expr_is_integer_arithmetic),
            crate::ClauseHead::False => true,
        }
}

/// Check whether a sort is BV-compatible (Bool or BitVec).
///
/// Used by `clause_is_bitvector_only` to detect problems where incremental
/// PDR is safe (#8205). Bool is included because BV problems naturally use
/// Bool for control flow and comparison results.
pub(super) fn sort_is_bitvector_compatible(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::BitVec(_))
}

/// Check whether an expression uses only BV-compatible sorts and operations.
///
/// Returns `true` when the expression contains only Bool constants, BitVec
/// constants/variables, and operations over those sorts. Int/Real/Array/UF
/// sorts and their operations cause rejection.
pub(super) fn expr_is_bitvector_only(expr: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Bool(_) => true,
        ChcExpr::BitVec(_, _) => true,
        ChcExpr::Int(_) | ChcExpr::Real(_, _) => false,
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) | ChcExpr::ConstArray(_, _) => {
            false
        }
        ChcExpr::Var(v) => sort_is_bitvector_compatible(&v.sort),
        ChcExpr::Op(_, args) => args.iter().all(|arg| expr_is_bitvector_only(arg)),
        ChcExpr::PredicateApp(_, _, args) => args.iter().all(|arg| expr_is_bitvector_only(arg)),
        ChcExpr::FuncApp(_, sort, args) => {
            sort_is_bitvector_compatible(sort) && args.iter().all(|arg| expr_is_bitvector_only(arg))
        }
    })
}

/// Check whether a clause uses only BV-compatible sorts (#8205).
///
/// Returns `true` when all predicate arguments, constraints, and head
/// arguments use only Bool/BitVec sorts. Used to gate incremental PDR
/// for BV-only HWMCC workloads where the #6583 LIA regression doesn't apply.
pub(super) fn clause_is_bitvector_only(clause: &crate::HornClause) -> bool {
    clause.body.constraint.iter().all(expr_is_bitvector_only)
        && clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter())
            .all(expr_is_bitvector_only)
        && match &clause.head {
            crate::ClauseHead::Predicate(_, args) => args.iter().all(expr_is_bitvector_only),
            crate::ClauseHead::False => true,
        }
}
