// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;
use std::sync::Arc;

pub(super) mod bit_level;
use bit_level::extract_bv_equality;
mod inductive;
mod lemma_simplify;

impl PdrSolver {
    /// The blocking formula is `NOT(lemma)`. We recover the lemma, simplify it,
    /// and negate back.
    pub(in crate::pdr::solver) fn try_simplify_bv_native_lemma(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> Option<ChcExpr> {
        lemma_simplify::try_simplify_bv_native_lemma(self, blocking_formula, predicate, level)
    }

    pub(in crate::pdr::solver) fn generalize_bv_inductive(
        &mut self,
        state: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> ChcExpr {
        inductive::generalize_bv_inductive(self, state, predicate, level)
    }
}

fn extract_bv_distinct_var(expr: &ChcExpr) -> Option<(ChcVar, u32)> {
    match expr {
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::BitVec(_, w), ChcExpr::Var(v))
                | (ChcExpr::Var(v), ChcExpr::BitVec(_, w))
                    if matches!(v.sort, ChcSort::BitVec(_)) =>
                {
                    Some((v.clone(), *w))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn collect_disjuncts(expr: &ChcExpr) -> Vec<ChcExpr> {
    match expr {
        ChcExpr::Op(ChcOp::Or, args) => args.iter().map(|a| a.as_ref().clone()).collect(),
        _ => vec![expr.clone()],
    }
}

fn atom_contains_bv_constant(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::BitVec(_, _) => true,
        ChcExpr::Op(_, args) => args.iter().any(|a| atom_contains_bv_constant(a)),
        _ => false,
    }
}

fn try_weaken_bv_equality_to_nonzero(expr: &ChcExpr) -> Option<ChcExpr> {
    if let ChcExpr::Op(ChcOp::Eq, args) = expr {
        if args.len() != 2 {
            return None;
        }
        let (var_expr, bv_val, bv_width) = match (args[0].as_ref(), args[1].as_ref()) {
            (ChcExpr::Var(_), ChcExpr::BitVec(val, width)) => {
                (args[0].as_ref().clone(), *val, *width)
            }
            (ChcExpr::BitVec(val, width), ChcExpr::Var(_)) => {
                (args[1].as_ref().clone(), *val, *width)
            }
            _ => return None,
        };

        let one = ChcExpr::BitVec(1, bv_width);
        let is_signed_positive =
            bv_width > 0 && bv_width <= 64 && bv_val != 0 && (bv_val >> (bv_width - 1)) & 1 == 0;

        if is_signed_positive {
            Some(ChcExpr::Op(
                ChcOp::BvSLe,
                vec![Arc::new(one), Arc::new(var_expr)],
            ))
        } else {
            Some(ChcExpr::not(ChcExpr::Op(
                ChcOp::BvSLe,
                vec![Arc::new(one), Arc::new(var_expr)],
            )))
        }
    } else {
        None
    }
}
