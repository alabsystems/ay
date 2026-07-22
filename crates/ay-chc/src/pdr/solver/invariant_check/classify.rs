// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Check if an expression is a disequality between two variables.
    pub(in crate::pdr::solver) fn is_disequality(expr: &ChcExpr, var1: &str, var2: &str) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                    if eq_args.len() == 2 {
                        if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) =
                            (eq_args[0].as_ref(), eq_args[1].as_ref())
                        {
                            return (v1.name == var1 && v2.name == var2)
                                || (v1.name == var2 && v2.name == var1);
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Check if two relations contradict each other (for the same variable pair in same order).
    pub(in crate::pdr::solver) fn relations_contradict(
        rel1: RelationType,
        rel2: RelationType,
    ) -> bool {
        use RelationType::{Ge, Gt, Le, Lt};
        matches!(
            (rel1, rel2),
            (Le | Lt, Gt) | (Gt, Le | Lt) | (Lt, Ge) | (Ge, Lt)
        )
    }

    /// Flip a relation (reverse the variable order).
    pub(in crate::pdr::solver) fn flip_relation(rel: RelationType) -> RelationType {
        use RelationType::{Ge, Gt, Le, Lt};
        match rel {
            Le => Ge,
            Lt => Gt,
            Ge => Le,
            Gt => Lt,
        }
    }

    /// Check if a lemma formula is a relational constraint (a <= b, a >= b, a < b, a > b).
    pub(in crate::pdr::solver) fn is_relational_lemma(formula: &ChcExpr) -> bool {
        Self::extract_relational_constraint(formula).is_some()
    }

    /// Check if a formula is a discovered invariant (relational, bound, or parity).
    /// These are invariants that were discovered proactively and verified for inductiveness.
    pub(in crate::pdr::solver) fn is_discovered_invariant(formula: &ChcExpr) -> bool {
        if Self::is_relational_lemma(formula) {
            return true;
        }

        match formula {
            ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(_), ChcExpr::Int(_)) | (ChcExpr::Int(_), ChcExpr::Var(_)) => {
                        return true;
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        if let ChcExpr::Op(ChcOp::Eq, args) = formula {
            if args.len() == 2 {
                if matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mod, _))
                    && matches!(args[1].as_ref(), ChcExpr::Int(_))
                {
                    return true;
                }
                if matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::Mod, _))
                    && matches!(args[0].as_ref(), ChcExpr::Int(_))
                {
                    return true;
                }
                if Self::is_sum_equality(args[0].as_ref(), args[1].as_ref())
                    || Self::is_sum_equality(args[1].as_ref(), args[0].as_ref())
                {
                    return true;
                }
            }
        }

        false
    }

    /// Check if expr1 is a sum expression and expr2 is a variable.
    /// Recognizes: (= (+ a b) c) or (= (+ (+ a b) c) d) patterns.
    pub(in crate::pdr::solver) fn is_sum_equality(sum_expr: &ChcExpr, var_expr: &ChcExpr) -> bool {
        if !matches!(var_expr, ChcExpr::Var(_)) {
            return false;
        }
        Self::is_sum_expression(sum_expr)
    }

    /// Check if expr is a sum expression (nested Add operations over variables).
    /// No stack guard needed: Add nodes are flattened, recursion depth <= 2.
    pub(in crate::pdr::solver) fn is_sum_expression(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Var(_) => true,
            ChcExpr::Op(ChcOp::Add, args) => args.iter().all(|a| Self::is_sum_expression(a)),
            _ => false,
        }
    }
}
