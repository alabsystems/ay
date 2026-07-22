// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parity-based algebraic proofs for relational invariants.
//!
//! Methods for checking mod-2 parity lemmas, step-2 parity preservation,
//! and incoming transition enforcement of relational bounds.

use super::PdrSolver;
use super::VarPairTransition;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, PredicateId};

impl PdrSolver {
    pub(in crate::pdr::solver) fn frame1_mod2_remainder(
        &self,
        predicate: PredicateId,
        var_name: &str,
    ) -> Option<i128> {
        if self.frames.len() <= 1 {
            return None;
        }

        for lemma in self.frames[1]
            .lemmas
            .iter()
            .filter(|l| l.predicate == predicate)
        {
            if let Some(rem) = Self::extract_mod2_remainder(&lemma.formula, var_name) {
                return Some(rem);
            }
        }
        None
    }

    pub(in crate::pdr::solver) fn extract_mod2_remainder(
        lemma: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        fn matches_mod2(expr: &ChcExpr, var_name: &str) -> bool {
            match expr {
                ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                    matches!(
                        (&*args[0], &*args[1]),
                        (ChcExpr::Var(v), ChcExpr::Int(2)) if v.name == var_name
                    )
                }
                _ => false,
            }
        }

        match lemma {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                if matches_mod2(&args[0], var_name) {
                    if let ChcExpr::Int(rem) = &*args[1] {
                        return Some(*rem);
                    }
                }
                if matches_mod2(&args[1], var_name) {
                    if let ChcExpr::Int(rem) = &*args[0] {
                        return Some(*rem);
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub(in crate::pdr::solver) fn constraint_contains_strict_gt(
        constraint: &ChcExpr,
        lhs: &str,
        rhs: &str,
    ) -> bool {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .any(|arg| Self::constraint_contains_strict_gt(arg, lhs, rhs)),
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                Self::is_var_expr(&args[0], lhs) && Self::is_var_expr(&args[1], rhs)
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                // rhs < lhs
                Self::is_var_expr(&args[0], rhs) && Self::is_var_expr(&args[1], lhs)
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match &*args[0] {
                ChcExpr::Op(ChcOp::Le, le_args) if le_args.len() == 2 => {
                    // not (lhs <= rhs) <=> lhs > rhs
                    Self::is_var_expr(&le_args[0], lhs) && Self::is_var_expr(&le_args[1], rhs)
                }
                _ => false,
            },
            _ => false,
        }
    }

    pub(in crate::pdr::solver) fn prove_le_preserved_by_step2_parity(
        &self,
        predicate: PredicateId,
        pair: &VarPairTransition<'_>,
        constraint: &ChcExpr,
    ) -> bool {
        let (ChcExpr::Var(bi), ChcExpr::Var(bj)) = (pair.body_i, pair.body_j) else {
            return false;
        };

        let rem_i = match self.frame1_mod2_remainder(predicate, &pair.var_i.name) {
            Some(r) => r,
            None => return false,
        };
        let rem_j = match self.frame1_mod2_remainder(predicate, &pair.var_j.name) {
            Some(r) => r,
            None => return false,
        };
        if rem_i != rem_j {
            return false;
        }

        // Require head_j == body_j (unchanged).
        let head_j_offset = match Self::extract_addition_offset(pair.head_j, &bj.name) {
            Some(off) => Some(off),
            None => match pair.head_j {
                ChcExpr::Var(hj) if hj.name == bj.name => Some(0),
                _ => None,
            },
        };
        if head_j_offset != Some(0) {
            return false;
        }

        // Require head_i = body_i + 2, either directly in the head or via an equality in the body.
        let head_i_offset = match Self::extract_addition_offset(pair.head_i, &bi.name) {
            Some(off) => Some(off),
            None => match pair.head_i {
                ChcExpr::Var(hi) => Self::find_offset_in_constraint(constraint, &bi.name, &hi.name),
                _ => None,
            },
        };
        if head_i_offset != Some(2) {
            return false;
        }

        if !Self::constraint_contains_strict_gt(constraint, &bj.name, &bi.name) {
            return false;
        }

        true
    }

    pub(in crate::pdr::solver) fn prove_ge_preserved_by_step2_parity(
        &self,
        predicate: PredicateId,
        pair: &VarPairTransition<'_>,
        constraint: &ChcExpr,
    ) -> bool {
        let (ChcExpr::Var(bi), ChcExpr::Var(bj)) = (pair.body_i, pair.body_j) else {
            return false;
        };

        let rem_i = match self.frame1_mod2_remainder(predicate, &pair.var_i.name) {
            Some(r) => r,
            None => return false,
        };
        let rem_j = match self.frame1_mod2_remainder(predicate, &pair.var_j.name) {
            Some(r) => r,
            None => return false,
        };
        if rem_i != rem_j {
            return false;
        }

        // Require head_i == body_i (unchanged).
        let head_i_offset = match Self::extract_addition_offset(pair.head_i, &bi.name) {
            Some(off) => Some(off),
            None => match pair.head_i {
                ChcExpr::Var(hi) if hi.name == bi.name => Some(0),
                _ => None,
            },
        };
        if head_i_offset != Some(0) {
            return false;
        }

        // Require head_j = body_j + 2.
        let head_j_offset = match Self::extract_addition_offset(pair.head_j, &bj.name) {
            Some(off) => Some(off),
            None => match pair.head_j {
                ChcExpr::Var(hj) => Self::find_offset_in_constraint(constraint, &bj.name, &hj.name),
                _ => None,
            },
        };
        if head_j_offset != Some(2) {
            return false;
        }

        if !Self::constraint_contains_strict_gt(constraint, &bi.name, &bj.name) {
            return false;
        }

        true
    }

    /// Check whether all incoming (cross-predicate) transitions into `target_pred`
    /// enforce `arg[idx_i] <= arg[idx_j]`, under the current frame-1 invariants of the
    /// source predicate.
    pub(in crate::pdr::solver) fn is_le_enforced_by_incoming_transitions(
        &mut self,
        target_pred: PredicateId,
        idx_i: usize,
        idx_j: usize,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(target_pred) {
            Some(v) => v.to_vec(),
            None => return false,
        };
        if idx_i >= canonical_vars.len() || idx_j >= canonical_vars.len() {
            return false;
        }

        let mut has_incoming = false;

        for clause in self.problem.clauses_defining(target_pred) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];

            // Only consider cross-predicate transitions.
            if *body_pred == target_pred {
                continue;
            }

            has_incoming = true;

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let src_invariants = if self.frames.len() > 1 {
                // Avoid feeding `mod` constraints into SMT during propagation checks; these
                // queries are just for inferring linear relationships from incoming edges.
                let mut conjuncts: Vec<ChcExpr> = Vec::new();
                for lemma in self.frames[1]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == *body_pred)
                {
                    if Self::contains_mod_or_div(&lemma.formula) {
                        continue;
                    }
                    if let Some(inst) = self.apply_to_args(*body_pred, &lemma.formula, body_args) {
                        conjuncts.push(inst);
                    }
                }
                if conjuncts.is_empty() {
                    ChcExpr::Bool(true)
                } else {
                    ChcExpr::and_all(conjuncts)
                }
            } else {
                ChcExpr::Bool(true)
            };

            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];
            let violates = ChcExpr::gt(head_i.clone(), head_j.clone());

            let query = ChcExpr::and(ChcExpr::and(src_invariants, clause_constraint), violates);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Sat(_) | SmtResult::Unknown => return false,
            }
        }

        has_incoming
    }

    /// Check whether all incoming (cross-predicate) transitions into `target_pred`
    /// enforce `arg[idx_i] >= arg[idx_j]`, under the current frame-1 invariants of the
    /// source predicate.
    pub(in crate::pdr::solver) fn is_ge_enforced_by_incoming_transitions(
        &mut self,
        target_pred: PredicateId,
        idx_i: usize,
        idx_j: usize,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(target_pred) {
            Some(v) => v.to_vec(),
            None => return false,
        };
        if idx_i >= canonical_vars.len() || idx_j >= canonical_vars.len() {
            return false;
        }

        let mut has_incoming = false;

        for clause in self.problem.clauses_defining(target_pred) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];

            if *body_pred == target_pred {
                continue;
            }

            has_incoming = true;

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let src_invariants = if self.frames.len() > 1 {
                let mut conjuncts: Vec<ChcExpr> = Vec::new();
                for lemma in self.frames[1]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == *body_pred)
                {
                    if Self::contains_mod_or_div(&lemma.formula) {
                        continue;
                    }
                    if let Some(inst) = self.apply_to_args(*body_pred, &lemma.formula, body_args) {
                        conjuncts.push(inst);
                    }
                }
                if conjuncts.is_empty() {
                    ChcExpr::Bool(true)
                } else {
                    ChcExpr::and_all(conjuncts)
                }
            } else {
                ChcExpr::Bool(true)
            };

            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];
            let violates = ChcExpr::lt(head_i.clone(), head_j.clone());

            let query = ChcExpr::and(ChcExpr::and(src_invariants, clause_constraint), violates);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Sat(_) | SmtResult::Unknown => return false,
            }
        }

        has_incoming
    }
}
