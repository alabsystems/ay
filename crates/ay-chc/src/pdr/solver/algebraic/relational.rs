// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relational invariant preservation checking.
//!
//! Checks whether `var_i <= var_j` (or `>=`) is preserved by all transitions
//! for a given predicate, using SMT-based verification with frame invariants.

use super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcVar, PredicateId};

/// A pair of variables and their body/head expressions in a transition clause.
///
/// Used by parity-based algebraic proofs that verify relational invariants
/// (e.g., `var_i <= var_j`) are preserved across a transition step.
pub(in crate::pdr::solver) struct VarPairTransition<'a> {
    pub(in crate::pdr::solver) var_i: &'a ChcVar,
    pub(in crate::pdr::solver) var_j: &'a ChcVar,
    pub(in crate::pdr::solver) body_i: &'a ChcExpr,
    pub(in crate::pdr::solver) body_j: &'a ChcExpr,
    pub(in crate::pdr::solver) head_i: &'a ChcExpr,
    pub(in crate::pdr::solver) head_j: &'a ChcExpr,
}

impl<'a> VarPairTransition<'a> {
    fn from_args(
        var_i: &'a ChcVar,
        var_j: &'a ChcVar,
        body_args: &'a [ChcExpr],
        head_args: &'a [ChcExpr],
        idx_i: usize,
        idx_j: usize,
    ) -> Self {
        Self {
            var_i,
            var_j,
            body_i: &body_args[idx_i],
            body_j: &body_args[idx_j],
            head_i: &head_args[idx_i],
            head_j: &head_args[idx_j],
        }
    }

    fn pre_le(&self) -> ChcExpr {
        ChcExpr::le(self.body_i.clone(), self.body_j.clone())
    }

    fn post_gt(&self) -> ChcExpr {
        ChcExpr::gt(self.head_i.clone(), self.head_j.clone())
    }

    fn pre_ge(&self) -> ChcExpr {
        ChcExpr::ge(self.body_i.clone(), self.body_j.clone())
    }

    fn post_lt(&self) -> ChcExpr {
        ChcExpr::lt(self.head_i.clone(), self.head_j.clone())
    }
}

impl PdrSolver {
    fn build_relational_pre_invariants(
        &self,
        predicate: PredicateId,
        body_args: &[ChcExpr],
    ) -> ChcExpr {
        let mut pre_conjuncts: Vec<ChcExpr> = Vec::new();
        if self.frames.len() > 1 {
            for lemma in self.frames[1]
                .lemmas
                .iter()
                .filter(|l| l.predicate == predicate)
            {
                if Self::contains_mod_or_div(&lemma.formula) {
                    continue;
                }
                if let Some(inst) = self.apply_to_args(predicate, &lemma.formula, body_args) {
                    pre_conjuncts.push(inst);
                }
            }
        }
        if pre_conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(pre_conjuncts)
        }
    }

    /// Check if var_i <= var_j is preserved by all transitions for a predicate.
    ///
    /// Returns true if for all transitions:
    ///   body_var_i <= body_var_j AND constraint => head_var_i <= head_var_j
    pub(in crate::pdr::solver) fn is_le_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let (idx_i, idx_j) = match (idx_i, idx_j) {
            (Some(i), Some(j)) => (i, j),
            _ => return false,
        };

        let mut checked_any_self_loop = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any_self_loop = true;

            let pair =
                VarPairTransition::from_args(var_i, var_j, body_args, head_args, idx_i, idx_j);

            let constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Step-2 parity proof: if body_i increments by 2 and body_j is unchanged
            // and both have same mod-2 residue and body_j > body_i, then post_i <= post_j.
            if self.prove_le_preserved_by_step2_parity(predicate, &pair, &constraint) {
                continue;
            }

            let pre_invariants = self.build_relational_pre_invariants(predicate, body_args);
            let pre = pair.pre_le();
            let post_negated = pair.post_gt();

            let query = ChcExpr::and(
                ChcExpr::and(ChcExpr::and(pre_invariants, pre), constraint),
                post_negated,
            );

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Sat(_) | SmtResult::Unknown => {
                    return false;
                }
            }
        }

        if !checked_any_self_loop {
            return false;
        }

        true
    }

    /// Check if var_i >= var_j is preserved by all transitions for a predicate.
    pub(in crate::pdr::solver) fn is_ge_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let (idx_i, idx_j) = match (idx_i, idx_j) {
            (Some(i), Some(j)) => (i, j),
            _ => return false,
        };

        let mut checked_any_self_loop = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any_self_loop = true;

            let pair =
                VarPairTransition::from_args(var_i, var_j, body_args, head_args, idx_i, idx_j);

            let constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Step-2 parity proof (symmetric): body_j increments by 2, body_i unchanged,
            // same mod-2, body_i > body_j => post_i >= post_j.
            if self.prove_ge_preserved_by_step2_parity(predicate, &pair, &constraint) {
                continue;
            }

            let pre_invariants = self.build_relational_pre_invariants(predicate, body_args);
            let pre = pair.pre_ge();
            let post_negated = pair.post_lt();

            let query = ChcExpr::and(
                ChcExpr::and(ChcExpr::and(pre_invariants, pre), constraint),
                post_negated,
            );

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Sat(_) | SmtResult::Unknown => {
                    return false;
                }
            }
        }

        if !checked_any_self_loop {
            return false;
        }

        true
    }
}
