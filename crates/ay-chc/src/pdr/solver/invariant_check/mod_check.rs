// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Apply modular equality substitution to simplify the error constraint.
    ///
    /// If the frame contains an invariant `(= (mod X k) Y)`, substitute all occurrences
    /// of `(mod X k)` in the error constraint with `Y`. This allows the SMT solver to
    /// reason about the simplified formula without dealing with `mod` expressions.
    ///
    /// Returns `Some(simplified)` if any substitutions were applied, `None` otherwise.
    pub(super) fn apply_mod_substitution(
        error_constraint: &ChcExpr,
        lemmas: &[Lemma],
        pred: PredicateId,
    ) -> Option<ChcExpr> {
        let mut pairs: Vec<(ChcExpr, ChcExpr)> = Vec::new();

        for lemma in lemmas {
            if lemma.predicate != pred {
                continue;
            }
            if let ChcExpr::Op(ChcOp::Eq, args) = &lemma.formula {
                if args.len() == 2 {
                    if let ChcExpr::Op(ChcOp::Mod, _) = args[0].as_ref() {
                        pairs.push((args[0].as_ref().clone(), args[1].as_ref().clone()));
                    }
                    if let ChcExpr::Op(ChcOp::Mod, _) = args[1].as_ref() {
                        pairs.push((args[1].as_ref().clone(), args[0].as_ref().clone()));
                    }
                }
            }
        }

        if pairs.is_empty() {
            return None;
        }

        let simplified = error_constraint.substitute_expr_pairs(&pairs);
        if simplified != *error_constraint {
            Some(simplified)
        } else {
            None
        }
    }

    /// Check if the error constraint is syntactically contradicted by any invariant.
    pub(in crate::pdr::solver) fn error_contradicts_invariants(
        error_constraint: &ChcExpr,
        lemmas: &[Lemma],
        pred: PredicateId,
    ) -> bool {
        let negated_atoms = Self::extract_negated_atoms(error_constraint);
        if negated_atoms.is_empty() {
            return false;
        }

        for lemma in lemmas {
            if lemma.predicate != pred {
                continue;
            }
            for atom in &negated_atoms {
                if lemma.formula == *atom {
                    return true;
                }
            }
        }
        false
    }

    /// Extract atoms `e` from a formula where `(not e)` appears.
    /// For `(not expr)`, returns `[expr]`.
    /// For `(and a (not b) c)`, returns `[b]`.
    fn extract_negated_atoms(expr: &ChcExpr) -> Vec<ChcExpr> {
        let mut atoms = Vec::new();
        match expr {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                atoms.push((*args[0]).clone());
            }
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let ChcExpr::Op(ChcOp::Not, not_args) = arg.as_ref() {
                        if not_args.len() == 1 {
                            atoms.push((*not_args[0]).clone());
                        }
                    }
                }
            }
            _ => {}
        }
        atoms
    }
}
