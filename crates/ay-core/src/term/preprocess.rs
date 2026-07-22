// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing transformations on terms.
//!
//! These operate on the TermStore before Tseitin encoding, normalizing
//! arithmetic constructs for better SAT-level propagation.

use super::*;

impl TermStore {
    /// Decompose arithmetic equalities into conjunctions of inequalities.
    ///
    /// Transforms `(= expr1 expr2)` where both are Real/Int into
    /// `(and (<= expr1 expr2) (>= expr1 expr2))`. This enables the SAT
    /// solver to generate bound ordering axioms for each half independently,
    /// matching Z3's behavior. Without this, equality atoms are opaque to
    /// the bound axiom system and the SAT solver makes orders of magnitude
    /// more decisions (#4919).
    ///
    /// Only applies to bare equality assertions and equalities inside AND
    /// (which are effectively top-level after FlattenAnd). Does NOT recurse
    /// into OR/NOT/=> to avoid creating extra variables inside clauses.
    pub fn decompose_arithmetic_eq(&mut self, term: TermId) -> TermId {
        match self.get(term).clone() {
            TermData::App(Symbol::Named(ref name), ref args) if name == "=" && args.len() == 2 => {
                let lhs = args[0];
                let rhs = args[1];
                let lhs_sort = self.sort(lhs).clone();
                if matches!(lhs_sort, Sort::Real | Sort::Int) {
                    // (= e1 e2) -> (and (<= e1 e2) (>= e1 e2))
                    let le = self.mk_app(Symbol::Named("<=".into()), vec![lhs, rhs], Sort::Bool);
                    let ge = self.mk_app(Symbol::Named(">=".into()), vec![lhs, rhs], Sort::Bool);
                    self.mk_and(vec![le, ge])
                } else {
                    term
                }
            }
            TermData::App(Symbol::Named(ref name), ref args) if name == "and" => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.decompose_arithmetic_eq(a))
                    .collect();
                self.mk_and(new_args)
            }
            _ => term,
        }
    }

    /// Decompose arithmetic equalities in all terms of a list.
    pub fn decompose_arithmetic_eq_all(&mut self, terms: &[TermId]) -> Vec<TermId> {
        terms
            .iter()
            .map(|&t| self.decompose_arithmetic_eq(t))
            .collect()
    }

    /// Decompose arithmetic disequalities into disjunctions of strict inequalities.
    ///
    /// Transforms `(distinct x c)` and `(not (= x c))` where both operands are
    /// Real/Int into `(or (< x c) (> x c))`. This creates SAT variables for both
    /// branches during Tseitin encoding, allowing the CDCL solver to handle the
    /// case-split natively instead of via the expensive split-loop restart (#4919).
    ///
    /// Recurses into AND (for top-level conjuncts after FlattenAnd) but not into
    /// OR/NOT/=> to avoid creating extra variables inside clauses.
    pub fn decompose_disequality(&mut self, term: TermId) -> TermId {
        match self.get(term).clone() {
            // (distinct e1 e2) where both are arithmetic
            TermData::App(Symbol::Named(ref name), ref args)
                if name == "distinct" && args.len() == 2 =>
            {
                let lhs = args[0];
                let rhs = args[1];
                let lhs_sort = self.sort(lhs).clone();
                if matches!(lhs_sort, Sort::Real | Sort::Int) {
                    let lt = self.mk_app(Symbol::Named("<".into()), vec![lhs, rhs], Sort::Bool);
                    let gt = self.mk_app(Symbol::Named(">".into()), vec![lhs, rhs], Sort::Bool);
                    self.mk_or(vec![lt, gt])
                } else {
                    term
                }
            }
            // (not (= e1 e2)) where both are arithmetic
            TermData::Not(inner) => match self.get(inner).clone() {
                TermData::App(Symbol::Named(ref name), ref eq_args)
                    if name == "=" && eq_args.len() == 2 =>
                {
                    let lhs = eq_args[0];
                    let rhs = eq_args[1];
                    let lhs_sort = self.sort(lhs).clone();
                    if matches!(lhs_sort, Sort::Real | Sort::Int) {
                        let lt = self.mk_app(Symbol::Named("<".into()), vec![lhs, rhs], Sort::Bool);
                        let gt = self.mk_app(Symbol::Named(">".into()), vec![lhs, rhs], Sort::Bool);
                        self.mk_or(vec![lt, gt])
                    } else {
                        term
                    }
                }
                _ => term,
            },
            // Recurse into AND
            TermData::App(Symbol::Named(ref name), ref args) if name == "and" => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.decompose_disequality(a))
                    .collect();
                self.mk_and(new_args)
            }
            _ => term,
        }
    }

    /// Decompose arithmetic disequalities in all terms of a list.
    pub fn decompose_disequality_all(&mut self, terms: &[TermId]) -> Vec<TermId> {
        terms
            .iter()
            .map(|&t| self.decompose_disequality(t))
            .collect()
    }
}
