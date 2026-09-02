// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cardinality constraint recognition and rewriting (#4919).
//!
//! Recognizes pseudo-boolean cardinality patterns like
//! `(<= (+ (ite c1 1 0) (ite c2 1 0) ... (ite cn 1 0)) k)` and rewrites
//! them into pure boolean clauses, avoiding exponential ITE lifting blowup.

use super::*;
use num_traits::ToPrimitive;

/// Capacity-hint clamp for the rewritten assertion list; assertion counts are
/// caller-controlled, and longer lists just grow past the hint.
const MAX_PREALLOC_ASSERTIONS: usize = 1 << 20;

impl TermStore {
    /// Rewrite pseudo-boolean cardinality constraints into boolean clauses.
    ///
    /// Recognizes patterns of the form:
    ///   `(<= (+ (ite c1 1 0) (ite c2 1 0) ... (ite cn 1 0)) k)`
    /// and rewrites them into pure boolean constraints.
    ///
    /// For at-most-1 (k=1): generates pairwise exclusion `¬ci ∨ ¬cj` for all i<j.
    /// This avoids the exponential 2^N ITE lifting blowup while producing an
    /// O(N^2) number of binary clauses that the SAT solver handles efficiently.
    ///
    /// Returns `Some(replacement_terms)` if the term was rewritten, `None` if not
    /// recognized as a cardinality constraint.
    fn try_rewrite_cardinality(&mut self, term: TermId) -> Option<Vec<TermId>> {
        // Match: (<= sum bound) where sum = (+ ite1 ite2 ... iten [+ other])
        let (pred_name, sum_term, bound_term) = match self.get(term).clone() {
            TermData::App(Symbol::Named(ref name), ref args) => match args.as_slice() {
                &[sum_term, bound_term] => (name.clone(), sum_term, bound_term),
                _ => return None,
            },
            _ => return None,
        };

        if pred_name != "<=" {
            return None;
        }

        // Extract bound value (must be a constant integer)
        let bound_val: i64 = match self.get(bound_term) {
            TermData::Const(Constant::Int(n)) => n.to_i64()?,
            _ => return None,
        };

        // Only handle at-most-1 for now (most common in verification benchmarks)
        if bound_val != 1 {
            return None;
        }

        // Extract sum arguments: (+ a1 a2 ... an)
        let sum_args = match self.get(sum_term).clone() {
            TermData::App(Symbol::Named(ref name), ref args) if name == "+" => args.clone(),
            _ => return None,
        };

        // Check if ALL sum arguments are `(ite cond 1 0)` indicators
        let mut conditions: Vec<TermId> = Vec::new();
        for &arg in &sum_args {
            // Handle nested (+ ...) from left-folded additions
            if let TermData::App(Symbol::Named(ref name), ref inner_args) = self.get(arg).clone() {
                if name == "+" {
                    // Recursively extract indicators from nested sums
                    for &inner in inner_args {
                        {
                            let cond = self.extract_ite_indicator(inner)?;
                            conditions.push(cond);
                        }
                    }
                    continue;
                }
            }
            {
                let cond = self.extract_ite_indicator(arg)?;
                conditions.push(cond);
            }
        }

        // Need at least 2 indicators and no more than 50 (to keep clause count manageable)
        if conditions.len() < 2 || conditions.len() > 50 {
            return None;
        }

        // Generate at-most-1: for each pair (ci, cj), add not-ci or not-cj
        let mut clauses = Vec::new();
        let mut rest = conditions.as_slice();
        while let Some((&ci, tail)) = rest.split_first() {
            for &cj in tail {
                let not_ci = self.mk_not(ci);
                let not_cj = self.mk_not(cj);
                let clause = self.mk_or(vec![not_ci, not_cj]);
                clauses.push(clause);
            }
            rest = tail;
        }

        Some(clauses)
    }

    /// Check if a term is `(ite cond 1 0)` and return the condition.
    fn extract_ite_indicator(&self, term: TermId) -> Option<TermId> {
        if let TermData::Ite(cond, then_t, else_t) = self.get(term) {
            let then_val = match self.get(*then_t) {
                TermData::Const(Constant::Int(n)) => n.to_i64()?,
                _ => return None,
            };
            let else_val = match self.get(*else_t) {
                TermData::Const(Constant::Int(n)) => n.to_i64()?,
                _ => return None,
            };
            if then_val == 1 && else_val == 0 {
                return Some(*cond);
            }
        }
        None
    }

    /// Rewrite cardinality constraints in an assertion list.
    ///
    /// Scans for `(<= sum_of_indicators k)` patterns and replaces them
    /// with pairwise boolean exclusion constraints. Returns a new assertion
    /// list with cardinality constraints expanded.
    pub fn rewrite_cardinality_constraints(&mut self, terms: &[TermId]) -> Vec<TermId> {
        let mut result = Vec::with_capacity(terms.len().min(MAX_PREALLOC_ASSERTIONS));
        for &t in terms {
            if let Some(replacements) = self.try_rewrite_cardinality(t) {
                result.extend(replacements);
            } else {
                result.push(t);
            }
        }
        result
    }
}
