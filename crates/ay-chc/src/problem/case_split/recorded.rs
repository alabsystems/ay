// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-problem case splitting, with each output clause's source clause.
//!
//! A split replaces one input clause, in place, by the cases it is split into
//! and drops non-query cases whose constraint is literally `false`. Retain
//! false queries as explicit vacuous safety obligations: losing the last one
//! would turn a valid preprocessed problem into `NoQuery`. The `_recorded`
//! forms return, for every output clause, the index of the input clause it
//! came from. A case is an instance of its source clause (the same predicates
//! and variables under a stronger constraint), so a counterexample found on
//! the split problem names its source clauses through this map (PDR restates
//! its Unsafe results over the problem it was handed with it,
//! `PdrSolver::restate_cex_for_input`).

use super::*;

/// `0..len`: every clause is its own source.
fn identity_origins(len: usize) -> Vec<usize> {
    (0..len).collect()
}

impl ChcProblem {
    /// Attempt to split clauses on `(ite ...)` occurrences by case-splitting on the condition.
    ///
    /// This is a semantics-preserving transformation for CHC:
    /// - `body ∧ φ(ite(c,t,e)) -> head` becomes two clauses:
    ///   - `body ∧ c ∧ φ(t) -> head`
    ///   - `body ∧ ¬c ∧ φ(e) -> head`
    ///
    /// The primary goal is to simplify CHC problems that encode program branches using `ite`,
    /// which can otherwise force PDR to learn many point-wise lemmas.
    ///
    /// To avoid exponential blow-ups, this pass limits the number of clauses generated from any
    /// single input clause. When the limit is reached, remaining `ite` nodes are left intact.
    pub fn try_split_ites_in_clauses(
        &mut self,
        max_clauses_per_input_clause: usize,
        verbose: bool,
    ) {
        self.try_split_ites_in_clauses_recorded(max_clauses_per_input_clause, verbose);
    }

    /// [`Self::try_split_ites_in_clauses`], returning each output clause's
    /// source clause index.
    pub(crate) fn try_split_ites_in_clauses_recorded(
        &mut self,
        max_clauses_per_input_clause: usize,
        verbose: bool,
    ) -> Vec<usize> {
        if max_clauses_per_input_clause <= 1 {
            return identity_origins(self.clauses.len());
        }

        let old = std::mem::take(&mut self.clauses);
        let old_len = old.len();
        let mut new_clauses: Vec<HornClause> = Vec::with_capacity(old_len);
        let mut origins: Vec<usize> = Vec::with_capacity(old_len);

        let mut total_splits: usize = 0;
        let mut clauses_with_splits: usize = 0;

        for (source, clause) in old.into_iter().enumerate() {
            let mut pending: Vec<HornClause> = vec![clause];
            let mut out: Vec<HornClause> = Vec::new();
            let mut did_split = false;

            while let Some(current) = pending.pop() {
                if out.len() + pending.len() >= max_clauses_per_input_clause {
                    out.push(current);
                    continue;
                }

                let Some((a, b)) = Self::split_clause_once_on_ite(&current) else {
                    out.push(current);
                    continue;
                };

                did_split = true;
                total_splits += 1;
                pending.push(a);
                pending.push(b);
            }

            if did_split {
                clauses_with_splits += 1;
            }
            for case in out {
                if case.is_query() || !Self::clause_is_trivially_false(&case) {
                    new_clauses.push(case);
                    origins.push(source);
                }
            }
        }

        if verbose && total_splits > 0 {
            Self::report_case_splits(
                "ite",
                total_splits,
                clauses_with_splits,
                old_len,
                new_clauses.len(),
            );
        }

        self.clauses = new_clauses;
        origins
    }

    /// Attempt to split clauses on `(or ...)` occurrences by case-splitting on each branch.
    ///
    /// This is a semantics-preserving transformation for CHC:
    /// - `body ∧ (or a b) -> head` becomes:
    ///   - `body ∧ a -> head`
    ///   - `body ∧ b -> head`
    ///
    /// The primary goal is to eliminate disjunctions inside clause constraints, since AY's
    /// SMT solver can return `Unknown` on disjunctive LIA queries and force expensive
    /// recursive case-splitting during model verification.
    ///
    /// To avoid exponential blow-ups, this pass limits:
    /// - the number of clauses generated per input clause, and
    /// - the OR arity that will be split.
    ///
    /// The result is shared process-wide (`or_split_share`): solvers built at
    /// the same time over the same clauses (the portfolio's two PDR variants on
    /// one preprocessed problem) split once.
    pub fn try_split_ors_in_clauses(&mut self, max_clauses_per_input_clause: usize, verbose: bool) {
        self.try_split_ors_in_clauses_recorded(max_clauses_per_input_clause, verbose);
    }

    /// [`Self::try_split_ors_in_clauses`], returning each output clause's
    /// source clause index.
    pub(crate) fn try_split_ors_in_clauses_recorded(
        &mut self,
        max_clauses_per_input_clause: usize,
        verbose: bool,
    ) -> Vec<usize> {
        if max_clauses_per_input_clause <= 1 {
            return identity_origins(self.clauses.len());
        }
        let cell =
            super::super::or_split_share::shared_split(&self.clauses, max_clauses_per_input_clause);
        // A concurrent caller with the same input blocks here until the first
        // one has split; both then take the identical clause vector and map.
        let mut computed = false;
        let split = cell.get_or_init(|| {
            computed = true;
            let origins = self.split_ors_in_clauses_uncached(max_clauses_per_input_clause, verbose);
            (self.clauses.clone(), origins)
        });
        if !computed {
            tracing::debug!("CHC: or-splitting shared with another solver (cache hit)");
            self.clauses = split.0.clone();
        }
        split.1.clone()
    }

    fn split_ors_in_clauses_uncached(
        &mut self,
        max_clauses_per_input_clause: usize,
        verbose: bool,
    ) -> Vec<usize> {
        // Keep this consistent with SMT-level OR split caps in verification.
        const MAX_OR_BRANCHES: usize = 8;

        let old = std::mem::take(&mut self.clauses);
        let old_len = old.len();
        let mut new_clauses: Vec<HornClause> = Vec::with_capacity(old_len);
        let mut origins: Vec<usize> = Vec::with_capacity(old_len);

        let mut total_splits: usize = 0;
        let mut clauses_with_splits: usize = 0;

        for (source, clause) in old.into_iter().enumerate() {
            let mut pending: Vec<HornClause> = vec![clause];
            let mut out: Vec<HornClause> = Vec::new();
            let mut did_split = false;

            while let Some(current) = pending.pop() {
                if out.len() + pending.len() >= max_clauses_per_input_clause {
                    out.push(current);
                    continue;
                }

                let Some(split) = Self::split_clause_once_on_or(&current, MAX_OR_BRANCHES) else {
                    out.push(current);
                    continue;
                };

                // Splitting adds `split.len() - 1` clauses. If that would exceed our cap,
                // keep the clause intact.
                if out.len() + pending.len() + split.len() > max_clauses_per_input_clause {
                    out.push(current);
                    continue;
                }

                did_split = true;
                total_splits += 1;
                pending.extend(split);
            }

            if did_split {
                clauses_with_splits += 1;
            }
            for case in out {
                if case.is_query() || !Self::clause_is_trivially_false(&case) {
                    new_clauses.push(case);
                    origins.push(source);
                }
            }
        }

        if verbose && total_splits > 0 {
            Self::report_case_splits(
                "or",
                total_splits,
                clauses_with_splits,
                old_len,
                new_clauses.len(),
            );
        }

        self.clauses = new_clauses;
        origins
    }
}
