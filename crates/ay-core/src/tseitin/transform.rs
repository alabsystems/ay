// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tseitin transform and incremental API: batch transform, incremental encoding,
//! clause extraction, and variable accessors.

use super::{
    ClausificationProof, CnfClause, CnfLit, Tseitin, TseitinEncodedAssertion, TseitinResult,
};
use crate::term::TermId;
use std::collections::BTreeMap;

impl Tseitin<'_> {
    /// Transform a term to CNF
    ///
    /// Returns the result containing clauses and mappings.
    #[must_use = "Tseitin transform result must be used"]
    pub fn transform(mut self, root: TermId) -> TseitinResult {
        let root_lit = self.encode(root, true);

        // Assert the root
        self.add_clause(CnfClause::unit(root_lit));

        TseitinResult {
            clauses: self.clauses,
            term_to_var: self.term_to_var,
            var_to_term: self.var_to_term,
            root: root_lit,
            num_vars: self.next_var.saturating_sub(1),
            proof_annotations: self.proof_annotations,
        }
    }

    /// Transform multiple terms to CNF (conjunction)
    #[must_use = "Tseitin transform result must be used"]
    pub fn transform_all(mut self, terms: &[TermId]) -> TseitinResult {
        let mut roots = Vec::new();

        for &term_id in terms {
            let lit = self.encode(term_id, true);
            roots.push(lit);
            self.add_clause(CnfClause::unit(lit));
        }

        let root = if roots.len() == 1 {
            roots[0]
        } else {
            // Create a dummy root for multiple assertions
            self.fresh_var() as i32
        };

        TseitinResult {
            clauses: self.clauses,
            term_to_var: self.term_to_var,
            var_to_term: self.var_to_term,
            root,
            num_vars: self.next_var.saturating_sub(1),
            proof_annotations: self.proof_annotations,
        }
    }

    // ==================== Incremental API ====================

    /// Encode and assert a term, returning the root literal
    ///
    /// This is the incremental version that doesn't consume self.
    /// Multiple calls build up the clause database while sharing
    /// term-to-variable mappings.
    #[must_use = "Tseitin encoding returns a literal that must be used"]
    pub fn encode_and_assert(&mut self, term_id: TermId) -> CnfLit {
        let lit = self.encode(term_id, true);
        self.add_clause(CnfClause::unit(lit));
        lit
    }

    /// Encode a term to CNF and assert it as a unit clause, discarding the literal.
    ///
    /// Use this when the side effect (asserting the clause) is the goal and the
    /// returned literal is not needed. This avoids `let _ = encode_and_assert()`
    /// patterns that trigger `#[must_use]` warnings.
    pub fn assert_term(&mut self, term_id: TermId) {
        let _lit = self.encode_and_assert(term_id);
    }

    /// Encode and assert multiple terms
    #[must_use = "Tseitin encoding results must be used"]
    pub fn encode_and_assert_all(&mut self, terms: &[TermId]) -> Vec<CnfLit> {
        terms
            .iter()
            .map(|&term_id| self.encode_and_assert(term_id))
            .collect()
    }

    /// Encode a term for incremental assertion, separating defs from activation.
    ///
    /// This is the preferred API for incremental SMT solving with push/pop.
    /// Returns a `TseitinEncodedAssertion` containing:
    /// - `root_lit`: the literal representing this assertion
    /// - `def_clauses`: definitional clauses for any new subterms
    ///
    /// **Usage pattern for incremental solving:**
    /// ```text
    /// let enc = tseitin.encode_assertion(term);
    /// // Add defs globally (survive push/pop):
    /// for clause in &enc.def_clauses {
    ///     sat_solver.add_clause_global(clause.literals());
    /// }
    /// // Add activation in current scope (follows push/pop):
    /// sat_solver.add_clause(&[enc.root_lit]);
    /// ```
    ///
    /// This ensures cached term→var mappings remain sound across scopes.
    /// See the development design notes.
    #[must_use = "Tseitin encoding result must be used"]
    pub fn encode_assertion(&mut self, term_id: TermId) -> TseitinEncodedAssertion {
        let root_lit = self.encode(term_id, true);
        let clause_start = self.clauses_extracted.min(self.clauses.len());
        // Iterator skip instead of `[clause_start..]`: the marker's `<= len`
        // invariant is not locally provable (trust L0 slice bounds).
        let def_clauses: Vec<CnfClause> = self.clauses.iter().skip(clause_start).cloned().collect();
        let def_proof_annotations = self.proof_annotations.as_ref().map(|annotations| {
            debug_assert_eq!(
                annotations.len(),
                self.clauses.len(),
                "proof annotations must stay aligned with generated clauses"
            );
            annotations.iter().skip(clause_start).cloned().collect()
        });
        self.clauses_extracted = self.clauses.len();
        TseitinEncodedAssertion {
            root_lit,
            def_clauses,
            def_proof_annotations,
        }
    }

    /// Encode a term for incremental assertion and return any new
    /// clausification proof annotations in the same order as `def_clauses`.
    ///
    /// The returned proof vector is `Some(...)` only when this `Tseitin`
    /// instance was created with proof tracking enabled.
    #[must_use = "Tseitin encoding result must be used"]
    pub fn encode_assertion_with_proofs(
        &mut self,
        term_id: TermId,
    ) -> (
        TseitinEncodedAssertion,
        Option<Vec<Option<ClausificationProof>>>,
    ) {
        let root_lit = self.encode(term_id, true);
        let end = self.clauses.len();
        let start = self.clauses_extracted.min(end);
        // `end` is `self.clauses.len()`, so skipping to `start` is exactly
        // `[start..end]`; iterator form carries no slice bounds obligation.
        let def_clauses: Vec<CnfClause> = self.clauses.iter().skip(start).cloned().collect();
        let def_proofs = self
            .proof_annotations
            .as_ref()
            .map(|proofs| proofs.iter().take(end).skip(start).cloned().collect());
        self.clauses_extracted = end;
        (
            TseitinEncodedAssertion {
                root_lit,
                def_clauses,
                def_proof_annotations: def_proofs.clone(),
            },
            def_proofs,
        )
    }

    /// Encode a term as an assertion root, returning just the root literal.
    ///
    /// This is an alias for `encode(term, true)` that makes the "assertion root"
    /// intent explicit. Use `take_new_clauses()` afterward to get definitional
    /// clauses separately.
    ///
    /// For most incremental use cases, prefer `encode_assertion()` which bundles
    /// the root literal and definitional clauses together with clear documentation.
    #[must_use = "Tseitin encoding returns a literal that must be used"]
    pub fn encode_root(&mut self, term_id: TermId) -> CnfLit {
        self.encode(term_id, true)
    }

    /// Get new clauses since last extraction
    ///
    /// This returns clauses added since the last call to this method
    /// or since construction if never called.
    #[must_use = "take_new_clauses advances the extraction marker; ignoring the return value will drop clauses"]
    pub fn take_new_clauses(&mut self) -> Vec<CnfClause> {
        let start = self.clauses_extracted.min(self.clauses.len());
        let new_clauses: Vec<CnfClause> = self.clauses.iter().skip(start).cloned().collect();
        self.clauses_extracted = self.clauses.len();
        new_clauses
    }

    /// Get all clauses (doesn't affect extraction marker)
    pub fn all_clauses(&self) -> &[CnfClause] {
        &self.clauses
    }

    /// Return the proof annotations parallel to [`Self::all_clauses`].
    ///
    /// `None` means this encoder was created without proof tracking.  When
    /// present, the slice has exactly one entry per generated clause; an entry
    /// may itself be `None` when that clause is an authored activation unit
    /// rather than a Tseitin tautology.
    pub fn proof_annotations(&self) -> Option<&[Option<ClausificationProof>]> {
        self.proof_annotations.as_deref()
    }

    /// Get the current number of variables
    pub fn num_vars(&self) -> u32 {
        self.next_var.saturating_sub(1)
    }

    /// Advance `next_var` so that freshly allocated Tseitin variables will
    /// not collide with SAT variables already reserved (e.g. scope selectors).
    ///
    /// `min_next` is a 1-indexed DIMACS lower bound: after this call,
    /// `fresh_var()` will return at least `min_next`.
    pub fn ensure_min_next_var(&mut self, min_next: u32) {
        if self.next_var < min_next {
            self.next_var = min_next;
        }
    }

    /// Get the term-to-variable mapping
    pub fn term_to_var(&self) -> &BTreeMap<TermId, u32> {
        &self.term_to_var
    }

    /// Get the variable-to-term mapping
    pub fn var_to_term(&self) -> &BTreeMap<u32, TermId> {
        &self.var_to_term
    }

    /// Get the CNF variable for a term if it exists
    pub fn get_var_for_term(&self, term: TermId) -> Option<u32> {
        self.term_to_var.get(&term).copied()
    }

    /// Get the term for a CNF variable if it exists
    pub fn get_term_for_var(&self, var: u32) -> Option<TermId> {
        self.var_to_term.get(&var).copied()
    }

    /// Reset clause extraction marker (but keep all mappings and clauses)
    pub fn reset_extraction_marker(&mut self) {
        self.clauses_extracted = 0;
    }
}
