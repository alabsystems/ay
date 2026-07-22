// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Normal form construction and utility helpers.
//!
//! Extracted from `core/mod.rs` per design
//! the development design notes.

use super::*;

impl CoreSolver {
    /// Compute normal forms for all equivalence classes.
    pub(super) fn compute_normal_forms(&mut self, terms: &TermStore, state: &SolverState) {
        self.normal_forms.clear();

        let reps = state.eqc_representatives();

        // First pass: compute NFs for non-concat EQCs.
        for &rep in &reps {
            if let Some(eqc) = state.get_eqc(&rep) {
                let has_active_concat = eqc
                    .concat_terms
                    .iter()
                    .any(|ct| !self.reduced_terms.contains(ct));
                if eqc.constant.is_some() || !has_active_concat {
                    self.normal_forms.insert(rep, NormalForm::singleton(rep));
                }
            }
        }

        // Second pass: compute NFs for concat EQCs via iterative flattening.
        let mut changed = true;
        let mut iterations = 0;
        while changed && iterations < 100 {
            changed = false;
            iterations += 1;

            for &rep in &reps {
                if self.normal_forms.contains_key(&rep) {
                    continue;
                }
                if let Some(eqc) = state.get_eqc(&rep) {
                    if let Some(concat_term) = eqc
                        .concat_terms
                        .iter()
                        .copied()
                        .find(|ct| !self.reduced_terms.contains(ct))
                    {
                        if let Some(nf) = self.try_compute_concat_nf(terms, state, rep, concat_term)
                        {
                            self.normal_forms.insert(rep, nf);
                            changed = true;
                        }
                    }
                }
            }
        }

        // Remaining EQCs get singleton forms.
        for &rep in &reps {
            self.normal_forms
                .entry(rep)
                .or_insert_with(|| NormalForm::singleton(rep));
        }
    }

    /// Try to compute a normal form for a concat term by flattening children.
    ///
    /// Returns `None` if a child's NF is not yet computed.
    pub(super) fn try_compute_concat_nf(
        &self,
        terms: &TermStore,
        state: &SolverState,
        rep: TermId,
        concat_term: TermId,
    ) -> Option<NormalForm> {
        let children = state.get_concat_children(terms, concat_term)?;
        let mut nf = NormalForm::new();
        nf.rep = Some(rep);
        nf.source = Some(concat_term);

        // Track why the concat term is in this EQC. Without this dep,
        // build_explanation() produces an empty explanation for concat NFs
        // where all children happen to be at their representative, causing
        // the all-assertions fallback (#3844).
        if concat_term != rep {
            nf.add_dep(concat_term, rep);
        }

        // Pre-scan: detect tautological self-reference (#3899).
        //
        // When x = str.++(c1, ..., cn) and exactly one ci has find(ci) == rep
        // while all other cj are empty strings, the concat is a tautological
        // identity (x = str.++("", ..., x, ..., "") = x). We can skip the
        // self-referencing child. Without this, the NF for rep is never
        // computed (it depends on itself), blocking NF computation for all
        // dependent EQCs.
        //
        // We must NOT skip when there are non-empty, non-self siblings — that
        // creates a real loop equation (x = str.++(a, x, b)) which requires
        // the loop-handling machinery, not NF flattening.
        let has_self_ref = children.iter().any(|&c| state.find(c) == rep);
        let self_ref_is_tautological = has_self_ref
            && children.iter().all(|&c| {
                let cr = state.find(c);
                cr == rep || state.is_empty_string(terms, c)
            });

        for &child in children {
            let child_rep = state.find(child);

            if state.is_empty_string(terms, child) {
                // Record why this child is empty (#3826). We need the dep
                // between `child` and the actual empty string constant, NOT
                // between `child` and `child_rep` — because when `child` IS
                // the EQC representative (e.g., F is rep of {F, ""}), then
                // `child == child_rep` and no dep would be recorded. The proof
                // forest path from `child` to the empty constant contains the
                // merge edge (e.g., F = ""), which build_explanation needs to
                // produce the correct blocking clause literal.
                if let Some(empty_id) = state.find_constant_term_id(terms, child) {
                    if child != empty_id {
                        nf.add_dep(child, empty_id);
                    }
                }
                if *DEBUG_STRING_CORE {
                    let empty_id = state.find_constant_term_id(terms, child);
                    eprintln!("[STRING_CORE] try_compute_concat_nf: skipping empty child {:?} (child_rep={:?}, empty_id={:?}, dep_added={})",
                        child, child_rep, empty_id, empty_id.is_some_and(|e| child != e));
                }
                continue;
            }

            // Skip tautological self-reference (#3899): x = str.++("", x, "")
            // reduces to x = x. The self-referencing child contributes nothing
            // to the NF.
            if child_rep == rep && self_ref_is_tautological {
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] try_compute_concat_nf: skipping tautological self-ref child {child:?} (rep={rep:?})"
                    );
                }
                continue;
            }

            {
                let child_nf = self.normal_forms.get(&child_rep)?;
                nf.base.extend_from_slice(&child_nf.base);
                nf.merge_deps(child_nf);
            }

            if child != child_rep {
                nf.add_dep(child, child_rep);
            }
        }

        // If all children were empty (or self-referential tautologies), the NF
        // is [rep].
        if nf.base.is_empty() {
            nf.base.push(rep);
        }

        Some(nf)
    }

    /// Compare two normal forms for structural equality under EQC representatives.
    ///
    /// Two NFs are equal if they have the same length and each pair of
    /// corresponding components shares the same EQC representative.
    pub(super) fn nfs_equal(&self, state: &SolverState, a: &NormalForm, b: &NormalForm) -> bool {
        if a.base.len() != b.base.len() {
            return false;
        }
        a.base
            .iter()
            .zip(b.base.iter())
            .all(|(&x, &y)| state.find(x) == state.find(y))
    }

    /// Try to resolve a normal form to a concrete constant string.
    ///
    /// Returns `Some(string)` if every component in the NF has a known
    /// constant value (via its EQC or syntactically). Returns `None` if
    /// any component is a variable with no known constant.
    pub(super) fn nf_to_constant(
        &self,
        terms: &TermStore,
        state: &SolverState,
        nf: &NormalForm,
    ) -> Option<String> {
        let mut result = String::new();
        for &component in &nf.base {
            let comp_rep = state.find(component);
            let comp_const = state
                .get_eqc(&comp_rep)
                .and_then(|e| e.constant.as_deref())
                .or_else(|| Self::get_string_constant(terms, component));
            {
                let s = comp_const?;
                result.push_str(s)
            }
        }
        Some(result)
    }
}

#[cfg(test)]
#[path = "normal_forms_tests.rs"]
mod tests;
