// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-boundary filtering for negative-congruence candidates.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::TermId;

use crate::solver::{atom_filter_enabled, EufSolver};

impl EufSolver<'_> {
    /// Pre-index same-sorted equality terms, optionally restricted to SAT atoms.
    pub(crate) fn init_eq_terms(&mut self) {
        if self.eq_terms_init {
            return;
        }
        self.eq_terms.clear();
        for term_id in self.terms.term_ids() {
            let Some((lhs, rhs)) = self.decode_eq(term_id) else {
                continue;
            };
            let is_sat_atom = self
                .sat_atom_eq_terms
                .as_ref()
                .is_none_or(|atoms| atoms.contains(&term_id));
            if is_sat_atom && self.terms.sort(lhs) == self.terms.sort(rhs) {
                self.eq_terms.push((term_id, lhs, rhs));
            }
        }
        self.eq_terms_init = true;
    }

    /// Install equality terms that have a SAT variable.
    ///
    /// A late installation clears every index derived from the old candidate
    /// set so the next propagation rebuilds them consistently.
    pub fn set_sat_atom_eq_terms(&mut self, atoms: DetHashSet<TermId>) {
        self.sat_atom_eq_terms = Some(atoms);
        if self.eq_terms_init {
            self.eq_terms_init = false;
            self.eq_terms.clear();
            self.class_eqs.clear();
            self.pos_dirty_reps.clear();
            self.pos_full_scan_needed = true;
            self.diseq_pair_index.clear();
            self.diseq_keys_by_rep.clear();
            self.neg_dirty_reps.clear();
            self.neg_full_scan_needed = true;
        }
    }

    /// Collect and install the executor's assignable equality terms.
    pub fn install_sat_atom_filter(&mut self, term_to_var: &DetHashMap<TermId, u32>) {
        if !atom_filter_enabled() {
            return;
        }
        let atoms = term_to_var
            .keys()
            .copied()
            .filter(|&term| self.decode_eq(term).is_some())
            .collect();
        self.set_sat_atom_eq_terms(atoms);
    }
}
