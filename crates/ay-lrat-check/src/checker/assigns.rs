// Copyright 2026 Andrew Yates
// Assignment management for the LRAT checker.
//
// Extracted from mod.rs for the 500-line limit (#5142).
// Value query, assign, backtrack, and variable capacity management.

use crate::dimacs::Literal;

use super::{LratChecker, MAX_DENSE_LITS, MAX_DENSE_VARS};

impl LratChecker {
    /// Query the current truth value of a literal.
    #[inline]
    pub(crate) fn value(&self, lit: Literal) -> Option<bool> {
        let var_idx = lit.variable().index();
        if var_idx >= self.assigns.len() {
            return None;
        }
        self.assigns[var_idx].map(|v| v == lit.is_positive())
    }

    /// Assign a literal (set its variable to the polarity that makes it true).
    ///
    /// Returns `false`, assigning nothing, when `lit` lies outside the dense
    /// envelope. Every literal assigned during a check comes from a clause
    /// admitted by `add_original`/`add_trusted`/`add_derived`, so callers only
    /// see `false` on an invariant break, and treat it as a failed check.
    #[inline]
    #[must_use]
    pub(crate) fn assign(&mut self, lit: Literal) -> bool {
        let var_idx = lit.variable().index();
        if !self.ensure_var_extended(lit) {
            return false;
        }
        assert!(
            self.assigns[var_idx].is_none(),
            "BUG: LRAT checker double-assign var {var_idx}"
        );
        self.assigns[var_idx] = Some(lit.is_positive());
        self.trail.push(var_idx);
        true
    }

    /// Undo assignments back to a saved trail position.
    pub(crate) fn backtrack(&mut self, saved_trail_len: usize) {
        while self.trail.len() > saved_trail_len {
            let var_idx = self.trail.pop().expect("invariant: trail non-empty");
            self.assigns[var_idx] = None;
        }
    }

    /// Ensure the assignment array is large enough for `lit`, enforcing the
    /// declared variable count. Returns `false` if the variable exceeds
    /// `num_vars` (malformed original clause).
    ///
    /// The constructor caps `num_vars` at [`MAX_DENSE_VARS`]; the second
    /// comparison states that bound where the growth below can see it.
    pub(super) fn ensure_var_strict(&mut self, lit: Literal) -> bool {
        let idx = lit.variable().index();
        if idx >= self.num_vars || idx >= MAX_DENSE_VARS {
            return false;
        }
        if idx >= self.assigns.len() {
            self.assigns.resize(idx + 1, None);
        }
        true
    }

    /// Ensure the assignment array is large enough for `lit`, allowing
    /// extension variables beyond the declared count. Used for derived clauses
    /// in proofs that employ extended resolution (CaDiCaL generates these for
    /// pigeon-hole problems). Reference: CaDiCaL `lratchecker.cpp:170-176`.
    ///
    /// Returns `false`, growing nothing, when the variable lies outside the
    /// dense envelope ([`MAX_DENSE_VARS`]).
    #[must_use]
    pub(crate) fn ensure_var_extended(&mut self, lit: Literal) -> bool {
        let idx = lit.variable().index();
        if idx >= MAX_DENSE_VARS {
            return false;
        }
        if idx >= self.assigns.len() {
            self.assigns.resize(idx + 1, None);
        }
        true
    }

    /// Ensure `marks` and `checked_lits` arrays are large enough for `lit`.
    /// Used by resolution check and blocked clause check.
    ///
    /// Growth stops at the dense envelope ([`MAX_DENSE_LITS`]). Every literal
    /// passed here belongs to a clause whose variables were admitted below
    /// [`MAX_DENSE_VARS`] (`ensure_var_strict`/`ensure_var_extended`), so its
    /// index is always inside the envelope and the arrays always cover it.
    pub(super) fn ensure_mark_capacity(&mut self, lit: Literal) {
        let idx = lit.index();
        if idx >= MAX_DENSE_LITS {
            return;
        }
        if idx >= self.marks.len() {
            self.marks.resize(idx + 1, false);
        }
        if idx >= self.checked_lits.len() {
            self.checked_lits.resize(idx + 1, false);
        }
    }
}
