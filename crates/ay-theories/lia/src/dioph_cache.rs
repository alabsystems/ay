// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What the equality-derived Diophantine caches depend on, and when they may
//! be reused (#C8, D2 of the 2026-09-23 hunt).
//!
//! `try_diophantine_solve` builds `dioph_cached_substitutions`,
//! `dioph_cached_modular_gcds`, `dioph_cached_reasons` and
//! `dioph_safe_dependent_vars`. #C8 keeps them across a backtrack keyed on the
//! asserted EQUALITY set, on the premise that they depend on nothing else. They
//! do: before eliminating, `fold_fixed_vars_in_equation` replaces every
//! variable whose justified bounds fix it (`x >= v`, `x <= v`, typically a
//! branch-and-bound atom pair) by its value. On `21x + 13y + 5z = 117` with `x`
//! so fixed, the fold leaves `13y + 5z = c` and the caches record `z ≡ 3
//! (mod 13)`, true only while `x` is. After the backtrack that retracts `x`'s
//! bounds the equality key is unchanged, the caches were kept, and the modular
//! check read `z ≡ 3 (mod 13)` against `18 <= z <= 20` and reported the whole
//! asserted set — which no longer contains `x`'s bounds — as a conflict: a
//! wrong `unsat` (`linear/wit/fib_k06_01`, model `x = -7, y = 13, z = 19`).
//! The periodic BCP-time re-check (65c1831dc3) is what made a mid-search
//! solve, with branch atoms in force, common.
//!
//! The caches are therefore keyed on the equality set AND the folded bounds:
//! the fold's reason literals are recorded next to them, and wherever #C8
//! re-validates the caches (after a pop, a soft reset, or an import into
//! another instance) they are dropped unless every one of those literals is
//! still asserted, and the full check is asked to rebuild them.

use super::*;

impl LiaSolver<'_> {
    /// Drop the equality-derived Diophantine caches and what they depend on.
    pub(crate) fn clear_dioph_equality_caches(&mut self) {
        self.dioph_safe_dependent_vars.clear();
        self.dioph_cached_substitutions.clear();
        self.dioph_cached_modular_gcds.clear();
        self.dioph_cached_reasons.clear();
        self.dioph_cached_fold_reasons.clear();
    }

    /// Whether every bound literal folded into the cached system is still
    /// asserted, so that the folded values — and everything derived from
    /// them — still hold.
    pub(crate) fn dioph_fold_reasons_live(&self) -> bool {
        self.dioph_cached_fold_reasons.is_empty()
            || self.conflict_reasons_all_live(&self.dioph_cached_fold_reasons)
    }

    /// #C8 re-validation, run once before any consumer reads the caches after
    /// a pop, a soft reset or an import. `equality_key_changed`: the asserted
    /// equality set differs from the one the caches were built for.
    pub(crate) fn revalidate_dioph_caches(&mut self, equality_key_changed: bool) {
        self.dioph_needs_revalidation = false;
        if equality_key_changed {
            self.clear_dioph_equality_caches();
            return;
        }
        if !self.dioph_fold_reasons_live() {
            // D2: a folded bound was retracted. The equality set is the same,
            // so nothing else would re-run the solve; ask the full check to.
            self.clear_dioph_equality_caches();
            self.dioph_needs_full_check = true;
        }
    }
}
