// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction and embedded LIA state access for `NiaSolver`.

use super::{HashSet, LiaSolver, Monomial, NiaModel, NiaSolver, TermId};

impl<'a> NiaSolver<'a> {
    /// Extract a model from the solver
    pub fn extract_model(&self) -> Option<NiaModel> {
        if let Some(enum_model) = &self.bounded_enum_model {
            let mut values = self
                .lia
                .extract_model()
                .map(|lia_model| lia_model.values)
                .unwrap_or_default();
            values.extend(
                enum_model
                    .iter()
                    .map(|(&term, value)| (term, value.clone())),
            );
            return Some(NiaModel { values });
        }

        self.lia.extract_model().map(|lia_model| NiaModel {
            values: lia_model.values,
        })
    }

    /// Get the auxiliary variable for a monomial (if registered)
    pub fn get_monomial_aux(&self, vars: &[TermId]) -> Option<TermId> {
        self.monomials.get(vars).map(|m| m.aux_var)
    }

    /// All registered monomials, sorted by variable list for deterministic iteration.
    pub fn monomials_sorted(&self) -> Vec<&Monomial> {
        let mut ms: Vec<&Monomial> = self.monomials.values().collect();
        ms.sort_unstable_by(|a, b| a.vars.cmp(&b.vars));
        ms
    }

    /// Passthrough: get the underlying LRA solver (via LIA) for bound
    /// conflict collection in the split-loop pipeline.
    pub fn lra_solver(&self) -> &ay_lra::LraSolver {
        self.lia.lra_solver()
    }

    /// Passthrough: replay learned cuts into the underlying LIA solver
    /// after asserting new literals in a fresh theory instance.
    pub fn replay_learned_cuts(&mut self) {
        self.lia.replay_learned_cuts();
    }

    /// Passthrough: take learned state from the underlying LIA solver for
    /// cross-iteration persistence in the split-loop pipeline.
    pub fn take_learned_state(&mut self) -> (Vec<ay_lia::StoredCut>, HashSet<ay_lia::HnfCutKey>) {
        self.lia.take_learned_state()
    }

    /// Passthrough: import previously learned state into the underlying LIA solver.
    pub fn import_learned_state(
        &mut self,
        cuts: Vec<ay_lia::StoredCut>,
        seen: HashSet<ay_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    /// Passthrough: take Diophantine solver state from the underlying LIA solver.
    pub fn take_dioph_state(&mut self) -> ay_lia::DiophState {
        self.lia.take_dioph_state()
    }

    /// Passthrough: import Diophantine solver state into the underlying LIA solver.
    pub fn import_dioph_state(&mut self, state: ay_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    /// Enable combined theory mode on the underlying LIA solver.
    ///
    /// When enabled, the LIA solver tracks shared equalities from EUF and
    /// participates in the Nelson-Oppen equality-propagation fixpoint loop.
    /// Required for UF+NIA theory combination (#4525).
    pub fn set_combined_theory_mode(&mut self, enabled: bool) {
        self.lia.set_combined_theory_mode(enabled);
    }

    /// Access the underlying LIA solver for model value extraction in N-O loops.
    ///
    /// Used by the UfNiaSolver adapter to evaluate interface terms under the
    /// LIA model and propagate equalities to EUF (#4525).
    pub fn lia(&self) -> &LiaSolver<'a> {
        &self.lia
    }
}
