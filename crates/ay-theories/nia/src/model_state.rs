// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction and embedded LIA state access for `NiaSolver`.

use super::{HashMap, HashSet, LiaSolver, Monomial, NiaModel, NiaSolver, TermId};
use num_traits::ToPrimitive;

impl<'a> NiaSolver<'a> {
    /// Genuine Boolean leaf assignments from the same verified local-search point.
    /// This is candidate data, not a proof or a current-query ownership grant.
    pub fn boolean_witness(&self) -> impl Iterator<Item = (TermId, bool)> + '_ {
        self.bounded_enum_bool_model
            .iter()
            .filter(|_| self.bounded_enum_model.is_some())
            .map(|(&term, &value)| (term, value))
    }

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

        // The model the NIA VERIFIED is the tableau point (`var_value` reads
        // `lra.get_value`). LIA's `extract_model` prefers its
        // direct-enumeration witness, a solution of the LINEAR atoms only,
        // which can differ from the point the monomial check accepted — the
        // executor's model gate then rejected a genuine `sat`
        // (#nia-sign-cut-soundness, the SAT side of the stale-point defect).
        // Serve the tableau point when the exact evaluator confirms it
        // against every asserted atom, or when the evaluator is inconclusive
        // (an opaque atom, e.g. a UF application) but the point is integral
        // and every monomial is consistent at it — i.e. exactly what this
        // solver vouched for. A point the evaluator PROVES wrong, or a
        // non-integral one, falls back to the LIA's own model. Any served
        // model is re-validated by the executor's gate, so this is a pure
        // completeness gain.
        match self.current_model_point_status() {
            Some(true) => {
                if let Some(lia_model) = self.lia.extract_tableau_model() {
                    return Some(NiaModel {
                        values: lia_model.values,
                    });
                }
            }
            None if !self.has_inconsistent_monomials() && !self.has_inconsistent_divisions() => {
                if let Some(lia_model) = self.lia.extract_tableau_model() {
                    return Some(NiaModel {
                        values: lia_model.values,
                    });
                }
            }
            _ => {}
        }
        self.lia.extract_model().map(|lia_model| NiaModel {
            values: lia_model.values,
        })
    }

    /// True only when the model [`Self::extract_model`] reports PROVABLY
    /// falsifies an original (root) assertion: every Int leaf of the roots
    /// has an i64 value in it and the exact evaluator answers a definite
    /// `false` for some root (#stale-accept-sat-lane). Anything the evaluator
    /// cannot decide, a missing leaf or no roots at all answer `false`, so the
    /// caller then leaves the model alone.
    pub(crate) fn reported_model_falsifies_a_root(&self) -> bool {
        if self.root_assertions.is_empty() {
            return false;
        }
        let Some(model) = self.extract_model() else {
            return false;
        };
        let mut leaves: Vec<TermId> = Vec::new();
        for &root in &self.root_assertions {
            self.collect_int_var_leaves(root, &mut leaves);
        }
        let mut var_map: HashMap<TermId, i64> = HashMap::default();
        for leaf in leaves {
            let Some(value) = model.values.get(&leaf).and_then(ToPrimitive::to_i64) else {
                return false;
            };
            var_map.insert(leaf, value);
        }
        self.root_assertions
            .iter()
            .any(|&root| self.eval_formula_exact(root, true, &var_map) == Some(false))
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
    pub fn lra_solver(&self) -> ay_lia::LraSolverView<'_> {
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
