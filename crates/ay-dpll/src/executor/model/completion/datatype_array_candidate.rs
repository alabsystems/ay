// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A fresh candidate for exact datatype-array completion, never SAT authority.

use super::super::datatype_array_fields::MAX_EXACT_ARRAY_FIELD_TERMS;
use super::super::Model;
use crate::executor::Executor;

impl Executor {
    /// Raw BV extraction quarantines unresolved definitions as well as actual
    /// read conflicts. Keep that raw-consumer contract intact. For a bounded
    /// ground query with authenticated datatype-array owners, offer a separate
    /// candidate with the finite entries retained only as proposed data and
    /// their extraction authority revoked. Existing exact construction
    /// must rebuild it; the caller additionally requires fully evaluated
    /// independent confirmation over every authored assertion.
    pub(in crate::executor::model) fn prepare_exact_datatype_array_rebuild(&self) -> Option<Model> {
        if self.evaluation_stop_origin().is_some() || self.solve_deadline.expired() {
            return None;
        }
        let model = self.last_model.as_ref()?;
        let arrays = model.array_model.as_ref()?;
        if model.bv_model.is_none()
            || !model.dt_ground.is_empty()
            || !model.dt_pins.is_empty()
            || !model.dt_array_field_classes.is_empty()
            || model.has_residual_arrays()
            || model.functional_arrays.is_some()
            || arrays.read_conflicted.is_empty()
            || arrays.read_conflicted.len() > MAX_EXACT_ARRAY_FIELD_TERMS
            || arrays.array_values.len() > MAX_EXACT_ARRAY_FIELD_TERMS
        {
            return None;
        }
        let plan = self.datatype_array_completion_plan(&[]);
        self.preflight_opaque_dt_collection(plan.roots())?;
        let owners = self.authored_datatype_array_construction_cells()?;
        if owners.is_empty() {
            return None;
        }
        let mut candidate = model.clone();
        candidate.revoke_all_quantified_model_seals();
        let arrays = candidate.array_model.as_mut()?;
        for term in &arrays.read_conflicted {
            arrays.definition_authoritative.remove(term);
        }
        arrays.read_conflicted.clear();
        arrays.store_chain_class_candidate = None;
        Some(candidate)
    }
}
