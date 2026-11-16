// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact full-function pins for the ordinary quantified independent gate.
//! This constructs constraints from original MODEL DATA; it mints no seal.

use std::sync::Arc;

use ay_core::term::ControlledTermInternError;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use ay_model_check::{
    ArraySnapshot, EvalOutcome, FunctionalArrayError, ModelValue, ModelView, SnapshotTermError,
};

use super::super::independent_gate::IndependentModelView;
use super::pin_admission::PinAdmission;
use super::Executor;

enum ConstructionRefusal {
    Resource,
    Unsupported,
}

/// Captured selected MODEL DATA, not a native validation or publication seal.
pub(in crate::executor::model) enum ModelPinValue {
    Scalar(ModelValue, Sort),
    CompleteArray(Arc<ArraySnapshot>),
}

/// Prefer the complete selected function before finite leaf evaluation.
/// A refusing complete lookup must not fall back to sampled/default values.
pub(in crate::executor::model) fn capture_model_pin_value(
    terms: &TermStore,
    view: &IndependentModelView<'_>,
    leaf: TermId,
) -> Option<ModelPinValue> {
    if matches!(terms.sort(leaf), Sort::Array(_)) {
        match view.array_snapshot(leaf) {
            Ok(Some(snapshot)) => return Some(ModelPinValue::CompleteArray(snapshot)),
            Err(_) => return None,
            Ok(None) => {}
        }
    }
    if let EvalOutcome::Value(value) = ay_model_check::evaluate_term(terms, view, leaf) {
        Some(ModelPinValue::Scalar(value, terms.sort(leaf).clone()))
    } else {
        None
    }
}

impl Executor {
    /// Pin the exact original free leaf to its SAME complete selected array.
    /// The caller must clear pin-set totality on None, never sample/fabricate a
    /// replacement. Existing full-matrix native validation remains required.
    pub(in crate::executor::model) fn complete_functional_array_model_pin(
        &mut self,
        leaf: TermId,
        captured: Arc<ArraySnapshot>,
    ) -> Option<TermId> {
        let birth = self.ctx.terms.entry_stamp(leaf)?;
        let model = self.last_model.as_ref()?;
        let current = IndependentModelView::new(self, model)
            .array_snapshot(leaf)
            .ok()??;
        // The captured view is MODEL DATA, not authority to substitute another
        // interpretation or erase the original free declaration identity.
        if !Arc::ptr_eq(&current, &captured) || self.ctx.terms.sort(leaf) != captured.sort() {
            return None;
        }
        let source = self.ctx.source_context_stamp();
        let admission = PinAdmission::capture(self, model).ok()?;
        drop(current);
        let result = construct(&mut self.ctx.terms, leaf, &captured, &mut |work, bytes| {
            admission.pay(work, bytes).is_ok()
        });
        // The exported topology and every constructor argument have dropped.
        // The model retains the immutable snapshot; this is one Arc release.
        drop(captured);
        if matches!(&result, Err(ConstructionRefusal::Resource)) {
            admission.refuse_resource();
        }
        let valid = source == self.ctx.source_context_stamp()
            && self.ctx.terms.entry_stamp(leaf) == Some(birth)
            && self.last_model.as_ref().is_some_and(|model| {
                model.validate_functional_array_source(self).is_ok()
                    && IndependentModelView::new(self, model)
                        .canonical_theory_bindings_are_coherent()
            });
        // Keep the captured original end alive through ALL validation tail
        // work. Release the arena and perform the final original-owner fence
        // LAST, on both success and refusal. Source validation's debit cannot
        // escape that final SAME-model counter/deadline/cancellation fence.
        let finished = admission.finish(self.ctx.terms.true_memory_bytes());
        if !valid || finished.is_err() {
            return None;
        }
        result.ok()
    }
}

fn construct(
    terms: &mut TermStore,
    leaf: TermId,
    snapshot: &ArraySnapshot,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<TermId, ConstructionRefusal> {
    let topology = snapshot
        .topology_with_progress(progress)
        .map_err(|error| match error {
            FunctionalArrayError::Resource | FunctionalArrayError::Allocation => {
                ConstructionRefusal::Resource
            }
            _ => ConstructionRefusal::Unsupported,
        })?;
    let value = topology
        .try_to_term_with_progress(terms, progress)
        .map_err(|error| match error {
            SnapshotTermError::ResourceLimit
            | SnapshotTermError::Producer(ControlledTermInternError::ResourceLimit) => {
                ConstructionRefusal::Resource
            }
            _ => ConstructionRefusal::Unsupported,
        })?;
    // Prepay bounded caller-owned arguments/name and their teardown as well as
    // the separately priced borrowed interner operation. No infallible Vec
    // growth or old unmetered mk_eq/mk_var builder is used on this route.
    if !progress(512, 2048) {
        return Err(ConstructionRefusal::Resource);
    }
    let mut args = Vec::new();
    args.try_reserve_exact(2)
        .map_err(|_| ConstructionRefusal::Resource)?;
    args.extend_from_slice(&[leaf, value]);
    let equality = TermData::App(Symbol::named("="), args);
    terms
        .try_intern_with_progress(&equality, &Sort::Bool, progress)
        .map_err(|error| match error {
            ControlledTermInternError::ResourceLimit => ConstructionRefusal::Resource,
            _ => ConstructionRefusal::Unsupported,
        })
}
