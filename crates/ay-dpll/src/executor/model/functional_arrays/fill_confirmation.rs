// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict original Fill arming is DATA eligibility, never semantic truth.

use super::super::independent_gate::IndependentModelView;
use super::copy_confirmation::{lookup_offer, overrides_active};
use super::pin_admission::PinAdmission;
use super::{Executor, Model};
use ay_core::TermId;
use ay_model_check::{FunctionalArrayError, ModelView};
use std::sync::Arc;

mod grammar;

enum Purpose {
    Arm,
    Confirm,
}

impl Executor {
    pub(in crate::executor::model) fn complete_array_fill_restoration_candidate(
        &self,
        root: TermId,
    ) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        if model.functional_arrays.is_none()
            || model.projection_ufs.has_interpretations()
            || overrides_active()
        {
            return false;
        }
        let Ok(mut admission) = PinAdmission::capture(self, model) else {
            return false;
        };
        if admission.pay(1024, 0).is_err() || !grammar::header(self, root) {
            return false;
        }
        let source = self.ctx.source_context_stamp();
        let epoch = self.query_authority_epoch.clone();
        let birth = self.ctx.terms.entry_stamp(root);
        // This arming caller has no existing view. Its ordinary constructor is
        // an inherited opaque boundary, NOT new work/copy/owner authority.
        let view = IndependentModelView::new(self, model);
        let result = grammar::recognize(self, &view, root, &mut admission)
            .and_then(|fill| check(self, model, &view, fill, Purpose::Arm, &mut admission));
        let exact = view.is_exact_functional_model(self, model);
        drop(view);
        // The new arming view and ALL selected capture handles are gone.
        let current = exact
            && source == self.ctx.source_context_stamp()
            && epoch.is_same_epoch(&self.query_authority_epoch)
            && birth.is_some()
            && birth == self.ctx.terms.entry_stamp(root);
        let finished = admission.finish(self.ctx.terms.true_memory_bytes());
        result == Some(true) && current && finished.is_ok() && !overrides_active()
    }

    pub(in crate::executor::model) fn confirm_complete_array_fill_model(
        &self,
        root: TermId,
        view: &IndependentModelView<'_>,
    ) -> bool {
        self.original_fill_model(root, view, Purpose::Confirm)
    }

    fn original_fill_model(
        &self,
        root: TermId,
        view: &IndependentModelView<'_>,
        purpose: Purpose,
    ) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        let Ok(mut admission) = PinAdmission::capture(self, model) else {
            return false;
        };
        if admission.pay(1024, 0).is_err() {
            return false;
        }
        if model.projection_ufs.has_interpretations()
            || !view.is_exact_functional_model(self, model)
            || overrides_active()
        {
            return false;
        }
        let source = self.ctx.source_context_stamp();
        let epoch = self.query_authority_epoch.clone();
        let birth = self.ctx.terms.entry_stamp(root);
        let result = grammar::recognize(self, view, root, &mut admission)
            .and_then(|fill| check(self, model, view, fill, purpose, &mut admission));
        let current = source == self.ctx.source_context_stamp()
            && epoch.is_same_epoch(&self.query_authority_epoch)
            && birth.is_some()
            && birth == self.ctx.terms.entry_stamp(root)
            && view.is_exact_functional_model(self, model);
        let finished = admission.finish(self.ctx.terms.true_memory_bytes());
        result == Some(true) && current && finished.is_ok() && !overrides_active()
    }
}

fn check(
    exec: &Executor,
    model: &Model,
    view: &IndependentModelView<'_>,
    fill: grammar::Fill<'_>,
    purpose: Purpose,
    admission: &mut PinAdmission,
) -> Option<bool> {
    let mut captures = [None, None];
    let mut births = [None, None];
    let literal_birth = fill
        .literal_term
        .map(|term| exec.ctx.terms.entry_stamp(term));
    if matches!(literal_birth, Some(None)) {
        return None;
    }
    for (index, term) in fill.arrays.iter().enumerate() {
        lookup_offer(exec, model, admission)?;
        births[index] = exec.ctx.terms.entry_stamp(*term);
        let captured = view.array_snapshot(*term).ok()??;
        if captured.sort() != exec.ctx.terms.sort(*term) || births[index].is_none() {
            return None;
        }
        captures[index] = Some(captured);
    }
    let [Some(target), Some(destination)] = captures else {
        return None;
    };
    let kept = [target, destination];
    let result = match purpose {
        Purpose::Arm => Ok(true), // Complete capture eligibility is NOT truth.
        Purpose::Confirm => kept[0].confirms_range_fill_with_progress(
            &kept[1],
            fill.lo,
            fill.hi,
            fill.value,
            &mut |work, bytes| admission.pay(work, bytes).is_ok(),
        ),
    };
    if matches!(
        &result,
        Err(FunctionalArrayError::Resource | FunctionalArrayError::Allocation)
    ) {
        admission.refuse_resource();
    }
    for (index, term) in fill.arrays.iter().enumerate() {
        lookup_offer(exec, model, admission)?;
        let current = view.array_snapshot(*term).ok()??;
        let exact = Arc::ptr_eq(&current, &kept[index])
            && births[index] == exec.ctx.terms.entry_stamp(*term);
        drop(current);
        if !exact {
            return None;
        }
    }
    let literal_current = fill
        .literal_term
        .map(|term| exec.ctx.terms.entry_stamp(term))
        == literal_birth;
    drop(kept);
    literal_current
        .then_some(result.ok()?)
        .filter(|_| !overrides_active())
}

#[cfg(test)]
mod tests;
