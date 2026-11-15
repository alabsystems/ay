// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-copy MODEL evaluation, not arming, a source pin, or a SAT permit.

use std::sync::Arc;

use ay_core::term::TermEntryStamp;
use ay_core::TermId;
use ay_model_check::{FunctionalArrayError, ModelView};

use super::super::independent_gate::IndependentModelView;
use super::pin_admission::PinAdmission;
use super::{Executor, Model};

mod grammar;

impl Executor {
    /// Only exact original-model truth confirms. Every refusal/mismatch falls
    /// through to the old QMG routes; this method can never return Refuted.
    pub(in crate::executor::model) fn confirm_complete_array_copy_model(
        &self,
        root: TermId,
        view: &IndependentModelView<'_>,
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
            .and_then(|copy| check(self, model, view, copy, &mut admission));
        // The kernel dropped all topology/frontier scratch, and check dropped
        // all retained/new lookup Arcs before the original final owner fence.
        let current = source == self.ctx.source_context_stamp()
            && epoch.is_same_epoch(&self.query_authority_epoch)
            && birth.is_some()
            && birth == self.ctx.terms.entry_stamp(root)
            && view.is_exact_functional_model(self, model);
        let finished = admission.finish(self.ctx.terms.true_memory_bytes());
        result == Some(true) && current && finished.is_ok() && !overrides_active()
    }
}

pub(super) fn overrides_active() -> bool {
    super::super::scoped_term_evaluation_override_active()
        || super::super::dt_model::scoped_term_binding_active()
}

pub(super) fn lookup_offer(
    exec: &Executor,
    model: &Model,
    admission: &mut PinAdmission,
) -> Option<()> {
    admission.pay(256, 0).ok()?;
    let Some((work, bytes)) = lookup_cost(exec, model) else {
        admission.refuse_resource();
        return None;
    };
    // Prepay the existing root-copy/coexistence/linear source-stamp validation.
    // The original view's canonical namespace fence is inherited, not a new
    // whole-query hash/namespace ownership claim; see COST and README.
    admission.pay(work, bytes).ok()?;
    (!overrides_active()).then_some(())
}

fn lookup_cost(exec: &Executor, model: &Model) -> Option<(usize, usize)> {
    let data = model.functional_arrays.as_ref()?;
    let roots = exec
        .independent_gate_authored_assertions
        .as_ref()
        .map_or(exec.ctx.assertions.len(), Vec::len);
    let assumptions = exec.last_assumptions.as_ref().map_or(0, Vec::len);
    let count = roots.checked_add(assumptions)?;
    let bytes = count.checked_mul(64)?.checked_add(1024)?;
    let work = count
        .checked_add(1)?
        .checked_mul(count.checked_add(1)?)?
        .checked_mul(32)?
        .checked_add(bytes.checked_mul(4)?)?
        .checked_add(
            data.roots
                .len()
                .checked_add(data.stamps.len())?
                .checked_add(data.entries.len())?
                .checked_mul(128)?,
        )?;
    Some((work, bytes))
}

fn check(
    exec: &Executor,
    model: &Model,
    view: &IndependentModelView<'_>,
    copy: grammar::Copy,
    admission: &mut PinAdmission,
) -> Option<bool> {
    let mut captures = [None, None, None];
    let mut births: [Option<TermEntryStamp>; 3] = [None, None, None];
    for (index, term) in copy.arrays.iter().enumerate() {
        lookup_offer(exec, model, admission)?;
        births[index] = exec.ctx.terms.entry_stamp(*term);
        // ALWAYS the SAME independent view's canonical binding fence, never a
        // raw functional_array_value or reconstructed source-definition model.
        let captured = view.array_snapshot(*term).ok()??;
        if captured.sort() != exec.ctx.terms.sort(*term) || births[index].is_none() {
            return None;
        }
        captures[index] = Some(captured);
    }
    let [Some(target), Some(destination), Some(source)] = captures else {
        return None;
    };
    let kept = [target, destination, source];
    let result = kept[0].confirms_range_copy_with_progress(
        &kept[1],
        &kept[2],
        copy.lo,
        copy.hi,
        copy.source_lo,
        &mut |work, bytes| admission.pay(work, bytes).is_ok(),
    );
    if matches!(
        &result,
        Err(FunctionalArrayError::Resource | FunctionalArrayError::Allocation)
    ) {
        admission.refuse_resource();
    }
    for (index, term) in copy.arrays.iter().enumerate() {
        lookup_offer(exec, model, admission)?;
        let current = view.array_snapshot(*term).ok()??;
        let exact = Arc::ptr_eq(&current, &kept[index])
            && births[index] == exec.ctx.terms.entry_stamp(*term);
        drop(current);
        if !exact {
            return None;
        }
    }
    drop(kept);
    result.ok()
}

#[cfg(test)]
mod tests;
