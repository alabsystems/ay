// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source/query-bound immutable functional MODEL DATA; never a proof seal.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use ay_core::term::{TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::{Sort, TermId};
use ay_frontend::SourceContextStamp;
use ay_model_check::{ArraySnapshot, EvalOutcome, Evaluator, ModelValue};

use super::{eval_memo_clear, Executor, Model};
use crate::executor::query_authority::QueryAuthorityEpoch;

mod copy_confirmation;
mod fill_confirmation;
mod model_pins;
mod named_values;
mod periodic_candidate;
mod pin_admission;
mod producer;

pub(super) use model_pins::{capture_model_pin_value, ModelPinValue};
pub(super) use pin_admission::PinAdmission;
mod work_counter;

pub(super) const MAX_FUNCTIONAL_WORK: usize = 1_048_576;

pub(super) fn debit_work(exec: &Executor, used: &AtomicUsize, amount: usize) -> Result<(), String> {
    exec.poll_evaluation_stop().map_err(|_| {
        // An observed original stop is terminal storage, not a work debit.
        work_counter::refuse(used);
        "functional array owner interrupted".to_owned()
    })?;
    if !work_counter::debit(used, amount) {
        return Err("functional array original cumulative work exhausted".to_owned());
    }
    Ok(())
}

// A later read owns its own live controls. Only a stop in the original
// construction attempt is terminal for the retained DATA ledger; cumulative
// exhaustion is terminal in every attempt. Never poll the old solve clock.
pub(super) fn debit_retained_work(
    exec: &Executor,
    used: &AtomicUsize,
    original: &super::EvaluationAttempt,
    amount: usize,
) -> Result<(), String> {
    exec.poll_evaluation_stop().map_err(|_| {
        if original.is_same_attempt(&exec.evaluation_attempt()) {
            work_counter::refuse(used);
        }
        "model read interrupted".to_owned()
    })?;
    if !work_counter::debit(used, amount) {
        return Err("model original cumulative work exhausted".to_owned());
    }
    Ok(())
}

#[derive(Clone, Debug)]
pub(super) struct FunctionalArrayModel {
    source: SourceContextStamp,
    epoch: QueryAuthorityEpoch,
    roots: Vec<TermId>,
    stamps: Vec<(TermId, TermEntryStamp)>,
    entries: Vec<(TermId, Arc<ArraySnapshot>)>,
    // Cloning a model preserves this original cumulative owner, never a new
    // work allowance. Model data still carries no publication authority.
    work_used: Arc<AtomicUsize>,
    // Arena snapshot at which `stamps` last fully validated (see
    // `validate_functional_array_source`). While it remains an append-only
    // prefix of the live store, every stamped slot still names the captured
    // entry, so the walk's verdict cannot change. Cloning shares this memo
    // with the work owner; it grants no authority, since the source/roots
    // checks and the owner fence run on every validation regardless.
    stamps_validated_at: Arc<Mutex<Option<TermStoreSnapshotStamp>>>,
}

impl Model {
    pub(super) fn functional_array_value(
        &self,
        exec: &Executor,
        term: TermId,
    ) -> Result<Option<Arc<ArraySnapshot>>, String> {
        let Some(data) = &self.functional_arrays else {
            return Ok(None);
        };
        let Ok(index) = data.entries.binary_search_by_key(&term, |(node, _)| *node) else {
            return Ok(None);
        };
        if super::dt_model::term_depends_on_scoped_binding(&exec.ctx.terms, term) {
            return Err("functional array lexical override active".to_owned());
        }
        self.validate_functional_array_source(exec)?;
        Ok(Some(Arc::clone(&data.entries[index].1)))
    }
    pub(super) fn validate_functional_array_source(&self, exec: &Executor) -> Result<(), String> {
        let Some(data) = &self.functional_arrays else {
            return Ok(());
        };
        // The entry-stamp walk's verdict depends only on the stamped slots.
        // While the snapshot at which it last passed remains an append-only
        // prefix of the live store (same identity and structural generation,
        // no rollback or compaction), those slots are immutable, so the walk
        // cannot newly fail; charge it only when it actually runs. The
        // source/roots checks and the closing owner fence are per-read and
        // run either way.
        let snapshot = exec.ctx.terms.snapshot_stamp();
        let stamps_current = {
            let memo = data
                .stamps_validated_at
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            memo.as_ref()
                .is_some_and(|validated| validated.is_append_only_prefix_of(&exec.ctx.terms))
        };
        let walk_charge = if stamps_current { 0 } else { data.stamps.len() };
        self.charge_functional_array_work(exec, data.roots.len() + walk_charge + 1)?;
        if !data.epoch.is_same_epoch(&exec.query_authority_epoch)
            || data.source != exec.ctx.source_context_stamp()
            || data.roots
                != exec
                    .independent_gate_query_roots()
                    .map_err(|origin| format!("query roots unavailable: {origin:?}"))?
            || (!stamps_current
                && data
                    .stamps
                    .iter()
                    .any(|(node, stamp)| exec.ctx.terms.entry_stamp(*node) != Some(*stamp)))
        {
            return Err("functional array source/query snapshot changed".to_owned());
        }
        if !stamps_current {
            *data
                .stamps_validated_at
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(snapshot);
        }
        self.charge_functional_array_work(exec, 0)?;
        Ok(())
    }

    pub(super) fn charge_functional_array_work(
        &self,
        exec: &Executor,
        amount: usize,
    ) -> Result<(), String> {
        let symbolic = &self.certified_total_ufs.symbolic;
        if !symbolic.is_empty() && !symbolic.pay_for(exec, amount, 0) {
            return Err("retained symbolic model work owner refused".to_owned());
        }
        if let Some(data) = &self.functional_arrays {
            debit_work(exec, &data.work_used, amount)?;
        } else if symbolic.is_empty() {
            if let Some(admission) = super::recovery_admission::RecoveryAdmission::current_for(exec)
            {
                admission.pay(amount, 0).then_some(()).ok_or_else(|| {
                    "functional array original recovery owner exhausted".to_owned()
                })?;
            } else {
                exec.poll_evaluation_stop()
                    .map_err(|_| "functional array owner interrupted".to_owned())?;
            }
        }
        Ok(())
    }

    pub(super) fn charge_exact_fp_work(
        &self,
        exec: &Executor,
        amount: usize,
    ) -> Result<(), String> {
        if let Some(owner) = &self.construction_owner {
            owner.charge(exec, amount)
        } else {
            self.charge_functional_array_work(exec, amount)
        }
    }

    pub(super) fn functional_work_left(&self) -> usize {
        let used = self.functional_arrays.as_ref().map(|data| &data.work_used);
        used.map_or(0, |used| {
            MAX_FUNCTIONAL_WORK.saturating_sub(used.load(Ordering::Acquire))
        })
    }
}

impl Executor {
    pub(super) fn install_functional_array_candidate(&self, model: &mut Model) {
        // No prior functional completion is reused as evidence for another
        // model. Declining construction leaves the existing model unchanged.
        if model.functional_arrays.is_some()
            || self.poll_evaluation_stop().is_err()
            || super::scoped_term_evaluation_override_active()
        {
            return;
        }
        if !self.bind_model_construction_owner(model) {
            return;
        }
        let Some((data, defined_terms)) = producer::capture(self, model) else {
            return;
        };
        if self.poll_evaluation_stop().is_err() {
            return;
        }
        model.revoke_all_quantified_model_seals();
        // A target formerly marked partial because store-only recovery could
        // not represent its lambda now has a COMPLETE selected interpretation.
        // Ground read constraints are not discarded: all original roots are
        // replayed under that one interpretation by the unchanged final gates.
        if let Some(arrays) = model.array_model.as_mut() {
            for term in defined_terms {
                arrays.read_conflicted.remove(&term);
            }
        }
        model.functional_arrays = Some(data);
        eval_memo_clear();
        super::independent_gate::invalidate_functional_model_caches();
    }

    pub(super) fn functional_array_read(
        &self,
        model: &Model,
        array: TermId,
        index: &super::EvalValue,
    ) -> Option<super::EvalValue> {
        let value = match model.functional_array_value(self, array) {
            Ok(None) => return None,
            Ok(Some(value)) => value,
            Err(_) => return Some(super::EvalValue::Unknown),
        };
        if model.charge_functional_array_work(self, 0).is_err() {
            return Some(super::EvalValue::Unknown);
        }
        let bytes = match index {
            super::EvalValue::BitVec { value, width: 64 } => value.bits().max(64).div_ceil(8),
            super::EvalValue::Rational(value) if value.is_integer() => {
                value.numer().bits().max(1).div_ceil(8)
            }
            _ => return Some(super::EvalValue::Unknown),
        };
        let Ok(bytes) = usize::try_from(bytes) else {
            return Some(super::EvalValue::Unknown);
        };
        if model.charge_functional_array_work(self, bytes + 1).is_err() {
            return Some(super::EvalValue::Unknown);
        }
        let key = match index {
            super::EvalValue::BitVec { value, width: 64 } => ModelValue::bitvec(value.clone(), 64),
            super::EvalValue::Rational(value) if value.is_integer() => {
                ModelValue::Int(value.to_integer())
            }
            _ => return Some(super::EvalValue::Unknown),
        };
        let before = model.functional_work_left();
        let mut work = before;
        let result = value.read_with_stop(&key, &mut work, &mut || {
            self.poll_evaluation_stop().is_err()
        });
        if model
            .charge_functional_array_work(self, before - work)
            .is_err()
        {
            return Some(super::EvalValue::Unknown);
        }
        Some(
            result
                .as_ref()
                .map_or(super::EvalValue::Unknown, super::dt_construct::mv_to_eval),
        )
    }

    pub(super) fn functional_array_equality(
        &self,
        model: &Model,
        equality: TermId,
        args: &[TermId],
    ) -> Option<super::EvalValue> {
        let mut owned = false;
        for &term in args {
            match model.functional_array_value(self, term) {
                Ok(Some(_)) => owned = true,
                Ok(None) => {}
                Err(_) => return Some(super::EvalValue::Unknown),
            }
        }
        if !owned {
            return None;
        }
        let view = super::independent_gate::IndependentModelView::new(self, model);
        let result = Evaluator::new(&self.ctx.terms, &view).evaluate(equality);
        Some(match result {
            EvalOutcome::Value(ModelValue::Bool(value)) => super::EvalValue::Bool(value),
            _ => super::EvalValue::Unknown,
        })
    }

    pub(super) fn functional_array_render(
        &self,
        model: &Model,
        term: TermId,
    ) -> Result<Option<String>, String> {
        let Some(value) = model.functional_array_value(self, term)? else {
            return Ok(None);
        };
        model.charge_functional_array_work(self, 0)?;
        let before = model.functional_work_left();
        let mut work = before;
        let result = value
            .to_smtlib_with_stop(&mut work, &mut || self.poll_evaluation_stop().is_err())
            .map_err(|error| error.to_string());
        model.charge_functional_array_work(self, before - work)?;
        result.map(Some)
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "functional_arrays/snapshot_terms.rs"]
mod snapshot_terms;
