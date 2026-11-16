// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Immutable field-candidate DATA; no model or theorem publication authority.
use super::{evaluation_copies, EvalValue, EvaluationArena, Executor, Model};
use crate::executor_types::UnknownOrigin;
use ay_core::term::{TermConstructionAdmission, TermStoreSnapshotStamp};
use ay_core::{FiniteFieldSort, Sort, TermData, TermId};
use ay_frontend::SourceContextStamp;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum FieldScalar {
    Bool(bool),
    Field { value: u32, field: FiniteFieldSort },
}
impl FieldScalar {
    fn matches(self, exec: &Executor, term: TermId) -> bool {
        if !matches!(exec.ctx.terms.get(term), TermData::Var(..)) {
            return false;
        }
        match self {
            Self::Bool(_) => exec.ctx.terms.sort(term) == &Sort::Bool,
            Self::Field { value, field } => {
                value < field.modulus() && exec.ctx.terms.sort(term) == &Sort::FiniteField(field)
            }
        }
    }
    fn value(self) -> EvalValue {
        match self {
            Self::Bool(value) => EvalValue::Bool(value),
            Self::Field { value, field } => EvalValue::FiniteField { value, field },
        }
    }
}

#[derive(Debug)]
struct Payload {
    source: SourceContextStamp,
    store: TermStoreSnapshotStamp,
    // Payload drops before its original prepaid arena custody.
    rows: Vec<(TermId, FieldScalar)>,
    memory: evaluation_copies::RetainedEvaluationMemory,
}
#[derive(Debug, Clone, Default)]
pub(super) struct FieldAssignments(Option<Arc<Payload>>);

/// A current immutable read borrows one original counter through all nested
/// scalar evaluations and keeps actual DATA alive until memo cleanup finishes.
pub(in crate::executor) struct FieldAssignmentRead {
    _scope: evaluation_copies::EvaluationCopyScope,
    _payload: Arc<Payload>,
    _charge: Option<EvaluationArena>,
}

impl Model {
    /// Copies only canonical scalar leaves. Both copy admission and lifetime
    /// retention refer to the original current attempt, never a new read grant.
    pub(in crate::executor) fn install_field_assignments(
        &mut self,
        exec: &Executor,
        rows: &[(TermId, FieldScalar)],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<()> {
        let source = exec.ctx.source_context_stamp();
        let store = exec.ctx.terms.snapshot_stamp();
        let scope = evaluation_copies::EvaluationCopyScope::enter(exec).ok()?;
        let admission = scope.read_admission(exec);
        let metadata = size_of::<Payload>().checked_add(2 * size_of::<usize>())?;
        if !progress(0, 0) {
            return None;
        }
        admission.admit(0, metadata).ok()?;
        let mut copied = Vec::new();
        ay_core::term::reserve_counted(&mut copied, rows.len(), &admission).ok()?;
        for &(term, value) in rows {
            if !progress(1, 0)
                || admission.check().is_err()
                || term.index() >= exec.ctx.terms.len()
                || !value.matches(exec, term)
            {
                return None;
            }
            copied.push((term, value));
        }
        // Fixed-width keys/values: unstable sort needs no auxiliary buffer.
        let levels = copied.len().bit_width() as usize + 1;
        if !progress(copied.len().checked_mul(levels)?, 0) || admission.check().is_err() {
            return None;
        }
        copied.sort_unstable_by_key(|(term, _)| term.index());
        for pair in copied.windows(2) {
            if !progress(1, 0) || admission.check().is_err() || pair[0].0 == pair[1].0 {
                return None;
            }
        }
        let memory = scope.retain_data_memory(exec)?;
        if !progress(0, 0)
            || admission.check().is_err()
            || source != exec.ctx.source_context_stamp()
            || store != exec.ctx.terms.snapshot_stamp()
        {
            return None;
        }
        let payload = Payload {
            source,
            store,
            rows: copied,
            memory,
        };
        self.revoke_all_quantified_model_seals();
        self.field_assignments = FieldAssignments(Some(Arc::new(payload)));
        super::eval_memo_clear();
        Some(())
    }

    pub(in crate::executor) fn has_field_assignments(&self) -> bool {
        self.field_assignments.0.is_some()
    }

    pub(in crate::executor) fn read_field_assignments(
        &self,
        exec: &Executor,
    ) -> Result<Option<FieldAssignmentRead>, UnknownOrigin> {
        let Some(payload) = &self.field_assignments.0 else {
            return Ok(None);
        };
        let scope = evaluation_copies::EvaluationCopyScope::enter(exec)?;
        let charge = self.field_read_charge(exec)?;
        if !evaluation_copies::validate(exec) {
            return Err(exec
                .evaluation_stop_origin()
                .unwrap_or(UnknownOrigin::IncompleteSolverLane));
        }
        Ok(Some(FieldAssignmentRead {
            _scope: scope,
            _payload: Arc::clone(payload),
            _charge: charge,
        }))
    }

    pub(in crate::executor) fn field_read_charge(
        &self,
        exec: &Executor,
    ) -> Result<Option<EvaluationArena>, UnknownOrigin> {
        let Some(payload) = &self.field_assignments.0 else {
            return Ok(None);
        };
        if payload.source != exec.ctx.source_context_stamp()
            || !payload.store.is_append_only_prefix_of(&exec.ctx.terms)
        {
            return Err(UnknownOrigin::IncompleteSolverLane);
        }
        let charge = payload.memory.read_charge(exec)?;
        if payload.source != exec.ctx.source_context_stamp()
            || !payload.store.is_append_only_prefix_of(&exec.ctx.terms)
        {
            return Err(UnknownOrigin::IncompleteSolverLane);
        }
        Ok(Some(charge))
    }

    /// Copy scalar rows into producer scratch under that scratch owner's
    /// progress, without exposing a cloneable mutable model assignment map.
    pub(in crate::executor) fn visit_field_assignments(
        &self,
        exec: &Executor,
        visit: &mut dyn FnMut(TermId, EvalValue) -> bool,
    ) -> Result<(), UnknownOrigin> {
        let Some(payload) = &self.field_assignments.0 else {
            return Ok(());
        };
        if payload.source != exec.ctx.source_context_stamp()
            || !payload.store.is_append_only_prefix_of(&exec.ctx.terms)
        {
            return Err(UnknownOrigin::IncompleteSolverLane);
        }
        for &(term, value) in &payload.rows {
            if !visit(term, value.value()) {
                return Err(exec
                    .evaluation_stop_origin()
                    .unwrap_or(UnknownOrigin::IncompleteSolverLane));
            }
        }
        Ok(())
    }

    pub(in crate::executor) fn field_assignment_value(
        &self,
        exec: &Executor,
        term: TermId,
    ) -> Result<Option<EvalValue>, UnknownOrigin> {
        let Some(payload) = &self.field_assignments.0 else {
            return Ok(None);
        };
        if payload.source != exec.ctx.source_context_stamp()
            || !payload.store.is_append_only_prefix_of(&exec.ctx.terms)
        {
            return Err(UnknownOrigin::IncompleteSolverLane);
        }
        // This is actual current-read work, not a debit or poll of the
        // completed solve's retained controls. Fixed-width binary lookup
        // compares at most this many keys.
        if evaluation_copies::active() && !evaluation_copies::validate(exec) {
            return Err(exec
                .evaluation_stop_origin()
                .unwrap_or(UnknownOrigin::IncompleteSolverLane));
        }
        exec.poll_evaluation_stop()?;
        let work = payload.rows.len().bit_width() as u64 + 1;
        #[expect(
            clippy::collection_is_never_read,
            reason = "owning the fallback evaluation scope keeps the current read admission live through the final source check and scalar lookup"
        )]
        let _fallback_scope;
        if let Some(guard) = ay_core::resource::current_guard() {
            _fallback_scope = None;
            if let Err(stop) = guard.tick(work) {
                use ay_core::resource::Exhausted;
                let origin = match stop {
                    Exhausted::Cancelled => UnknownOrigin::InterruptFlag,
                    Exhausted::Deadline | Exhausted::Cpu => UnknownOrigin::SolveDeadline,
                    Exhausted::Rlimit => UnknownOrigin::DeterministicResourceBudget,
                    Exhausted::Memory => UnknownOrigin::MemoryBudget,
                };
                return Err(exec.evaluation_attempt().record_stop(origin));
            }
        } else {
            // Ordinary no-Guard model reads still own the existing evaluation
            // counter. Entering a frame borrows that SAME current attempt;
            // repeated lookups cannot replenish its fallback work balance.
            let scope = evaluation_copies::EvaluationCopyScope::enter(exec)?;
            scope
                .read_admission(exec)
                .admit(work as usize, 0)
                .map_err(|_| {
                    exec.evaluation_stop_origin()
                        .unwrap_or(UnknownOrigin::IncompleteSolverLane)
                })?;
            _fallback_scope = Some(scope);
        }
        // Every potentially reentrant native admission precedes this final
        // source bookend. No callback runs between it and the scalar lookup.
        if payload.source != exec.ctx.source_context_stamp()
            || !payload.store.is_append_only_prefix_of(&exec.ctx.terms)
        {
            return Err(UnknownOrigin::IncompleteSolverLane);
        }
        let Ok(index) = payload
            .rows
            .binary_search_by_key(&term.index(), |(id, _)| id.index())
        else {
            return Ok(None);
        };
        let (_, value) = payload.rows[index];
        if !value.matches(exec, term) {
            return Err(UnknownOrigin::IncompleteSolverLane);
        }
        Ok(Some(value.value()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn immutable_field_rows_share_actual_storage_and_refuse_foreign_source() {
        let mut exec = Executor::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = exec.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let b = exec.ctx.terms.mk_var("b", Sort::Bool);
        let mut model = Model::empty();
        let mut owner = super::super::CandidateOwner::capture(&exec).unwrap();
        model
            .install_field_assignments(
                &exec,
                &[
                    (b, FieldScalar::Bool(true)),
                    (x, FieldScalar::Field { value: 3, field }),
                ],
                &mut |work, bytes| owner.pay(work, bytes).is_ok(),
            )
            .unwrap();
        let cloned = model.clone();
        assert!(Arc::ptr_eq(
            model.field_assignments.0.as_ref().unwrap(),
            cloned.field_assignments.0.as_ref().unwrap()
        ));
        assert!(model.completed_values.is_empty() && model.bool_overrides.is_empty());
        assert_eq!(
            cloned.field_assignment_value(&exec, x).unwrap(),
            Some(EvalValue::FiniteField { value: 3, field })
        );
        let mut foreign = Executor::new();
        let _ = foreign.ctx.terms.mk_var("x", Sort::FiniteField(field));
        assert!(cloned.field_assignment_value(&foreign, x).is_err());
    }

    #[test]
    fn field_payload_rejects_noncanonical_duplicate_and_wrong_sort_rows() {
        let mut exec = Executor::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = exec.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let mut model = Model::empty();
        let mut owner = super::super::CandidateOwner::capture(&exec).unwrap();
        for rows in [
            vec![(x, FieldScalar::Field { value: 7, field })],
            vec![(x, FieldScalar::Bool(true))],
            vec![
                (x, FieldScalar::Field { value: 1, field }),
                (x, FieldScalar::Field { value: 2, field }),
            ],
        ] {
            assert!(model
                .install_field_assignments(&exec, &rows, &mut |work, bytes| owner
                    .pay(work, bytes)
                    .is_ok())
                .is_none());
            assert!(!model.has_field_assignments());
        }
    }

    #[test]
    fn callback_retiring_original_install_owner_stops_before_row_preparation() {
        let mut exec = Executor::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = exec.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let mut model = Model::empty();
        let mut changed_read = None;
        let mut prepared_work = 0usize;
        assert!(model
            .install_field_assignments(
                &exec,
                &[(x, FieldScalar::Field { value: 3, field })],
                &mut |work, _| {
                    prepared_work += work;
                    if changed_read.is_none() {
                        changed_read = Some(exec.begin_external_evaluation_read());
                    }
                    true
                }
            )
            .is_none());
        assert_eq!(prepared_work, 0);
        assert!(!model.has_field_assignments());
        drop(changed_read);
        assert!(exec.evaluation_stop_origin().is_some());
    }

    #[test]
    fn recursive_field_read_retains_one_scope_and_shared_dag_progress() {
        let mut exec = Executor::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = exec.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let mut rows = vec![(x, FieldScalar::Field { value: 1, field })];
        let mut term = x;
        let mut expected = 1u32;
        for i in 0..20u32 {
            let y = exec
                .ctx
                .terms
                .mk_var(format!("y{i}"), Sort::FiniteField(field));
            let value = i % 7;
            rows.push((y, FieldScalar::Field { value, field }));
            term = exec
                .ctx
                .terms
                .mk_ff_app("ff.add", &[term, y, term])
                .unwrap();
            expected = (2 * expected + value) % 7;
        }
        let mut model = Model::empty();
        let mut owner = super::super::CandidateOwner::capture(&exec).unwrap();
        model
            .install_field_assignments(&exec, &rows, &mut |work, bytes| {
                owner.pay(work, bytes).is_ok()
            })
            .unwrap();
        let guard = ay_core::resource::Guard::root_child(
            ay_core::resource::ChildSpec::new(ay_core::resource::NodeLabel::Check)
                .with_rlimit(Some(10_000)),
        );
        let _scope = guard.enter();
        // The ordinary immutable render/read caller establishes this session;
        // retaining the field scope must not clear it at each scalar leaf.
        let _memo = super::super::EvalMemoSession::new();
        assert_eq!(
            exec.evaluate_term(&model, term),
            EvalValue::FiniteField {
                value: expected,
                field
            }
        );
        assert!(guard.remaining().unwrap() > 0);
    }

    #[test]
    fn no_guard_field_lookups_debit_the_same_current_read_and_cannot_refresh_it() {
        let mut exec = Executor::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = exec.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let mut model = Model::empty();
        let mut owner = super::super::CandidateOwner::capture(&exec).unwrap();
        model
            .install_field_assignments(
                &exec,
                &[(x, FieldScalar::Field { value: 3, field })],
                &mut |work, bytes| owner.pay(work, bytes).is_ok(),
            )
            .unwrap();
        assert!(
            ay_core::resource::current_guard().is_none(),
            "control requires the real no-Guard read path"
        );
        {
            let _read = exec.begin_external_evaluation_read();
            let used = exec.evaluation_attempt().functional_work_counter();
            let before = used.load(std::sync::atomic::Ordering::Acquire);
            assert!(model.field_assignment_value(&exec, x).unwrap().is_some());
            assert!(used.load(std::sync::atomic::Ordering::Acquire) > before);
            // Spend through actual lookups, rather than manufacturing a refused
            // counter. A real batch retains one owner; nested getter frames
            // still borrow the exact same balance as the preceding direct read.
            let copies = evaluation_copies::EvaluationCopyScope::enter(&exec).unwrap();
            let cloned = model.clone();
            let mut refused = false;
            for _ in 0..super::super::functional_arrays::MAX_FUNCTIONAL_WORK {
                if cloned.field_assignment_value(&exec, x).is_err() {
                    refused = true;
                    break;
                }
            }
            assert!(refused);
            drop(copies);
            assert!(model.field_assignment_value(&exec, x).is_err());
        }
        let _read = exec.begin_external_evaluation_read();
        assert_eq!(
            model.field_assignment_value(&exec, x).unwrap(),
            Some(EvalValue::FiniteField { value: 3, field })
        );
    }

    #[test]
    fn field_payload_current_read_memory_refusal_does_not_corrupt_old_data() {
        let mut exec = Executor::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = exec.ctx.terms.mk_var("x", Sort::FiniteField(field));
        let mut model = Model::empty();
        let mut owner = super::super::CandidateOwner::capture(&exec).unwrap();
        model
            .install_field_assignments(
                &exec,
                &[(x, FieldScalar::Field { value: 3, field })],
                &mut |work, bytes| owner.pay(work, bytes).is_ok(),
            )
            .unwrap();
        exec.term_memory_limit = Some(0);
        {
            let _read = exec.begin_external_evaluation_read();
            assert!(model.field_read_charge(&exec).is_err());
        }
        exec.term_memory_limit = None;
        let _read = exec.begin_external_evaluation_read();
        let _charge = model.field_read_charge(&exec).unwrap();
        assert_eq!(
            model.field_assignment_value(&exec, x).unwrap(),
            Some(EvalValue::FiniteField { value: 3, field })
        );
    }
}
