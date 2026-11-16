// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original model DATA construction custody, independent of array completion.
use super::{Executor, Model};
use crate::executor::QueryAuthorityEpoch;
use crate::executor_types::UnknownOrigin;
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::TermId;
use ay_frontend::SourceContextStamp;
use std::ops::ControlFlow;
use std::sync::{atomic::AtomicUsize, Arc};

pub(super) struct ModelConstructionOwner {
    original_attempt: super::EvaluationAttempt,
    source: SourceContextStamp,
    query: QueryAuthorityEpoch,
    store: TermStoreSnapshotStamp,
    roots: Vec<TermId>,
    pub(super) used: Arc<AtomicUsize>,
    // Observability only: never consulted for permission or allowance.
    #[cfg(test)]
    metadata_root_steps: AtomicUsize,
    // Drop retained ID storage before releasing its original arena slot.
    _arena: super::EvaluationArena,
}

impl std::fmt::Debug for ModelConstructionOwner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModelConstructionOwner")
            .field("source", &self.source)
            .field("query", &self.query)
            .field("store", &self.store)
            .field("root_count", &self.roots.len())
            .finish_non_exhaustive()
    }
}

impl ModelConstructionOwner {
    pub(super) fn capture(exec: &Executor) -> Option<Self> {
        let attempt = exec.evaluation_attempt();
        let used = attempt.functional_work_counter();
        Self::capture_retaining(exec, used, attempt)
    }

    fn capture_retaining(
        exec: &Executor,
        used: Arc<AtomicUsize>,
        original_attempt: super::EvaluationAttempt,
    ) -> Option<Self> {
        let attempt = exec.evaluation_attempt();
        pay_metadata(exec, 0, 0).ok()?;
        let metadata = Self::metadata_bytes;
        let memory_refusal = || {
            attempt.record_stop(UnknownOrigin::MemoryBudget);
            None
        };
        let Some(bound) = exec.independent_gate_query_root_bound() else {
            return memory_refusal();
        };
        let arena = match attempt.temporary_arena() {
            Ok(arena) => arena,
            Err(_) => return memory_refusal(),
        };
        let mut roots = Vec::new();
        let Some(bytes) = metadata(bound) else {
            return memory_refusal();
        };
        if pay_metadata(exec, 0, bytes).is_err() {
            return None;
        }
        let prepaid_bytes = bytes;
        if arena
            .check_usage(
                exec.ctx.terms.true_memory_bytes(),
                bytes,
                exec.evaluation_term_memory_limit(),
            )
            .is_err()
            || roots.try_reserve_exact(bound).is_err()
        {
            return memory_refusal();
        }
        // Exact reserve can conservatively expose more capacity. Price it
        // before copying any source IDs into the retained buffer.
        let Some(bytes) = metadata(roots.capacity()) else {
            return memory_refusal();
        };
        if pay_metadata(exec, 0, bytes.saturating_sub(prepaid_bytes)).is_err() {
            return None;
        }
        if arena
            .check_usage(
                exec.ctx.terms.true_memory_bytes(),
                bytes,
                exec.evaluation_term_memory_limit(),
            )
            .is_err()
        {
            return memory_refusal();
        }
        #[cfg(test)]
        let mut metadata_steps = 0usize;
        let _ = exec
            .visit_independent_gate_query_roots(
                || {
                    pay_metadata(exec, 1, 0)?;
                    #[cfg(test)]
                    {
                        metadata_steps = metadata_steps.saturating_add(1);
                    }
                    Ok::<_, UnknownOrigin>(())
                },
                |root| {
                    roots.push(root);
                    ControlFlow::Continue(())
                },
            )
            .ok()?;
        pay_metadata(exec, 0, 0).ok()?;
        Some(Self {
            original_attempt,
            source: exec.ctx.source_context_stamp(),
            query: exec.query_authority_epoch.clone(),
            store: exec.ctx.terms.snapshot_stamp(),
            roots,
            used,
            #[cfg(test)]
            metadata_root_steps: AtomicUsize::new(metadata_steps),
            _arena: arena,
        })
    }

    fn metadata_bytes(capacity: usize) -> Option<usize> {
        capacity
            .checked_mul(size_of::<TermId>())
            .and_then(|bytes| bytes.checked_add(size_of::<Self>()))
            .and_then(|bytes| bytes.checked_add(2 * size_of::<usize>()))
    }

    #[cfg(test)]
    pub(super) fn retained_metadata_bytes_for_test(&self) -> usize {
        Self::metadata_bytes(self.roots.capacity()).expect("already admitted metadata capacity")
    }

    // Interpretation can test this retained DATA against another obligation.
    // Declaration/schema readers still validate their native handles; context
    // identity and the physical prefix prevent cross-store slot substitution.
    pub(super) fn validate_data_source(&self, exec: &Executor) -> bool {
        self.source
            .is_same_context(&exec.ctx.source_context_stamp())
            && self.store.is_append_only_prefix_of(&exec.ctx.terms)
    }

    pub(super) fn charge(&self, exec: &Executor, amount: usize) -> Result<(), String> {
        if !super::recovery_admission::pay_for(exec, amount, 0) {
            return Err("model construction recovery admission refused".to_owned());
        }
        super::functional_arrays::debit_retained_work(
            exec,
            &self.used,
            &self.original_attempt,
            // `pay_for` already debited an active read with this exact owner.
            // Distinct retained/read ledgers must each pay; aliasing one ledger
            // does not turn a single event into two units of work.
            if super::evaluation_copies::charges_work_to(&self.used) {
                0
            } else {
                amount
            },
        )
    }

    /// A constructor request that stops while checking metadata still belongs
    /// to its original attempt. This is not used by DATA-only validation, and
    /// a different read's stop never poisons this earlier model's ledger.
    pub(super) fn latch_original_constructor_stop(&self, exec: &Executor) {
        let _ = super::functional_arrays::debit_retained_work(
            exec,
            &self.used,
            &self.original_attempt,
            0,
        );
    }

    pub(super) fn query_binding_matches(&self, exec: &Executor) -> Result<bool, UnknownOrigin> {
        pay_metadata(exec, 0, 0)?;
        if self.source != exec.ctx.source_context_stamp()
            || !self.query.is_same_epoch(&exec.query_authority_epoch)
            || !self.store.is_append_only_prefix_of(&exec.ctx.terms)
        {
            return Ok(false);
        }
        let mut position = 0usize;
        let result = exec.visit_independent_gate_query_roots(
            || {
                pay_metadata(exec, 1, 0)?;
                #[cfg(test)]
                {
                    self.metadata_root_steps
                        .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                Ok::<_, UnknownOrigin>(())
            },
            |root| {
                if self.roots.get(position) != Some(&root) {
                    return ControlFlow::Break(());
                }
                position += 1;
                ControlFlow::Continue(())
            },
        )?;
        pay_metadata(exec, 0, 0)?;
        Ok(result.is_continue() && position == self.roots.len())
    }

    pub(super) fn validate(&self, exec: &Executor) -> bool {
        self.query_binding_matches(exec).unwrap_or(false)
    }
}

/// DATA metadata belongs to the enclosing native operation, not to the
/// specialized cumulative FP/functional-construction ledger. No timer or
/// allowance is created here; callers poll this INSIDE their borrowed walks.
pub(super) fn pay_metadata(
    exec: &Executor,
    work: usize,
    bytes: usize,
) -> Result<(), UnknownOrigin> {
    exec.poll_evaluation_stop()?;
    if !super::recovery_admission::pay_for(exec, work, bytes) {
        return Err(exec
            .evaluation_attempt()
            .record_stop(UnknownOrigin::DeterministicResourceBudget));
    }
    exec.poll_evaluation_stop()
}

fn query_roots_match(exec: &Executor, roots: &[TermId]) -> Result<bool, UnknownOrigin> {
    pay_metadata(exec, 0, 0)?;
    let mut position = 0usize;
    let result = exec.visit_independent_gate_query_roots(
        || pay_metadata(exec, 1, 0),
        |root| {
            if roots.get(position) != Some(&root) {
                return ControlFlow::Break(());
            }
            position += 1;
            ControlFlow::Continue(())
        },
    )?;
    pay_metadata(exec, 0, 0)?;
    Ok(result.is_continue() && position == roots.len())
}

/// Reconstruct accounting only from the owned model consumed by the native
/// checked finite-table stage. The old DATA record remains immutable, and its
/// cumulative counter/attempt are conserved; this supplies no proof authority.
pub(in crate::executor) fn reconstruct_checked_finite_model_owner(
    exec: &Executor,
    checked: crate::executor::mbqi::CheckedFiniteModelConstruction<'_>,
) -> Option<Model> {
    let (mut model, roots) = checked.into_parts();
    reconstruct_checked_owner(exec, &mut model, roots)?;
    Some(model)
}

pub(in crate::executor) fn reconstruct_checked_cegqi_model_owner(
    exec: &Executor,
    checked: crate::executor::quantifier_loop::result_mapping::CheckedCegqiModelConstruction<'_>,
) -> Option<Box<Model>> {
    let (mut model, roots) = checked.into_parts();
    // This model descends from the ordinary validated-model certificate,
    // whose SAT funnel requires an original owner. Missing custody is not a
    // reason to borrow the current attempt's counter as a replacement.
    model.construction_owner.as_ref()?;
    reconstruct_checked_owner(exec, &mut model, roots)?;
    Some(model)
}

pub(in crate::executor) fn reconstruct_checked_ground_model_owner(
    exec: &Executor,
    checked: crate::executor::quantifier_loop::result_mapping::CheckedGroundModelConstruction<'_>,
) -> Option<Model> {
    let (mut model, roots) = checked.into_parts();
    model.construction_owner.as_ref()?;
    reconstruct_checked_owner(exec, &mut model, roots)?;
    Some(model)
}

pub(in crate::executor) fn reconstruct_checked_dt_model_owner(
    exec: &Executor,
    checked: crate::executor::mbqi::CheckedDtModelConstruction<'_>,
) -> Option<()> {
    let (model, roots) = checked.into_parts();
    let Some(owner) = model.construction_owner.as_ref() else {
        // A fresh completed theorem model acquires its first owner at the
        // ordinary final candidate binder, never from this transfer.
        return Some(());
    };
    if owner.query_binding_matches(exec).ok()? {
        return Some(());
    }
    reconstruct_checked_owner(exec, model, roots)
}

pub(super) fn reconstruct_scoped_optimization_model_owner(
    exec: &Executor,
    handoff: super::sat_emit::ScopedOptimizationModel<'_>,
) -> Option<()> {
    let (model, roots) = handoff.into_parts();
    reconstruct_checked_owner(exec, model, roots)
}

/// Only native construction witnesses may transfer retained accounting into
/// a different query window. This never renews a proof or semantic seal.
fn reconstruct_checked_owner(exec: &Executor, model: &mut Model, roots: &[TermId]) -> Option<()> {
    if !query_roots_match(exec, roots).ok()? {
        return None;
    }
    // The finite-table producer can legitimately start from Model::empty()
    // when no ground witness is needed. Leave that DATA unbound: only its
    // genuine final candidate binder can attach the existing current attempt,
    // and the public SAT funnel separately requires a current owner.
    if let Some(prior) = &model.construction_owner {
        if !prior.validate_data_source(exec) {
            return None;
        }
        if !prior.query_binding_matches(exec).ok()? {
            let replacement = ModelConstructionOwner::capture_retaining(
                exec,
                Arc::clone(&prior.used),
                prior.original_attempt.clone(),
            )?;
            model.construction_owner = Some(Arc::new(replacement));
        }
    }
    Some(())
}

#[cfg(test)]
impl Model {
    pub(in crate::executor) fn clear_construction_owner_for_test(&mut self) {
        self.construction_owner = None;
    }
}

impl Model {
    pub(super) fn validate_construction_owner(&self, exec: &Executor) -> bool {
        self.construction_owner
            .as_ref()
            .is_some_and(|owner| owner.validate(exec))
    }
}

/// One actual immutable render/value batch. Public single-term retrieval uses
/// the same batch entry with one element; internal recursive evaluation does
/// not repeatedly re-scan the source window for each symbol or field.
pub(super) struct ModelConstructionRead<'a> {
    exec: &'a Executor,
    model: &'a Model,
    // Retire memo DATA before releasing either retained-input read charge.
    _copy_scope: Option<super::evaluation_copies::EvaluationCopyScope>,
    _array_read: Option<super::EvaluationArena>,
    _field_read: Option<super::EvaluationArena>,
}

/// Interpretation-only borrowed witness; it authenticates DATA, not SAT.
pub(super) struct ModelDataRead<'a> {
    exec: &'a Executor,
    model: &'a Model,
    // Retire memo DATA before releasing either retained-input read charge.
    _copy_scope: Option<super::evaluation_copies::EvaluationCopyScope>,
    _array_read: Option<super::EvaluationArena>,
    _field_read: Option<super::EvaluationArena>,
}

pub(super) trait ModelRead {
    fn model(&self) -> &Model;
    fn evaluate(&self, term: TermId) -> super::EvalValue;
    fn check_array_functions(
        &self,
        term: TermId,
    ) -> Result<Option<ay_model_check::ModelValue>, String>;
}

fn retained_read_copy_scope(
    exec: &Executor,
    model: &Model,
) -> Result<Option<super::evaluation_copies::EvaluationCopyScope>, String> {
    let retained = model.has_field_assignments()
        || model.has_constant_array_functions()
        || exec
            .has_array_function_declarations()
            .map_err(|origin| format!("{origin:?}"))?;
    // Legacy variable/select/store array DATA already has its original read
    // binding. Only actual retained packages or declared array functions need
    // this specialized copy/coherence owner; array presence alone must not
    // impose the unrelated functional-work ceiling on ordinary model output.
    if retained {
        let scope = super::evaluation_copies::EvaluationCopyScope::enter(exec)
            .map_err(|origin| format!("{origin:?}"))?;
        exec.check_evaluation_read()?;
        if !super::evaluation_copies::validate(exec) {
            return Err("retained model read source changed".to_owned());
        }
        Ok(Some(scope))
    } else {
        Ok(None)
    }
}

impl ModelRead for ModelDataRead<'_> {
    fn check_array_functions(
        &self,
        term: TermId,
    ) -> Result<Option<ay_model_check::ModelValue>, String> {
        self.exec
            .check_coherent_array_function_read(self.model, term, self._copy_scope.as_ref())
    }
    fn model(&self) -> &Model {
        self.model
    }
    fn evaluate(&self, term: TermId) -> super::EvalValue {
        self.exec.evaluate_term_source_validated(self.model, term)
    }
}

impl<'a> ModelDataRead<'a> {
    fn new(exec: &'a Executor, model: &'a Model) -> Result<Self, String> {
        exec.check_evaluation_read()?;
        if !exec.materialized_scalar_functions_current(model) {
            return Err("materialized scalar function model is stale".to_owned());
        }
        if model
            .construction_owner
            .as_ref()
            .is_some_and(|owner| !owner.validate_data_source(exec))
        {
            return Err("model construction DATA source changed".to_owned());
        }
        model.validate_functional_array_source(exec)?;
        exec.check_evaluation_read()?;
        let copy_scope = retained_read_copy_scope(exec, model)?;
        let array_read = model
            .constant_array_read_charge(exec)
            .map_err(|origin| format!("{origin:?}"))?;
        let field_read = model
            .field_read_charge(exec)
            .map_err(|origin| format!("{origin:?}"))?;
        if copy_scope.is_some() && !super::evaluation_copies::validate(exec) {
            return Err("retained model read source changed".to_owned());
        }
        Ok(Self {
            exec,
            model,
            _copy_scope: copy_scope,
            _array_read: array_read,
            _field_read: field_read,
        })
    }
    fn finish(self) -> Result<(), String> {
        self.exec.check_evaluation_read()?;
        if self
            ._copy_scope
            .as_ref()
            .is_some_and(|_| !super::evaluation_copies::validate(self.exec))
        {
            return Err("retained model read source changed".to_owned());
        }
        Ok(())
    }
}

impl ModelRead for ModelConstructionRead<'_> {
    fn check_array_functions(
        &self,
        term: TermId,
    ) -> Result<Option<ay_model_check::ModelValue>, String> {
        self.exec
            .check_coherent_array_function_read(self.model, term, self._copy_scope.as_ref())
    }
    fn model(&self) -> &Model {
        self.model
    }
    fn evaluate(&self, term: TermId) -> super::EvalValue {
        self.exec.evaluate_term_source_validated(self.model, term)
    }
}

impl<'a> ModelConstructionRead<'a> {
    pub(super) fn new(exec: &'a Executor, model: &'a Model) -> Result<Self, String> {
        exec.check_evaluation_read()?;
        if !exec.materialized_scalar_functions_current(model) {
            return Err("materialized scalar function model is stale".to_owned());
        }
        if model
            .construction_owner
            .as_ref()
            .is_some_and(|owner| !owner.validate(exec))
        {
            return Err("model construction source/query snapshot changed".to_owned());
        }
        model.validate_functional_array_source(exec)?;
        exec.check_evaluation_read()?;
        let copy_scope = retained_read_copy_scope(exec, model)?;
        let array_read = model
            .constant_array_read_charge(exec)
            .map_err(|origin| format!("{origin:?}"))?;
        let field_read = model
            .field_read_charge(exec)
            .map_err(|origin| format!("{origin:?}"))?;
        if copy_scope.is_some() && !super::evaluation_copies::validate(exec) {
            return Err("retained model read source changed".to_owned());
        }
        Ok(Self {
            exec,
            model,
            _copy_scope: copy_scope,
            _array_read: array_read,
            _field_read: field_read,
        })
    }

    pub(super) fn finish(self) -> Result<(), String> {
        // Plain source/model fields cannot change while these immutable borrows
        // live. Resource controls remain live and must cross the closing fence.
        self.exec.check_evaluation_read()?;
        if self
            ._copy_scope
            .as_ref()
            .is_some_and(|_| !super::evaluation_copies::validate(self.exec))
        {
            return Err("retained model read source changed".to_owned());
        }
        Ok(())
    }
}

impl Executor {
    /// Attach accounting only to a genuine current candidate. This neither
    /// changes semantic model data nor revokes/re-mints any checked model seal.
    pub(super) fn bind_model_construction_owner(&self, model: &mut Model) -> bool {
        if self.poll_evaluation_stop().is_err() || super::scoped_term_evaluation_override_active() {
            return false;
        }
        if let Some(owner) = &model.construction_owner {
            return owner.validate(self);
        }
        if !super::independent_gate::IndependentModelView::new(self, model)
            .canonical_theory_bindings_are_coherent()
        {
            return false;
        }
        // A complete array package has its own original counter. An unbound
        // package must not acquire a replacement counter through this seam.
        if model.functional_arrays.is_some() {
            return false;
        }
        let Some(owner) = ModelConstructionOwner::capture(self) else {
            return false;
        };
        model.construction_owner = Some(Arc::new(owner));
        true
    }

    pub(super) fn bind_current_candidate_construction_owner(&mut self) -> bool {
        let Some(mut model) = self.last_model.take() else {
            return false;
        };
        let bound = self.bind_model_construction_owner(&mut model);
        self.last_model = Some(model);
        bound
    }

    pub(super) fn with_model_data_read(
        &self,
        model: &Model,
        read: impl FnOnce(&dyn ModelRead) -> String,
    ) -> String {
        let witness = match ModelDataRead::new(self, model) {
            Ok(witness) => witness,
            Err(error) => return format!("(error \"{error}\")"),
        };
        let output = read(&witness);
        match witness.finish() {
            Ok(()) => output,
            Err(error) => format!("(error \"{error}\")"),
        }
    }

    pub(super) fn with_model_construction_read(
        &self,
        model: &Model,
        read: impl FnOnce(&dyn ModelRead) -> String,
    ) -> String {
        let witness = match ModelConstructionRead::new(self, model) {
            Ok(witness) => witness,
            Err(error) => return format!("(error \"{error}\")"),
        };
        let output = read(&witness);
        match witness.finish() {
            Ok(()) => output,
            Err(error) => format!("(error \"{error}\")"),
        }
    }
}

#[cfg(test)]
impl Executor {
    pub(crate) fn model_construction_metadata_steps_for_test(&self) -> Option<usize> {
        self.last_model
            .as_ref()?
            .construction_owner
            .as_ref()
            .map(|owner| {
                owner
                    .metadata_root_steps
                    .load(std::sync::atomic::Ordering::Relaxed)
            })
    }

    pub(crate) fn model_construction_work_for_test(&self) -> Option<usize> {
        self.last_model
            .as_ref()?
            .construction_owner
            .as_ref()
            .map(|owner| owner.used.load(std::sync::atomic::Ordering::Acquire))
    }
}

#[cfg(test)]
mod tests {
    use super::super::functional_arrays::PinAdmission;
    use super::*;
    use ay_frontend::parse;
    use std::sync::atomic::Ordering;

    fn fixture() -> (Executor, Model) {
        let mut exec = Executor::new();
        exec.execute_all(&parse("(declare-const x (_ FloatingPoint 8 200)) (declare-fun f (Int) (_ FloatingPoint 8 200)) (assert (forall ((n Int)) (fp.leq (f n) x)))").unwrap()).unwrap();
        exec.begin_external_decision_query(false);
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.construction_owner.is_some());
        assert!(
            model.functional_arrays.is_none(),
            "unsupported array plan is not forged into data"
        );
        (exec, model)
    }

    #[test]
    fn unsupported_array_plan_retains_only_original_shared_model_counter() {
        let (exec, model) = fixture();
        let owner = model.construction_owner.as_ref().unwrap();
        assert!(Arc::ptr_eq(
            &owner.used,
            &exec.evaluation_attempt().functional_work_counter()
        ));
        let clone = model.clone();
        assert!(Arc::ptr_eq(
            owner,
            clone.construction_owner.as_ref().unwrap()
        ));
        let admission = PinAdmission::capture(&exec, &clone).unwrap();
        let before = owner.used.load(Ordering::Acquire);
        admission.pay(7, 0).unwrap();
        assert_eq!(owner.used.load(Ordering::Acquire), before + 7);
        assert!(admission.matches_model(&model));
        admission
            .finish(exec.ctx.terms.true_memory_bytes())
            .unwrap();
    }

    #[test]
    fn exact_fp_admission_charges_shared_and_distinct_ledgers_once() {
        use super::super::evaluation_copies::EvaluationCopyScope;
        use super::super::independent_gate::IndependentModelView;
        use ay_model_check::ModelView;
        let (exec, model) = fixture();
        let retained = &model.construction_owner.as_ref().unwrap().used;
        {
            let _scope = EvaluationCopyScope::enter(&exec).unwrap();
            let view = IndependentModelView::new(&exec, &model);
            let before = retained.load(Ordering::Acquire);
            view.admit_exact_fp_work(71, 19).unwrap();
            assert_eq!(retained.load(Ordering::Acquire), before + 71);
            let before = retained.load(Ordering::Acquire);
            view.charge_exact_fp_work(13).unwrap();
            assert_eq!(retained.load(Ordering::Acquire), before + 13);
        }
        let _read = exec.begin_external_evaluation_read();
        let current = exec.evaluation_attempt().functional_work_counter();
        assert!(!Arc::ptr_eq(retained, &current));
        let _scope = EvaluationCopyScope::enter(&exec).unwrap();
        let view = IndependentModelView::new(&exec, &model);
        let before = retained.load(Ordering::Acquire);
        let read_before = current.load(Ordering::Acquire);
        view.admit_exact_fp_work(71, 19).unwrap();
        assert_eq!(retained.load(Ordering::Acquire), before + 71);
        assert_eq!(current.load(Ordering::Acquire), read_before + 71);
        let remaining =
            super::super::functional_arrays::MAX_FUNCTIONAL_WORK - retained.load(Ordering::Acquire);
        assert!(view.admit_exact_fp_work(remaining + 1, 0).is_err());
        assert!(view.admit_exact_fp_work(1, 0).is_err());
        assert!(view.exact_fp_interrupted());
    }

    #[test]
    fn unchanged_attempt_cannot_replace_model_identity_or_rebind_an_old_owner() {
        let (mut exec, mut model) = fixture();
        let admission = PinAdmission::capture(&exec, &model).unwrap();
        let mut replacement = Model::empty();
        exec.install_functional_array_candidate(&mut replacement);
        assert!(
            !admission.matches_model(&replacement),
            "same budget does not mean same model"
        );
        admission
            .finish(exec.ctx.terms.true_memory_bytes())
            .unwrap();
        let original = Arc::clone(model.construction_owner.as_ref().unwrap());
        exec.execute_all(&parse("(declare-const later Int)").unwrap())
            .unwrap();
        exec.install_functional_array_candidate(&mut model);
        assert!(Arc::ptr_eq(
            &original,
            model.construction_owner.as_ref().unwrap()
        ));
        assert!(PinAdmission::capture(&exec, &model).is_err());
    }

    #[test]
    fn cloned_store_and_new_query_retire_original_binding_but_appends_do_not() {
        for replace_store in [false, true] {
            let (mut exec, model) = fixture();
            let _ = exec.ctx.terms.mk_int(99.into());
            assert!(model.validate_construction_owner(&exec));
            if replace_store {
                exec.ctx.terms = exec.ctx.terms.clone();
            } else {
                exec.begin_external_decision_query(false);
            }
            assert!(!model.validate_construction_owner(&exec));
            assert!(PinAdmission::capture(&exec, &model).is_err());
        }
    }
    #[test]
    fn canonical_root_or_assumption_change_refuses_with_other_stamps_unchanged() {
        for change_assumption in [false, true] {
            let (mut exec, model) = fixture();
            let source = exec.ctx.source_context_stamp();
            let query = exec.query_authority_epoch.clone();
            let store = exec.ctx.terms.snapshot_stamp();
            let yes = exec.ctx.terms.mk_bool(true);
            if change_assumption {
                exec.last_assumptions = Some(vec![yes]);
            } else {
                exec.independent_gate_authored_assertions = Some(vec![yes]);
            }
            assert_eq!(source, exec.ctx.source_context_stamp());
            assert!(query.is_same_epoch(&exec.query_authority_epoch));
            assert!(store.is_append_only_prefix_of(&exec.ctx.terms));
            assert!(!model.validate_construction_owner(&exec));
            assert!(PinAdmission::capture(&exec, &model).is_err());
        }
    }
    #[test]
    fn borrowed_canonical_walk_preserves_base_duplicates_and_assumption_order() {
        let mut exec = Executor::new();
        let a = exec.ctx.terms.mk_var("a", ay_core::Sort::Bool);
        let b = exec.ctx.terms.mk_var("b", ay_core::Sort::Bool);
        let c = exec.ctx.terms.mk_var("c", ay_core::Sort::Bool);
        exec.ctx.assertions = vec![a, a];
        exec.last_assumptions = Some(vec![a, b, b, c]);
        assert_eq!(
            exec.independent_gate_query_roots().unwrap(),
            vec![a, a, b, c]
        );
        assert!(exec.independent_gate_query_root_ids().eq([a, a, b, c]));
    }

    #[test]
    fn metadata_memory_refusal_precedes_original_root_copy() {
        let mut exec = Executor::new();
        exec.execute_all(&parse("(declare-const x Int) (assert (= x 7))").unwrap())
            .unwrap();
        exec.begin_external_decision_query(false);
        let source_bytes = exec.ctx.terms.true_memory_bytes();
        exec.set_term_memory_limit(Some(source_bytes));
        assert!(
            exec.poll_evaluation_stop().is_ok(),
            "source alone fits original allowance"
        );
        let before = exec.ctx.terms.len();
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.construction_owner.is_none());
        assert!(model.functional_arrays.is_none());
        assert_eq!(exec.ctx.terms.len(), before);
        assert_eq!(
            exec.evaluation_stop_origin(),
            Some(UnknownOrigin::MemoryBudget)
        );
    }

    #[test]
    fn no_array_model_evaluation_and_clones_share_original_work_across_reads() {
        use super::super::functional_arrays::MAX_FUNCTIONAL_WORK;
        use super::super::independent_gate::IndependentModelView;
        use ay_model_check::{EvalOutcome, ModelView};
        let (exec, mut model) = fixture();
        let x = exec.ctx.symbol_info("x").unwrap().term.unwrap();
        let fields = ay_fp::FpFields::from_shared(
            false,
            Arc::new(127u8.into()),
            Arc::new((num_bigint::BigUint::from(1u8) << 198usize) + 1u8),
            8,
            200,
        )
        .unwrap();
        let mut fp = ay_fp::FpModel::default();
        fp.values.insert(x, ay_fp::FpModelValue::Exact(fields));
        model.fp_model = Some(fp);
        let cloned = model.clone();
        let used = Arc::clone(&model.construction_owner.as_ref().unwrap().used);
        {
            let view = IndependentModelView::new(&exec, &model);
            assert!(!view.has_functional_arrays());
            assert!(!view.functional_array_interrupted()); // pay source validation first
            let before = used.load(Ordering::Acquire);
            assert!(matches!(
                ay_model_check::evaluate_term(&exec.ctx.terms, &view, x),
                EvalOutcome::Value(ay_model_check::ModelValue::FloatingPointExact { .. })
            ));
            assert!(
                used.load(Ordering::Acquire) > before,
                "actual field copy/evaluation is charged beyond source validation"
            );
            let copy_view = IndependentModelView::new(&exec, &cloned);
            assert!(!copy_view.functional_array_interrupted());
            let before = used.load(Ordering::Acquire);
            assert!(matches!(
                ay_model_check::evaluate_term(&exec.ctx.terms, &copy_view, x),
                EvalOutcome::Value(_)
            ));
            assert!(used.load(Ordering::Acquire) > before);
            let evaluator = ay_model_check::Evaluator::new(&exec.ctx.terms, &copy_view);
            assert!(matches!(evaluator.evaluate(x), EvalOutcome::Value(_)));
            assert!(copy_view
                .charge_exact_fp_work(MAX_FUNCTIONAL_WORK + 1)
                .is_err());
            assert!(view.exact_fp_interrupted());
            assert!(
                matches!(evaluator.evaluate(x), EvalOutcome::Unevaluable(_)),
                "a cached exact value cannot publish after the retained FP ledger refuses"
            );
        }
        let read = exec.begin_external_evaluation_read();
        let view = IndependentModelView::new(&exec, &cloned);
        assert!(matches!(
            ay_model_check::evaluate_term(&exec.ctx.terms, &view, x),
            EvalOutcome::Unevaluable(_)
        ));
        assert!(!view.has_functional_arrays());
        drop(view);
        drop(read);
    }

    #[test]
    fn rejected_finite_staging_cannot_reconstruct_a_model_owner() {
        let (mut exec, model) = fixture();
        let original = Arc::clone(model.construction_owner.as_ref().unwrap());
        let roots = exec.independent_gate_query_roots().unwrap();
        // The maintained private fixture exercises staging custody, not the
        // finite-table proof checker. The real zero-point regression exercises
        // that production proof and its reconstructed model end to end.
        let stage = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &roots,
            model.clone(),
            Default::default(),
        )
        .unwrap();
        let yes = exec.ctx.terms.mk_bool(true);
        exec.last_assumptions = Some(vec![yes]);
        let before = original.used.load(Ordering::Acquire);
        assert!(stage
            .into_staging(&exec, &exec.independent_gate_query_roots().unwrap())
            .is_none());
        assert!(Arc::ptr_eq(
            &original,
            model.construction_owner.as_ref().unwrap()
        ));
        assert_eq!(
            original.used.load(Ordering::Acquire),
            before,
            "failed native staging never enters reconstruction or mints a counter"
        );
        let subset = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &[],
            model.clone(),
            Default::default(),
        )
        .unwrap();
        assert!(
            subset.into_staging(&exec, &[]).is_none(),
            "even current private subset staging cannot reconstruct a full-query owner"
        );
        assert!(Arc::ptr_eq(
            &original,
            model.construction_owner.as_ref().unwrap()
        ));
        assert!(exec.last_model.is_none());
    }

    #[test]
    fn checked_finite_reconstruction_conserves_original_counter_and_refusal() {
        let (mut exec, model) = fixture();
        let original = Arc::clone(model.construction_owner.as_ref().unwrap());
        let yes = exec.ctx.terms.mk_bool(true);
        exec.last_assumptions = Some(vec![yes]);
        let roots = exec.independent_gate_query_roots().unwrap();
        let stage = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &roots,
            model.clone(),
            Default::default(),
        )
        .unwrap();
        let before = original.used.load(Ordering::Acquire);
        let (_, reconstructed) = stage.into_staging(&exec, &roots).unwrap();
        let current = reconstructed.construction_owner.as_ref().unwrap();
        assert!(
            !Arc::ptr_eq(&original, current),
            "old DATA record remains immutable"
        );
        assert!(Arc::ptr_eq(&original.used, &current.used));
        assert!(original
            .original_attempt
            .is_same_attempt(&current.original_attempt));
        assert_eq!(
            original.used.load(Ordering::Acquire),
            before,
            "DATA reconstruction retains, but does not spend, the FP ledger"
        );
        assert!(reconstructed.validate_construction_owner(&exec));
        assert!(!model.validate_construction_owner(&exec));
        assert!(original
            .charge(
                &exec,
                super::super::functional_arrays::MAX_FUNCTIONAL_WORK + 1
            )
            .is_err());
        assert!(
            current.charge(&exec, 0).is_err(),
            "reconstruction cannot revive prior refusal"
        );
        assert!(
            exec.last_model.is_none(),
            "accounting is DATA, not publication"
        );
    }

    #[test]
    fn retained_root_validation_preserves_enclosing_recovery_work_refusal() {
        let (exec, model) = fixture();
        let owner = model.construction_owner.as_ref().unwrap();
        let before = owner.used.load(Ordering::Acquire);
        let _scope =
            super::super::recovery_admission::RecoveryScope::enter(&exec, 0, usize::MAX).unwrap();
        assert!(!owner.validate(&exec));
        assert_eq!(
            owner.used.load(Ordering::Acquire),
            before,
            "a refused enclosing transaction cannot debit or bypass its owner"
        );
    }

    #[test]
    fn model_metadata_copy_respects_enclosing_recovery_bytes_before_copy() {
        let (exec, _) = fixture();
        let mut model = Model::empty();
        let terms = exec.ctx.terms.len();
        let _scope =
            super::super::recovery_admission::RecoveryScope::enter(&exec, usize::MAX, 0).unwrap();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.construction_owner.is_none());
        assert!(model.functional_arrays.is_none());
        assert_eq!(exec.ctx.terms.len(), terms);
    }

    #[test]
    fn native_stop_is_polled_inside_assumption_dedup_without_an_fp_quota() {
        use std::sync::atomic::AtomicBool;
        let (mut exec, model) = fixture();
        let a = exec.ctx.terms.mk_var("root_a", ay_core::Sort::Bool);
        let b = exec.ctx.terms.mk_var("root_b", ay_core::Sort::Bool);
        let c = exec.ctx.terms.mk_var("root_c", ay_core::Sort::Bool);
        exec.independent_gate_authored_assertions = Some(vec![a, b, c]);
        exec.last_assumptions = Some(vec![b]);
        let interrupt = Arc::new(AtomicBool::new(false));
        exec.set_interrupt(Arc::clone(&interrupt));
        let before = model
            .construction_owner
            .as_ref()
            .unwrap()
            .used
            .load(Ordering::Acquire);
        let mut steps = 0usize;
        let mut emitted = Vec::new();
        let result = exec.visit_independent_gate_query_roots(
            || {
                steps += 1;
                // Three base emissions, one assumption visit, then two real
                // contains comparisons: stop BEFORE the second comparison.
                if steps == 6 {
                    interrupt.store(true, Ordering::Release);
                }
                pay_metadata(&exec, 1, 0)
            },
            |root| {
                emitted.push(root);
                ControlFlow::Continue(())
            },
        );
        assert_eq!(result, Err(UnknownOrigin::InterruptFlag));
        assert_eq!(steps, 6);
        assert_eq!(emitted, vec![a, b, c]);
        assert_eq!(
            model
                .construction_owner
                .as_ref()
                .unwrap()
                .used
                .load(Ordering::Acquire),
            before,
            "metadata cancellation does not corrupt retained FP DATA accounting"
        );
    }

    #[test]
    fn root_collection_propagates_budget_refusal_without_empty_obligations() {
        let (exec, _) = fixture();
        let expected = exec.independent_gate_query_roots().unwrap();
        assert_ne!(expected, [] as [TermId; 0]);
        let _scope = super::super::recovery_admission::RecoveryScope::enter(&exec, 0, 0).unwrap();
        assert_eq!(
            exec.independent_gate_query_roots(),
            Err(UnknownOrigin::DeterministicResourceBudget)
        );
        assert_eq!(
            query_roots_match(&exec, &expected),
            Err(UnknownOrigin::DeterministicResourceBudget)
        );
        assert_eq!(exec.ctx.assertions, expected);
    }

    #[test]
    fn actual_public_model_batches_do_not_revalidate_roots_per_symbol() {
        use crate::api::{Logic, Solver};
        let mut solver = Solver::new(Logic::QfLia);
        let mut terms = Vec::new();
        for index in 0..500 {
            let x = solver.int_var(&format!("model_owner_x{index}"));
            let value = solver.int_const(index);
            let equality = solver.eq(x, value);
            solver.assert_term(equality);
            terms.push(x);
        }
        assert!(
            solver.check_sat().is_sat(),
            "real solve, no synthetic model/allowance"
        );
        let before = solver
            .model_construction_metadata_steps_for_test()
            .expect("actual retained model owner from real SAT completion");
        assert_eq!(
            solver.model_construction_work_for_test(),
            Some(0),
            "ordinary DATA capture creates no FP/source-size ceiling"
        );
        let values = solver.try_get_values(&terms).unwrap();
        let map = solver.try_get_model_map().unwrap();
        let printed = solver.try_get_model_for_consumer().unwrap();
        let after = solver.model_construction_metadata_steps_for_test().unwrap();
        assert_eq!(
            solver.model_construction_work_for_test(),
            Some(0),
            "ordinary published reads do not spend an unrelated FP ledger"
        );
        eprintln!("real500 FPwork=0 metadata root-steps={before}->{after}");
        assert!(
            after > before,
            "real batch fences actually visit the native roots"
        );
        assert!(
            after - before < 100_000,
            "batch validation is not roots times symbols: {before} -> {after}"
        );
        assert_eq!(values.len(), 500);
        for (index, model_value) in values.iter().enumerate() {
            let expected = num_bigint::BigInt::from(index);
            assert!(
                matches!(model_value, crate::api::ModelValue::Int(value) if value == &expected)
            );
            assert!(
                matches!(map.get(&format!("model_owner_x{index}")), Some(crate::api::ModelValue::Int(value)) if value == &expected)
            );
            assert_eq!(
                printed.model().int_val(&format!("model_owner_x{index}")),
                Some(&expected)
            );
        }
    }
    #[test]
    fn stale_no_array_model_cannot_use_the_legacy_single_term_entry() {
        let (mut exec, model) = fixture();
        let yes = exec.ctx.terms.mk_bool(true);
        assert!(matches!(
            exec.evaluate_term(&model, yes),
            super::super::EvalValue::Bool(true)
        ));
        exec.ctx.terms = ay_core::TermStore::new();
        let replacement = exec.ctx.terms.mk_bool(true);
        assert!(model.functional_arrays.is_none());
        assert!(matches!(
            exec.evaluate_term(&model, replacement),
            super::super::EvalValue::Unknown
        ));
    }
}
