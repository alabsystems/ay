// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Immutable constant-function candidate DATA, shared across model clones.

use super::*;
use crate::executor::model::evaluation_copies::{self, RetainedEvaluationMemory};
use crate::executor::model::{EvaluationArena, Executor};
use crate::executor::QueryAuthorityEpoch;
use ay_core::term::{Symbol, TermStoreSnapshotStamp};
use std::sync::atomic::AtomicUsize;

pub(in crate::executor::model) struct ConstantArrayReadAdmission<'a> {
    data: &'a ConstantArrayFunctions,
    exec: &'a Executor,
}
impl ay_core::term::TermConstructionAdmission for ConstantArrayReadAdmission<'_> {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        use ay_core::original_query::{
            CountedAdmissionError, OriginalAdmissionError, QueryError, StopReason,
        };
        self.data.pay(self.exec, work, bytes).map_err(|_| {
            match self.exec.evaluation_stop_origin() {
                Some(crate::executor_types::UnknownOrigin::MemoryBudget) => {
                    CountedAdmissionError::Memory
                }
                Some(crate::executor_types::UnknownOrigin::DeterministicResourceBudget) => {
                    CountedAdmissionError::WorkExhausted
                }
                Some(crate::executor_types::UnknownOrigin::SolveDeadline) => {
                    OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Deadline))
                        .into()
                }
                Some(crate::executor_types::UnknownOrigin::InterruptFlag) => {
                    OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Cancelled))
                        .into()
                }
                _ => OriginalAdmissionError::ObserverStopped.into(),
            }
        })
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        evaluation_copies::refuse_original(error)
    }
}

#[derive(Debug)]
pub(in crate::executor::model) struct ConstantArrayFunction {
    pub(in crate::executor::model) arguments: Vec<Sort>,
    pub(in crate::executor::model) result: Sort,
    pub(in crate::executor::model) value: Arc<ModelValue>,
}

#[derive(Debug)]
pub(in crate::executor::model) struct ConstantArrayFunctions {
    pub(in crate::executor::model) source: SourceContextStamp,
    pub(in crate::executor::model) query: QueryAuthorityEpoch,
    pub(in crate::executor::model) store: TermStoreSnapshotStamp,
    pub(in crate::executor::model) functions:
        ay_core::kani_compat::DetHashMap<String, ConstantArrayFunction>,
    pub(in crate::executor::model) used: Arc<AtomicUsize>,
    pub(in crate::executor::model) memory: RetainedEvaluationMemory,
}

impl ConstantArrayFunctions {
    fn current(&self, exec: &Executor) -> bool {
        self.source == exec.ctx.source_context_stamp()
            && self.query.is_same_epoch(&exec.query_authority_epoch)
            && self.store.is_append_only_prefix_of(&exec.ctx.terms)
    }

    fn pay(&self, exec: &Executor, work: usize, bytes: usize) -> Result<(), ()> {
        if !evaluation_copies::active()
            || !self
                .memory
                .original
                .is_same_attempt(&exec.evaluation_attempt())
        {
            super::super::functional_arrays::debit_retained_work(
                exec,
                &self.used,
                &self.memory.original,
                work,
            )
            .map_err(|_| {
                if exec.evaluation_stop_origin().is_none() {
                    exec.record_evaluation_stop(
                        crate::executor_types::UnknownOrigin::DeterministicResourceBudget,
                    );
                }
            })?;
        }
        if !self.current(exec)
            || !evaluation_copies::pay(work, bytes)
            || !evaluation_copies::validate(exec)
            || !self.current(exec)
        {
            return Err(());
        }
        Ok(())
    }

    fn value(&self, exec: &Executor, term: TermId) -> Result<Option<&ModelValue>, ()> {
        self.pay(exec, 0, 0)?;
        let TermData::App(Symbol::Named(symbol), args) = exec.ctx.terms.get(term) else {
            return Ok(None);
        };
        self.pay(exec, symbol.len().saturating_mul(2) + 1, 0)?;
        let Some(function) = self.functions.get(symbol.as_ref()) else {
            return Ok(None);
        };
        if args.len() != function.arguments.len() {
            return Err(());
        }
        for (sort, &arg) in function.arguments.iter().zip(args) {
            ay_core::TermStore::inspect_sort_with_progress(sort, &mut |work, bytes| {
                work.checked_add(bytes)
                    .is_some_and(|work| self.pay(exec, work, 0).is_ok())
            })
            .map_err(|_| ())?;
            if sort != exec.ctx.terms.sort(arg) {
                return Err(());
            }
        }
        for sort in [&function.result, exec.ctx.terms.sort(term)] {
            ay_core::TermStore::inspect_sort_with_progress(sort, &mut |work, bytes| {
                work.checked_add(bytes)
                    .is_some_and(|work| self.pay(exec, work, 0).is_ok())
            })
            .map_err(|_| ())?;
        }
        if &function.result != exec.ctx.terms.sort(term) {
            return Err(());
        }
        self.pay(exec, 0, 0)?;
        Ok(Some(function.value.as_ref()))
    }
}

impl Model {
    pub(in crate::executor::model) fn constant_array_read_admission<'a>(
        &'a self,
        exec: &'a Executor,
    ) -> Option<ConstantArrayReadAdmission<'a>> {
        Some(ConstantArrayReadAdmission {
            data: self
                .residual_arrays
                .as_ref()?
                .constant_functions
                .as_deref()?,
            exec,
        })
    }

    pub(in crate::executor::model) fn constant_array_function_for_output(
        &self,
        exec: &Executor,
        identity: &str,
        arguments: &[Sort],
        result: &Sort,
    ) -> Result<Option<&ModelValue>, ()> {
        let Some(data) = self
            .residual_arrays
            .as_ref()
            .and_then(|p| p.constant_functions.as_ref())
        else {
            return Ok(None);
        };
        data.pay(exec, 0, 0)?;
        data.pay(exec, identity.len().saturating_mul(2) + 1, 0)?;
        let Some(function) = data.functions.get(identity) else {
            return Ok(None);
        };
        for sort in function
            .arguments
            .iter()
            .chain(arguments)
            .chain([&function.result, result])
        {
            ay_core::TermStore::inspect_sort_with_progress(sort, &mut |w, b| {
                w.checked_add(b)
                    .is_some_and(|work| data.pay(exec, work, 0).is_ok())
            })
            .map_err(|_| ())?;
        }
        if function.arguments != arguments || &function.result != result {
            return Err(());
        }
        data.pay(exec, 0, 0)?;
        Ok(Some(function.value.as_ref()))
    }
    pub(in crate::executor::model) fn has_constant_array_functions(&self) -> bool {
        self.residual_arrays
            .as_ref()
            .is_some_and(|package| package.constant_functions.is_some())
    }

    pub(in crate::executor::model) fn constant_array_read_charge(
        &self,
        exec: &Executor,
    ) -> Result<Option<EvaluationArena>, crate::executor_types::UnknownOrigin> {
        self.residual_arrays
            .as_ref()
            .and_then(|package| package.constant_functions.as_ref())
            .map(|data| data.memory.read_charge(exec))
            .transpose()
    }

    pub(in crate::executor::model) fn constant_array_value(
        &self,
        exec: &Executor,
        term: TermId,
    ) -> Result<Option<&ModelValue>, ()> {
        if !self.residual_arrays_are_current(&exec.ctx) {
            return Err(());
        }
        self.residual_arrays
            .as_ref()
            .and_then(|package| package.constant_functions.as_ref())
            .map_or(Ok(None), |data| data.value(exec, term))
    }

    pub(in crate::executor::model) fn clone_constant_array_value(
        &self,
        exec: &Executor,
        term: TermId,
    ) -> Result<Option<ModelValue>, ()> {
        let Some(value) = self.constant_array_value(exec, term)? else {
            return Ok(None);
        };
        // The actual owning native gate/read must retain the temporary copy
        // scope through consumption of the returned value.
        if !evaluation_copies::active() {
            return Err(());
        }
        let data = self
            .residual_arrays
            .as_ref()
            .and_then(|p| p.constant_functions.as_ref())
            .ok_or(())?;
        ay_model_check::admit_model_value_work(value, &mut |work, bytes| {
            data.pay(exec, work, bytes)
                .map_err(|_| "constant array copy refused".to_owned())
        })
        .map_err(|_| ())?;
        data.pay(exec, 0, 0)?;
        Ok(Some(value.clone()))
    }

    pub(in crate::executor::model) fn install_constant_array_candidate(
        &mut self,
        ctx: &Context,
        functions: Arc<ConstantArrayFunctions>,
    ) {
        self.revoke_all_quantified_model_seals();
        self.residual_arrays = Some(ResidualArrayModel {
            source: ctx.source_context_stamp(),
            entries: Vec::new(),
            constant_functions: Some(functions),
        });
        eval_memo_clear();
        super::super::independent_gate::invalidate_functional_model_caches();
    }

    pub(in crate::executor::model) fn remove_constant_array_candidate(&mut self) {
        self.revoke_all_quantified_model_seals();
        self.residual_arrays = None;
        eval_memo_clear();
        super::super::independent_gate::invalidate_functional_model_caches();
    }
}
