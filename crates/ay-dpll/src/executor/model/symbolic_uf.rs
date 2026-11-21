// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Immutable total function DATA proposed by the authored-equation model lane.
//! Neither a source equation nor this package grants SAT authority: the QMC,
//! original residual and independent publication gates still decide that.

use std::sync::Arc;

use ay_core::{term::TermStoreSnapshotStamp, Symbol, TermId};
use ay_frontend::{CheckedProjectionBinding, SourceContextStamp};

use super::{eval_memo_clear, independent_gate::IndependentModelView, Executor, Model};
use crate::executor::QueryAuthorityEpoch;

mod inventory;
mod output;
mod recovery;
pub(in crate::executor) use inventory::symbolic_source_inventory_work;
pub(in crate::executor) use recovery::{SymbolicAdmission, SymbolicRecoveryScope};

const NATIVE_OPERATORS: [&str; 24] = [
    "+",
    "-",
    "*",
    "/",
    "div",
    "mod",
    "abs",
    "to_int",
    "and",
    "or",
    "xor",
    "=>",
    "not",
    "=",
    "distinct",
    "<",
    "<=",
    ">",
    ">=",
    "to_real",
    "is_int",
    "select",
    "store",
    "const-array",
];

/// One source-authenticated candidate function after capture-free expansion.
#[derive(Debug)]
pub(in crate::executor) struct SymbolicUfDefinition {
    pub(in crate::executor) binding: CheckedProjectionBinding,
    pub(in crate::executor) parameters: Vec<TermId>,
    pub(in crate::executor) body: TermId,
    pub(in crate::executor) rendered_body: String,
}

#[derive(Debug)]
struct Source {
    epoch: QueryAuthorityEpoch,
    context: SourceContextStamp,
    prefix: TermStoreSnapshotStamp,
    projection_storage: ay_frontend::ProjectionLookupFootprint,
    to_real_shadowed: bool,
    is_int_shadowed: bool,
    operator_lookup_work: [usize; NATIVE_OPERATORS.len()],
    operator_flags: [bool; NATIVE_OPERATORS.len()],
    roots: Vec<TermId>,
    authored_roots: Vec<TermId>,
    definitions: Vec<SymbolicUfDefinition>,
    lookup_work: usize,
}

/// Sharing preserves immutable semantics; model confirmation remains non-cloning.
#[derive(Debug, Clone, Default)]
pub(in crate::executor) struct SymbolicUfModel(Option<Arc<Source>>, Option<SymbolicAdmission>);

impl SymbolicUfModel {
    pub(in crate::executor) fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    pub(super) fn pay_for(&self, executor: &Executor, work: usize, bytes: usize) -> bool {
        match (&self.0, &self.1) {
            (None, None) => true,
            (Some(_), Some(owner)) => owner.pay_for(executor, work, bytes),
            _ => false,
        }
    }

    pub(super) fn refuse(&self) {
        if let Some(owner) = &self.1 {
            owner.refuse();
        }
    }

    pub(super) fn refusal(&self) -> Option<super::recovery_admission::RecoveryRefusal> {
        self.1.as_ref().and_then(SymbolicAdmission::refusal)
    }

    fn owned_by(&self, admission: &SymbolicAdmission) -> bool {
        self.1
            .as_ref()
            .is_some_and(|owner| owner.shares_owner(admission))
    }

    pub(in crate::executor) fn contains(&self, symbol: &Symbol) -> bool {
        self.0.as_ref().is_some_and(|source| {
            source
                .definitions
                .iter()
                .any(|definition| definition.binding.symbol() == symbol)
        })
    }

    pub(in crate::executor) fn contains_name(&self, name: &str) -> bool {
        name.len() <= 256
            && self.0.as_ref().is_some_and(|source| {
                source
                    .definitions
                    .iter()
                    .any(|definition| definition.binding.symbol().name() == name)
            })
    }

    /// All copies and the authored/DAG validation precede this final move.
    pub(in crate::executor) fn from_prepared(
        executor: &Executor,
        roots: Vec<TermId>,
        definitions: Vec<SymbolicUfDefinition>,
        admission: &SymbolicAdmission,
    ) -> Option<Self> {
        let context = &executor.ctx;
        if definitions.is_empty() || !admission.pay(1, std::mem::size_of::<Source>()) {
            return None;
        }
        // Every repeated binding check searches for one of THESE immutable
        // exact heads. Use their actual widest byte width, not the parser's
        // unrelated maximum admitted spelling. Physical namespace geometry
        // and all actual retained source names still determine the scan fee.
        admission.pay(definitions.len(), 0).then_some(())?;
        let incoming_bytes = definitions
            .iter()
            .map(|definition| definition.binding.symbol().name().len())
            .max()?;
        let (inventory_work, projection_storage) =
            symbolic_source_inventory_work(executor, admission, incoming_bytes)?;
        // The slow source/signature checks below are paid once, before the
        // immutable package is published. Subsequent views execute only the
        // frontend's opaque fixed-header binding leases, plus the independent
        // guards and actual core-operator probes retained below. Do not charge
        // a namespace scan that those views no longer perform.
        let mut lookup_work = definitions.len().checked_mul(4)?.checked_add(64)?;
        let mut operator_lookup_work = [0; NATIVE_OPERATORS.len()];
        let mut operator_flags = [false; NATIVE_OPERATORS.len()];
        for (index, name) in NATIVE_OPERATORS.iter().enumerate() {
            let work = context.terms.declared_function_lookup_work(name.len())?;
            admission.pay(work, 0).then_some(())?;
            lookup_work = lookup_work.checked_add(work)?;
            operator_lookup_work[index] = work;
            operator_flags[index] = context.terms.is_declared_function(name);
        }
        let authored = executor.independent_gate_authored_assertions.as_ref()?;
        let mut authored_roots = Vec::new();
        admission.reserve(&mut authored_roots, authored.len())?;
        authored_roots.extend_from_slice(authored);
        lookup_work = lookup_work.checked_add(authored.len())?;
        for definition in &definitions {
            let mut signature_work = definition.binding.symbol().name().len();
            for sort in definition
                .binding
                .parameter_sorts()
                .iter()
                .chain(std::iter::once(definition.binding.result_sort()))
            {
                signature_work =
                    signature_work.checked_add(header_sort_cost(sort, admission, 0)?)?;
            }
            if !admission.pay(inventory_work.checked_add(signature_work)?, 0) {
                return None;
            }
            if !context.projection_binding_still_current(&definition.binding)
                || context.terms.entry_stamp(definition.body).is_none()
                || definition.parameters.len() != definition.binding.parameter_sorts().len()
                || context.terms.sort(definition.body) != definition.binding.result_sort()
                || definition
                    .parameters
                    .iter()
                    .zip(definition.binding.parameter_sorts())
                    .any(|(&term, sort)| {
                        context.terms.entry_stamp(term).is_none()
                            || context.terms.sort(term) != sort
                    })
            {
                return None;
            }
        }
        Some(Self(
            Some(Arc::new(Source {
                epoch: executor.query_authority_epoch.clone(),
                context: context.source_context_stamp(),
                prefix: context.terms.snapshot_stamp(),
                projection_storage,
                to_real_shadowed: context.terms.to_real_is_shadowed(),
                is_int_shadowed: context.terms.is_int_is_shadowed(),
                operator_lookup_work,
                operator_flags,
                roots,
                authored_roots,
                definitions,
                lookup_work,
            })),
            Some(admission.clone()),
        ))
    }

    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        let context = &executor.ctx;
        self.0.as_ref().is_none_or(|source| {
            source.epoch.is_same_epoch(&executor.query_authority_epoch)
                && source.context == context.source_context_stamp()
                && source.prefix.is_append_only_prefix_of(&context.terms)
                && source.projection_storage.matches_storage(context)
                && source.to_real_shadowed == context.terms.to_real_is_shadowed()
                && source.is_int_shadowed == context.terms.is_int_is_shadowed()
                && NATIVE_OPERATORS.iter().enumerate().all(|(index, name)| {
                    context
                        .terms
                        .declared_function_lookup_work(name.len())
                        .is_some_and(|work| work <= source.operator_lookup_work[index])
                        && source.operator_flags[index] == context.terms.is_declared_function(name)
                })
                && executor
                    .independent_gate_authored_assertions
                    .as_ref()
                    .is_some_and(|roots| roots.as_slice() == source.authored_roots.as_slice())
                && source.definitions.iter().all(|definition| {
                    context.projection_binding_lease_still_current(&definition.binding)
                })
        })
    }

    pub(in crate::executor) fn definition(&self, symbol: &Symbol) -> Option<&SymbolicUfDefinition> {
        self.0
            .as_ref()?
            .definitions
            .iter()
            .find(|definition| definition.binding.symbol() == symbol)
    }

    pub(in crate::executor) fn definitions(&self) -> &[SymbolicUfDefinition] {
        self.0
            .as_ref()
            .map_or(&[], |source| source.definitions.as_slice())
    }

    pub(in crate::executor) fn source_roots(&self) -> &[TermId] {
        self.0
            .as_ref()
            .map_or(&[], |source| source.roots.as_slice())
    }

    pub(super) fn lookup_work(&self) -> usize {
        self.0.as_ref().map_or(0, |source| source.lookup_work)
    }

    pub(super) fn head_lookup_work(&self, bytes: usize) -> Option<usize> {
        self.definitions()
            .len()
            .checked_mul(bytes.checked_add(256)?)?
            .checked_add(1)
    }
}

impl Executor {
    pub(in crate::executor) fn install_model_check_symbolic_ufs(
        &self,
        model: &mut Model,
        candidate: SymbolicUfModel,
        admission: &SymbolicAdmission,
    ) -> Option<()> {
        if !admission.pay(candidate.lookup_work(), 0) {
            return None;
        }
        if candidate.is_empty()
            || !candidate.owned_by(admission)
            || !candidate.is_current(self)
            || !model.certified_total_ufs.symbolic.is_empty()
            || model.projection_ufs.has_interpretations()
            || candidate.definitions().iter().any(|definition| {
                model.has_certified_const_interp_symbol(definition.binding.symbol())
                    || model
                        .has_formula_neutral_function_default_symbol(definition.binding.symbol())
                    || model
                        .certified_total_ufs
                        .by_symbol
                        .contains_key(definition.binding.symbol().name())
            })
        {
            return None;
        }
        model.quantified_confirmation_seal.revoke();
        model.revoke_quantified_grant_model();
        model.certified_total_ufs.cegqi_recompletion_epoch = None;
        // Old search tables remain inert fallback data. Every owned head is
        // interpreted ahead of pins/completions in evaluation and output, so
        // installing an immutable body neither clones nor disposes unbounded
        // raw-model payloads here.
        model.certified_total_ufs.symbolic = candidate;
        eval_memo_clear();
        Some(())
    }

    pub(super) fn symbolic_function_value(
        &self,
        model: &Model,
        term: TermId,
    ) -> Result<Option<ay_model_check::ModelValue>, String> {
        let ay_core::TermData::App(symbol, _) = self.ctx.terms.get(term) else {
            return Ok(None);
        };
        if model.certified_total_ufs.symbolic.is_empty() {
            return Ok(None);
        }
        let view = IndependentModelView::new(self, model);
        let work = model
            .certified_total_ufs
            .symbolic
            .head_lookup_work(symbol.name().len())
            .ok_or("symbolic head lookup accounting overflow")?;
        ay_model_check::ModelView::admit_evaluation_work(&view, work, 0)?;
        if !model.certified_total_ufs.symbolic.contains(symbol) {
            return Ok(None);
        }
        match ay_model_check::Evaluator::new(&self.ctx.terms, &view).evaluate(term) {
            ay_model_check::EvalOutcome::Value(value) => Ok(Some(value)),
            ay_model_check::EvalOutcome::Unevaluable(reason) => Err(reason),
        }
    }

    pub(in crate::executor) fn symbolic_residual_holds(
        &self,
        model: &Model,
        roots: &[TermId],
    ) -> bool {
        self.symbolic_residual_check(model, roots).is_ok()
    }

    pub(in crate::executor) fn symbolic_residual_check(
        &self,
        model: &Model,
        roots: &[TermId],
    ) -> Result<(), String> {
        let view = IndependentModelView::new(self, model);
        let evaluator = ay_model_check::Evaluator::new(&self.ctx.terms, &view);
        for &root in roots {
            match evaluator.evaluate(root) {
                ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Bool(true)) => {}
                ay_model_check::EvalOutcome::Value(_) => {
                    return Err("original symbolic residual is not true".to_owned())
                }
                ay_model_check::EvalOutcome::Unevaluable(reason) => {
                    // Array/functional stop hooks may observe the same
                    // original refusal before the generic evaluator's admit
                    // hook. Preserve the retained FIRST cause, rather than
                    // returning only that hook's generic interruption text.
                    if let Some(refusal) = model.certified_total_ufs.symbolic.refusal() {
                        return Err(format!(
                            "retained symbolic model admission refused: {refusal:?}"
                        ));
                    }
                    return Err(reason);
                }
            }
        }
        Ok(())
    }
}

fn header_sort_cost(
    sort: &ay_core::Sort,
    owner: &SymbolicAdmission,
    depth: usize,
) -> Option<usize> {
    if depth > 64 || !owner.pay(1, 0) {
        return None;
    }
    match sort {
        ay_core::Sort::Bool | ay_core::Sort::Int | ay_core::Sort::Real => Some(1),
        ay_core::Sort::Array(array) => Some(
            1usize
                .checked_add(header_sort_cost(&array.index_sort, owner, depth + 1)?)?
                .checked_add(header_sort_cost(&array.element_sort, owner, depth + 1)?)?,
        ),
        _ => None,
    }
}
