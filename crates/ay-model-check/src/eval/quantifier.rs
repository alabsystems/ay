// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact finite-carrier enumeration and source-derived finite range support.
//! Triggers guide solver search, not model semantics, and are ignored here.

use super::{
    EvalError, EvalResource, EvalResult, Evaluator, LocalBinding, LocalBindingGuard, LocalVariable,
};
use crate::ModelValue;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use std::cell::Cell;
use std::fmt;

pub(crate) mod array_frame;
mod domain_support;
mod equality;
mod joint;
use domain_support::GuardedDomain;

#[cfg(test)]
mod error_tests;
#[cfg(test)]
#[path = "fp_arithmetic_admission_tests.rs"]
mod fp_arithmetic_admission_tests;
#[cfg(test)]
#[path = "fp_to_real_admission_tests.rs"]
mod fp_to_real_admission_tests;

const MAX_QUANTIFIER_ASSIGNMENTS: usize = 65_536;
const MAX_QUANTIFIER_WORK: usize = 1_048_576;
const MAX_QUANTIFIER_BINDERS: usize = 16;
const MAX_QUANTIFIER_NESTING: usize = 32;
const MAX_QUANTIFIED_EVAL_CALLS: usize = 128;
const MAX_QUANTIFIER_PLAN_BYTES: usize = 16 * 1024 * 1024;

/// Shared across nested quantifiers and every assertion of one model check.
pub(super) struct QuantifierState {
    assignments_left: Cell<usize>,
    work_left: Cell<usize>,
    nesting: Cell<usize>,
    plan_bytes_left: Cell<usize>,
}

impl Default for QuantifierState {
    fn default() -> Self {
        Self {
            assignments_left: Cell::new(MAX_QUANTIFIER_ASSIGNMENTS),
            work_left: Cell::new(MAX_QUANTIFIER_WORK),
            nesting: Cell::new(0),
            plan_bytes_left: Cell::new(MAX_QUANTIFIER_PLAN_BYTES),
        }
    }
}

impl QuantifierState {
    /// Immutable model data conversion shares the existing cumulative plan
    /// storage envelope with all quantifiers in this evaluator.
    pub(super) fn admit_model_data_storage(&self, bytes: usize) -> super::EvalResult<()> {
        let Some(left) = self.plan_bytes_left.get().checked_sub(bytes) else {
            self.plan_bytes_left.set(0);
            return Err(super::EvalError::resource(
                super::EvalResource::Work,
                "model data exceeds original plan storage budget",
            ));
        };
        self.plan_bytes_left.set(left);
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub(super) enum QuantifierKind {
    Forall,
    Exists,
}

impl QuantifierKind {
    fn decisive_value(self) -> bool {
        matches!(self, Self::Exists)
    }
}

/// Typed internal failures map to the established `EvalOutcome::Unevaluable`
/// string boundary; no new solver option or public result variant is needed.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum QuantifierRejection {
    UnsupportedDomain,
    AssignmentBudget,
    EvaluationBudget,
    NestingLimit,
    BinderLimit,
    DuplicateBinder,
    BindingSortMismatch,
    NonBooleanBody,
    UnevaluableBody(EvalError),
}

impl fmt::Display for QuantifierRejection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let reason = match self {
            Self::UnsupportedDomain => {
                "requires a supported finite Bool/BV carrier or guarded Int/BV range"
            }
            Self::AssignmentBudget => "assignment budget exceeded",
            Self::EvaluationBudget => "evaluation work budget exceeded",
            Self::NestingLimit => "nesting or native evaluation depth limit exceeded",
            Self::BinderLimit => "binder count limit exceeded",
            Self::DuplicateBinder => "duplicate name in one binder list",
            Self::BindingSortMismatch => "bound variable sort does not match its binder",
            Self::NonBooleanBody => "body is not Boolean",
            Self::UnevaluableBody(reason) => {
                return write!(formatter, "finite quantifier body is unevaluable: {reason}");
            }
        };
        write!(formatter, "finite quantifier {reason}")
    }
}

impl std::error::Error for QuantifierRejection {}

impl From<QuantifierRejection> for EvalError {
    fn from(rejection: QuantifierRejection) -> Self {
        match rejection {
            QuantifierRejection::UnevaluableBody(error) => {
                error.context("finite quantifier body is unevaluable: ")
            }
            other => {
                let kind = match &other {
                    QuantifierRejection::AssignmentBudget => Some(EvalResource::Assignments),
                    QuantifierRejection::EvaluationBudget | QuantifierRejection::BinderLimit => {
                        Some(EvalResource::Work)
                    }
                    QuantifierRejection::NestingLimit => Some(EvalResource::Depth),
                    _ => None,
                };
                let reason = other.to_string();
                match kind {
                    Some(kind) => Self::Resource { kind, reason },
                    None => Self::Refused(reason),
                }
            }
        }
    }
}

struct QuantifierDepthGuard<'a>(&'a Cell<usize>);

impl Drop for QuantifierDepthGuard<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get().saturating_sub(1));
    }
}

/// Check the entire Cartesian domain before enumeration. Even an unused wide
/// binder declines: short-circuiting must not make an over-budget domain look
/// like an exhaustively checked one.
fn domain_sizes(
    bindings: &[(String, Sort)],
    assignments_left: usize,
) -> Result<(Vec<usize>, usize), QuantifierRejection> {
    if bindings.len() > MAX_QUANTIFIER_BINDERS {
        return Err(QuantifierRejection::BinderLimit);
    }
    let mut sizes = Vec::with_capacity(bindings.len());
    let mut product = 1usize;
    for (index, (name, sort)) in bindings.iter().enumerate() {
        if bindings[..index]
            .iter()
            .any(|(previous, _)| previous == name)
        {
            return Err(QuantifierRejection::DuplicateBinder);
        }
        let size = match sort {
            Sort::Bool => 2,
            Sort::BitVec(bitvec) if bitvec.width > 0 => 1usize
                .checked_shl(bitvec.width)
                .ok_or(QuantifierRejection::AssignmentBudget)?,
            _ => return Err(QuantifierRejection::UnsupportedDomain),
        };
        product = product
            .checked_mul(size)
            .filter(|total| *total <= assignments_left)
            .ok_or(QuantifierRejection::AssignmentBudget)?;
        sizes.push(size);
    }
    if product > assignments_left {
        return Err(QuantifierRejection::AssignmentBudget);
    }
    Ok((sizes, product))
}

fn domain_value(sort: &Sort, ordinal: usize) -> Result<ModelValue, QuantifierRejection> {
    match sort {
        Sort::Bool => Ok(ModelValue::Bool(ordinal != 0)),
        Sort::Int => Ok(ModelValue::Int(BigInt::from(ordinal))),
        // Only ever a placeholder before an equality-support tuple overwrites
        // it (see `equality`); no Real carrier is enumerated by ordinal.
        Sort::Real => Ok(ModelValue::Real(num_rational::BigRational::from_integer(
            BigInt::from(ordinal),
        ))),
        Sort::BitVec(bitvec) if bitvec.width > 0 => Ok(ModelValue::BitVec {
            width: bitvec.width,
            value: BigInt::from(ordinal),
        }),
        _ => Err(QuantifierRejection::UnsupportedDomain),
    }
}

enum QuantifierDomain {
    Cartesian(Vec<usize>),
    Guarded(GuardedDomain),
    Joint(Vec<Vec<ModelValue>>),
}

impl Evaluator<'_> {
    fn quantifier_domain(
        &self,
        kind: QuantifierKind,
        bindings: &[(String, Sort)],
        body: TermId,
        depth: usize,
    ) -> Result<(QuantifierDomain, usize), QuantifierRejection> {
        let assignments_left = self.quantifier_state.assignments_left.get();
        let mut rejection = match domain_sizes(bindings, assignments_left) {
            Ok((sizes, count)) => return Ok((QuantifierDomain::Cartesian(sizes), count)),
            Err(rejection) => rejection,
        };
        if bindings.len() > 1
            && matches!(
                rejection,
                QuantifierRejection::UnsupportedDomain | QuantifierRejection::AssignmentBudget
            )
        {
            match joint::plan(self, kind, bindings, body, depth) {
                Ok(tuples) => {
                    let count = tuples.len();
                    return Ok((QuantifierDomain::Joint(tuples), count));
                }
                // No finite range support: the equality-only planner below
                // may still decide the group exactly. Otherwise the joint
                // planner's own rejection stands, exactly as before.
                Err(QuantifierRejection::UnsupportedDomain) => {
                    rejection = QuantifierRejection::UnsupportedDomain;
                }
                Err(other) => return Err(other),
            }
        } else {
            let eligible = bindings.len() == 1
                && matches!(
                    (&rejection, &bindings[0].1),
                    (QuantifierRejection::UnsupportedDomain, Sort::Int)
                        | (QuantifierRejection::AssignmentBudget, Sort::BitVec(_))
                );
            if eligible {
                if let Some(guarded) =
                    GuardedDomain::derive(self, kind, bindings, body, depth, assignments_left)?
                {
                    let count = guarded.count;
                    return Ok((QuantifierDomain::Guarded(guarded), count));
                }
            }
        }
        // (#eq-only-quantifier-eval) An infinite Int/Real carrier whose
        // binders the body only compares for equality is decided exactly by
        // a finite candidate set; see `equality`'s module header.
        // Any planner failure (outside the fragment, an unevaluable
        // comparand, a spent budget) keeps the pre-existing rejection, so
        // the group stays exactly as unevaluable as it was.
        if matches!(rejection, QuantifierRejection::UnsupportedDomain) {
            if let Ok(Some(tuples)) = equality::plan(self, bindings, body, depth) {
                let count = tuples.len();
                return Ok((QuantifierDomain::Joint(tuples), count));
            }
        }
        Err(rejection)
    }

    /// Account borrowed children before reserving stack capacity. Cloning
    /// `TermStore::children` first would allocate before the resource guard.
    pub(super) fn push_binding_scan_children(
        &self,
        term: TermId,
        stack: &mut Vec<TermId>,
    ) -> EvalResult<()> {
        let data = self.terms.get(term);
        let count = crate::residual::term_child_count(data)
            .ok_or_else(|| "unsupported binding-scan term".to_string())?;
        self.charge_quantifier_work(count)?;
        stack
            .try_reserve(count)
            .map_err(|_| EvalError::from(QuantifierRejection::EvaluationBudget))?;
        crate::residual::for_each_term_child(data, |child| stack.push(child))
            .ok_or_else(|| EvalError::from("unsupported binding-scan term"))
    }

    /// Meter recursive evaluation and binder-dependence scans under the SAME
    /// envelope. Merely bounding each quantifier separately leaves nested
    /// enumeration exponential and lets sibling assertions reset the cap.
    pub(super) fn charge_quantifier_work(&self, amount: usize) -> EvalResult<()> {
        if self.quantifier_state.nesting.get() == 0 {
            return Ok(());
        }
        if self.active_eval_calls.get() >= MAX_QUANTIFIED_EVAL_CALLS {
            return Err(QuantifierRejection::NestingLimit.into());
        }
        let remaining = self.quantifier_state.work_left.get();
        let Some(remaining) = remaining.checked_sub(amount) else {
            self.quantifier_state.work_left.set(0);
            return Err(QuantifierRejection::EvaluationBudget.into());
        };
        self.quantifier_state.work_left.set(remaining);
        Ok(())
    }

    pub(super) fn eval_finite_quantifier(
        &self,
        kind: QuantifierKind,
        bindings: &[(String, Sort)],
        body: TermId,
        depth: usize,
    ) -> EvalResult<ModelValue> {
        self.enumerate_quantifier(kind, bindings, body, depth)
            .map(ModelValue::Bool)
            .map_err(EvalError::from)
    }

    fn enumerate_quantifier(
        &self,
        kind: QuantifierKind,
        bindings: &[(String, Sort)],
        body: TermId,
        depth: usize,
    ) -> Result<bool, QuantifierRejection> {
        if self.terms.sort(body) != &Sort::Bool {
            return Err(QuantifierRejection::NonBooleanBody);
        }
        let state = &self.quantifier_state;
        if state.nesting.get() >= MAX_QUANTIFIER_NESTING {
            return Err(QuantifierRejection::NestingLimit);
        }
        state.nesting.set(state.nesting.get() + 1);
        let _depth_guard = QuantifierDepthGuard(&state.nesting);
        if matches!(kind, QuantifierKind::Forall) {
            if let Some(value) = array_frame::evaluate(self, bindings, body, depth)
                .map_err(QuantifierRejection::UnevaluableBody)?
            {
                return Ok(value);
            }
        }
        // Range support and endpoint evaluation spend the same envelope as
        // enumeration, including when this is the outermost quantifier.
        let (domain, count) = self.quantifier_domain(kind, bindings, body, depth)?;
        if count == 0 {
            return Ok(!kind.decisive_value());
        }
        let restore_len = self.local_bindings.borrow().len();
        let _binding_guard = LocalBindingGuard {
            bindings: &self.local_bindings,
            restore_len,
        };
        for (name, sort) in bindings {
            self.local_bindings.borrow_mut().push(LocalBinding {
                variable: LocalVariable::Named(name.clone(), sort.clone()),
                value: domain_value(sort, 0)?,
            });
        }
        let mut pending = None;
        for assignment in 0..count {
            let remaining = state
                .assignments_left
                .get()
                .checked_sub(1)
                .ok_or(QuantifierRejection::AssignmentBudget)?;
            state.assignments_left.set(remaining);
            match &domain {
                QuantifierDomain::Cartesian(sizes) => {
                    self.assign_quantifier_tuple(bindings, sizes, assignment, restore_len)?;
                }
                QuantifierDomain::Guarded(guarded) => {
                    let [(_, sort)] = bindings else {
                        return Err(QuantifierRejection::BindingSortMismatch);
                    };
                    let value = guarded.value_at(self, sort, assignment)?;
                    let mut locals = self.local_bindings.borrow_mut();
                    let binding = locals
                        .get_mut(restore_len)
                        .ok_or(QuantifierRejection::BindingSortMismatch)?;
                    binding.value = value;
                }
                QuantifierDomain::Joint(tuples) => {
                    let tuple = tuples
                        .get(assignment)
                        .ok_or(QuantifierRejection::BindingSortMismatch)?;
                    for (index, value) in tuple.iter().enumerate() {
                        let copied = self
                            .clone_value(value)
                            .map_err(QuantifierRejection::UnevaluableBody)?;
                        let mut locals = self.local_bindings.borrow_mut();
                        let binding = locals
                            .get_mut(restore_len + index)
                            .ok_or(QuantifierRejection::BindingSortMismatch)?;
                        binding.value = copied;
                    }
                }
            }
            match self.eval(body, depth + 1) {
                Ok(ModelValue::Bool(value)) if value == kind.decisive_value() => return Ok(value),
                Ok(ModelValue::Bool(_)) => {}
                Ok(_) => return Err(QuantifierRejection::NonBooleanBody),
                Err(reason) => {
                    if state.work_left.get() == 0 {
                        return Err(QuantifierRejection::EvaluationBudget);
                    }
                    EvalError::record(&mut pending, reason);
                }
            }
        }
        match pending {
            Some(reason) => Err(QuantifierRejection::UnevaluableBody(reason)),
            None => Ok(!kind.decisive_value()),
        }
    }

    fn assign_quantifier_tuple(
        &self,
        bindings: &[(String, Sort)],
        sizes: &[usize],
        mut assignment: usize,
        restore_len: usize,
    ) -> Result<(), QuantifierRejection> {
        let mut locals = self.local_bindings.borrow_mut();
        for (index, ((_, sort), size)) in bindings.iter().zip(sizes).enumerate() {
            let value = domain_value(sort, assignment % size)?;
            assignment /= size;
            let binding = locals
                .get_mut(restore_len + index)
                .ok_or(QuantifierRejection::BindingSortMismatch)?;
            binding.value = value;
        }
        Ok(())
    }
}
