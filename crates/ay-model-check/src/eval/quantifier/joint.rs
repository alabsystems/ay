// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact finite support for ordered groups of dependent range binders.
//!
//! A range for each prefix overapproximates every possible decisive extension.
//! Unknown atoms retain whole support. No future binder may supply an endpoint.
//! Plan all relevant tuples before a body result can short-circuit evaluation.

use super::*;

pub(super) fn plan(
    evaluator: &Evaluator<'_>,
    kind: QuantifierKind,
    bindings: &[(String, Sort)],
    body: TermId,
    depth: usize,
) -> Result<Vec<Vec<ModelValue>>, QuantifierRejection> {
    validate_bindings(evaluator, bindings)?;
    let restore_len = evaluator.local_bindings.borrow().len();
    let _bindings = LocalBindingGuard {
        bindings: &evaluator.local_bindings,
        restore_len,
    };
    // Mask the entire group before evaluating any model-dependent endpoint.
    // Endpoint syntax additionally refuses current/future names; zero is never
    // used as an assumed value for an as-yet-unassigned binder.
    for (name, sort) in bindings {
        evaluator.local_bindings.borrow_mut().push(LocalBinding {
            variable: LocalVariable::Named(name.clone(), sort.clone()),
            value: domain_value(sort, 0)?,
        });
    }
    let mut planner = Planner {
        evaluator,
        kind,
        bindings,
        body,
        depth,
        restore_len,
        tuples: Vec::new(),
    };
    planner.prefix(0)?;
    // Planning spends assignments too. Reserve enough of the same remaining
    // allowance for ALL planned body evaluations, including an early witness.
    if planner.tuples.len() > evaluator.quantifier_state.assignments_left.get() {
        return Err(QuantifierRejection::AssignmentBudget);
    }
    Ok(planner.tuples)
}

fn charge(evaluator: &Evaluator<'_>, work: usize) -> Result<(), QuantifierRejection> {
    evaluator
        .charge_quantifier_work(work)
        .map_err(QuantifierRejection::UnevaluableBody)
}

fn validate_bindings(
    evaluator: &Evaluator<'_>,
    bindings: &[(String, Sort)],
) -> Result<(), QuantifierRejection> {
    if bindings.len() > MAX_QUANTIFIER_BINDERS {
        return Err(QuantifierRejection::BinderLimit);
    }
    for (index, (name, sort)) in bindings.iter().enumerate() {
        charge(
            evaluator,
            name.len()
                .checked_add(1)
                .ok_or(QuantifierRejection::EvaluationBudget)?,
        )?;
        if bindings[..index].iter().any(|(prior, _)| prior == name) {
            return Err(QuantifierRejection::DuplicateBinder);
        }
        match sort {
            Sort::Bool | Sort::Int => {}
            Sort::BitVec(bitvec) if (1..=128).contains(&bitvec.width) => {}
            _ => return Err(QuantifierRejection::UnsupportedDomain),
        }
    }
    Ok(())
}

enum Domain {
    Carrier(usize),
    Guarded(GuardedDomain),
}

impl Domain {
    fn count(&self) -> usize {
        match self {
            Self::Carrier(count) => *count,
            Self::Guarded(domain) => domain.count,
        }
    }

    fn value(
        &self,
        evaluator: &Evaluator<'_>,
        sort: &Sort,
        ordinal: usize,
    ) -> Result<ModelValue, QuantifierRejection> {
        match self {
            Self::Carrier(_) => domain_value(sort, ordinal),
            Self::Guarded(domain) => domain.value_at(evaluator, sort, ordinal),
        }
    }
}

struct Planner<'a, 'model> {
    evaluator: &'a Evaluator<'model>,
    kind: QuantifierKind,
    bindings: &'a [(String, Sort)],
    body: TermId,
    depth: usize,
    restore_len: usize,
    tuples: Vec<Vec<ModelValue>>,
}

impl Planner<'_, '_> {
    fn domain(&self, index: usize) -> Result<Domain, QuantifierRejection> {
        charge(self.evaluator, 1)?;
        let binding = self
            .bindings
            .get(index)
            .ok_or(QuantifierRejection::BindingSortMismatch)?;
        let left = self.evaluator.quantifier_state.assignments_left.get();
        match domain_sizes(std::slice::from_ref(binding), left) {
            Ok((_, count)) => Ok(Domain::Carrier(count)),
            Err(QuantifierRejection::UnsupportedDomain | QuantifierRejection::AssignmentBudget) => {
                GuardedDomain::derive_pending(
                    self.evaluator,
                    self.kind,
                    binding,
                    &self.bindings[index..],
                    self.body,
                    self.depth,
                    left,
                )?
                .map(Domain::Guarded)
                .ok_or(QuantifierRejection::UnsupportedDomain)
            }
            Err(error) => Err(error),
        }
    }

    fn prefix(&mut self, index: usize) -> Result<(), QuantifierRejection> {
        charge(self.evaluator, 1)?;
        if index == self.bindings.len() {
            return self.retain();
        }
        let domain = self.domain(index)?;
        for ordinal in 0..domain.count() {
            charge(self.evaluator, 1)?;
            let state = &self.evaluator.quantifier_state;
            let left = state
                .assignments_left
                .get()
                .checked_sub(1)
                .ok_or(QuantifierRejection::AssignmentBudget)?;
            state.assignments_left.set(left);
            let value = domain.value(self.evaluator, &self.bindings[index].1, ordinal)?;
            let slot = self
                .restore_len
                .checked_add(index)
                .ok_or(QuantifierRejection::BindingSortMismatch)?;
            self.evaluator
                .local_bindings
                .borrow_mut()
                .get_mut(slot)
                .ok_or(QuantifierRejection::BindingSortMismatch)?
                .value = value;
            self.prefix(index + 1)?;
        }
        Ok(())
    }

    fn retain(&mut self) -> Result<(), QuantifierRejection> {
        let locals = self.evaluator.local_bindings.borrow();
        let values = locals
            .get(self.restore_len..)
            .ok_or(QuantifierRejection::BindingSortMismatch)?;
        if values.len() != self.bindings.len() {
            return Err(QuantifierRejection::BindingSortMismatch);
        }
        // Two outer-vector slots account for amortized capacity slack. Value
        // layout is platform-dependent (the enum also contains BigRational).
        let mut bytes = size_of::<Vec<ModelValue>>() * 2;
        for binding in values {
            let limbs = match &binding.value {
                ModelValue::Bool(_) => 0,
                ModelValue::Int(value) | ModelValue::BitVec { value, .. } => {
                    usize::try_from(value.bits().div_ceil(64).saturating_mul(8))
                        .map_err(|_| QuantifierRejection::EvaluationBudget)?
                        .checked_add(32)
                        .ok_or(QuantifierRejection::EvaluationBudget)?
                }
                _ => return Err(QuantifierRejection::BindingSortMismatch),
            };
            charge(self.evaluator, limbs.max(1))?;
            bytes = bytes
                .checked_add(size_of::<ModelValue>())
                .and_then(|bytes| bytes.checked_add(limbs))
                .ok_or(QuantifierRejection::EvaluationBudget)?;
        }
        // Charge retained values AND their later body-environment clones.
        let state = &self.evaluator.quantifier_state;
        let Some(left) = bytes
            .checked_mul(2)
            .and_then(|bytes| state.plan_bytes_left.get().checked_sub(bytes))
        else {
            state.plan_bytes_left.set(0);
            state.work_left.set(0);
            return Err(QuantifierRejection::EvaluationBudget);
        };
        state.plan_bytes_left.set(left);
        self.tuples
            .try_reserve(1)
            .map_err(|_| QuantifierRejection::EvaluationBudget)?;
        let mut tuple = Vec::new();
        tuple
            .try_reserve_exact(values.len())
            .map_err(|_| QuantifierRejection::EvaluationBudget)?;
        tuple.extend(values.iter().map(|binding| binding.value.clone()));
        self.tuples.push(tuple);
        Ok(())
    }
}

#[cfg(test)]
mod tests;
