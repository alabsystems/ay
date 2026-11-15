// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Atomic selection of one acyclic range-function assignment, including its
//! complete old source/destination captures. No check or seal is manufactured.

use std::collections::{BTreeMap, BTreeSet};

use ay_core::term::TermData;
use ay_model_check::{
    recognize_fill_lambda, recognize_identity_lambda, recognize_range_lambda, ArrayValue, ModelView,
};

use super::*;
use crate::executor::model::independent_gate::IndependentModelView;

struct Work {
    left: usize,
    used: Arc<AtomicUsize>,
}

mod plan;
use plan::Plan;
struct Builder<'a> {
    exec: &'a Executor,
    model: &'a Model,
    plan: &'a Plan,
    entries: BTreeMap<TermId, Arc<ArraySnapshot>>,
    active: BTreeSet<TermId>,
    work: Work,
}

struct CaptureView<'a> {
    ordinary: IndependentModelView<'a>,
    exec: &'a Executor,
    used: &'a AtomicUsize,
    entries: &'a BTreeMap<TermId, Arc<ArraySnapshot>>,
}

impl ModelView for CaptureView<'_> {
    fn has_evaluation_admission(&self) -> bool {
        self.ordinary.has_evaluation_admission()
    }
    fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        self.ordinary.admit_evaluation_work(work, bytes)
    }
    fn refuse_evaluation_work(&self, reason: &str) {
        self.ordinary.refuse_evaluation_work(reason);
    }
    fn exact_fp_interrupted(&self) -> bool {
        self.ordinary.exact_fp_interrupted()
    }
    fn charge_exact_fp_work(&self, amount: usize) -> Result<(), String> {
        self.ordinary.charge_exact_fp_work(amount)
    }
    fn admit_exact_fp_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        self.ordinary.admit_exact_fp_work(work, bytes)
    }
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        match self.entries.get(&term) {
            Some(_) => None, // complete data is available only through array_snapshot
            None => self.ordinary.leaf_value(term),
        }
    }
    fn array_snapshot(&self, term: TermId) -> Result<Option<Arc<ArraySnapshot>>, String> {
        Ok(self.entries.get(&term).cloned())
    }
    fn charge_functional_array_work(&self, amount: usize) -> Result<(), String> {
        debit_work(self.exec, self.used, amount)
    }
    fn projection_argument(
        &self,
        term: TermId,
    ) -> Result<Option<usize>, ay_model_check::ProjectionLookupError> {
        self.ordinary.projection_argument(term)
    }
    fn functional_array_interrupted(&self) -> bool {
        self.ordinary.functional_array_interrupted()
    }
}

fn spend(exec: &Executor, work: &mut Work, amount: usize) -> Option<()> {
    exec.poll_evaluation_stop().ok()?;
    debit_work(exec, &work.used, amount).ok()?;
    work.left = work.left.checked_sub(amount)?;
    Some(())
}

fn array_variables(exec: &Executor, root: TermId, work: &mut Work) -> Option<Vec<TermId>> {
    let mut stack = vec![root];
    let mut seen = BTreeSet::new();
    let mut variables = BTreeSet::new();
    while let Some(term) = stack.pop() {
        spend(exec, work, 1)?;
        if (term.0 as usize) >= exec.ctx.terms.len() {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        if matches!(exec.ctx.terms.get(term), TermData::Var(..))
            && matches!(exec.ctx.terms.sort(term), Sort::Array(_))
        {
            variables.insert(term);
        }
        let children = exec.ctx.terms.children(term);
        spend(exec, work, children.len())?;
        stack.try_reserve(children.len()).ok()?;
        stack.extend(children);
    }
    Some(variables.into_iter().collect())
}

impl Builder<'_> {
    fn build(&mut self, canonical: TermId, depth: usize) -> Option<()> {
        spend(self.exec, &mut self.work, 1)?;
        if self.entries.contains_key(&canonical) {
            return Some(());
        }
        if depth > 64 || !self.active.insert(canonical) {
            return None;
        }
        let source_members = self.plan.members.get(&canonical)?;
        spend(self.exec, &mut self.work, source_members.len())?;
        let members = source_members.clone();
        let value = match self.plan.definitions.get(&canonical).copied() {
            Some(rhs) => {
                self.original_constructor_has_no_projections(rhs)?;
                match self.empty_destination(rhs)? {
                    Some(destination) => {
                        let destination = *self.plan.representative.get(&destination)?;
                        if destination == canonical {
                            self.capture_base(canonical, &members)?
                        } else {
                            self.build(destination, depth + 1)?;
                            Arc::clone(self.entries.get(&destination)?)
                        }
                    }
                    None => {
                        for dependency in array_variables(self.exec, rhs, &mut self.work)? {
                            let dependency = *self.plan.representative.get(&dependency)?;
                            // Finite hard pins do not create a new default for an
                            // unowned base/capture. Its complete source definition
                            // must be part of this same atomic construction.
                            if plan::finite_constructor(self.exec, rhs)
                                && !self.plan.definitions.contains_key(&dependency)
                            {
                                return None;
                            }
                            self.build(dependency, depth + 1)?;
                        }
                        let ordinary = IndependentModelView::new(self.exec, self.model);
                        let view = CaptureView {
                            ordinary,
                            exec: self.exec,
                            used: &self.work.used,
                            entries: &self.entries,
                        };
                        Evaluator::new(&self.exec.ctx.terms, &view)
                            .capture_array_snapshot_with_work(rhs, &mut self.work.left)
                            .ok()?
                    }
                }
            }
            None => self.capture_base(canonical, &members)?,
        };
        for &member in &members {
            self.entries.insert(member, Arc::clone(&value));
        }
        self.active.remove(&canonical);
        Some(())
    }

    fn original_constructor_has_no_projections(&mut self, root: TermId) -> Option<()> {
        let view = IndependentModelView::new(self.exec, self.model);
        let mut pending = vec![root];
        let mut seen = BTreeSet::new();
        while let Some(term) = pending.pop() {
            spend(self.exec, &mut self.work, 1)?;
            if !seen.insert(term) {
                continue;
            }
            if matches!(self.exec.ctx.terms.get(term), TermData::App(..))
                && view.projection_argument(term).ok()?.is_some()
            {
                return None;
            }
            let children = self.exec.ctx.terms.children(term);
            spend(self.exec, &mut self.work, children.len())?;
            pending.try_reserve(children.len()).ok()?;
            pending.extend(children);
        }
        Some(())
    }

    fn empty_destination(&mut self, rhs: TermId) -> Option<Option<TermId>> {
        if let Some(recipe) = recognize_identity_lambda(&self.exec.ctx.terms, rhs) {
            let mut pending = vec![recipe.array];
            let mut seen = BTreeSet::new();
            while let Some(term) = pending.pop() {
                spend(self.exec, &mut self.work, 1)?;
                if term == recipe.bound {
                    return None;
                }
                if !seen.insert(term) {
                    continue;
                }
                let children = self.exec.ctx.terms.children(term);
                spend(self.exec, &mut self.work, children.len())?;
                pending.try_reserve(children.len()).ok()?;
                pending.extend(children);
            }
            return Some(Some(recipe.array));
        }
        // Scalar fill captures remain checked even for empty/reversed ranges.
        if recognize_fill_lambda(&self.exec.ctx.terms, rhs).is_some() {
            return Some(None);
        }
        let Some(recipe) = recognize_range_lambda(&self.exec.ctx.terms, rhs) else {
            // Only exact selected finite constructors may bypass the range
            // empty-interval shortcut; the evaluator validates their whole DAG.
            return plan::finite_constructor(self.exec, rhs).then_some(None);
        };
        let used = Arc::clone(&self.work.used);
        let view = CaptureView {
            ordinary: IndependentModelView::new(self.exec, self.model),
            exec: self.exec,
            used: &used,
            entries: &self.entries,
        };
        let evaluator = Evaluator::new(&self.exec.ctx.terms, &view);
        let EvalOutcome::Value(ModelValue::BitVec {
            value: lo,
            width: 64,
        }) = evaluator.evaluate_with_functional_work(recipe.lo, &mut self.work.left)
        else {
            return None;
        };
        let EvalOutcome::Value(ModelValue::BitVec {
            value: hi,
            width: 64,
        }) = evaluator.evaluate_with_functional_work(recipe.hi, &mut self.work.left)
        else {
            return None;
        };
        if lo.sign() == num_bigint::Sign::Minus
            || hi.sign() == num_bigint::Sign::Minus
            || lo.bits() > 64
            || hi.bits() > 64
        {
            return None;
        }
        Some((lo >= hi).then_some(recipe.destination))
    }

    fn capture_base(
        &mut self,
        canonical: TermId,
        members: &[TermId],
    ) -> Option<Arc<ArraySnapshot>> {
        let Sort::Array(sort) = self.exec.ctx.terms.sort(canonical) else {
            return None;
        };
        if !matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64) {
            return None;
        }
        let scalar_bytes = match &sort.element_sort {
            Sort::Bool => 1,
            Sort::BitVec(cell) if cell.width > 0 => (cell.width as usize).div_ceil(8),
            _ => return None,
        };
        spend(self.exec, &mut self.work, scalar_bytes)?;
        let ordinary = IndependentModelView::new(self.exec, self.model);
        let mut captured = None;
        for &member in members {
            spend(self.exec, &mut self.work, 1)?;
            if let Some(interp) = self
                .model
                .array_model
                .as_ref()
                .and_then(|arrays| arrays.array_values.get(&member))
            {
                let bytes = interp.stores.iter().try_fold(0usize, |sum, (key, value)| {
                    sum.checked_add(key.len())?.checked_add(value.len())
                })?;
                let bytes = bytes
                    .checked_add(interp.default.as_ref().map_or(0, String::len))?
                    .checked_add(interp.stores.len())?;
                spend(self.exec, &mut self.work, bytes)?;
            }
            if let Some(ModelValue::Array(value)) = ordinary.functional_base_array_value(member) {
                captured = Some(*value);
                break;
            }
        }
        let mut value = match captured {
            Some(value) => value,
            None => ArrayValue {
                default: match &sort.element_sort {
                    Sort::Bool => ModelValue::Bool(false),
                    Sort::BitVec(bv) => ModelValue::bitvec(0.into(), bv.width),
                    _ => return None,
                },
                store: Vec::new(),
            },
        };
        // Actual hard reads constrain a complete default/cell model choice;
        // every original root must validate it, without domain sampling.
        if let Some(reads) = self.plan.base_reads.get(&canonical) {
            let used = Arc::clone(&self.work.used);
            let view = CaptureView {
                ordinary,
                exec: self.exec,
                used: &used,
                entries: &self.entries,
            };
            let evaluator = Evaluator::new(&self.exec.ctx.terms, &view);
            let mut observed: Vec<(ModelValue, ModelValue)> = Vec::new();
            for &(index, datum) in reads {
                spend(self.exec, &mut self.work, 1 + observed.len())?;
                let EvalOutcome::Value(index) =
                    evaluator.evaluate_with_functional_work(index, &mut self.work.left)
                else {
                    return None;
                };
                let EvalOutcome::Value(datum) =
                    evaluator.evaluate_with_functional_work(datum, &mut self.work.left)
                else {
                    return None;
                };
                if !matches!(&index, ModelValue::BitVec { width: 64, .. }) {
                    return None;
                }
                // Conflicting hard cells are not overwritten. The
                // original query is not made satisfiable by a choice.
                for (prior, value) in &observed {
                    if same_scalar(prior, &index)? && !same_scalar(value, &datum)? {
                        return None;
                    }
                }
                observed.push((index, datum));
            }
            value.store.try_reserve(observed.len()).ok()?;
            value.store.extend(observed);
        }
        let before = self.work.left;
        let captured = ArraySnapshot::finite(
            value,
            self.exec.ctx.terms.sort(canonical),
            &mut self.work.left,
        );
        debit_work(self.exec, &self.work.used, before - self.work.left).ok()?;
        captured.ok()
    }
}

fn same_scalar(left: &ModelValue, right: &ModelValue) -> Option<bool> {
    match (left, right) {
        (ModelValue::Bool(left), ModelValue::Bool(right)) => Some(left == right),
        (
            ModelValue::BitVec {
                width: lw,
                value: lv,
            },
            ModelValue::BitVec {
                width: rw,
                value: rv,
            },
        ) => Some(lw == rw && lv == rv),
        _ => None,
    }
}

pub(super) fn capture(
    exec: &Executor,
    model: &Model,
) -> Option<(FunctionalArrayModel, Vec<TermId>)> {
    // The sole candidate-hook caller just paid and checked canonical bindings
    // under these same immutable exec/model borrows. Do not scan them again.
    let source = exec.ctx.source_context_stamp();
    let binding = model.construction_owner.as_ref()?;
    if !binding.validate(exec) {
        return None;
    }
    let used = Arc::clone(&binding.used);
    let mut work = Work {
        left: MAX_FUNCTIONAL_WORK.saturating_sub(used.load(Ordering::Acquire)),
        used,
    };
    let plan = plan::capture(exec, &mut work)?;
    let mut builder = Builder {
        exec,
        model,
        plan: &plan,
        entries: BTreeMap::new(),
        active: BTreeSet::new(),
        work,
    };
    for &canonical in plan.definitions.keys() {
        builder.build(canonical, 0)?;
    }
    spend(exec, &mut builder.work, 1)?;
    if source != exec.ctx.source_context_stamp()
        || plan.roots != exec.independent_gate_query_roots().ok()?
    {
        return None;
    }
    let mut defined_terms = Vec::new();
    for (&canonical, &rhs) in &plan.definitions {
        let members = plan.members.get(&canonical)?;
        spend(exec, &mut builder.work, members.len() + 1)?;
        defined_terms.try_reserve(members.len() + 1).ok()?;
        defined_terms.extend(members.iter().copied());
        defined_terms.push(rhs);
    }
    spend(
        exec,
        &mut builder.work,
        plan.roots.len() + plan.stamps.len(),
    )?;
    Some((
        FunctionalArrayModel {
            source,
            roots: plan.roots.clone(),
            stamps: plan.stamps.clone(),
            entries: builder.entries.into_iter().collect(),
            work_used: builder.work.used,
            stamps_validated_at: Arc::new(Mutex::new(None)),
        },
        defined_terms,
    ))
}
