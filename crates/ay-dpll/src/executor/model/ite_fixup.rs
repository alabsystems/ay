// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-arithmetic ITE model consistency pass (#8373).
//!
//! After an arithmetic solver finds a satisfying assignment, the LRA or LIA
//! model maps term IDs to numeric values. However, these values are assigned to
//! individual variables without knowledge of ITE-level branch constraints. For
//! example:
//!
//!   `(ite (= x 1.0) (= y 0.0) (= y 1.0))`
//!
//! The simplex model may assign `y = 0.5` which satisfies the linear constraints
//! but violates both branches of the ITE. The model evaluator then picks a
//! branch based on the condition value and finds the branch equality unsatisfied.
//!
//! This module walks ITE-containing assertions after model extraction and
//! patches the arithmetic model to ensure active-branch equalities are
//! satisfied. This is the model-construction fix for the ITE gap — as opposed
//! to the SAT-fallback workaround in the validation pipeline.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::ite_fixup_limits::{patch_candidate_bytes, IteFixupLimits, ITE_FIXUP_LIMITS};
use super::{
    eval_memo_clear, eval_node_visits, EvalMemoSession, EvalValue, EvalWorkBudget, Executor, Model,
    EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RawLiteralValue {
    Known(bool),
    Unknown,
    Inconsistent,
}

struct ItePatchState {
    patches: HashMap<TermId, BigRational>,
    visited: HashSet<TermId>,
    extracted: HashSet<TermId>,
    work_used: usize,
    work_limit: usize,
    patch_payload_bytes: usize,
    patch_payload_limit: usize,
    patch_candidates: usize,
    patch_candidate_limit: usize,
    failed: bool,
}

impl ItePatchState {
    fn new(limits: IteFixupLimits) -> Self {
        Self {
            patches: HashMap::default(),
            visited: HashSet::default(),
            extracted: HashSet::default(),
            work_used: 0,
            work_limit: limits.work,
            patch_payload_bytes: 0,
            patch_payload_limit: limits.patch_payload_bytes,
            patch_candidates: 0,
            patch_candidate_limit: limits.patch_candidates,
            failed: false,
        }
    }

    fn spend(&mut self, amount: usize) -> bool {
        let Some(next) = self.work_used.checked_add(amount) else {
            self.failed = true;
            return false;
        };
        if next > self.work_limit {
            self.failed = true;
            return false;
        }
        self.work_used = next;
        true
    }

    fn insert(&mut self, term: TermId, value: BigRational) {
        let Some(candidate_bytes) = patch_candidate_bytes(&value) else {
            self.failed = true;
            return;
        };
        let Some(next_candidates) = self.patch_candidates.checked_add(1) else {
            self.failed = true;
            return;
        };
        let Some(next_payload) = self.patch_payload_bytes.checked_add(candidate_bytes) else {
            self.failed = true;
            return;
        };
        if next_candidates > self.patch_candidate_limit || next_payload > self.patch_payload_limit {
            self.failed = true;
            return;
        }
        // Charge every actual candidate before map lookup or BigRational
        // comparison. Repeated equal candidates still clone/compare their
        // exact payload, so deduplication must not make that work unbounded.
        self.patch_candidates = next_candidates;
        self.patch_payload_bytes = next_payload;
        match self.patches.get(&term) {
            Some(existing) if existing != &value => self.failed = true,
            Some(_) => {}
            None => {
                self.patches.insert(term, value);
            }
        }
    }

    fn remaining(&self) -> usize {
        self.work_limit.saturating_sub(self.work_used)
    }
}

impl Executor {
    /// Fix up arithmetic model values to satisfy ITE branch equalities.
    ///
    /// For each assertion containing ITE subterms, evaluates the ITE condition
    /// and patches the arithmetic model so that variables in the active branch
    /// have values consistent with the branch constraint.
    ///
    /// This is a no-op when no LRA or LIA model exists (pure SAT, BV-only, etc.).
    pub(in crate::executor) fn fix_ite_model_values(&mut self) {
        self.fix_ite_model_values_bounded(ITE_FIXUP_LIMITS);
    }

    fn fix_ite_model_values_bounded(&mut self, limits: IteFixupLimits) {
        let model = match &self.last_model {
            Some(m) if m.lra_model.is_some() || m.lia_model.is_some() => m,
            _ => return,
        };

        // Walk the original assertion DAG directly. Flattening conjunctions into
        // a temporary vector can expand a shared DAG before the visited/work
        // guards below get a chance to bound it.
        let _eval_memo = EvalMemoSession::new();
        let eval_work_budget = EvalWorkBudget::new(limits.work);
        let mut state = ItePatchState::new(limits);
        for &assertion in &self.ctx.assertions {
            self.collect_required_true_ite_patches(model, assertion, &mut state);
            if state.failed {
                return;
            }
        }

        if eval_work_budget.exhausted() {
            return;
        }
        drop(eval_work_budget);

        if state.patches.is_empty() {
            return;
        }

        // Preflight every conversion and destination before mutating either
        // arithmetic model. A conflicting/non-integral/inapplicable repair must
        // leave both models byte-for-byte untouched.
        let has_lra = model.lra_model.is_some();
        let has_lia = model.lia_model.is_some();
        let mut patches = Vec::with_capacity(state.patches.len());
        for (term, value) in state.patches {
            let integer = match self.ctx.terms.sort(term) {
                Sort::Int => {
                    let Some(integer) = value.to_integer_if_whole() else {
                        return;
                    };
                    if !has_lra && !has_lia {
                        return;
                    }
                    Some(integer)
                }
                Sort::Real => {
                    if !has_lra {
                        return;
                    }
                    None
                }
                _ => return,
            };
            patches.push((term, value, integer));
        }

        let model = self.last_model.as_mut().expect("checked above");
        if let Some(ref mut lra_model) = model.lra_model {
            for (term, value, _) in &patches {
                lra_model.values.insert(*term, value.clone());
            }
        }
        if let Some(ref mut lia_model) = model.lia_model {
            for (term, _, integer) in &patches {
                if let Some(integer) = integer {
                    lia_model.values.insert(*term, integer.clone());
                }
            }
        }
        eval_memo_clear();
    }

    /// Return the SAT assignment of a Boolean literal without confusing a
    /// missing `Not` Tseitin variable with an unknown literal. Tseitin encodes
    /// `Not(inner)` by flipping `inner`, so both representations must agree when
    /// both happen to be present.
    fn raw_literal_value(&self, model: &Model, term: TermId) -> RawLiteralValue {
        let direct = self.term_value(&model.sat_model, &model.term_to_var, term);
        let inverted = match self.ctx.terms.get(term) {
            TermData::Not(inner) => self
                .term_value(&model.sat_model, &model.term_to_var, *inner)
                .map(|value| !value),
            _ => None,
        };

        match (direct, inverted) {
            (Some(a), Some(b)) if a != b => RawLiteralValue::Inconsistent,
            (Some(value), _) | (_, Some(value)) => RawLiteralValue::Known(value),
            (None, None) => RawLiteralValue::Unknown,
        }
    }

    /// Evaluate one term and debit the evaluator's actual DAG-node work from
    /// the same global repair clock as the structural walk.
    fn evaluate_bounded(
        &self,
        model: &Model,
        term: TermId,
        state: &mut ItePatchState,
    ) -> Option<EvalValue> {
        let before = eval_node_visits();
        let work_budget = EvalWorkBudget::new(state.remaining());
        let value = self.evaluate_term(model, term);
        let exhausted = work_budget.exhausted();
        drop(work_budget);
        let Some(delta) = eval_node_visits().checked_sub(before) else {
            state.failed = true;
            return None;
        };
        let Ok(delta) = usize::try_from(delta) else {
            state.failed = true;
            return None;
        };
        if exhausted || !state.spend(delta) {
            state.failed = true;
            return None;
        }
        Some(value)
    }

    /// Walk only Boolean positions known to be required true by the asserted
    /// formula. Patching below negation, implication, equality, or another
    /// unknown-polarity application can satisfy the wrong branch, so those
    /// contexts deliberately stop the optional repair.
    ///
    /// When an ITE condition can be evaluated, determines which branch is active
    /// and extracts equalities from it. For each equality `(= var value)` where
    /// `var` is a variable and `value` can be evaluated, patches the variable's
    /// model value.
    fn collect_required_true_ite_patches(
        &self,
        model: &Model,
        term: TermId,
        state: &mut ItePatchState,
    ) {
        if state.failed || !state.spend(1) || !state.visited.insert(term) {
            return;
        }
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term) {
                TermData::Ite(cond, then_br, else_br)
                    if matches!(self.ctx.terms.sort(term), Sort::Bool) =>
                {
                    // Prefer the SAT branch selected by the Boolean skeleton.
                    // The arithmetic evaluator is exactly what this pass is
                    // repairing and can still disagree before patches commit.
                    let condition = match self.raw_literal_value(model, *cond) {
                        RawLiteralValue::Known(value) => Some(value),
                        RawLiteralValue::Unknown => {
                            match self.evaluate_bounded(model, *cond, state) {
                                Some(EvalValue::Bool(value)) => Some(value),
                                Some(_) => None,
                                None => return,
                            }
                        }
                        RawLiteralValue::Inconsistent => {
                            state.failed = true;
                            return;
                        }
                    };

                    let Some(condition) = condition else {
                        state.failed = true;
                        return;
                    };
                    let branch = if condition { *then_br } else { *else_br };
                    let Some(branch_value) = self.evaluate_bounded(model, branch, state) else {
                        return;
                    };
                    if matches!(branch_value, EvalValue::Bool(false)) {
                        self.extract_equality_patches(model, branch, state);
                    }
                    self.collect_required_true_ite_patches(model, branch, state);
                }
                TermData::App(sym, args) if sym.name() == "and" => {
                    for &arg in args {
                        if !state.spend(1) {
                            return;
                        }
                        self.collect_required_true_ite_patches(model, arg, state);
                    }
                }
                TermData::App(sym, args) if sym.name() == "or" => {
                    let mut has_known_true = false;
                    for &arg in args {
                        if !state.spend(1) {
                            return;
                        }
                        match self.raw_literal_value(model, arg) {
                            RawLiteralValue::Known(true) => has_known_true = true,
                            RawLiteralValue::Inconsistent => {
                                state.failed = true;
                                return;
                            }
                            RawLiteralValue::Known(false) | RawLiteralValue::Unknown => {}
                        }
                    }

                    let mut selected = false;
                    for &arg in args {
                        if !state.spend(1) {
                            return;
                        }
                        let raw = self.raw_literal_value(model, arg);
                        let active = if has_known_true {
                            raw == RawLiteralValue::Known(true)
                        } else {
                            if raw != RawLiteralValue::Unknown {
                                false
                            } else {
                                let Some(value) = self.evaluate_bounded(model, arg, state) else {
                                    return;
                                };
                                matches!(value, EvalValue::Bool(true))
                            }
                        };
                        if active {
                            selected = true;
                            self.collect_required_true_ite_patches(model, arg, state);
                        }
                    }
                    if !selected {
                        state.failed = true;
                    }
                }
                // Leaves and unsupported/negative/unknown Boolean contexts stop.
                _ => {}
            }
        })
    }

    /// Extract equality patches from a branch term.
    ///
    /// Handles:
    /// - `(= var constant)` — patches var to constant
    /// - `(= var expr)` — patches var to evaluated expr value
    /// - `(and (= var1 val1) (= var2 val2))` — patches multiple vars
    fn extract_equality_patches(&self, model: &Model, branch: TermId, state: &mut ItePatchState) {
        if state.failed || !state.spend(1) || !state.extracted.insert(branch) {
            return;
        }
        match self.ctx.terms.get(branch) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let lhs = args[0];
                let rhs = args[1];
                // Try both directions: (= var expr) and (= expr var)
                if let Some(patch) = self.try_equality_patch(model, lhs, rhs, state) {
                    state.insert(patch.0, patch.1);
                } else if !state.failed {
                    if let Some(patch) = self.try_equality_patch(model, rhs, lhs, state) {
                        state.insert(patch.0, patch.1);
                    }
                }
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                for &arg in args {
                    if !state.spend(1) {
                        return;
                    }
                    self.extract_equality_patches(model, arg, state);
                }
            }
            _ => {}
        }
    }

    /// Try to create a model patch from `(= var_term value_term)`.
    ///
    /// Returns `Some((var_term_id, value))` if `var_term` is a Real/Int-sorted
    /// variable and `value_term` can be evaluated to a rational.
    fn try_equality_patch(
        &self,
        model: &Model,
        var_term: TermId,
        value_term: TermId,
        state: &mut ItePatchState,
    ) -> Option<(TermId, BigRational)> {
        // Check that var_term is a variable with arithmetic sort.
        let sort = self.ctx.terms.sort(var_term);
        if !matches!(sort, Sort::Real | Sort::Int) {
            return None;
        }
        if !matches!(self.ctx.terms.get(var_term), TermData::Var(_, _)) {
            return None;
        }

        // Evaluate the value term to get the target value.
        let value = match self.evaluate_bounded(model, value_term, state)? {
            EvalValue::Rational(r) => Some(r),
            _ => {
                // The value term might be a constant that doesn't need model lookup.
                match self.ctx.terms.get(value_term) {
                    TermData::Const(Constant::Int(n)) => Some(BigRational::from(n.clone())),
                    TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
                    _ => None,
                }
            }
        }?;
        if matches!(sort, Sort::Int) && !value.is_integer() {
            state.failed = true;
            return None;
        }
        Some((var_term, value))
    }

    #[cfg(test)]
    pub(in crate::executor::model) fn fix_ite_model_values_with_work_limit_for_test(
        &mut self,
        work_limit: usize,
    ) {
        self.fix_ite_model_values_bounded(IteFixupLimits {
            work: work_limit,
            ..ITE_FIXUP_LIMITS
        });
    }

    #[cfg(test)]
    pub(in crate::executor::model) fn fix_ite_model_values_with_limits_for_test(
        &mut self,
        patch_payload_bytes: usize,
        patch_candidates: usize,
    ) {
        self.fix_ite_model_values_bounded(IteFixupLimits {
            patch_payload_bytes,
            patch_candidates,
            ..ITE_FIXUP_LIMITS
        });
    }
}

/// Extension trait for BigRational to convert to BigInt when the value is integral.
trait BigRationalExt {
    fn to_integer_if_whole(&self) -> Option<BigInt>;
}

impl BigRationalExt for BigRational {
    fn to_integer_if_whole(&self) -> Option<BigInt> {
        if self.is_integer() {
            Some(self.numer().clone())
        } else {
            None
        }
    }
}
