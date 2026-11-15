// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reconstruct original variables erased by array-query preprocessing.
//!
//! This is equality/model-converter reconstruction, not new search or a
//! proof-authorizing default (cf. Z3's solve_eqs::save_subst and its model trail:
//! https://github.com/Z3Prover/z3/blob/master/src/ast/simplifiers/solve_eqs.cpp).
//! Only positive top-level conjunction equalities supply definitions.
//! Missing scalar defaults only propose concrete witness candidates. The
//! original expression, not the normalized expression, must strictly verify.
//! Local scan/payload limits do not claim the caller's aggregate work/storage
//! owner: SmtContext has no borrowed WorkBudget for this existing native lane.

mod values;

use super::super::context::SmtContext;
use super::super::model_verify::verify_sat_model_strict;
use super::super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use std::time::Duration;

/// One shared conservative logical ledger for census, fixpoint scans and
/// proposed copied values. It does not measure allocator bookkeeping.
struct Budget<'a> {
    remaining: usize,
    poll: &'a mut dyn FnMut() -> bool,
}

impl Budget<'_> {
    fn charge(&mut self, amount: usize) -> Option<()> {
        if !(self.poll)() {
            return None;
        }
        self.remaining = self.remaining.checked_sub(amount)?;
        Some(())
    }
}

impl SmtContext {
    /// A partial model from a positive trivial preprocessing exit is only a
    /// witness candidate. Arrays require reconstruction and strict ORIGINAL
    /// validation before the legacy scalar-only gate can prematurely refuse.
    /// This entry never upgrades an existing Unknown/Unsat result.
    pub(super) fn finish_trivial_preprocessed_candidate(
        &self,
        original: &ChcExpr,
        model: FxHashMap<String, SmtValue>,
        source: &'static str,
        start: Instant,
        timeout: Option<Duration>,
    ) -> SmtResult {
        let live = || {
            !self.deadlines_expired()
                && !self.exact_term_memory_exceeded()
                && timeout.is_none_or(|limit| start.elapsed() < limit)
        };
        if !live() {
            return SmtResult::Unknown;
        }
        let has_arrays = original.scan_features().has_array_ops;
        if !live() {
            return SmtResult::Unknown;
        }
        let candidate = if has_arrays {
            SmtResult::Sat(model)
        } else {
            Self::sat_or_unknown(original, model, source)
        };
        self.restore_preprocessed_array_model(original, candidate, start, timeout)
    }

    pub(super) fn restore_preprocessed_array_model(
        &self,
        original: &ChcExpr,
        result: SmtResult,
        start: Instant,
        timeout: Option<Duration>,
    ) -> SmtResult {
        let SmtResult::Sat(model) = result else {
            return result;
        };
        let mut live = || {
            !self.deadlines_expired()
                && !self.exact_term_memory_exceeded()
                && timeout.is_none_or(|limit| start.elapsed() < limit)
        };
        if !live() {
            return SmtResult::Unknown;
        }
        // Healthy scalar routes and all non-SAT verdicts remain unchanged.
        // This existing opaque feature scan is bracketed by the original
        // stop/deadline, not represented as fully controlled traversal.
        let has_arrays = original.scan_features().has_array_ops;
        if !live() {
            return SmtResult::Unknown;
        }
        if !has_arrays {
            return SmtResult::Sat(model);
        }
        let completed = reconstruct(original, model, &mut live);
        // The source census/binding temporaries have dropped. Publication
        // still belongs to the unchanged original timeout and native stops.
        if !live() {
            return SmtResult::Unknown;
        }
        match completed {
            Some(model) => SmtResult::Sat(model),
            None => SmtResult::Unknown,
        }
    }
}

type Binding<'a> = (&'a ChcVar, &'a ChcExpr);

struct Source<'a> {
    variables: FxHashMap<&'a str, &'a ChcVar>,
    bindings: Vec<Binding<'a>>,
}

fn source<'a>(original: &'a ChcExpr, budget: &mut Budget<'_>) -> Option<Source<'a>> {
    let mut variables: FxHashMap<&str, &ChcVar> = FxHashMap::default();
    let mut bindings = Vec::new();
    let mut stack = vec![(original, 0usize, true)];
    let mut nodes = 0usize;
    while let Some((expr, depth, positive)) = stack.pop() {
        budget.charge(1)?;
        nodes = nodes.checked_add(1)?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH / 2 {
            return None;
        }
        if let ChcExpr::Var(var) = expr {
            values::sort(&var.sort, budget)?;
            budget.charge(var.name.len())?;
            if variables
                .get(var.name.as_str())
                .is_some_and(|old| old.sort != var.sort)
            {
                // A name-only model cannot authenticate two carried sorts.
                return None;
            }
            variables.try_reserve(1).ok()?;
            variables.insert(var.name.as_str(), var);
        }
        match expr {
            ChcExpr::ArrayLambda(_) => return None,
            ChcExpr::ConstArray(key, _) | ChcExpr::FuncApp(_, key, _) => values::sort(key, budget)?,
            ChcExpr::BitVec(_, width) if *width == 0 || *width > crate::MAX_BITVECTOR_WIDTH => {
                return None;
            }
            ChcExpr::Real(_, 0) => return None,
            _ => {}
        }
        if positive {
            if let ChcExpr::Op(ChcOp::Eq, args) = expr {
                if args.len() == 2 {
                    for (left, right) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                        if let ChcExpr::Var(var) = left.as_ref() {
                            budget.charge(1)?;
                            bindings.try_reserve(1).ok()?;
                            bindings.push((var, right.as_ref()));
                        }
                    }
                }
            }
        }
        let children = crate::expr::dag::children(expr);
        if stack.len().checked_add(children.len())? > budget.remaining {
            return None;
        }
        stack.try_reserve(children.len()).ok()?;
        let conjunction = positive && matches!(expr, ChcExpr::Op(ChcOp::And, _));
        stack.extend(
            children
                .iter()
                .map(|child| (child.as_ref(), depth + 1, conjunction)),
        );
    }
    // Recursive legacy validation is safe to enter only after the complete
    // depth/tree admission above. It is not replaced by sort() alone.
    budget.charge(nodes)?;
    if super::super::executor_sort_guard::unsupported_executor_expr_reason(original).is_some() {
        return None;
    }
    budget.charge(0)?;
    Some(Source {
        variables,
        bindings,
    })
}

fn reconstruct(
    original: &ChcExpr,
    mut model: FxHashMap<String, SmtValue>,
    poll: &mut dyn FnMut() -> bool,
) -> Option<FxHashMap<String, SmtValue>> {
    let mut budget = Budget {
        remaining: crate::expr::MAX_PREPROCESSING_NODES,
        poll,
    };
    budget.charge(1)?;
    let source = source(original, &mut budget)?;
    validate_assigned(&source, &model, &mut budget)?;
    resolve_bindings(&source, &mut model, &mut budget)?;
    // Scalar candidates can make original store/const-array definitions
    // evaluable. Replay the SAME forced definitions without replacing values.
    if propose_missing_scalars(&source, &mut model, &mut budget)? != 0 {
        resolve_bindings(&source, &mut model, &mut budget)?;
    }
    validate_assigned(&source, &model, &mut budget)?;
    if source
        .variables
        .keys()
        .any(|name| !model.contains_key(*name))
    {
        return None;
    }
    project_original_variables(&source, &mut model, &mut budget)?;
    admit_verification(original, &model, &mut budget)?;
    let valid = matches!(
        verify_sat_model_strict(original, &model),
        ModelVerifyResult::Valid
    );
    budget.charge(0)?;
    valid.then_some(model)
}

fn resolve_bindings(
    source: &Source<'_>,
    model: &mut FxHashMap<String, SmtValue>,
    budget: &mut Budget<'_>,
) -> Option<()> {
    loop {
        let mut progressed = false;
        for &(var, rhs) in &source.bindings {
            budget.charge(1)?;
            // Both operands must carry the same supported sort. The whole
            // source guard already checked actual store/select child sorts.
            if var.sort != rhs.sort() {
                return None;
            }
            // Pre-price the whole borrowed RHS and the source-model values
            // its existing evaluator can clone. Poll around that opaque phase.
            admit_evaluation(rhs, model, budget)?;
            let proposed = crate::expr::evaluate_expr(rhs, model);
            budget.charge(0)?;
            let Some(value) = proposed else { continue };
            values::typed(&value, &var.sort, budget)?;
            match model.get(&var.name) {
                Some(existing) => {
                    let left = values::size(existing, budget)?;
                    let right = values::size(&value, budget)?;
                    budget.charge(left.checked_mul(right)?)?;
                    if crate::expr::smt_values_equal(existing, &value) != Some(true) {
                        return None;
                    }
                }
                None => {
                    budget.charge(var.name.len())?;
                    model.try_reserve(1).ok()?;
                    model.insert(var.name.clone(), value);
                    progressed = true;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    Some(())
}

/// Missing scalar values are witness candidates, never derived premises.
/// Reuse the existing scalar default policy only AFTER forced definitions.
/// Free arrays and unsupported sorts stay missing/refused. Every candidate
/// shares the original ledger/poll, and publication still requires strict
/// validation of the ORIGINAL expression after the second definition pass.
fn propose_missing_scalars(
    source: &Source<'_>,
    model: &mut FxHashMap<String, SmtValue>,
    budget: &mut Budget<'_>,
) -> Option<usize> {
    let mut proposed = 0usize;
    for (name, var) in &source.variables {
        budget.charge(1)?;
        if model.contains_key(*name) || matches!(var.sort, ChcSort::Array(..)) {
            continue;
        }
        // Admit the zero/false scalar carrier and copied key BEFORE creating
        // the candidate. Three logical slots cover Real's value and two small
        // integer carriers; the wide zero BV uses an Arc carrier, not a mask.
        // This is not a claim about allocator overhead or aggregate storage.
        budget.charge(name.len().checked_add(3)?)?;
        model.try_reserve(1).ok()?;
        let value = super::default_scalar_smt_value(&var.sort)?;
        values::typed(&value, &var.sort, budget)?;
        budget.charge(0)?;
        model.insert((*name).to_owned(), value);
        proposed = proposed.checked_add(1)?;
    }
    Some(proposed)
}

fn validate_assigned(
    source: &Source<'_>,
    model: &FxHashMap<String, SmtValue>,
    budget: &mut Budget<'_>,
) -> Option<()> {
    for (name, var) in &source.variables {
        budget.charge(1)?;
        if let Some(value) = model.get(*name) {
            values::typed(value, &var.sort, budget)?;
        }
    }
    Some(())
}

fn project_original_variables(
    source: &Source<'_>,
    model: &mut FxHashMap<String, SmtValue>,
    budget: &mut Budget<'_>,
) -> Option<()> {
    // Pre-admit every key and the cleanup shape of every foreign value.
    // Destruction remains opaque; no arbitrary source-typing authority is
    // inferred from an auxiliary value that is about to be discarded.
    for (name, value) in model.iter() {
        budget.charge(name.len().checked_add(1)?)?;
        if !source.variables.contains_key(name.as_str()) {
            values::discarded(value, budget)?;
        }
    }
    let mut refused = false;
    model.retain(|name, _| {
        if refused {
            return true;
        }
        if budget.charge(1).is_none() {
            refused = true;
            return true;
        }
        source.variables.contains_key(name.as_str())
    });
    if refused {
        return None;
    }
    // All removed values have dropped before the final original verification.
    budget.charge(0)
}

/// Local expression carriers actually referenced by one evaluator subtree.
/// Arithmetic growth remains opaque; this is not an all-allocation bound.
struct EvaluationCost {
    nodes: usize,
    carrier: usize,
}

fn admit_evaluation(
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    budget: &mut Budget<'_>,
) -> Option<EvaluationCost> {
    let mut stack = vec![rhs];
    let (mut nodes, mut payload) = (0usize, 0usize);
    while let Some(expr) = stack.pop() {
        budget.charge(1)?;
        if matches!(expr, ChcExpr::ArrayLambda(_)) {
            return None;
        }
        nodes = nodes.checked_add(1)?;
        if let ChcExpr::Var(var) = expr {
            if let Some(value) = model.get(&var.name) {
                payload = payload.checked_add(values::size(value, budget)?)?;
            }
        }
        let children = crate::expr::dag::children(expr);
        if stack.len().checked_add(children.len())? > budget.remaining {
            return None;
        }
        stack.try_reserve(children.len()).ok()?;
        stack.extend(children.iter().map(AsRef::as_ref));
    }
    let carrier = nodes.checked_add(payload)?;
    budget.charge(nodes.checked_mul(carrier)?)?;
    Some(EvaluationCost { nodes, carrier })
}

/// Canonical verification evaluates an And by visiting its children separately
/// and retains only a Bool/None result. Its memo likewise stores that node's
/// Bool result, not the full model or the children's array carriers.
/// Price each non-And evaluator subtree from its own source and referenced
/// values, rather than multiplying unrelated variables' payload into every
/// equation. This does not replace the final strict original-expression check.
fn admit_verification(
    original: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    budget: &mut Budget<'_>,
) -> Option<()> {
    let mut stack = vec![original];
    while let Some(expr) = stack.pop() {
        budget.charge(1)?;
        if let ChcExpr::Op(ChcOp::And, children) = expr {
            if stack.len().checked_add(children.len())? > budget.remaining {
                return None;
            }
            stack.try_reserve(children.len()).ok()?;
            stack.extend(children.iter().map(AsRef::as_ref));
        } else {
            let cost = admit_evaluation(expr, model, budget)?;
            let comparisons = cost.carrier.checked_mul(cost.carrier)?;
            budget.charge(cost.nodes.checked_mul(comparisons)?)?;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests;
