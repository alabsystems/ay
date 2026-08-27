// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-preserving counterexample minimization.
//!
//! After a SAT result, tries replacing variable values with smaller candidates
//! while re-evaluating all assertions to ensure the model remains valid.

use ay_core::{Sort, Symbol, TermData, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Signed;

// Re-exported for tests (used via `use super::*` in tests.rs).
#[cfg(test)]
use {ay_arrays::ArrayInterpretation, num_traits::One, num_traits::Zero};

use super::{EvalValue, Model};
use crate::executor::Executor;

mod bv_dependents;
mod candidates;
mod scalar_passes;
use bv_dependents::BvDependentIndex;
use candidates::*;

/// Maximum minimization passes. After shrinking one variable, others may
/// become shrinkable (e.g., x + y = 10: shrinking x enables shrinking y).
const MAX_MINIMIZATION_PASSES: usize = 3;

/// A pending minimization attempt: which variable to try, what value.
enum MinAttempt {
    Lia(TermId, Vec<BigInt>),
    Lra(TermId, Vec<BigRational>),
    Bv(TermId, Vec<BigInt>),
}

/// Extract leading u64 digit from a BigUint magnitude (0 if empty).
fn leading_u64(mag: &num_bigint::BigUint) -> u64 {
    mag.to_u64_digits().first().copied().unwrap_or(0)
}

impl MinAttempt {
    /// Magnitude of the current value, for sorting (largest first).
    fn magnitude(&self) -> u64 {
        match self {
            Self::Lia(_, c) | Self::Bv(_, c) => {
                c.last().map(|v| leading_u64(v.magnitude())).unwrap_or(0)
            }
            Self::Lra(_, c) => c
                .last()
                .map(|v| leading_u64(v.abs().to_integer().magnitude()))
                .unwrap_or(0),
        }
    }
}

impl Executor {
    /// Minimize the stored model in-place, preserving satisfiability.
    ///
    /// For each variable in the LIA, LRA, and BV models, tries smaller
    /// candidate values and validates all assertions still hold. Only keeps
    /// a replacement when the model evaluator confirms validity.
    ///
    /// Uses multi-pass convergence: after shrinking one variable, dependent
    /// variables may become shrinkable. Runs up to MAX_MINIMIZATION_PASSES.
    ///
    /// Call this after `self.last_model` is populated and before
    /// `finalize_sat_model_validation`.
    pub(in crate::executor) fn minimize_model_sat_preserving(&mut self) {
        self.minimize_model_sat_preserving_with_stop(|executor| executor.solve_deadline.expired());
    }

    /// Implementation of [`Self::minimize_model_sat_preserving`] with an
    /// explicit cooperative-stop predicate.
    ///
    /// Keeping the poll as a parameter makes the post-mutation stop path
    /// deterministic under test. Production always supplies the live solve
    /// deadline above.
    fn minimize_model_sat_preserving_with_stop(
        &mut self,
        mut should_stop: impl FnMut(&Self) -> bool,
    ) {
        // Gate-consistency snapshot (#minimize-gate-consistent, 2026-07-11):
        // the per-candidate accept check evaluates through the TOLERANT
        // model evaluator, which resolves a UF application's self-row via
        // the OTHER congruent row's committed value — so shrinking a UF
        // ARGUMENT variable can silently create a multi-valued UF point
        // (f at (0,0) = -1 and 0) that still "validates" here but is then
        // correctly rejected by the value-keyed independent model gate,
        // downgrading a genuine sat to unknown (multiarg_6146; the pre-gate
        // "pass" shipped that invalid witness as sat). Snapshot the
        // extracted model and, if minimization changed anything, re-check
        // through the SAME gate that will judge the final model. Only a
        // ConfirmedSat verdict authorizes the cosmetic replacement; every
        // non-confirming verdict restores the solver-produced snapshot.
        //
        // Deadline discipline (model-checker-consumer #39/#42): minimization is best-effort
        // COSMETICS for witness quality — the stored model is already valid.
        // Each candidate re-solve re-evaluates every assertion (and, with
        // datatypes present, walks term DAGs), which historically burned tens
        // of seconds past the solve deadline. A stop before any mutation returns
        // immediately. A stop after a kept candidate restores the original
        // model before returning, so the deadline cannot bypass the final gate.
        // Observable proof that the cosmetic pass RAN (#model-demand). The
        // demand gate lives at the four call sites, so without a counter here
        // "it was skipped" is only visible as a wall-clock difference, and a
        // gate that quietly stopped gating would look identical to one that
        // works. Counts entries, not accepted candidates: a pass that shrinks
        // nothing still spent the time this gate exists to save.
        let runs = self
            .last_statistics
            .get_int("model_minimization.runs")
            .unwrap_or(0);
        self.last_statistics
            .set_int("model_minimization.runs", runs.saturating_add(1));

        let Some((pre_minimization, scalar_changed, stopped)) =
            self.minimize_scalar_model_values(&mut should_stop)
        else {
            return;
        };
        if scalar_changed {
            let confirmed = !stopped
                && matches!(
                    self.confirm_sat_with_independent_gate(),
                    ay_model_check::GateVerdict::ConfirmedSat
                );
            if !confirmed {
                self.last_model = pre_minimization;
                super::eval_memo_clear();
            }
        }

        if stopped {
            return;
        }

        // Phase 3: Exact structural array minimization (#4522).
        //
        // Remove only stores that already equal the interpretation's committed
        // default. Changing (or inventing) a default from store-value frequency
        // is not semantics-preserving: it changes every unlisted index. This
        // exact reduction is safe even with the #5478 evaluator bug that blocks
        // scalar minimization when arrays are present.
        self.minimize_array_models();
    }

    /// Collect all minimization attempts from the current model.
    fn collect_min_attempts(&self, model: &Model) -> Vec<MinAttempt> {
        let mut attempts = Vec::new();
        let has_datatypes = self.ctx.ctor_selectors_iter().next().is_some();
        // Skip ALL theory minimization when array model exists (#5478).
        // The SAT-level fallback in evaluate_term (mod.rs:669-682) overrides
        // correctly-computed Bool(false) with the stale SAT model truth value
        // for any equality involving an array subterm. This affects LIA, LRA,
        // and BV equally — not just BV as originally fixed.
        let has_arrays = model.array_model.is_some();

        if !has_arrays {
            if let Some(ref lia_model) = model.lia_model {
                for (&term_id, original) in &lia_model.values {
                    // Skip DT selector application terms — minimization would
                    // clobber their values since DT assertions are not evaluable (#5432).
                    if has_datatypes && self.is_dt_selector_app(term_id) {
                        continue;
                    }
                    let candidates = int_candidates(original);
                    if candidates.len() > 1 || candidates.first() != Some(original) {
                        attempts.push(MinAttempt::Lia(term_id, candidates));
                    }
                }
            }
        }

        if !has_arrays {
            if let Some(ref lra_model) = model.lra_model {
                for (&term_id, original) in &lra_model.values {
                    if has_datatypes && self.is_dt_selector_app(term_id) {
                        continue;
                    }
                    let candidates = rational_candidates(original);
                    if candidates.len() > 1 || candidates.first() != Some(original) {
                        attempts.push(MinAttempt::Lra(term_id, candidates));
                    }
                }
            }
        }

        if !has_arrays {
            if let Some(ref bv_model) = model.bv_model {
                // BV variables whose value flows into an `(_ to_fp …)` /
                // `(_ to_fp_unsigned …)` conversion are pinned by the FP
                // bit-blaster. The minimizer's tolerant re-evaluation cannot
                // validate FP constraints (the ground gate reports FP as
                // "cannot-confirm", not a refutation), so shrinking these vars
                // silently corrupts the model — e.g. a NaN/1.0-encoding BV value
                // gets minimized to 0, producing an invalid `(get-model)` while
                // the verdict stays correctly `sat`. Exclude them, exactly like
                // the DT-selector exclusion below. (#bvfp-model-min)
                let fp_pinned_bv_vars = if model.fp_model.is_some() {
                    self.fp_conversion_bv_vars()
                } else {
                    ay_core::kani_compat::DetHashSet::default()
                };
                for (&term_id, original) in &bv_model.values {
                    // Only minimize free BV VARIABLES (#bv-ite-bool-model).
                    // The BV model also caches bit-blast values for compound
                    // terms (App/Ite) and constants; those values are DERIVED
                    // from the leaf assignment, so "minimizing" them merely
                    // decouples the cache from the leaves and corrupts every
                    // later consumer of the cached value.
                    if !matches!(self.ctx.terms.get(term_id), TermData::Var(_, _)) {
                        continue;
                    }
                    if fp_pinned_bv_vars.contains(&term_id) {
                        continue;
                    }
                    if has_datatypes && self.is_dt_selector_app(term_id) {
                        continue;
                    }
                    let width = match self.ctx.terms.sort(term_id) {
                        Sort::BitVec(bv) => bv.width,
                        _ => continue,
                    };
                    let candidates = bv_candidates(original, width);
                    if candidates.len() > 1 || candidates.first() != Some(original) {
                        attempts.push(MinAttempt::Bv(term_id, candidates));
                    }
                }
            }
        }

        attempts
    }

    /// BV *variables* whose value flows (transitively) into a `(_ to_fp …)` or
    /// `(_ to_fp_unsigned …)` conversion argument in the assertions.
    ///
    /// These variables' bits are constrained by the FP bit-blaster, and the
    /// counterexample minimizer's tolerant re-evaluation cannot validate FP
    /// constraints — so they must be excluded from BV minimization (shrinking
    /// them corrupts the model; see the call site). Collected once per model.
    fn fp_conversion_bv_vars(&self) -> ay_core::kani_compat::DetHashSet<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        // Pass 1: find the argument subterms of every to_fp/to_fp_unsigned app.
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut conv_args: Vec<TermId> = Vec::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if let TermData::App(Symbol::Indexed(name, _), _) = self.ctx.terms.get(t) {
                if name == "to_fp" || name == "to_fp_unsigned" {
                    for child in self.ctx.terms.children(t) {
                        conv_args.push(child);
                    }
                }
            }
            for child in self.ctx.terms.children(t) {
                stack.push(child);
            }
        }
        // Pass 2: collect BV-sorted variable leaves under those arguments.
        let mut result: HashSet<TermId> = HashSet::default();
        let mut leaf_visited: HashSet<TermId> = HashSet::default();
        let mut leaf_stack = conv_args;
        while let Some(t) = leaf_stack.pop() {
            if !leaf_visited.insert(t) {
                continue;
            }
            if matches!(self.ctx.terms.get(t), TermData::Var(..)) {
                if matches!(self.ctx.terms.sort(t), Sort::BitVec(_)) {
                    result.insert(t);
                }
            } else {
                for child in self.ctx.terms.children(t) {
                    leaf_stack.push(child);
                }
            }
        }
        result
    }

    /// Check if a term is a DT selector application (e.g., `(ival x)`).
    ///
    /// When datatypes are present, selector applications produce theory-model
    /// values that the model evaluator cannot validate (DT assertions are
    /// skipped). Minimizing these terms silently clobbers correct values (#5432).
    fn is_dt_selector_app(&self, term_id: TermId) -> bool {
        let name = match self.ctx.terms.get(term_id) {
            TermData::App(sym, _) => sym.name(),
            TermData::Var(name, _) => name.as_str(),
            _ => return false,
        };
        self.ctx
            .ctor_selectors_iter()
            .any(|(_, selectors)| selectors.iter().any(|sel| sel == name))
    }

    /// Try replacing a LIA variable with smaller candidates. Returns true if changed.
    fn try_lia_candidates(&mut self, term_id: TermId, candidates: Vec<BigInt>) -> bool {
        let original = match self
            .last_model
            .as_ref()
            .and_then(|m| m.lia_model.as_ref())
            .and_then(|lia| lia.values.get(&term_id))
        {
            Some(v) => v.clone(),
            None => return false,
        };

        for candidate in candidates {
            if candidate == original {
                break;
            }
            // Deadline bail (#42): keeping the current valid value is sound.
            if self.solve_deadline.expired() {
                break;
            }
            // Mutate
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lia) = model.lia_model {
                    lia.values.insert(term_id, candidate.clone());
                }
            }
            // Check
            if self.model_satisfies_assertions() {
                return true; // Keep the smaller value
            }
            // Revert
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lia) = model.lia_model {
                    lia.values.insert(term_id, original.clone());
                }
            }
        }
        false
    }

    /// Try replacing a LRA variable with smaller candidates. Returns true if changed.
    fn try_lra_candidates(&mut self, term_id: TermId, candidates: Vec<BigRational>) -> bool {
        let original = match self
            .last_model
            .as_ref()
            .and_then(|m| m.lra_model.as_ref())
            .and_then(|lra| lra.values.get(&term_id))
        {
            Some(v) => v.clone(),
            None => return false,
        };

        for candidate in candidates {
            if candidate == original {
                break;
            }
            // Deadline bail (#42): keeping the current valid value is sound.
            if self.solve_deadline.expired() {
                break;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lra) = model.lra_model {
                    lra.values.insert(term_id, candidate.clone());
                }
            }
            if self.model_satisfies_assertions() {
                return true;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lra) = model.lra_model {
                    lra.values.insert(term_id, original.clone());
                }
            }
        }
        false
    }

    /// Try replacing a BV variable with smaller candidates. Returns true if changed.
    ///
    /// `dependents` is the pass's [`BvDependentIndex`]; it answers "which cached
    /// compound values go stale if I move this leaf?" in one hash lookup.
    fn try_bv_candidates(
        &mut self,
        term_id: TermId,
        candidates: Vec<BigInt>,
        dependents: &BvDependentIndex,
    ) -> bool {
        let original = match self
            .last_model
            .as_ref()
            .and_then(|m| m.bv_model.as_ref())
            .and_then(|bv| bv.values.get(&term_id))
        {
            Some(v) => v.clone(),
            None => return false,
        };

        // Cached bit-blast values of COMPOUND terms that mention `term_id`
        // become stale the moment `term_id` is mutated: the model evaluator's
        // bv_model_cache_fallback (#5627) would otherwise keep answering with
        // the pre-mutation value and wrongly confirm an invalid candidate
        // (this is how all-zero invalid BV models escaped as sat,
        // #bv-ite-bool-model). Remove them for the duration of the check so
        // the oracle is forced to recompute from the mutated leaves (an
        // assertion that cannot be recomputed evaluates Unknown and the
        // candidate is rejected — fail-closed). Restore the entries verbatim
        // when every candidate is rejected; recompute them semantically when
        // one is kept.
        //
        // Served from the pass's reverse index instead of re-walking the whole
        // BV model per candidate leaf; debug builds re-derive the set by the
        // original full scan as the oracle (see `bv_dependents`).
        let Some(stale) = self.stale_bv_cache_entries(term_id, dependents) else {
            return false;
        };
        if let Some(bv) = self.last_model.as_mut().and_then(|m| m.bv_model.as_mut()) {
            for (t, _) in &stale {
                bv.values.remove(t);
            }
        }

        for candidate in candidates {
            if candidate == original {
                break;
            }
            // Deadline bail (#42): breaking here leaves the leaf at `original`
            // (every rejected iteration reverts it) and falls through to the
            // verbatim stale-cache restore below — the same state as "every
            // candidate rejected". Keeping the current valid value is sound.
            if self.solve_deadline.expired() {
                break;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut bv) = model.bv_model {
                    bv.values.insert(term_id, candidate.clone());
                }
            }
            if self.model_satisfies_assertions() {
                // Keep the smaller value; refresh the dependent cached
                // compound values from the new leaf assignment. Entries the
                // evaluator cannot recompute stay absent (fail-closed).
                let recomputed: Vec<(TermId, BigInt)> = {
                    let model = self
                        .last_model
                        .as_ref()
                        .expect("last_model present throughout minimization");
                    stale
                        .iter()
                        .filter_map(|&(t, _)| match self.evaluate_term(model, t) {
                            EvalValue::BitVec { value, width } => {
                                Some((t, Self::normalize_bv_value(value, width)))
                            }
                            _ => None,
                        })
                        .collect()
                };
                if let Some(bv) = self.last_model.as_mut().and_then(|m| m.bv_model.as_mut()) {
                    for (t, v) in recomputed {
                        bv.values.insert(t, v);
                    }
                }
                return true;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut bv) = model.bv_model {
                    bv.values.insert(term_id, original.clone());
                }
            }
        }
        // No candidate kept: the leaf is back at `original`, so the removed
        // cached values are valid again — restore them verbatim.
        if let Some(bv) = self.last_model.as_mut().and_then(|m| m.bv_model.as_mut()) {
            for (t, v) in stale {
                bv.values.insert(t, v);
            }
        }
        false
    }

    /// Check whether all assertions evaluate to true under the stored model.
    pub(in crate::executor) fn model_satisfies_assertions(&self) -> bool {
        let model = match self.last_model.as_ref() {
            Some(m) => m,
            None => return false,
        };
        // Evaluate the (DAG-shared) assertion set with the eval-memo active so
        // subterms shared across / within assertions are computed once per pass
        // instead of re-walked per reference. The model is immutable for this
        // whole call, so `evaluate_term(term_id)` is a pure function of
        // `term_id` here; the session is function-scoped and is the outermost
        // session over the minimize loop (which opens none), so its `Drop`
        // clears the cache before the loop's next candidate mutation. Purely a
        // speedup — it cannot change any evaluation result (#eval-memo).
        let _memo = super::EvalMemoSession::new();
        for &assertion in &self.ctx.assertions {
            if self.contains_internal_symbol(assertion)
                || self.contains_quantifier(assertion)
                || self.contains_datatype_term(assertion)
            {
                continue;
            }
            match self.evaluate_term(model, assertion) {
                EvalValue::Bool(true) => {}
                _ => return false,
            }
        }
        true
    }

    /// Aggressive model minimization (#8297).
    ///
    /// Runs additional minimization passes beyond the standard pipeline,
    /// with more iterations to allow inter-variable constraints to converge.
    /// Specifically targets BV variables with strict 0/1 pinning and runs
    /// up to 10 additional passes (vs the standard 3).
    ///
    /// Called when `--minimize-model` CLI flag is active.
    pub(in crate::executor) fn aggressive_minimize_model(&mut self) {
        const AGGRESSIVE_PASSES: usize = 10;

        let has_arrays = self
            .last_model
            .as_ref()
            .is_some_and(|m| m.array_model.is_some());
        if has_arrays {
            // Array evaluator bug (#5478) prevents safe scalar minimization.
            return;
        }

        for _pass in 0..AGGRESSIVE_PASSES {
            let Some((mut attempts, dependents)) = self.collect_min_attempts_and_dependents()
            else {
                return;
            };

            if attempts.is_empty() {
                break;
            }

            attempts.sort_by_key(|a| std::cmp::Reverse(a.magnitude()));

            let mut any_changed = false;
            for attempt in attempts {
                let changed = match attempt {
                    MinAttempt::Lia(term_id, candidates) => {
                        self.try_lia_candidates(term_id, candidates)
                    }
                    MinAttempt::Lra(term_id, candidates) => {
                        self.try_lra_candidates(term_id, candidates)
                    }
                    MinAttempt::Bv(term_id, candidates) => {
                        self.try_bv_candidates(term_id, candidates, &dependents)
                    }
                };
                any_changed |= changed;
            }

            if !any_changed {
                break;
            }
        }
    }

    /// Structurally minimize array models by removing redundant stores.
    ///
    /// A store is redundant exactly when its value equals the interpretation's
    /// existing default. The default itself is immutable here: changing it from
    /// store-value frequency would alter every unlisted index and therefore the
    /// array's denotation. Partial interpretations (no default) and conflicted
    /// interpretations remain untouched. No evaluator calls are needed.
    fn minimize_array_models(&mut self) {
        let model = match self.last_model.as_mut() {
            Some(m) => m,
            None => return,
        };
        if model.bv_model.is_some() {
            // QF_ABV validation relies on explicit reconstructed stores taking
            // precedence over exact select bits that may be stale after
            // preprocessing. Promoting stores into defaults erases that signal.
            return;
        }
        let array_model = match model.array_model.as_mut() {
            Some(am) => am,
            None => return,
        };

        for (term, interp) in array_model.array_values.iter_mut() {
            // #select-read-conflict-fail-closed: a read-conflicted interp is
            // deliberately partial — no default may be invented for it.
            minimize_array_interpretation(interp, array_model.read_conflicted.contains(term));
        }
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

#[allow(clippy::panic)]
#[cfg(test)]
mod demand_tests;
