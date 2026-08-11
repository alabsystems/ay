// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model completion: make the final model total over the original free
//! variables before full model validation runs.
//!
//! Preprocessing (`VariableSubstitution`) eliminates variables bound by
//! definitional equalities (e.g. `(= v9 (or v3 (<= v8 20)))` substitutes
//! `v9 -> (or v3 (<= v8 20))`), so the SAT/theory models carry no entry for
//! them. Truly unconstrained variables (`v3`, `v8` above) may also be absent
//! from every theory model. Model validation evaluates the ORIGINAL
//! assertions, so any missing value surfaces as `EvalValue::Unknown` and
//! degrades a correct SAT answer to Unknown.
//!
//! This pass completes the model in two phases at finalize time:
//!
//! 1. Default truly-free variables that have no value in any model and are
//!    not substitution keys: Bool -> false, Int/Real -> 0.
//! 2. Replay the recorded variable substitutions to a fixpoint, evaluating
//!    each eliminated variable's replacement RHS under the (now richer)
//!    model via the full term evaluator (`evaluate_term`), which resolves
//!    Bool variables through the SAT model / `bool_overrides` chain and
//!    arithmetic variables through the LIA/LRA/EUF chain.
//!
//! SOUNDNESS CONTRACT: completion only ADDS values for variables that have
//! none — it never overwrites a solver-assigned value (fill-only, gated by
//! an `evaluate_term(var) == Unknown` check that mirrors exactly what
//! validation will later see). The completed values are candidates only:
//! full model validation still runs afterwards and decides acceptance. A
//! wrong default makes an assertion evaluate to definitively-false, which
//! the strict gate / observation pipeline rejects, degrading to Unknown
//! exactly as before — so no wrong-sat can be introduced by this pass.

use ay_arrays::ArrayInterpretation;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::time::Instant;
use ay_core::{Sort, TermId};
use ay_fp::FpModelValue;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use std::time::Duration;

use super::{string_witness, EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::SolveResult;

/// How [`Executor::complete_constrained_gaps`] chooses a candidate value for a
/// constrained-but-unpinned gap variable. Strategies are tried in declaration
/// order; the first whose completed model the gates accept is kept.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GapStrategy {
    /// Resolve from the recorded substitution RHS, then asserted defining
    /// equalities, then assertion bounds / seq reconstruction, and only then the
    /// sort default. Faithful to constraints that DEFINE the variable (#5450).
    Derived,
    /// Use the canonical sort default directly, ignoring assertion-derived
    /// values. The recovery attempt when `Derived` produced a value that
    /// falsifies the model (#array-completion-order).
    SortDefault,
}

/// How a pre-existing array else-value participates in completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExistingArrayDefaultPolicy {
    /// A genuinely free base may keep the extractor's chosen completion.
    Preserve,
    /// An explicit scalar `(default a)` is semantic and must agree.
    Require,
    /// A defined target inherits its RHS default; an extractor fallback on the
    /// target is not an independent semantic authority.
    Ignore,
}

impl Executor {
    /// Complete the last SAT model so it is total over the original free
    /// variables (Bool/Int/Real sorts), then leave acceptance to validation.
    ///
    /// Runs at the top of `finalize_sat_model_validation` (and the
    /// assumption variant) so every solve path benefits. Idempotent and
    /// fill-only: variables that already resolve to a value through the
    /// evaluation chain are never touched.
    pub(in crate::executor) fn complete_model_for_validation(&mut self, extra_roots: &[TermId]) {
        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return;
        }
        // Completion can add or replace assertion-relevant witness values. This
        // method is normally entered with validation already pending, but inner
        // assumption routes can call it after an earlier validation pass. Make
        // the mutation primitive uphold the invariant itself: evidence for the
        // pre-completion model is invalid BEFORE ownership is taken or any value
        // changes. The outer SAT funnel must validate the completed model anew.
        if self.last_model.is_some() {
            self.last_model_validated = false;
        }
        let Some(mut model) = self.last_model.take() else {
            return;
        };

        // Memoize `evaluate_term` across this completion pass. The model mutates
        // here (defaulting/recovery), but every mutation runs through
        // `insert_completed_value`, which clears the cache, so no stale value is
        // ever read (#eval-memo). The session's `drop` clears the cache before
        // validation installs its own.
        let _eval_memo = super::EvalMemoSession::new();

        // Phase 0: before blindly defaulting missing Int/Real terms to 0,
        // try to resolve arithmetic atoms that are constrained by ground
        // assertions but absent from the extracted theory model. The nested
        // solve only proposes candidates; final validation below remains the
        // sole acceptance authority.
        if !self.final_lia_resolve_disabled {
            self.resolve_ground_constrained_absent_atoms(&mut model);
        }

        // Snapshot the recorded substitutions (TermId pairs — cheap).
        let substitutions: Vec<(TermId, TermId)> = self
            .recorded_var_substitutions
            .iter()
            .map(|(&from, &to)| (from, to))
            .collect();
        let substituted: HashSet<TermId> = substitutions.iter().map(|&(from, _)| from).collect();

        // Phase 1: default truly-free original variables that are missing a
        // value. Substitution keys are skipped — they are DEFINED by their
        // RHS and get their value in phase 2; defaulting them could
        // contradict the defining equality.
        let mut defaulted = 0usize;
        for var in self.collect_assertion_free_vars() {
            if substituted.contains(&var) {
                continue;
            }
            if !matches!(self.evaluate_term(&model, var), EvalValue::Unknown) {
                continue;
            }
            let Some(default) = self.unconstrained_default_value(self.ctx.terms.sort(var)) else {
                continue;
            };
            if Self::insert_completed_value(&self.ctx.terms, &mut model, var, &default) {
                defaulted += 1;
            }
        }

        // Phase 2: substitution fixpoint. Chained definitions
        // (a -> f(b), b -> g(c)) need multiple passes; each pass must make
        // progress or we stop (RHS not evaluatable — the variable stays
        // unknown and validation degrades to Unknown, sound as before).
        let mut recovered = 0usize;
        let max_passes = substitutions.len();
        let mut remaining = substitutions;
        for _ in 0..max_passes {
            if remaining.is_empty() {
                break;
            }
            let mut next = Vec::new();
            let mut progress = false;
            for (from, to) in remaining {
                // A target reading a substituted-away array (`select(v, _)`,
                // `v` eliminated) may have left this variable with a stale
                // BV-lane value, so re-derive it through the array-aware
                // evaluator even if it already has a value. For every other
                // target this stays fill-only: never overwrite a value the
                // solver assigned or an earlier recovery derived.
                let override_stale =
                    Self::target_reads_substituted_array(&self.ctx.terms, to, &substituted);
                let current = self.evaluate_term(&model, from);
                if !override_stale && !matches!(current, EvalValue::Unknown) {
                    continue;
                }
                let value = self.evaluate_term(&model, to);
                if matches!(value, EvalValue::Unknown) {
                    next.push((from, to));
                    continue;
                }
                // Already consistent with the array-aware value: nothing to do.
                if override_stale && value == current {
                    continue;
                }
                if !Self::insert_completed_value(&self.ctx.terms, &mut model, from, &value) {
                    next.push((from, to));
                    continue;
                }
                recovered += 1;
                progress = true;
            }
            if !progress {
                break;
            }
            remaining = next;
        }

        // Phase 2.5: default substitution keys the fixpoint could not recover.
        // A key `from -> RHS` whose RHS still evaluates to Unknown is defined by
        // an unconstrained term — e.g. `seed -> (select arr i)` over a free array
        // whose element sort is not bit-blastable (Bool/Int/Real), the shape the
        // VC encoder produces for a slice head. Phase 1 deliberately skipped it
        // (a key must not be defaulted before its RHS is tried); now that the RHS
        // is confirmed unconstrained, defaulting the key is consistent — the read
        // resolves back to the key through the same asserted equality
        // (`resolve_select_via_asserted_equality`). Fill-only and validation-
        // gated, so a contradicting default degrades to Unknown, never wrong-SAT.
        let mut late_defaulted = 0usize;
        for var in self.collect_assertion_free_vars() {
            if !substituted.contains(&var) {
                continue;
            }
            if !matches!(self.evaluate_term(&model, var), EvalValue::Unknown) {
                continue;
            }
            let Some(default) = self.unconstrained_default_value(self.ctx.terms.sort(var)) else {
                continue;
            };
            if Self::insert_completed_value(&self.ctx.terms, &mut model, var, &default) {
                late_defaulted += 1;
            }
        }

        // NOTE: declared-but-unconstrained constants of the remaining sorts are
        // NOT defaulted here. This method also runs on INNER solves where
        // theory dispatch has temporarily swapped/lowered `ctx.assertions`
        // (e.g. the seq path solves against a rewritten set), so "occurs in no
        // assertion" is NOT evidence of unconstrainedness at this point.
        // `complete_unconstrained_constants_for_output` runs that sweep at the
        // OUTER check-sat level, where `ctx.assertions` is the original set
        // the validation gates read (#no-fabricated-model-values).

        if defaulted > 0 || recovered > 0 || late_defaulted > 0 {
            tracing::debug!(
                defaulted,
                recovered,
                late_defaulted,
                "model completion: filled missing variable values before validation"
            );
            self.last_statistics
                .set_int("model_completion.defaulted", defaulted as u64);
            self.last_statistics
                .set_int("model_completion.recovered", recovered as u64);
            self.last_statistics
                .set_int("model_completion.late_defaulted", late_defaulted as u64);
        }

        // Phase 3: synthesize equality-class values for opaque carriers that
        // carry no model value. The eager BV/AUFBV path bit-blasts only the
        // BV/array index structure; an array whose element sort is an
        // uninterpreted (free) sort, or a bare uninterpreted variable / UF
        // application, gets NO element value. Likewise, a sequence encoded as
        // an equality-only carrier can have no concrete SeqModel payload even
        // though the SAT model commits its equality atoms. In either case an
        // equality over the missing carrier evaluates to Unknown and the
        // validator fails closed — returning Unknown for a genuinely SAT
        // query. This phase assigns each SAT-committed equality class a
        // distinct, model-resident element so exact validation can decide
        // equality-only uses. Sequence builtins still require a concrete
        // SeqModel value and remain fail-closed.
        self.complete_uninterpreted_sort_model(&mut model, extra_roots);

        // Phase 4 (#g4-dt-ce-select): re-derive substituted BV/Bool vars whose
        // defining term reads a DATATYPE/uninterpreted-ELEMENT array. Phase 2's
        // fixpoint ran BEFORE the EUF element model existed — Phase 3
        // (`complete_uninterpreted_sort_model`) is what pins each `select`
        // congruence-class element into `euf_model.term_values` — so a
        // datatype-selector-over-array read (e.g. `(fld_rhs (select a i))`)
        // evaluated to Unknown then and the variable kept the STALE BV-lane
        // default the pre-EUF recovery produced (e.g. 0), invalidating the
        // emitted model (a subst-recovered guard mis-derived). Now that the
        // elements are pinned, the array-aware `evaluate_term` — via the
        // committed-element `select` fallback in `bv_select_fallback` — resolves
        // the read; re-derive to a small fixpoint so chained defs settle. SOUND:
        // `evaluate_term` reads only committed theory-model values and fails
        // closed to Unknown (the value is then left unchanged and validation
        // degrades to Unknown), so this only ever replaces a stale value with
        // the committed-model value, never fabricates one — and validation
        // re-checks every assertion under the result.
        let sub_pairs: Vec<(TermId, TermId)> = self
            .recorded_var_substitutions
            .iter()
            .map(|(&from, &to)| (from, to))
            .collect();
        // Closure: substituted vars whose value transitively depends on a
        // datatype-element-array read — the direct readers, plus any substituted
        // var whose def references one of them (e.g. `kani_assert_12` reads
        // `local_6_0`). Only these need re-derivation; leaving the rest untouched
        // keeps the change minimal and avoids disturbing correctly-recovered vars.
        let mut dt_dep: HashSet<TermId> = sub_pairs
            .iter()
            .filter(|&&(_, to)| Self::target_reads_datatype_element_array(&self.ctx.terms, to))
            .map(|&(from, _)| from)
            .collect();
        loop {
            let mut added = false;
            for &(from, to) in &sub_pairs {
                if !dt_dep.contains(&from)
                    && Self::term_references_var_in_set(&self.ctx.terms, to, &dt_dep)
                {
                    dt_dep.insert(from);
                    added = true;
                }
            }
            if !added {
                break;
            }
        }
        let dt_targets: Vec<(TermId, TermId)> = sub_pairs
            .into_iter()
            .filter(|&(f, _)| dt_dep.contains(&f))
            .collect();
        if !dt_targets.is_empty() {
            // Re-derive to a fixpoint: each pass overwrites any dt-dependent var
            // whose def now evaluates (through the committed EUF element model) to
            // a concrete value different from its stale one; `insert_completed_value`
            // clears the eval memo so dependents see the update next pass. Bounded
            // by chain length. Fail-closed: Unknown leaves the value as-is.
            let max_passes = dt_targets.len() + 1;
            for _ in 0..max_passes {
                let mut changed = false;
                for &(from, to) in &dt_targets {
                    let value = self.evaluate_term(&model, to);
                    if matches!(value, EvalValue::Unknown)
                        || value == self.evaluate_term(&model, from)
                    {
                        continue;
                    }
                    if Self::insert_completed_value(&self.ctx.terms, &mut model, from, &value) {
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
        }

        // Phase 5 (#dt-total-model): total datatype model construction. Build
        // equivalence classes over the datatype-sorted terms, assign every
        // class a concrete constructor value (forced constructor with
        // recursively-resolved fields; well-founded base default for free
        // classes; occurs-check fails cyclic chains closed), and pin the
        // values into the model so ALL downstream validators — and the
        // printers — see one total assignment. Candidates only: the full
        // validation pipeline still decides acceptance, so an inconsistent
        // construction degrades SAT to Unknown exactly as an incomplete model
        // does today (see dt_construct.rs module docs for the soundness
        // argument).
        let dt_constructed = self.construct_total_datatype_model(&mut model, extra_roots);
        if dt_constructed > 0 {
            self.last_statistics
                .set_int("model_completion.dt_constructed", dt_constructed as u64);
        }

        // Phase 6: make assertion-relevant array interpretations total in the
        // model itself.  Explicit `(default a)` scalar assignments are mirrored
        // first; store definitions and hard aliases then propagate that
        // authority.  Read conflicts poison their whole dependency component
        // and are deliberately left partial.  The printer is not a completion
        // authority and will fail closed if this phase cannot build a coherent
        // candidate.
        let (arrays_completed, _) =
            self.complete_array_models_for_validation(&mut model, extra_roots);
        if arrays_completed > 0 {
            self.last_statistics
                .set_int("model_completion.arrays_completed", arrays_completed as u64);
        }

        self.last_model = Some(model);
    }

    /// Commit total interpretations for array terms that participate in the
    /// current query.  This is deliberately a model-completion phase, not an
    /// output-formatting convenience: validation, scalar reads, minimization,
    /// and printing must all observe the same else value and store order.
    fn complete_array_models_for_validation(
        &mut self,
        model: &mut Model,
        extra_roots: &[TermId],
    ) -> (usize, bool) {
        let (mut relevant, edges, alias_edges, definitions, required_reads) =
            self.collect_array_completion_graph(model, extra_roots);
        if relevant.is_empty() {
            return (0, false);
        }
        relevant.sort_by_key(|term| term.index());
        relevant.dedup();
        let relevant_set: HashSet<TermId> = relevant.iter().copied().collect();

        // Record provenance BEFORE mirroring.  Array extractors commonly put a
        // zero-like fallback in every interpretation, while an independently
        // evaluated `(default a)` term is an actual semantic observation.  The
        // distinction matters for store definitions: the RHS default must
        // replace a stale target fallback, but must agree with an explicit
        // `(default target)` value.
        let mut semantic_default_arrays = HashSet::default();
        for default_term in self.ctx.terms.term_ids() {
            let Some(array) = self.ctx.terms.get_array_default(default_term) else {
                continue;
            };
            if !relevant_set.contains(&array)
                || model
                    .array_model
                    .as_ref()
                    .is_some_and(|arrays| arrays.read_conflicted.contains(&array))
            {
                continue;
            }
            let value = self.evaluate_symbolic_array_default_scalar(model, default_term);
            if matches!(value, EvalValue::Unknown)
                || self.try_format_eval_value(&value, default_term).is_err()
            {
                continue;
            }
            semantic_default_arrays.insert(array);
        }

        // A scalar assignment to `(default a)` is semantic authority.  Mirror
        // it before considering a canonical default for any remaining gap, but
        // only for arrays in this query's relevance closure.
        let mut model_changed =
            self.materialize_relevant_symbolic_array_defaults_in_model(model, &relevant_set);
        if model_changed {
            super::eval_memo_clear();
        }

        let conflict_seeds = model
            .array_model
            .as_ref()
            .map_or_else(HashSet::default, |arrays| arrays.read_conflicted.clone());
        let mut tainted = Self::propagate_array_completion_taint(&edges, &conflict_seeds);

        // A direct select that occurs in an active assertion/assumption is a
        // required observation.  If it is still unknown before completion,
        // silently dropping it from the witness and assigning the base default
        // would manufacture the value at a constrained cell.  Leave the whole
        // hard dependency component partial instead.  Inactive/query-only
        // select terms in the global interner are deliberately excluded.
        let incomplete_read_arrays: HashSet<TermId> = required_reads
            .iter()
            .filter(|&&read| match self.ctx.terms.sort(read) {
                // `EvalValue` has no whole-array variant, so an array-valued
                // select is necessarily `Unknown` even when its recursively
                // observed cells form a complete witness.  Ask the array
                // completion builder instead; it fails closed if any active
                // nested read or key is genuinely unresolved.
                Sort::Array(array_sort) => self
                    .array_completion_candidate_interp(
                        model,
                        read,
                        &array_sort.element_sort,
                        super::output_format::ArrayInterpMode::CompleteDefault,
                    )
                    .is_none(),
                _ => {
                    matches!(self.evaluate_term(model, read), EvalValue::Unknown)
                        && self
                            .extract_value_from_asserted_equalities(model, read)
                            .is_none()
                        // Pure QF_AX can safely try the array's canonical
                        // default for an otherwise-unpinned read: its
                        // authoritative fail-closed gate re-checks every
                        // ground assertion against the committed candidate.
                        && self.ctx.logic() != Some("QF_AX")
                }
            })
            // An unresolved read poisons its base array only while it is still
            // semantically OBSERVED.  Ground instantiation schemas (e.g. the
            // per-length `(=> (= len k) (= r (select a k)))` family a frontend
            // emits for `last()`) keep every `select` in the assertion tree
            // even when the model falsifies every guard; such a read constrains
            // no cell, and treating it as a required observation left a
            // declared, never-actually-read array permanently partial — and
            // therefore unprintable (#array-decl-default-witness).
            .filter(|&&read| self.array_read_is_semantic_observation(model, read, extra_roots))
            .filter_map(|&read| match self.ctx.terms.get(read) {
                TermData::App(symbol, args) if symbol.name() == "select" && args.len() == 2 => {
                    Some(args[0])
                }
                _ => None,
            })
            .collect();
        let incomplete = Self::propagate_array_completion_taint(&edges, &incomplete_read_arrays);

        // Build in a shadow model.  Definition fixpoint passes may depend on an
        // interpretation derived in an earlier pass, but no speculative value
        // becomes observable in the real model until conflict/alias checks have
        // succeeded.
        let original_arrays = model.array_model.clone().unwrap_or_default();
        let mut working_model = model.clone();
        // Only VARIABLE targets suppress the first-pass candidate. An opaque
        // array-valued APPLICATION target (#opaque-array-app-def) still gets
        // its reads-derived candidate here, and the definition fixpoint below
        // OVERWRITES it whenever the definition's right-hand side interprets.
        // That keeps the change fill-only: a definition whose RHS cannot be
        // interpreted (an uninterpreted store base, say) leaves exactly
        // today's candidate in place instead of stripping the application of
        // any interpretation at all.
        let defined_targets: HashSet<TermId> = definitions
            .iter()
            .filter(|&&(var, _)| matches!(self.ctx.terms.get(var), TermData::Var(_, _)))
            .map(|&(var, _)| var)
            .collect();
        let mut candidates: HashMap<TermId, ArrayInterpretation> = HashMap::default();
        let mut discovered_conflicts: HashSet<TermId> = HashSet::default();

        for &term in &relevant {
            if tainted.contains(&term)
                || incomplete.contains(&term)
                || defined_targets.contains(&term)
            {
                continue;
            }
            let Sort::Array(array_sort) = self.ctx.terms.sort(term) else {
                continue;
            };
            let Some(candidate) =
                self.array_completion_interpretation(&working_model, term, array_sort)
            else {
                continue;
            };
            match Self::merge_array_completion_candidate(
                original_arrays.array_values.get(&term),
                candidate,
                array_sort,
                ExistingArrayDefaultPolicy::Preserve,
            ) {
                Ok(candidate) => {
                    candidates.insert(term, candidate.clone());
                    working_model
                        .array_model
                        .get_or_insert_with(Default::default)
                        .array_values
                        .insert(term, candidate);
                    super::eval_memo_clear();
                }
                Err(()) => {
                    discovered_conflicts.insert(term);
                }
            }
        }

        // Directed hard definitions (including recorded substitutions and
        // active assumption equalities) are solved to a bounded fixpoint.  A
        // target's pre-existing explicit default is checked against, never
        // allowed to replace, the inherited base default: disagreement taints
        // the dependency component instead of choosing a winner.
        for _ in 0..definitions.len().max(1) {
            let mut progress = false;
            for &(target, rhs) in &definitions {
                if tainted.contains(&target)
                    || tainted.contains(&rhs)
                    || incomplete.contains(&target)
                    || incomplete.contains(&rhs)
                {
                    continue;
                }
                let Sort::Array(array_sort) = self.ctx.terms.sort(target) else {
                    continue;
                };
                let Some(candidate) =
                    self.array_completion_interpretation(&working_model, rhs, array_sort)
                else {
                    continue;
                };
                let candidate = match Self::merge_array_completion_candidate(
                    original_arrays.array_values.get(&target),
                    candidate,
                    array_sort,
                    if semantic_default_arrays.contains(&target) {
                        ExistingArrayDefaultPolicy::Require
                    } else {
                        ExistingArrayDefaultPolicy::Ignore
                    },
                ) {
                    Ok(candidate) => candidate,
                    Err(()) => {
                        discovered_conflicts.insert(target);
                        continue;
                    }
                };
                if candidates
                    .get(&target)
                    .is_some_and(|old| Self::same_array_interpretation(old, &candidate))
                {
                    continue;
                }
                candidates.insert(target, candidate.clone());
                working_model
                    .array_model
                    .get_or_insert_with(Default::default)
                    .array_values
                    .insert(target, candidate);
                super::eval_memo_clear();
                progress = true;
            }
            if !progress {
                break;
            }
        }

        // Direct array aliases form one semantic interpretation.  Prefer the
        // (unique) explicit default from any member, merge disjoint stores, and
        // reject differing values for one concrete key.  This also repairs
        // aliases eliminated by preprocessing whose representative alone kept
        // the extracted array model.
        let alias_components = Self::array_alias_components(&alias_edges);
        for component in alias_components {
            if component
                .iter()
                .any(|term| tainted.contains(term) || incomplete.contains(term))
            {
                continue;
            }
            let mut explicit_default: Option<String> = None;
            let mut alias_conflict = false;
            for term in &component {
                if !semantic_default_arrays.contains(term) {
                    continue;
                }
                let Some(default) = original_arrays
                    .array_values
                    .get(term)
                    .and_then(|interp| interp.default.as_ref())
                    .filter(|value| !value.contains('@'))
                else {
                    continue;
                };
                if explicit_default
                    .as_ref()
                    .is_some_and(|authority| authority != default)
                {
                    alias_conflict = true;
                    break;
                }
                explicit_default = Some(default.clone());
            }

            let mut merged: Option<ArrayInterpretation> = None;
            for term in &component {
                let Some(candidate) = candidates.get(term) else {
                    continue;
                };
                if let Some(ref mut accumulated) = merged {
                    // Differing extractor defaults are alternative heuristic
                    // completions, not contradictory facts.  Keep the first
                    // deterministic choice unless the component has the
                    // explicit authority collected above.
                    for (index, value) in &candidate.stores {
                        match accumulated.stores.iter().find(|(key, _)| key == index) {
                            Some((_, old_value)) if old_value != value => {
                                alias_conflict = true;
                                break;
                            }
                            Some(_) => {}
                            None => accumulated.stores.push((index.clone(), value.clone())),
                        }
                    }
                    if alias_conflict {
                        break;
                    }
                } else {
                    merged = Some(candidate.clone());
                }
            }
            if alias_conflict {
                discovered_conflicts.extend(component);
                continue;
            }
            let Some(mut merged) = merged else {
                continue;
            };
            if let Some(authority) = explicit_default {
                merged.default = Some(authority);
            }
            for term in component {
                let Sort::Array(array_sort) = self.ctx.terms.sort(term) else {
                    continue;
                };
                let mut member = merged.clone();
                member.index_sort = Some(array_sort.index_sort.clone());
                member.element_sort = Some(array_sort.element_sort.clone());
                candidates.insert(term, member);
            }
        }

        if !discovered_conflicts.is_empty() {
            tainted = Self::propagate_array_completion_taint(&edges, &discovered_conflicts)
                .into_iter()
                .chain(tainted)
                .collect();
        }

        let arrays = model.array_model.get_or_insert_with(Default::default);
        for term in &tainted {
            if arrays.read_conflicted.insert(*term) {
                model_changed = true;
            }
        }

        let mut completed = 0usize;
        let mut ordered_candidates: Vec<_> = candidates.into_iter().collect();
        ordered_candidates.sort_by_key(|(term, _)| term.index());
        for (term, candidate) in ordered_candidates {
            if tainted.contains(&term) {
                continue;
            }
            if arrays
                .array_values
                .get(&term)
                .is_some_and(|old| Self::same_array_interpretation(old, &candidate))
            {
                continue;
            }
            arrays.array_values.insert(term, candidate);
            completed += 1;
            model_changed = true;
        }

        if model_changed {
            super::eval_memo_clear();
        }

        // SECOND, GATE-VERIFIED PASS for the arrays excluded above ONLY because
        // an ACTIVE required `select` read still evaluates Unknown
        // (`incomplete`). That is the guarded-vacuous-read shape: the read
        // literal sits under an implication/disjunct the SAT assignment
        // satisfies without it, so no theory ever assigned the cell — yet
        // refusing to complete the array poisons the ENTIRE `(get-model)` /
        // `(get-value)` answer ("model value for array ... is not available")
        // even though check-sat answered Sat and the gates validated the model.
        //
        // Candidates are built with `CompleteSkipUnknownReads` (an
        // Unknown-VALUED active read at a NAMEABLE cell is skipped; an Unknown
        // INDEX still fails the array closed — the cell cannot be named),
        // committed into the model, and then accepted ONLY if the strict
        // oracles AND the independent model-check gate re-confirm the COMPLETED
        // model over all assertions/assumptions
        // ([`Self::completed_gap_model_accepted`], the same snapshot-and-
        // RETRACT discipline as `complete_constrained_gaps`,
        // #array-completion-order). Any refutation retracts to the pre-pass
        // snapshot — exactly today's fail-closed partial model. SOUND BY
        // CONSTRUCTION: a manufactured cell value that actually matters
        // falsifies re-validation and is retracted, so no invalid witness can
        // ship and no verdict can change (this runs only under an existing Sat
        // and every mutation revokes `last_model_validated`, so the outer
        // funnel re-validates the final model regardless).
        //
        // Outer solves only: inner pivot-enum solves run against
        // swapped/lowered assertion sets where "active read" and gate
        // acceptance are not meaningful (#inner-assertion-swap).
        if self.pivot_enum_depth == 0 {
            let gate_targets: Vec<TermId> = relevant
                .iter()
                .copied()
                .filter(|term| incomplete.contains(term) && !tainted.contains(term))
                .collect();
            // Definition targets the first-pass fixpoint left without ANY
            // interpretation: their RHS is a shape only the skip mode can
            // interpret (e.g. an array-valued `select` cell of an
            // incomplete-read array — the deductive-checks ground-seed constants,
            // `(= (select m 0) seed)`). A target that already has a committed
            // interpretation is never revisited here.
            let unresolved_definitions: Vec<(TermId, TermId)> = definitions
                .iter()
                .copied()
                .filter(|&(target, rhs)| {
                    !tainted.contains(&target)
                        && !tainted.contains(&rhs)
                        && model
                            .array_model
                            .as_ref()
                            .is_none_or(|arrays| !arrays.array_values.contains_key(&target))
                })
                .collect();
            if !gate_targets.is_empty() || !unresolved_definitions.is_empty() {
                let snapshot = model.clone();
                let mut committed = 0usize;
                for &term in &gate_targets {
                    let Sort::Array(array_sort) = self.ctx.terms.sort(term) else {
                        continue;
                    };
                    let Some(candidate) = self.array_completion_interpretation_with_mode(
                        model,
                        term,
                        array_sort,
                        super::output_format::ArrayInterpMode::CompleteSkipUnknownReads,
                    ) else {
                        continue;
                    };
                    // Solver-extracted authority (explicit defaults/stores) is
                    // merged exactly as in the first pass; a conflict leaves
                    // the array partial rather than choosing a winner.
                    let candidate = match Self::merge_array_completion_candidate(
                        original_arrays.array_values.get(&term),
                        candidate,
                        array_sort,
                        ExistingArrayDefaultPolicy::Preserve,
                    ) {
                        Ok(candidate) => candidate,
                        Err(()) => continue,
                    };
                    let arrays = model.array_model.get_or_insert_with(Default::default);
                    if arrays
                        .array_values
                        .get(&term)
                        .is_some_and(|old| Self::same_array_interpretation(old, &candidate))
                    {
                        continue;
                    }
                    arrays.array_values.insert(term, candidate);
                    super::eval_memo_clear();
                    committed += 1;
                }
                // Bounded definition fixpoint, mirroring the first pass:
                // resolve each still-uninterpreted target from its RHS with
                // the skip-mode candidate builder (chains may need multiple
                // rounds). Fill-only: a target completed above or in an
                // earlier round is never overwritten.
                for _ in 0..unresolved_definitions.len().max(1) {
                    let mut progress = false;
                    for &(target, rhs) in &unresolved_definitions {
                        if model
                            .array_model
                            .as_ref()
                            .is_some_and(|arrays| arrays.array_values.contains_key(&target))
                        {
                            continue;
                        }
                        let Sort::Array(array_sort) = self.ctx.terms.sort(target) else {
                            continue;
                        };
                        let Some(candidate) = self.array_completion_interpretation_with_mode(
                            model,
                            rhs,
                            array_sort,
                            super::output_format::ArrayInterpMode::CompleteSkipUnknownReads,
                        ) else {
                            continue;
                        };
                        let candidate = match Self::merge_array_completion_candidate(
                            original_arrays.array_values.get(&target),
                            candidate,
                            array_sort,
                            if semantic_default_arrays.contains(&target) {
                                ExistingArrayDefaultPolicy::Require
                            } else {
                                ExistingArrayDefaultPolicy::Ignore
                            },
                        ) {
                            Ok(candidate) => candidate,
                            Err(()) => continue,
                        };
                        model
                            .array_model
                            .get_or_insert_with(Default::default)
                            .array_values
                            .insert(target, candidate);
                        super::eval_memo_clear();
                        committed += 1;
                        progress = true;
                    }
                    if !progress {
                        break;
                    }
                }
                if committed > 0 {
                    if self.completed_gap_model_accepted(model) {
                        completed += committed;
                        model_changed = true;
                        self.last_statistics
                            .set_int("model_completion.incomplete_read_arrays", committed as u64);
                    } else {
                        *model = snapshot;
                        super::eval_memo_clear();
                    }
                }
            }
        }

        (completed, model_changed)
    }

    /// Whether a query-owned array read is a SEMANTIC observation: some
    /// top-level assertion/assumption conjunct containing it still needs its
    /// value.  A conjunct already FORCED true while the read is `Unknown`
    /// ([`Self::bool_term_forced`]) is satisfied by EVERY element the read
    /// could take — forcing only answers `true` when the unknown subterms
    /// cannot flip the verdict (a falsified implication guard, an
    /// independently satisfied disjunct, ...), so refining the read to any
    /// concrete value keeps that conjunct true.  A read contained ONLY in such
    /// conjuncts constrains nothing: completing its base array with the
    /// canonical default fabricates no observed value
    /// (#no-fabricated-model-values, #array-decl-default-witness), and full
    /// validation still re-checks every original assertion against the
    /// committed candidate — a wrong skip degrades to Unknown, never a wrong
    /// model.  An EUF-aliased base (`(= a b)`) is unaffected: alias edges are
    /// collected independently of reads, so a genuinely observed alias member
    /// still taints / merges its whole component.
    ///
    /// Fail-closed: a containing conjunct that does NOT already evaluate to
    /// `true` (false, Unknown, or unevaluable) keeps the read an observation.
    pub(super) fn array_read_is_semantic_observation(
        &self,
        model: &Model,
        read: TermId,
        extra_roots: &[TermId],
    ) -> bool {
        // Top-level conjuncts of the active query, mirroring the root set of
        // `collect_array_completion_graph` / `term_is_required_by_last_query`.
        let mut roots: Vec<TermId> = self.ctx.assertions.clone();
        roots.extend(self.last_assumptions.iter().flatten().copied());
        roots.extend_from_slice(extra_roots);
        let mut conjuncts = Vec::new();
        let mut seen_roots = HashSet::default();
        while let Some(root) = roots.pop() {
            if !seen_roots.insert(root) {
                continue;
            }
            match self.ctx.terms.get(root) {
                TermData::App(symbol, args) if symbol.name() == "and" => {
                    roots.extend(args.iter().copied());
                }
                _ => conjuncts.push(root),
            }
        }
        for conjunct in conjuncts {
            // Ground containment only: binder bodies do not name ground model
            // cells (the same exclusion the observation collectors apply).
            let mut contains = false;
            let mut seen = HashSet::default();
            let mut stack = vec![conjunct];
            while let Some(term) = stack.pop() {
                if term == read {
                    contains = true;
                    break;
                }
                if !seen.insert(term) {
                    continue;
                }
                match self.ctx.terms.get(term) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(condition, then_term, else_term) => {
                        stack.extend([*condition, *then_term, *else_term]);
                    }
                    TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    }
                    _ => {}
                }
            }
            if contains && !self.bool_term_forced(model, conjunct, true) {
                return true;
            }
        }
        false
    }

    /// Non-strict three-valued verdict for the Boolean SKELETON of `term`:
    /// `true` only when the term is guaranteed to evaluate to `want` under
    /// EVERY refinement of the current partial model.  `evaluate_term` is
    /// deliberately eager on connectives — `or` answers Unknown at the first
    /// unknown argument without scanning the rest — which is the right
    /// fail-closed shape for validation, but too weak to recognize a
    /// falsified-guard disjunction `(or (= r (select a k)) (not (= len k)))`
    /// as forced.  This walker restores the Kleene short-circuit for the
    /// connectives only; every leaf still defers to `evaluate_term` and fails
    /// closed on Unknown, so a `true` answer is refinement-stable.
    fn bool_term_forced(&self, model: &Model, term: TermId, want: bool) -> bool {
        // Recursion depth mirrors the Boolean nesting depth, exactly like the
        // evaluator itself — grow the stack the same way (#4602).
        stacker::maybe_grow(super::EVAL_STACK_RED_ZONE, super::EVAL_STACK_SIZE, || {
            self.bool_term_forced_inner(model, term, want)
        })
    }

    fn bool_term_forced_inner(&self, model: &Model, term: TermId, want: bool) -> bool {
        match self.ctx.terms.get(term) {
            TermData::App(symbol, args) if symbol.name() == "or" => {
                if want {
                    args.iter()
                        .any(|&arg| self.bool_term_forced(model, arg, true))
                } else {
                    args.iter()
                        .all(|&arg| self.bool_term_forced(model, arg, false))
                }
            }
            TermData::App(symbol, args) if symbol.name() == "and" => {
                if want {
                    args.iter()
                        .all(|&arg| self.bool_term_forced(model, arg, true))
                } else {
                    args.iter()
                        .any(|&arg| self.bool_term_forced(model, arg, false))
                }
            }
            TermData::App(symbol, args) if symbol.name() == "=>" && args.len() == 2 => {
                if want {
                    self.bool_term_forced(model, args[0], false)
                        || self.bool_term_forced(model, args[1], true)
                } else {
                    self.bool_term_forced(model, args[0], true)
                        && self.bool_term_forced(model, args[1], false)
                }
            }
            TermData::Not(inner) => self.bool_term_forced(model, *inner, !want),
            TermData::Ite(condition, then_term, else_term) => {
                match self.evaluate_term(model, *condition) {
                    EvalValue::Bool(true) => self.bool_term_forced(model, *then_term, want),
                    EvalValue::Bool(false) => self.bool_term_forced(model, *else_term, want),
                    // Unknown condition: forced only when BOTH branches are.
                    _ => {
                        self.bool_term_forced(model, *then_term, want)
                            && self.bool_term_forced(model, *else_term, want)
                    }
                }
            }
            _ => matches!(self.evaluate_term(model, term), EvalValue::Bool(b) if b == want),
        }
    }

    /// Convert the witness builder's oldest-first unique point list into the
    /// `ArrayInterpretation` contract (authoritative/newest first).
    fn array_completion_interpretation(
        &self,
        model: &Model,
        term: TermId,
        array_sort: &ay_core::ArraySort,
    ) -> Option<ArrayInterpretation> {
        self.array_completion_interpretation_with_mode(
            model,
            term,
            array_sort,
            super::output_format::ArrayInterpMode::CompleteDefault,
        )
    }

    /// [`Self::array_completion_interpretation`] with an explicit candidate
    /// mode. `CompleteSkipUnknownReads` is reserved for the gate-verified,
    /// retracting second pass (see `complete_array_models_for_validation`).
    fn array_completion_interpretation_with_mode(
        &self,
        model: &Model,
        term: TermId,
        array_sort: &ay_core::ArraySort,
        mode: super::output_format::ArrayInterpMode,
    ) -> Option<ArrayInterpretation> {
        // Datatype elements containing array fields are eligible here too. The
        // recursive witness renderer preserves every observed nested cell; any
        // missing field is only a completion candidate, and the strict plus
        // independent gates re-check the completed model before publication.
        // Refusing the entire sort left even unconstrained arrays in a simple
        // asserted disequality without a printable witness.
        let (default, mut stores) =
            self.array_completion_candidate_interp(model, term, &array_sort.element_sort, mode)?;
        stores.reverse();
        Some(ArrayInterpretation {
            default: Some(default),
            stores,
            index_sort: Some(array_sort.index_sort.clone()),
            element_sort: Some(array_sort.element_sort.clone()),
        })
    }

    /// Merge solver-extracted authority into a completion candidate.  Existing
    /// stores are newest-first, so only their first occurrence for an index is
    /// semantic; a shadowed older duplicate is intentionally ignored.
    fn merge_array_completion_candidate(
        existing: Option<&ArrayInterpretation>,
        mut candidate: ArrayInterpretation,
        array_sort: &ay_core::ArraySort,
        default_policy: ExistingArrayDefaultPolicy,
    ) -> Result<ArrayInterpretation, ()> {
        candidate.index_sort = Some(array_sort.index_sort.clone());
        candidate.element_sort = Some(array_sort.element_sort.clone());
        let Some(existing) = existing else {
            return Ok(candidate);
        };
        if existing
            .index_sort
            .as_ref()
            .is_some_and(|sort| sort != &array_sort.index_sort)
            || existing
                .element_sort
                .as_ref()
                .is_some_and(|sort| sort != &array_sort.element_sort)
        {
            return Err(());
        }
        if let Some(authority) = existing
            .default
            .as_ref()
            .filter(|value| !value.contains('@'))
        {
            match default_policy {
                ExistingArrayDefaultPolicy::Preserve => {
                    candidate.default = Some(authority.clone());
                }
                ExistingArrayDefaultPolicy::Require
                    if candidate.default.as_ref() != Some(authority) =>
                {
                    return Err(());
                }
                ExistingArrayDefaultPolicy::Require | ExistingArrayDefaultPolicy::Ignore => {}
            }
        }

        let mut merged_stores = Vec::new();
        let mut seen = HashSet::default();
        for (index, value) in &existing.stores {
            if seen.insert(index.clone()) {
                merged_stores.push((index.clone(), value.clone()));
            }
        }
        for (index, value) in candidate.stores {
            match merged_stores.iter().find(|(key, _)| key == &index) {
                Some((_, authority)) if authority != &value => {
                    if std::env::var_os("AY_DEBUG_COMPLETION_MERGE").is_some() {
                        eprintln!(
                            "[completion-merge] cell conflict idx={index} existing={authority} candidate={value}"
                        );
                    }
                    // ABSTRACT-ATOM cells (#qfax-atom-spelling): the extracted
                    // entry is the solver's newest-first authority; the
                    // candidate cell is a completion-time re-derivation whose
                    // sources (per-term committed reads, class propagation)
                    // can lag it. Before the internal-dialect normalization
                    // these two NEVER collided — the candidate arrived in the
                    // printer's `(as @X S)` spelling and slid in as a phantom
                    // duplicate cell, and the gate battery confirmed genuine
                    // sats using the EXISTING value (swap_invalid family).
                    // Preserve exactly that semantics minus the phantom: the
                    // authority wins, the candidate cell is dropped, and the
                    // full strict + independent gates still decide acceptance
                    // (a bad authority still degrades, never a wrong SAT).
                    // Concrete-valued cells (Int/BV/...) keep the strict
                    // conflict -> taint path unchanged.
                    if index.contains('@') || value.contains('@') || authority.contains('@') {
                        continue;
                    }
                    return Err(());
                }
                Some(_) => {}
                None => merged_stores.push((index, value)),
            }
        }
        candidate.stores = merged_stores;
        Ok(candidate)
    }

    pub(super) fn same_array_interpretation(
        lhs: &ArrayInterpretation,
        rhs: &ArrayInterpretation,
    ) -> bool {
        lhs.default == rhs.default
            && lhs.stores == rhs.stores
            && lhs.index_sort == rhs.index_sort
            && lhs.element_sort == rhs.element_sort
    }

    /// Collect only hard query structure: top-level conjunction equalities are
    /// alias/definition edges; equalities under disjunction, negation, or ITE
    /// are never treated as model authority.  Structural `store(result, base)`
    /// edges are unconditional term semantics and always propagate taint.
    pub(super) fn collect_array_completion_graph(
        &self,
        model: &Model,
        extra_roots: &[TermId],
    ) -> (
        Vec<TermId>,
        Vec<(TermId, TermId)>,
        Vec<(TermId, TermId)>,
        Vec<(TermId, TermId)>,
        HashSet<TermId>,
    ) {
        let mut relevant = HashSet::default();
        let mut edges = Vec::new();
        let mut aliases = Vec::new();
        let mut definitions = Vec::new();
        let mut required_reads = HashSet::default();
        // (#opaque-array-app-def) Candidate definitions whose TARGET is an
        // opaque array-valued UF application rather than a bare array
        // variable. Held aside and congruence-filtered after the DAG walk
        // below, which is what counts the application's sibling terms.
        let mut opaque_app_definitions: Vec<(TermId, TermId)> = Vec::new();
        let mut opaque_array_apps: Vec<TermId> = Vec::new();
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);

        let mut hard = roots.clone();
        while let Some(term) = hard.pop() {
            let TermData::App(symbol, args) = self.ctx.terms.get(term) else {
                continue;
            };
            if symbol.name() == "and" {
                hard.extend(args.iter().copied());
                continue;
            }
            if symbol.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            if !matches!(self.ctx.terms.sort(lhs), Sort::Array(_))
                || !matches!(self.ctx.terms.sort(rhs), Sort::Array(_))
            {
                continue;
            }
            relevant.insert(lhs);
            relevant.insert(rhs);
            edges.push((lhs, rhs));
            match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
                (TermData::Var(_, _), TermData::Var(_, _)) => aliases.push((lhs, rhs)),
                (TermData::Var(_, _), _) => definitions.push((lhs, rhs)),
                (_, TermData::Var(_, _)) => definitions.push((rhs, lhs)),
                // (#opaque-array-app-def) Neither side is a bare array
                // variable, but ONE side is an OPAQUE array-valued UF
                // application — `(g v)` / verification-consumer's Seq carrier
                // `(seq_array v)` — and the other is an array CONSTRUCTOR
                // (`const-array`/`store`). Such an application is exactly as
                // structure-free as a declared array constant: nothing in the
                // term itself says what array it denotes, so without this the
                // completion falls back to a reads-derived guess. Measured on
                // `(= (const-array 7) (g v))` over a BitVec-indexed,
                // Int-valued array: the published interpretation came out
                // `default 0` with every cell `0`, and the strict arrays
                // oracle then refuted the companion assertion
                // `(= (select (g v) #x3) 7)` — a genuine `sat` (z3) degraded
                // to `unknown`.
                //
                // Recorded as a CANDIDATE only; the congruence filter after
                // the DAG walk decides admission.
                _ => {
                    for (app, other) in [(lhs, rhs), (rhs, lhs)] {
                        if self.is_opaque_array_valued_app(app)
                            && !self.is_opaque_array_valued_app(other)
                            && self.is_array_definition_shape(other)
                        {
                            opaque_app_definitions.push((app, other));
                            break;
                        }
                    }
                }
            }
        }

        let mut seen = HashSet::default();
        let mut stack = roots;
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if matches!(self.ctx.terms.sort(term), Sort::Array(_)) {
                relevant.insert(term);
                if self.is_opaque_array_valued_app(term) {
                    opaque_array_apps.push(term);
                }
            }
            match self.ctx.terms.get(term) {
                TermData::App(symbol, args) => {
                    if symbol.name() == "select"
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
                    {
                        required_reads.insert(term);
                    }
                    if symbol.name() == "store"
                        && args.len() == 3
                        && matches!(self.ctx.terms.sort(term), Sort::Array(_))
                    {
                        edges.push((term, args[0]));
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.push(*condition);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                // Bound variables are represented by ordinary Var nodes.  Do
                // not mistake them for free model terms.
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
                _ => {}
            }
        }

        if let Some(arrays) = model.array_model.as_ref() {
            relevant.extend(arrays.array_values.keys().copied());
            relevant.extend(arrays.read_conflicted.iter().copied());
        }
        // User-declared 0-arity arrays are output-relevant even when the
        // formula never reads them.  Symbol metadata distinguishes these free
        // constants from quantifier/let binders, whose Var nodes must never be
        // completed as declarations.
        for (name, info) in self.ctx.symbol_iter() {
            if !info.arg_sorts.is_empty() || self.is_dt_internal_symbol(name) {
                continue;
            }
            let Some(term) = info.term else {
                continue;
            };
            if matches!(info.sort, Sort::Array(_)) {
                relevant.insert(term);
            }
        }
        for (&from, &to) in &self.recorded_var_substitutions {
            if !matches!(self.ctx.terms.sort(from), Sort::Array(_))
                || !matches!(self.ctx.terms.sort(to), Sort::Array(_))
            {
                continue;
            }
            relevant.insert(from);
            relevant.insert(to);
            edges.push((from, to));
            if matches!(self.ctx.terms.get(to), TermData::Var(_, _)) {
                aliases.push((from, to));
            } else {
                definitions.push((from, to));
            }
        }

        // (#opaque-array-app-def) CONGRUENCE FILTER for opaque array-valued
        // application targets.
        //
        // An array VARIABLE denotes one array per model, so its definitional
        // equality constrains nothing else. An APPLICATION does not have that
        // luxury: `v = w` forces `g(v) = g(w)`, and publishing an
        // interpretation for `(g v)` alone can contradict what the same model
        // says about a sibling `(g w)`. Nothing downstream re-derives UF
        // congruence over WHOLE-ARRAY values, so a congruence-inconsistent
        // interpretation published here would be re-checked only
        // per-application — and every assertion could then evaluate true under
        // a model no real interpretation of `g` realizes. That is a wrong-SAT
        // shape, so admission is refused unless congruence is vacuous:
        //
        //   (i)  the application has exactly ONE definitional right-hand side
        //        (competing definitions are ambiguous, never a chosen winner),
        //        and no other application of the same symbol carries one; and
        //   (ii) it is the ONLY application of its symbol (name, arity, array
        //        sort) anywhere in the query's term DAG, so there is no
        //        sibling application for congruence to relate it to.
        //
        // Under (ii) the value we publish for `(g v)` cannot conflict with any
        // other application of `g`, because there is none. Both tests are
        // purely restrictive: failing either falls back to today's
        // reads-derived candidate, which is exactly the pre-change behaviour.
        //
        // This mirrors, in the completion layer, the guard
        // `opaque_app_congruent_definitions_agree` already applies in
        // `normalize_array_with_definitions` (#seq-array-uf-def).
        if !opaque_app_definitions.is_empty() {
            let group_key = |term: TermId| -> Option<(String, usize, Sort)> {
                let TermData::App(symbol, args) = self.ctx.terms.get(term) else {
                    return None;
                };
                Some((
                    symbol.name().to_string(),
                    args.len(),
                    self.ctx.terms.sort(term).clone(),
                ))
            };
            for &(app, rhs) in &opaque_app_definitions {
                let Some(key) = group_key(app) else {
                    continue;
                };
                let ambiguous = opaque_app_definitions
                    .iter()
                    .any(|&(other_app, other_rhs)| {
                        (other_app != app || other_rhs != rhs)
                            && group_key(other_app).as_ref() == Some(&key)
                    });
                if ambiguous {
                    continue;
                }
                let has_congruent_sibling = opaque_array_apps
                    .iter()
                    .any(|&other| other != app && group_key(other).as_ref() == Some(&key));
                if has_congruent_sibling {
                    continue;
                }
                definitions.push((app, rhs));
            }
        }

        edges.sort_by_key(|(lhs, rhs)| (lhs.index(), rhs.index()));
        edges.dedup();
        aliases.sort_by_key(|(lhs, rhs)| (lhs.index(), rhs.index()));
        aliases.dedup();
        definitions.sort_by_key(|(lhs, rhs)| (lhs.index(), rhs.index()));
        definitions.dedup();
        (
            relevant.into_iter().collect(),
            edges,
            aliases,
            definitions,
            required_reads,
        )
    }

    fn propagate_array_completion_taint(
        edges: &[(TermId, TermId)],
        seeds: &HashSet<TermId>,
    ) -> HashSet<TermId> {
        let mut adjacency: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &(lhs, rhs) in edges {
            adjacency.entry(lhs).or_default().push(rhs);
            adjacency.entry(rhs).or_default().push(lhs);
        }
        let mut tainted = seeds.clone();
        let mut stack: Vec<TermId> = seeds.iter().copied().collect();
        while let Some(term) = stack.pop() {
            if let Some(neighbors) = adjacency.get(&term) {
                for &neighbor in neighbors {
                    if tainted.insert(neighbor) {
                        stack.push(neighbor);
                    }
                }
            }
        }
        tainted
    }

    fn array_alias_components(edges: &[(TermId, TermId)]) -> Vec<Vec<TermId>> {
        let mut adjacency: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &(lhs, rhs) in edges {
            adjacency.entry(lhs).or_default().push(rhs);
            adjacency.entry(rhs).or_default().push(lhs);
        }
        let mut nodes: Vec<TermId> = adjacency.keys().copied().collect();
        nodes.sort_by_key(|term| term.index());
        let mut seen = HashSet::default();
        let mut components = Vec::new();
        for node in nodes {
            if !seen.insert(node) {
                continue;
            }
            let mut component = Vec::new();
            let mut stack = vec![node];
            while let Some(term) = stack.pop() {
                component.push(term);
                if let Some(neighbors) = adjacency.get(&term) {
                    for &neighbor in neighbors {
                        if seen.insert(neighbor) {
                            stack.push(neighbor);
                        }
                    }
                }
            }
            component.sort_by_key(|term| term.index());
            components.push(component);
        }
        components
    }

    /// Synthesize concrete equality-class values for carrier terms that have
    /// none, consistent with the SAT model's equality atoms
    /// (#aufbv-uninterp-elem, #seq-exact-equality-carrier).
    ///
    /// MECHANISM. Build a union-find over every supported carrier subterm of the
    /// assertions, merging two same-sorted terms whenever the SAT model assigns
    /// their equality atom `(= a b)` true. A `select(arr, i)` whose element sort
    /// is uninterpreted is one such subterm: the equality
    /// `(= seed (select arr i))` puts the read and `seed` in one class. A
    /// sequence term with no concrete `SeqModel` value is another. Free-sort
    /// classes get distinct abstract elements in `model.euf_model`; sequence
    /// classes get actual `EvalValue::Seq` witnesses in `completed_values`.
    ///
    /// SOUNDNESS. Fill-only: a term that already resolves to a concrete value is
    /// never overwritten. A sequence class containing a concrete value reuses
    /// that value; otherwise classes of the same sequence sort receive values
    /// of distinct lengths. The synthesized values are candidates only —
    /// the full model validation that runs immediately afterward re-checks every
    /// original assertion against them, so a mis-synthesis makes an assertion
    /// evaluate definitively false or remain unevaluable and degrades SAT to
    /// Unknown — never a wrong SAT. No opaque sequence identity is exposed as a
    /// sequence value: both validation and output consume the same concrete
    /// `EvalValue::Seq` entries.
    fn complete_uninterpreted_sort_model(&mut self, model: &mut Model, extra_roots: &[TermId]) {
        use ay_core::kani_compat::DetHashMap as HashMap;

        // Uninterpreted-sort completion remains confined to the eager BV/AUFBV
        // gap: the array-theory paths produce their own EUF + array model and
        // must not be perturbed. Sequence equality carriers are independent of
        // that lane and may need completion even when no BV model exists.
        fn carrier_sort_key(sort: &Sort, allow_uninterpreted: bool) -> Option<String> {
            match sort {
                Sort::Uninterpreted(name) if allow_uninterpreted => Some(name.clone()),
                // This is an INTERNAL EufModel namespace, not an SMT-LIB sort
                // declaration. Including the complete sort keeps Seq Int and
                // Seq Bool class domains separate even if their printable class
                // names happen to match.
                Sort::Seq(_) => Some(format!("@ay-seq-carrier:{sort}")),
                _ => None,
            }
        }
        let allow_uninterpreted = model.bv_model.is_some();

        // 1. Gather supported carrier subterms + same-carrier equality atoms
        //    reachable from the assertions (skip quantifier/let bodies, whose
        //    bound vars are not free model variables).
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut carrier_terms: Vec<TermId> = Vec::new();
        let mut eq_atoms: Vec<(TermId, TermId, TermId)> = Vec::new();
        // Roots are the top-level assertions PLUS any `extra_roots` (the
        // assumptions a `check_sat_assuming` model is being validated against).
        // Under strict self-check, include the pre-preprocessing authored
        // window too: the authority-grade gate evaluates that exact window,
        // and proof-mode preprocessing may have removed its sequence carrier
        // terms from `ctx.assertions` entirely.
        // The body-equality `(= result (uf ..))` and disequality the VC encoder
        // hands deductive-checks as ASSUMPTIONS are not in `ctx.assertions`, so their
        // datatype-valued operands (e.g. the `result` binding) would otherwise
        // never be gathered as candidates and stay value-less — the model
        // evaluator then returns Unknown for the assumption and the SAT degrades
        // to Unknown (#aufbv-uninterp-elem, assumption roots).
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        stack.extend_from_slice(extra_roots);
        if let Some(authored) = self.self_check_authored_assertions.as_ref() {
            stack.extend_from_slice(authored);
        }
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            if carrier_sort_key(self.ctx.terms.sort(tid), allow_uninterpreted).is_some() {
                carrier_terms.push(tid);
            }
            match self.ctx.terms.get(tid) {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 {
                        let lhs_sort = self.ctx.terms.sort(args[0]);
                        let rhs_sort = self.ctx.terms.sort(args[1]);
                        if lhs_sort == rhs_sort
                            && carrier_sort_key(lhs_sort, allow_uninterpreted).is_some()
                        {
                            eq_atoms.push((tid, args[0], args[1]));
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        if carrier_terms.is_empty() {
            return;
        }
        carrier_terms.sort_by_key(|t| t.index());
        let sequence_carrier_idx: HashSet<usize> = carrier_terms
            .iter()
            .enumerate()
            .filter_map(|(idx, &term)| {
                let opaque = match self.ctx.terms.get(term) {
                    // Declared constants are opaque carrier leaves. Internal
                    // variables can also be model points, but only when the
                    // declaration registry owns their identity.
                    TermData::Var(name, _) => self.ctx.symbol_info_by_identity(name).is_some(),
                    // Use the shared authoritative builtin classifier and the
                    // declaration registry. Native theory applications may
                    // anchor a class through evaluation but can never receive
                    // a completion value; only registered declared UFs can.
                    TermData::App(sym, args) => {
                        !args.is_empty()
                            && !crate::features::is_builtin_symbol_name(sym.name())
                            && self.ctx.symbol_info_by_identity(sym.name()).is_some()
                            && !self.ctx.is_defined_fun(sym.name())
                            && self.ctx.adopted_macro_interp(sym.name()).is_none()
                    }
                    _ => false,
                };
                (matches!(self.ctx.terms.sort(term), Sort::Seq(_)) && opaque).then_some(idx)
            })
            .collect();

        // 2. Snapshot how each carrier term currently resolves. An existing
        //    EUF value is a real value only for an uninterpreted sort. For a
        //    sequence it is merely an internal equality-class label: remember
        //    it for class unification, but never expose it as a Seq value.
        let mut index_of: HashMap<TermId, usize> = HashMap::default();
        for (i, &t) in carrier_terms.iter().enumerate() {
            index_of.insert(t, i);
        }
        let mut resolved_elem: HashMap<usize, String> = HashMap::default();
        let mut resolved_seq: HashMap<usize, Vec<EvalValue>> = HashMap::default();
        let mut opaque_seq_class: HashMap<usize, String> = HashMap::default();
        let mut unknown_idx: Vec<usize> = Vec::new();
        for (i, &t) in carrier_terms.iter().enumerate() {
            if let Some(elem) = model
                .euf_model
                .as_ref()
                .and_then(|euf| euf.term_values.get(&t))
            {
                if matches!(self.ctx.terms.sort(t), Sort::Seq(_)) {
                    opaque_seq_class.insert(i, elem.clone());
                } else {
                    resolved_elem.insert(i, elem.clone());
                    continue;
                }
            }
            match self.evaluate_term(model, t) {
                EvalValue::Element(e) => {
                    if matches!(self.ctx.terms.sort(t), Sort::Seq(_)) {
                        // A generic EUF fallback can surface the internal class
                        // label as `Element`. It is not a concrete sequence.
                        opaque_seq_class.entry(i).or_insert(e);
                        unknown_idx.push(i);
                    } else {
                        resolved_elem.insert(i, e);
                    }
                }
                EvalValue::Seq(elems) => {
                    resolved_seq.insert(i, elems);
                }
                // Prefer a LENGTH-PINNED witness over this pass's arbitrary
                // "next unused length". Gated on `sequence_carrier_idx` so the
                // O(N x |terms|) reconstruction stays off non-carriers.
                // Distinctness does not regress: `used_lengths` is built from
                // `seq_class_value`, which now includes these resolved entries,
                // so an unpinned class still skips a taken length.
                EvalValue::Unknown => match self.length_pinned_seq_witness(model, t) {
                    Some(EvalValue::Seq(elems)) if sequence_carrier_idx.contains(&i) => {
                        resolved_seq.insert(i, elems);
                    }
                    _ => unknown_idx.push(i),
                },
                // Any defensive sort/value mismatch remains unresolved and
                // therefore fail-closed.
                _ => {}
            }
        }
        if unknown_idx.is_empty() && resolved_seq.is_empty() {
            return;
        }

        // 3. Union-find over the carrier terms, merged on equality atoms the
        //    model commits to true: a TOP-LEVEL `(= a b)` assertion is
        //    true in every model (even when preprocessing collapsed its SAT atom
        //    to a tautology and dropped the variable), and a nested atom is
        //    merged when the SAT model assigns it true.
        let mut parent: Vec<usize> = (0..carrier_terms.len()).collect();
        fn find(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        let union = |parent: &mut [usize], a: usize, b: usize| {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra != rb {
                parent[ra] = rb;
            }
        };
        // A top-level assertion is true in every model; an `extra_roots`
        // assumption is enforced true for this `check_sat_assuming`, so a
        // positive `=` atom appearing as one merges its operands' classes (the
        // `result == uf(..)` body binding the VC hands us as an assumption).
        let top_level: HashSet<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .chain(extra_roots.iter().copied())
            .chain(
                self.self_check_authored_assertions
                    .iter()
                    .flatten()
                    .copied(),
            )
            .collect();
        for &(atom, a, b) in &eq_atoms {
            let committed_true = top_level.contains(&atom)
                || self.term_value(&model.sat_model, &model.term_to_var, atom) == Some(true);
            if committed_true {
                if let (Some(&ia), Some(&ib)) = (index_of.get(&a), index_of.get(&b)) {
                    union(&mut parent, ia, ib);
                }
            }
        }

        // EUF may already have assigned the same internal class label to two
        // sequence terms (notably congruent UF applications) even when there is
        // no surviving equality atom between their exact TermIds. Preserve
        // that committed equality in the concrete completion.
        let mut first_seq_class_member: HashMap<(Sort, String), usize> = HashMap::default();
        for (&idx, class) in &opaque_seq_class {
            let sort_key = self.ctx.terms.sort(carrier_terms[idx]).clone();
            if let Some(&first) = first_seq_class_member.get(&(sort_key.clone(), class.clone())) {
                union(&mut parent, first, idx);
            } else {
                first_seq_class_member.insert((sort_key, class.clone()), idx);
            }
        }

        // 4a. Canonical element per uninterpreted-sort class: preserve the
        //     pre-existing behavior for the eager BV/AUFBV gap.
        let mut class_elem: HashMap<usize, String> = HashMap::default();
        let mut blocked_class: HashSet<usize> = HashSet::default();
        for (&idx, elem) in &resolved_elem {
            let root = find(&mut parent, idx);
            if class_elem
                .get(&root)
                .is_some_and(|existing| existing != elem)
            {
                // The candidate model already assigns two different elements
                // to a SAT-committed equality class. Preserve both values and
                // leave missing members unresolved so validation fails closed.
                blocked_class.insert(root);
            } else {
                class_elem.entry(root).or_insert_with(|| elem.clone());
            }
        }
        let mut sort_counters: HashMap<String, usize> = HashMap::default();
        let mut new_values: Vec<(TermId, String, String)> = Vec::new();
        for &idx in &unknown_idx {
            let t = carrier_terms[idx];
            let sort = self.ctx.terms.sort(t);
            if matches!(sort, Sort::Seq(_)) {
                continue;
            }
            let Some(sort_name) = carrier_sort_key(sort, allow_uninterpreted) else {
                continue;
            };
            let root = find(&mut parent, idx);
            if blocked_class.contains(&root) {
                continue;
            }
            let elem = if let Some(name) = class_elem.get(&root) {
                name.clone()
            } else if matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode") {
                // FIXED 5-element FP domain (#P0.2 symbolic RoundingMode):
                // never mint an `@RoundingMode!n` token — it is not a valid
                // value of the sort. Any class reaching here is UNCONSTRAINED
                // (the executor's rm_domain coverage pass pins every RM term
                // in the assertion DAG to a literal-mode class, which resolves
                // above), so the shared IEEE default cannot violate a
                // distinctness the solver relied on.
                let name = "roundNearestTiesToEven".to_string();
                class_elem.insert(root, name.clone());
                name
            } else {
                let counter = sort_counters.entry(sort_name.clone()).or_insert(0);
                let name = format!("@{sort_name}!{counter}");
                *counter += 1;
                class_elem.insert(root, name.clone());
                name
            };
            new_values.push((t, sort_name, elem));
        }

        // 4b. Materialize each sequence class as an actual sequence. Existing
        //     concrete members determine their class value. Pure equality-only
        //     classes receive distinct lengths over one canonical element;
        //     length distinction is valid for every non-empty SMT sort and
        //     avoids inventing an element disequality the element sort may not
        //     support.
        let mut seq_class_value: HashMap<usize, Vec<EvalValue>> = HashMap::default();
        for (&idx, elems) in &resolved_seq {
            let root = find(&mut parent, idx);
            match seq_class_value.get(&root) {
                Some(existing) if existing != elems => {
                    // Two different concrete sequences are forced equal by the
                    // candidate model. Do not repair over either commitment.
                    blocked_class.insert(root);
                }
                None => {
                    seq_class_value.insert(root, elems.clone());
                }
                _ => {}
            }
        }

        let mut seq_roots_by_sort: HashMap<Sort, Vec<usize>> = HashMap::default();
        for (idx, &term) in carrier_terms.iter().enumerate() {
            if sequence_carrier_idx.contains(&idx) {
                let root = find(&mut parent, idx);
                let roots = seq_roots_by_sort
                    .entry(self.ctx.terms.sort(term).clone())
                    .or_default();
                if !roots.contains(&root) {
                    roots.push(root);
                }
            }
        }
        for roots in seq_roots_by_sort.values_mut() {
            roots.sort_unstable();
        }

        // Distinct lengths are deliberately bounded: materializing lengths
        // 0..N-1 otherwise costs O(N^2) cells on an untrusted equality DAG.
        // If either bound is exceeded, skip ALL sequence completion in this
        // pass; the normal validator/output pipeline then remains fail-closed.
        const MAX_SEQUENCE_COMPLETION_CLASSES: usize = 1_024;
        const MAX_SEQUENCE_COMPLETION_CELLS: usize = 4_096;
        let sequence_class_count: usize = seq_roots_by_sort.values().map(Vec::len).sum();
        let mut sequence_completion_allowed =
            sequence_class_count <= MAX_SEQUENCE_COMPLETION_CLASSES;
        let mut allocated_cells = 0usize;
        for elems in seq_class_value.values() {
            let Some(next) = allocated_cells.checked_add(elems.len()) else {
                sequence_completion_allowed = false;
                break;
            };
            if next > MAX_SEQUENCE_COMPLETION_CELLS {
                sequence_completion_allowed = false;
                break;
            }
            allocated_cells = next;
        }

        for (sort, roots) in &seq_roots_by_sort {
            if !sequence_completion_allowed {
                break;
            }
            let Sort::Seq(elem_sort) = sort else {
                continue;
            };
            let mut used_lengths: HashSet<usize> = roots
                .iter()
                .filter_map(|root| seq_class_value.get(root).map(Vec::len))
                .collect();
            let mut next_len = 0usize;
            for &root in roots.iter() {
                if blocked_class.contains(&root) || seq_class_value.contains_key(&root) {
                    continue;
                }
                while used_lengths.contains(&next_len) {
                    next_len += 1;
                }
                let default_elem = if next_len == 0 {
                    None
                } else {
                    let Some(value) = self.unconstrained_default_value(elem_sort) else {
                        sequence_completion_allowed = false;
                        break;
                    };
                    // `@U!n` is a valid internal EUF identity but not a
                    // standalone element term accepted by all model checkers
                    // when nested under `seq.unit`. Do not build a public Seq
                    // witness from such an opaque token.
                    if matches!(&value, EvalValue::Element(atom)
                        if atom.starts_with('@') || atom.contains('!'))
                    {
                        sequence_completion_allowed = false;
                        break;
                    }
                    Some(value)
                };
                let Some(next_cells) = allocated_cells.checked_add(next_len) else {
                    sequence_completion_allowed = false;
                    break;
                };
                if next_cells > MAX_SEQUENCE_COMPLETION_CELLS {
                    sequence_completion_allowed = false;
                    break;
                }
                let elems = match default_elem {
                    Some(elem) => vec![elem; next_len],
                    None => Vec::new(),
                };
                allocated_cells = next_cells;
                seq_class_value.insert(root, elems);
                used_lengths.insert(next_len);
                next_len += 1;
            }
        }

        // Account for the actual per-term clones committed below, including
        // propagation of pre-existing concrete values. This bounds both the
        // synthetic class representatives and the completed-values payload.
        if sequence_completion_allowed {
            let mut committed_cells = allocated_cells;
            for (idx, _) in carrier_terms.iter().enumerate() {
                if !sequence_carrier_idx.contains(&idx) {
                    continue;
                }
                let root = find(&mut parent, idx);
                let Some(elems) = seq_class_value.get(&root) else {
                    continue;
                };
                let Some(next) = committed_cells.checked_add(elems.len()) else {
                    sequence_completion_allowed = false;
                    break;
                };
                if next > MAX_SEQUENCE_COMPLETION_CELLS {
                    sequence_completion_allowed = false;
                    break;
                }
                committed_cells = next;
            }
        }
        if !sequence_completion_allowed {
            self.last_statistics
                .set_int("model_completion.sequence_budget_or_value_blocked", 1);
        }

        // 5. Commit free-sort elements into EUF and concrete sequences into the
        //    common completion slot. `insert_completed_value` is intentionally
        //    used for every sequence carrier term, including UF applications,
        //    so validation, get-model, get-value, and function-table rendering
        //    all observe the same witness.
        let mut synthesized_uninterpreted = 0usize;
        let mut synthesized_sequence = 0usize;
        if !new_values.is_empty() {
            let euf_model = model.euf_model.get_or_insert_with(Default::default);
            for (t, sort_name, elem) in new_values {
                if euf_model.term_values.contains_key(&t) {
                    continue;
                }
                let elements = euf_model.sort_elements.entry(sort_name).or_default();
                if !elements.contains(&elem) {
                    elements.push(elem.clone());
                }
                euf_model.term_values.insert(t, elem);
                synthesized_uninterpreted += 1;
            }
        }
        for (idx, &term) in carrier_terms.iter().enumerate() {
            if !sequence_completion_allowed {
                break;
            }
            if !sequence_carrier_idx.contains(&idx) {
                continue;
            }
            let root = find(&mut parent, idx);
            if blocked_class.contains(&root) {
                continue;
            }
            let Some(elems) = seq_class_value.get(&root) else {
                continue;
            };
            let value = EvalValue::Seq(elems.clone());
            if model.completed_values.get(&term) == Some(&value) {
                continue;
            }
            if Self::insert_completed_value(&self.ctx.terms, model, term, &value) {
                synthesized_sequence += 1;
            }
        }
        if synthesized_uninterpreted > 0 || synthesized_sequence > 0 {
            self.last_statistics.set_int(
                "model_completion.uninterpreted_elements",
                synthesized_uninterpreted as u64,
            );
            self.last_statistics.set_int(
                "model_completion.sequence_equality_classes",
                synthesized_sequence as u64,
            );
            // This phase mutates `euf_model` directly (not via
            // `insert_completed_value`), so invalidate the eval memo here too
            // (#eval-memo).
            super::eval_memo_clear();
        }
    }

    /// Repair an EUF model that over-populates a finite ENUM (all-nullary
    /// datatype) sort (#enum-model-repair).
    ///
    /// The eager DT axiomatization leaves an enum-sorted selector application
    /// (e.g. `(top (rest x))`) that no committed equality pins to a
    /// constructor in its own fresh EUF class; model extraction (and the
    /// uninterpreted-sort completion above) then mints a fresh `@Sort!n`
    /// element per class, so the model claims MORE distinct inhabitants than
    /// the sort's `k` constructor constants — and the sound, fail-closed
    /// enum-cardinality gate in `finalize_sat_model_validation` degrades the
    /// SAT to Unknown (the iterative-deepening loop then fixpoints on the same
    /// gate). Such surplus classes are merely UNCONSTRAINED: in any real model
    /// every enum value IS one of the `k` constructors, so this pass maps each
    /// surplus element onto a constructor slot consistent with
    ///
    /// (a) every (dis)equality over the sort that the model commits to
    ///     (top-level assertions and SAT-assigned atoms), and
    /// (b) functional consistency of every UF table: no two applications may
    ///     become argument-equal with different results under the remap.
    ///
    /// If no consistent mapping exists the model is left untouched and the
    /// gate degrades exactly as before (soundness first).
    ///
    /// SOUNDNESS: strictly candidate-producing — the enum-cardinality gate
    /// re-counts the repaired elements and the full assertion-level validation
    /// (strict oracles included) still decides acceptance, so a wrong mapping
    /// degrades to Unknown, never a wrong SAT.
    pub(in crate::executor) fn repair_enum_model_overpopulation(&mut self) {
        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return;
        }
        let Some(mut model) = self.last_model.take() else {
            return;
        };
        // Sorts whose materialized element count exceeds their enum cardinality.
        let overfull: Vec<(String, usize)> = model
            .euf_model
            .as_ref()
            .map(|euf| {
                euf.sort_elements
                    .iter()
                    .filter_map(|(name, elems)| {
                        let k = self
                            .enum_datatype_constructor_count(&Sort::Uninterpreted(name.clone()))?;
                        (elems.len() > k).then(|| (name.clone(), k))
                    })
                    .collect()
            })
            .unwrap_or_default();
        for (sort_name, k) in overfull {
            self.repair_one_enum_sort(&mut model, &sort_name, k);
        }
        self.last_model = Some(model);
    }

    /// One-sort worker for [`Self::repair_enum_model_overpopulation`]: compute
    /// a `k`-coloring of the sort's elements (constructor-anchored elements
    /// pre-colored, forced-distinct pairs as edges), verify UF-table
    /// consistency under the induced merge, then rewrite the model. Leaves the
    /// model untouched on any inconsistency (the cardinality gate then
    /// degrades as before).
    fn repair_one_enum_sort(&mut self, model: &mut Model, sort_name: &str, k: usize) {
        use ay_core::kani_compat::DetHashMap as HashMap;

        let Some(euf) = model.euf_model.as_ref() else {
            return;
        };
        let elements: Vec<String> = match euf.sort_elements.get(sort_name) {
            Some(e) if e.len() > k => e.clone(),
            _ => return,
        };
        let ctors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(name, _)| *name == sort_name)
            .map(|(_, cs)| cs.to_vec())
            .unwrap_or_default();
        if ctors.len() != k {
            return;
        }
        let ctor_color: HashMap<&str, usize> = ctors
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();
        let elem_index: HashMap<&str, usize> = elements
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();

        // Element -> constructor anchors: an element whose class contains the
        // constructor constant `Ci` already denotes `Ci` and keeps that slot.
        // Bail out on a broken model (one element claiming two constructors,
        // or one constructor split across two elements).
        let mut anchor: Vec<Option<usize>> = vec![None; elements.len()];
        let mut ctor_elem: Vec<Option<usize>> = vec![None; k];
        let mut term_elem: HashMap<TermId, usize> = HashMap::default();
        for (&tid, val) in &euf.term_values {
            if !matches!(self.ctx.terms.sort(tid), Sort::Uninterpreted(s) if s == sort_name) {
                continue;
            }
            let Some(&ei) = elem_index.get(val.as_str()) else {
                continue;
            };
            term_elem.insert(tid, ei);
            let ctor_name = match self.ctx.terms.get(tid) {
                TermData::Var(name, _) => Some(name.as_str()),
                TermData::App(sym, args) if args.is_empty() => Some(sym.name()),
                _ => None,
            };
            let Some(&color) = ctor_name.and_then(|n| ctor_color.get(n)) else {
                continue;
            };
            if anchor[ei].is_some_and(|prev| prev != color)
                || ctor_elem[color].is_some_and(|prev| prev != ei)
            {
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    eprintln!("c phase-trace enum-model-repair-abort reason=anchor-conflict");
                }
                return;
            }
            anchor[ei] = Some(color);
            ctor_elem[color] = Some(ei);
        }

        // Forced-distinct edges between elements, from (dis)equality atoms
        // over the sort that the model commits to: a top-level `(not (= a b))`
        // / `(distinct ..)` assertion, or a nested atom the SAT model assigns.
        // (At finalize time `ctx.assertions` may include the DT axioms — all
        // datatype tautologies, so honoring their commitments is sound.)
        let mut top_true: HashSet<TermId> = HashSet::default();
        let mut top_false: HashSet<TermId> = HashSet::default();
        for &root in &self.ctx.assertions {
            match self.ctx.terms.get(root) {
                TermData::Not(inner) => {
                    top_false.insert(*inner);
                }
                _ => {
                    top_true.insert(root);
                }
            }
        }
        let mut edges: HashSet<(usize, usize)> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            match self.ctx.terms.get(tid) {
                TermData::App(sym, args) => {
                    let is_eq = sym.name() == "=" && args.len() == 2;
                    let is_distinct = sym.name() == "distinct" && args.len() >= 2;
                    if (is_eq || is_distinct)
                        && args.iter().all(|&a| {
                            matches!(self.ctx.terms.sort(a),
                                Sort::Uninterpreted(s) if s == sort_name)
                        })
                    {
                        let committed = if top_true.contains(&tid) {
                            Some(true)
                        } else if top_false.contains(&tid) {
                            Some(false)
                        } else {
                            self.term_value(&model.sat_model, &model.term_to_var, tid)
                        };
                        let forced_distinct = committed == Some(!is_eq);
                        if forced_distinct {
                            for (i, &a) in args.iter().enumerate() {
                                for &b in &args[i + 1..] {
                                    if let (Some(&ea), Some(&eb)) =
                                        (term_elem.get(&a), term_elem.get(&b))
                                    {
                                        if ea != eb {
                                            edges.insert((ea.min(eb), ea.max(eb)));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }

        // Greedy k-coloring: anchored elements keep their constructor slot;
        // each remaining element takes the smallest slot no forced-distinct
        // neighbor holds. Failure (all k slots blocked) => keep the degrade.
        let mut color: Vec<Option<usize>> = anchor.clone();
        for ei in 0..elements.len() {
            if color[ei].is_some() {
                continue;
            }
            // A SINGLE-INHABITANT enum (k == 1) has exactly one slot: every
            // element MUST denote the sole nullary constructor. A forced-distinct
            // edge over such a sort is UNSATISFIABLE — no real model has two
            // distinct values of a 1-inhabitant sort — so the committed model is
            // a non-model, and the only enum-valid candidate is "collapse
            // everything onto slot 0". Produce it (the repair is strictly
            // candidate-producing) and let the full assertion-level validation
            // decide: a genuine committed disequality then makes its `(not (= a
            // b))` / `(distinct ..)` assertion evaluate FALSE and degrades the
            // SAT to Unknown — never a wrong SAT. Without this, a spurious
            // don't-care disequality between two over-populated reps (the
            // eager-DT selector-congruence artifact, e.g. `excl`'s `PhantomData`)
            // blocks the k == 1 coloring and defeats the cardinality collapse,
            // fixpointing iterative deepening on the degrade.
            if k == 1 {
                color[ei] = Some(0);
                continue;
            }
            let mut blocked = vec![false; k];
            for &(a, b) in &edges {
                let other = if a == ei {
                    b
                } else if b == ei {
                    a
                } else {
                    continue;
                };
                if let Some(c) = color[other] {
                    blocked[c] = true;
                }
            }
            match (0..k).find(|&c| !blocked[c]) {
                Some(c) => color[ei] = Some(c),
                None => {
                    if std::env::var_os("AY_PHASE_TRACE").is_some() {
                        eprintln!(
                            "c phase-trace enum-model-repair-abort reason=coloring elem={}",
                            elements[ei]
                        );
                    }
                    return;
                }
            }
        }

        // Canonical element per slot: the anchored element if the constructor
        // occurs in the model, else the first element assigned the slot. All
        // other same-slot elements are renamed onto the canonical one.
        //
        // For a SINGLE-CONSTRUCTOR enum (`k == 1`) slot 0 is unambiguously that
        // sole constructor, so canonicalize onto the CONSTRUCTOR NAME itself, not
        // the `@Sort!n` rep the over-populated model happened to assign (even
        // when a constructor constant was anchored to a rep). An all-nullary enum
        // value IS its constructor, and representing it by the constructor name
        // keeps the datatype tautologies the strict definitive-false oracle
        // checks — `is-C(m)` iff `(C = m)` — mutually consistent: `is-C` is
        // recomputed from the coloring (true), and `(C = m)` compares constructor
        // NAMES, so both agree only when `m` denotes the name `C`. Collapsing
        // onto a fresh rep instead leaves `is-C` true while `(C = m)` is false,
        // which the oracle rejects (the residual `excl` PhantomData degrade).
        // Confined to `k == 1` so the `k > 1` blocksworld canonicalization is
        // byte-identical.
        let mut canon: Vec<Option<&str>> = (0..k)
            .map(|c| {
                if k == 1 {
                    Some(ctors[0].as_str())
                } else {
                    ctor_elem[c].map(|ei| elements[ei].as_str())
                }
            })
            .collect();
        let mut remap: HashMap<String, String> = HashMap::default();
        for (ei, elem) in elements.iter().enumerate() {
            let c = color[ei].expect("every element colored above");
            match canon[c] {
                None => canon[c] = Some(elem.as_str()),
                Some(target) if target != elem.as_str() => {
                    remap.insert(elem.clone(), target.to_string());
                }
                Some(_) => {}
            }
        }
        // len > k pigeonholes at least one merge.
        debug_assert!(!remap.is_empty());
        let mapped = |s: &str| -> String { remap.get(s).cloned().unwrap_or_else(|| s.to_string()) };

        // Functional-consistency check BEFORE committing: the merge must not
        // make two same-symbol applications argument-equal with different
        // results, or the "model" would no longer be a well-defined structure
        // (assertion-level validation cannot see that defect, so it is checked
        // here and any violation keeps the degrade). The sort's own TESTER
        // tables are exempt: a tester's semantics are fixed by the datatype
        // (`is-Ci(e)` is true iff `e` denotes `Ci`), its extracted rows merely
        // echo don't-care SAT assignments, and the commit below RECOMPUTES
        // every row from the final coloring — so a pre-remap row conflict there
        // is repaired, not a defect.
        //
        // The solver-internal DT acyclicity DEPTH instrumentation
        // (`__ay_dt_depth_<dt>`, injected by `dt_axioms/acyclicity.rs`) is
        // likewise exempt: its semantics are fixed (the well-founded depth of a
        // datatype element), and for an all-nullary ENUM sort — the only sorts
        // this repair touches — every element denotes one of the `k` nullary
        // constructors, whose depth is a fixed constant, so a post-merge row
        // conflict there is a don't-care artifact of the over-populated model,
        // not a genuine functional defect. The commit's per-arg dedup below
        // keeps the table functional regardless, and the full assertion-level
        // validation (which re-evaluates the depth/acyclicity axioms) still
        // decides acceptance — so a bad merge degrades to Unknown, never a wrong
        // SAT. Without this exemption the depth table's stale per-`@Even!n` rows
        // (distinct Int depths the SAT solver left as don't-cares) spuriously
        // abort the repair, defeating the enum-cardinality collapse and
        // fixpointing iterative deepening on the degrade (mutex, excl).
        // A CONSTRUCTOR table over a SINGLE-INHABITANT enum (`k == 1`) is also
        // exempt: the sole inhabitant forces every application of an injective
        // constructor to the collapsed value, so a pre-merge row conflict there
        // is another don't-care fragment of the over-populated model (`excl`'s
        // `Resource` wrapping `PhantomData`). The commit's per-arg dedup keeps
        // the table functional and the full validation still decides, so this is
        // candidate-only. Kept to `k == 1` so the `k > 1` blocksworld coloring
        // (where a genuine constructor conflict is a real signal) is unchanged.
        let tester_names: HashSet<String> = ctors.iter().map(|c| format!("is-{c}")).collect();
        for (fn_name, table) in euf.function_tables.iter() {
            if tester_names.contains(fn_name)
                || fn_name.starts_with("__ay_dt_depth_")
                || (k == 1 && self.ctx.is_constructor(fn_name).is_some())
            {
                continue;
            }
            let mut seen_rows: HashMap<Vec<String>, String> = HashMap::default();
            for (args, result) in table {
                let margs: Vec<String> = args.iter().map(|a| mapped(a)).collect();
                let mres = mapped(result);
                match seen_rows.get(&margs) {
                    Some(prev) if *prev != mres => {
                        if std::env::var_os("AY_PHASE_TRACE").is_some() {
                            eprintln!(
                                "c phase-trace enum-model-repair-abort \
                                 reason=fn-consistency fn={fn_name}"
                            );
                        }
                        return;
                    }
                    Some(_) => {}
                    None => {
                        seen_rows.insert(margs, mres);
                    }
                }
            }
        }

        // Commit: rewrite term values, the sort's element list, UF tables and
        // completed Element values; then invalidate the eval memo (#eval-memo).
        let merged = remap.len();
        let Some(euf) = model.euf_model.as_mut() else {
            return;
        };
        for val in euf.term_values.values_mut() {
            if let Some(target) = remap.get(val) {
                *val = target.clone();
            }
        }
        if let Some(elems) = euf.sort_elements.get_mut(sort_name) {
            elems.retain(|e| !remap.contains_key(e));
            // A canonical slot element may be a constructor NAME that was never
            // an extracted `@Sort!n` rep (the single-constructor canonicalization
            // above): make sure the sort's surviving inhabitant is listed, so the
            // element set stays consistent with the remapped term values.
            for name in canon.iter().flatten() {
                if !elems.iter().any(|e| e == name) {
                    elems.push((*name).to_string());
                }
            }
        }
        for table in euf.function_tables.values_mut() {
            for (args, result) in table.iter_mut() {
                for a in args.iter_mut() {
                    if let Some(target) = remap.get(a) {
                        *a = target.clone();
                    }
                }
                if let Some(target) = remap.get(result) {
                    *result = target.clone();
                }
            }
            // Rows made identical by the merge collapse to one.
            let mut dedup_seen: HashSet<Vec<String>> = HashSet::default();
            table.retain(|(args, _)| dedup_seen.insert(args.clone()));
        }
        // Recompute the sort's tester tables from the final coloring: slot `c`
        // denotes constructor `ctors[c]`, so `is-Ci(e)` is true exactly when
        // `e` is the canonical element of slot `i`. Rows whose arg is not one
        // of the sort's elements (unresolved `@?id` placeholders) are left as
        // extracted.
        let canon_color: HashMap<&str, usize> = canon
            .iter()
            .enumerate()
            .filter_map(|(c, e)| e.map(|name| (name, c)))
            .collect();
        for (i, ctor) in ctors.iter().enumerate() {
            let Some(table) = euf.function_tables.get_mut(&format!("is-{ctor}")) else {
                continue;
            };
            for (args, result) in table.iter_mut() {
                if let [arg] = args.as_slice() {
                    if let Some(&c) = canon_color.get(arg.as_str()) {
                        *result = if c == i { "true" } else { "false" }.to_string();
                    }
                }
            }
        }
        for value in model.completed_values.values_mut() {
            if let EvalValue::Element(name) = value {
                if let Some(target) = remap.get(name) {
                    *name = target.clone();
                }
            }
        }
        super::eval_memo_clear();
        self.last_statistics
            .set_int("model_completion.enum_repair_merged", merged as u64);
        if std::env::var_os("AY_PHASE_TRACE").is_some() {
            eprintln!("c phase-trace enum-model-repair sort={sort_name} merged={merged} k={k}");
        }
        tracing::debug!(
            sort = sort_name,
            merged,
            k,
            "model repair: merged surplus enum elements onto constructor slots"
        );
    }

    /// Complete absent Int/Real atoms that are constrained by ground assertions.
    ///
    /// This is deliberately only a candidate generator. It never overwrites an
    /// existing model value, never changes `last_result`, and any filled values
    /// are still checked by the normal full-model validation pipeline.
    fn resolve_ground_constrained_absent_atoms(&mut self, model: &mut Model) -> usize {
        if !matches!(self.last_result, Some(SolveResult::Sat))
            || !(model.lia_model.is_some() || model.lra_model.is_some())
        {
            return 0;
        }

        let targets = self.collect_ground_constrained_absent_atoms(model);
        if targets.is_empty() {
            return 0;
        }
        self.last_statistics.set_int(
            "model_completion.ground_resolve_targets",
            targets.len() as u64,
        );

        let target_set: HashSet<TermId> = targets.iter().copied().collect();
        let residual: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| self.assertion_mentions_any(a, &target_set))
            .collect();
        if residual.is_empty() {
            return 0;
        }

        let mut atoms = HashSet::default();
        for &assertion in &residual {
            Self::collect_model_completion_atoms(&self.ctx.terms, assertion, &mut atoms);
        }
        let mut ordered_atoms: Vec<TermId> = atoms.into_iter().collect();
        ordered_atoms.sort_by_key(|t| t.index());

        let mut freezes = Vec::new();
        for atom in ordered_atoms {
            if target_set.contains(&atom) {
                continue;
            }
            let value = self.evaluate_term(model, atom);
            let Some(freeze) = self.freeze_atom_to_value(atom, &value) else {
                continue;
            };
            freezes.push(freeze);
        }

        let mut sub = Executor::new();
        sub.ctx = self.ctx.clone();
        sub.ctx.assertions = residual;
        sub.ctx.assertions.extend(freezes);
        sub.final_lia_resolve_disabled = true;
        sub.set_deadline(Some(Instant::now() + Duration::from_millis(150)));

        if !matches!(sub.check_sat(), Ok(result) if result.is_sat()) {
            return 0;
        }
        let Some(sub_model) = sub.last_model.as_ref() else {
            return 0;
        };

        let snapshot = model.clone();
        let mut filled = 0usize;
        for &target in &targets {
            if !matches!(self.evaluate_term(model, target), EvalValue::Unknown) {
                continue;
            }
            let value = sub.evaluate_term(sub_model, target);
            if !matches!(value, EvalValue::Rational(_)) {
                continue;
            }
            if Self::insert_completed_value(&self.ctx.terms, model, target, &value) {
                filled += 1;
            }
        }

        if filled == 0 {
            return 0;
        }
        if !self.completed_gap_model_accepted(model) {
            *model = snapshot;
            super::eval_memo_clear();
            return 0;
        }

        self.last_statistics
            .set_int("model_completion.ground_resolved", filled as u64);
        filled
    }

    fn collect_ground_constrained_absent_atoms(&self, model: &Model) -> Vec<TermId> {
        let mut seen = HashSet::default();
        let mut atoms = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            if Self::is_absent_arithmetic_completion_atom(&self.ctx.terms, tid)
                && matches!(self.evaluate_term(model, tid), EvalValue::Unknown)
            {
                atoms.insert(tid);
            }
            match self.ctx.terms.get(tid) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                // Skip quantifier and let bodies: this phase only reasons about
                // ground top-level assertions, matching the existing completion
                // collectors' defensive treatment of binders.
                _ => {}
            }
        }
        let mut ordered: Vec<TermId> = atoms.into_iter().collect();
        ordered.sort_by_key(|t| t.index());
        ordered
    }

    fn assertion_mentions_any(&self, root: TermId, targets: &HashSet<TermId>) -> bool {
        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(tid) = stack.pop() {
            if targets.contains(&tid) {
                return true;
            }
            if !seen.insert(tid) {
                continue;
            }
            match self.ctx.terms.get(tid) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
                _ => {}
            }
        }
        false
    }

    fn collect_model_completion_atoms(
        terms: &ay_core::TermStore,
        root: TermId,
        atoms: &mut HashSet<TermId>,
    ) {
        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            if Self::is_model_completion_atom(terms, tid) {
                atoms.insert(tid);
            }
            match terms.get(tid) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
                _ => {}
            }
        }
    }

    fn is_absent_arithmetic_completion_atom(terms: &ay_core::TermStore, term: TermId) -> bool {
        matches!(terms.sort(term), Sort::Int | Sort::Real)
            && Self::is_model_completion_atom(terms, term)
    }

    fn is_model_completion_atom(terms: &ay_core::TermStore, term: TermId) -> bool {
        match terms.sort(term) {
            Sort::Bool => match terms.get(term) {
                TermData::Var(_, _) => true,
                TermData::App(sym, _) => {
                    !matches!(sym, Symbol::Named(name) if Self::is_logical_connective(name))
                }
                _ => false,
            },
            Sort::Int | Sort::Real => match terms.get(term) {
                TermData::Var(_, _) => true,
                TermData::App(sym, _) => {
                    !matches!(sym, Symbol::Named(name) if Self::is_arithmetic_builtin(name))
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn is_logical_connective(name: &str) -> bool {
        matches!(name, "and" | "or" | "xor" | "=>" | "not" | "ite")
    }

    fn is_arithmetic_builtin(name: &str) -> bool {
        matches!(
            name,
            "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int" | "ite"
        )
    }

    fn freeze_atom_to_value(&mut self, atom: TermId, value: &EvalValue) -> Option<TermId> {
        match (self.ctx.terms.sort(atom).clone(), value) {
            (Sort::Bool, EvalValue::Bool(true)) => Some(atom),
            (Sort::Bool, EvalValue::Bool(false)) => Some(self.ctx.terms.mk_not(atom)),
            (Sort::Int, EvalValue::Rational(r)) if r.is_integer() => {
                let c = self.ctx.terms.mk_int(r.numer().clone());
                Some(self.ctx.terms.mk_eq(atom, c))
            }
            (Sort::Real, EvalValue::Rational(r)) => {
                let c = self.ctx.terms.mk_rational(r.clone());
                Some(self.ctx.terms.mk_eq(atom, c))
            }
            _ => None,
        }
    }

    /// Insert a completed value into the model slot matching the variable's
    /// sort: the sort's theory sub-model when one is present, else the
    /// dedicated completion slot (`Model::completed_values`), which
    /// `evaluate_var` consults strictly as the last resort. Returns `false`
    /// when the value's shape does not match the sort (never inserted).
    ///
    /// The completion slot exists so a completed value NEVER requires creating
    /// an absent theory sub-model: materializing e.g. an empty `bv_model` would
    /// flip `evaluate_var`'s missing-entry semantics for every OTHER variable
    /// of that theory (#no-fabricated-model-values).
    fn insert_completed_value(
        terms: &ay_core::TermStore,
        model: &mut Model,
        var: TermId,
        value: &EvalValue,
    ) -> bool {
        // Any model mutation invalidates the `evaluate_term` result memo so no
        // cached value outlives its model state (#eval-memo).
        super::eval_memo_clear();
        match (terms.sort(var), value) {
            (Sort::Bool, EvalValue::Bool(b)) => {
                model.bool_overrides.insert(var, *b);
                true
            }
            (Sort::Int, EvalValue::Rational(r)) if r.is_integer() => {
                if let Some(ref mut lia) = model.lia_model {
                    tracing::debug!(
                        var = ?terms.get(var),
                        old = ?lia.values.get(&var),
                        new = %r.numer(),
                        "model completion: inserting Int value"
                    );
                    lia.values.insert(var, r.numer().clone());
                    return true;
                }
                if let Some(ref mut lra) = model.lra_model {
                    lra.values.insert(var, r.clone());
                    return true;
                }
                model.completed_values.insert(var, value.clone());
                true
            }
            (Sort::Real, EvalValue::Rational(r)) => {
                if let Some(ref mut lra) = model.lra_model {
                    lra.values.insert(var, r.clone());
                    return true;
                }
                model.completed_values.insert(var, value.clone());
                true
            }
            (Sort::BitVec(w), EvalValue::BitVec { value: bits, width }) if *width == w.width => {
                if let Some(ref mut bv) = model.bv_model {
                    bv.values.insert(var, bits.clone());
                    return true;
                }
                model.completed_values.insert(var, value.clone());
                true
            }
            // Sorts with no writable theory sub-model slot: String / Seq / FP /
            // RegLan / uninterpreted elements go to the completion slot (read
            // by `evaluate_var` only after every theory lookup missed).
            (Sort::String, EvalValue::String(_))
            | (Sort::Seq(_), EvalValue::Seq(_))
            | (Sort::RegLan, EvalValue::Element(_))
            | (Sort::Uninterpreted(_), EvalValue::Element(_)) => {
                model.completed_values.insert(var, value.clone());
                true
            }
            (Sort::FloatingPoint(eb, sb), EvalValue::Fp(fp))
                if fp.eb() == *eb && fp.sb() == *sb =>
            {
                model.completed_values.insert(var, value.clone());
                true
            }
            _ => false,
        }
    }

    /// Default every DECLARED constant that occurs in no assertion (and no
    /// `check_sat_assuming` assumption), is not a substitution key, and has no
    /// value anywhere in `last_model`. Such a constant is UNCONSTRAINED by the
    /// formula — any value is a valid witness — so assigning its canonical
    /// sort default is legitimate model completion, and doing it in the MODEL
    /// (before the outer validation gates run) means the printers only ever
    /// read values that EXIST in the gate-checked model
    /// (#no-fabricated-model-values). Constants that DO occur in assertions
    /// are never touched: their values must come from the theory models /
    /// substitution replay, and a missing value surfaces honestly (validation
    /// gap or print-time error), never as a fabricated default.
    ///
    /// MUST be called at the OUTER check-sat level only, where
    /// `ctx.assertions` is the original assertion set (inner theory dispatch
    /// temporarily swaps/lowers it, making "occurs in no assertion" false
    /// evidence there — a seq definitional equality `(= q (seq.unit 3))`
    /// substituted away during the inner solve must not get `q` defaulted to
    /// the empty sequence). Fill-only and idempotent.
    ///
    /// A declared constant that DOES occur in an assertion but still has no
    /// value (a solver model gap — e.g. the QF_AX `(= (select a i) v)` shape,
    /// where `i`/`v` live only in the array constraint) is completed as a
    /// GATE-VERIFIED CANDIDATE by [`Self::complete_constrained_gaps`]: derive
    /// from asserted equalities / bounds where possible, default otherwise,
    /// then re-check the completed model with the strict oracles and the
    /// independent gate — if either refutes it, the candidates are RETRACTED
    /// (the model returns to its pre-candidate state) so a bad guess can
    /// neither print nor influence the verdict. The former print-time
    /// fabricator "completed" these same variables silently, unvalidated, at
    /// print time (#no-fabricated-model-values).
    pub(in crate::executor) fn complete_unconstrained_constants_for_output(
        &mut self,
        extra_roots: &[TermId],
    ) {
        let Some(mut model) = self.last_model.take() else {
            return;
        };
        if model
            .euf_model
            .as_ref()
            .is_some_and(|euf| !euf.function_table_conflicts.is_empty())
        {
            // Cross-theory model merging can make formerly-distinct UF rows
            // collide at one final arithmetic argument point.  Atomic result
            // sorts are normalized in the combiner.  A contradictory hard pin
            // or a compound result that cannot be represented faithfully is
            // marked explicitly instead.  Such a candidate is not a model of
            // one mathematical function: discard it before validation rather
            // than allowing TermId-keyed fallbacks to interpret each congruent
            // application independently.
            self.last_statistics
                .set_int("model_validation.uf_table_conflict", 1);
            self.last_model_validated = false;
            self.last_unknown_reason = Some(crate::executor_types::UnknownReason::Incomplete);
            if std::env::var_os("AY_F1_DIAG").is_some() {
                if let Some(euf) = model.euf_model.as_ref() {
                    eprintln!(
                        "AY_F1_DIAG: model discarded on function_table_conflicts={:?} \
                         uflia_lane={}",
                        euf.function_table_conflicts, self.uflia_congruence_lane
                    );
                }
            }
            // #uflia-cong-repair-arm: a conflicted UF function table on the
            // UFLIA lane is the SAME evidence class as an independent-gate
            // function-graph refutation (two congruent applications pinned to
            // different values by cross-theory merging) — but this discard runs
            // BEFORE the gate, so without arming here the model never reaches
            // the gate site that would trigger the reactive congruence-repair
            // re-solve (`check_sat_guarded`), and a genuine SAT dies as a final
            // "No model available" Unknown (mathsat Hash hash_sat_07_05).
            // Scoped to the UFLIA lane exactly like the gate site; the verdict
            // here still degrades (the conflicted model is discarded, never
            // shipped), and the armed re-solve routes through the full
            // strict/independent/authoritative gate funnel — so this can only
            // recover a validated SAT, never mint an unvalidated one.
            if self.uflia_congruence_lane {
                self.uflia_congruence_gate_rejected = true;
                // #uflia-model-repair (env-gated): this discard previously
                // ERASED the evidence a targeted repair needs (relevancy
                // design §7) — the model is dropped here, before the gate
                // that would have named a falsified assertion. Preserve the
                // conflicted table names for the §3.2 repair re-solve (the
                // candidate model itself was snapshotted in
                // `check_sat_guarded` before this funnel ran). Verdict flow
                // is byte-identical: the conflicted model is still discarded,
                // never shipped.
                if super::super::uflia_model_repair::uflia_model_repair_enabled() {
                    if let Some(euf) = model.euf_model.as_ref() {
                        self.uflia_repair_conflict_tables =
                            euf.function_table_conflicts.iter().cloned().collect();
                        self.uflia_repair_conflict_tables.sort_unstable();
                    }
                }
            }
            return;
        }
        let occurring = self.collect_occurring_vars(extra_roots);
        let substituted: HashSet<TermId> =
            self.recorded_var_substitutions.keys().copied().collect();
        let mut candidates: Vec<TermId> = self
            .ctx
            .symbol_iter()
            .filter(|(name, info)| {
                info.arg_sorts.is_empty()
                    && info.term.is_some()
                    && !self.is_dt_internal_symbol(name)
            })
            .filter_map(|(_, info)| info.term)
            .collect();
        // Deterministic order for reproducible completion.
        candidates.sort_by_key(|t| t.index());
        candidates.dedup();

        let mut filled = 0usize;
        let mut gap_vars: Vec<TermId> = Vec::new();
        for var in candidates {
            if !matches!(self.evaluate_term(&model, var), EvalValue::Unknown) {
                continue;
            }
            if occurring.contains(&var) || substituted.contains(&var) {
                // Constrained but unpinned (occurs in an assertion, or is a
                // substitution key whose phase-2 recovery failed): a solver
                // model gap, handled by the gate-verified candidate pass below.
                gap_vars.push(var);
                continue;
            }
            let Some(default) = self.unconstrained_default_value(self.ctx.terms.sort(var)) else {
                continue;
            };
            if Self::insert_completed_value(&self.ctx.terms, &mut model, var, &default) {
                filled += 1;
            }
        }
        if filled > 0 {
            tracing::debug!(
                filled,
                "model completion: defaulted unconstrained declared constants"
            );
            self.last_statistics
                .set_int("model_completion.unconstrained", filled as u64);
        }

        // Unlike the unconstrained defaults above, these variables occur in an
        // assertion/assumption or substitution definition. Candidate completion
        // can therefore change the validated formula's witness. Invalidate old
        // evidence before the first candidate mutation; emit_sat_verdict will run
        // canonical validation over assertions + assumption roots afterward.
        if !gap_vars.is_empty() {
            self.last_model_validated = false;
        }
        let filled_gaps = self.complete_constrained_gaps(&mut model, &gap_vars);
        if filled_gaps > 0 {
            self.last_statistics
                .set_int("model_completion.constrained_gaps", filled_gaps as u64);
        }

        let repaired_defaults = self.complete_opaque_array_default_disequalities(&mut model);
        if repaired_defaults > 0 {
            self.last_model_validated = false;
            self.last_statistics.set_int(
                "model_completion.opaque_array_defaults",
                repaired_defaults as u64,
            );
        }

        // Array completion used to run only from the full validation path.
        // An in-loop validated SAT takes the outer fast path, however, so a
        // declared free array could reach the printer with no committed
        // interpretation.  Finalize arrays here as part of the same outer
        // witness sweep that handles scalar declarations.  Any semantic
        // mutation revokes evidence for the predecessor model; `emit_sat_verdict`
        // will validate the exact completed witness before minting a certificate.
        let (arrays_completed, arrays_changed) =
            self.complete_array_models_for_validation(&mut model, extra_roots);
        if arrays_completed > 0 {
            self.last_statistics
                .set_int("model_completion.arrays_completed", arrays_completed as u64);
        }
        if arrays_changed {
            self.last_model_validated = false;
        }
        self.last_model = Some(model);
    }

    /// Repair an opaque `(default a)` scalar whose extracted value directly
    /// violates authored ground disequalities.
    ///
    /// Dependent-lambda and `as-array` defaults are independent scalar values in
    /// Z3's observable model semantics.  The combined EUF/arithmetic extractor
    /// can nevertheless leave their application class at a stale canonical
    /// value (usually zero), even when SAT chose the disequality atoms true.
    /// Try deterministic scalar alternatives and retain one only through the
    /// same strict + independent gate check used by other constrained-gap
    /// completion.  This is recovery-only: a default whose current value does
    /// not falsify a direct disequality is untouched, and every rejected trial
    /// is rolled back.
    fn complete_opaque_array_default_disequalities(&mut self, model: &mut Model) -> usize {
        let mut defaults = Vec::new();
        for term in self.ctx.terms.term_ids() {
            let Some(array) = self.ctx.terms.get_array_default(term) else {
                continue;
            };
            if self.ctx.terms.get_lambda_array(array).is_some()
                || self.ctx.terms.get_as_array_func(array).is_some()
            {
                defaults.push(term);
            }
        }
        defaults.sort_by_key(|term| term.index());

        let assertions = self.flatten_assertion_conjunctions();
        let mut repaired = 0;
        for default_term in defaults {
            let mut forbidden = Vec::new();
            for &assertion in &assertions {
                let args: Option<Vec<TermId>> = match self.ctx.terms.get(assertion) {
                    TermData::Not(inner) => match self.ctx.terms.get(*inner) {
                        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                            Some(args.clone())
                        }
                        _ => None,
                    },
                    TermData::App(sym, args) if sym.name() == "distinct" && args.len() >= 2 => {
                        Some(args.clone())
                    }
                    _ => None,
                };
                let Some(args) = args else {
                    continue;
                };
                if !args.contains(&default_term) {
                    continue;
                }
                for other in args.into_iter().filter(|&arg| arg != default_term) {
                    if let EvalValue::Rational(value) = self.evaluate_term(model, other) {
                        forbidden.push(value);
                    }
                }
            }
            if forbidden.is_empty() {
                continue;
            }
            let EvalValue::Rational(current) =
                self.evaluate_symbolic_array_default_scalar(model, default_term)
            else {
                continue;
            };
            if !forbidden.iter().any(|value| value == &current) {
                continue;
            }

            let sort = self.ctx.terms.sort(default_term).clone();
            if !matches!(sort, Sort::Int | Sort::Real) {
                continue;
            }
            let mut candidates = Vec::new();
            if matches!(sort, Sort::Int) {
                if let Some(bound) = self.extract_int_from_assertion_bounds(default_term) {
                    candidates.push(BigRational::from(bound));
                }
            } else if let Some(bound) = self.extract_real_from_assertion_bounds(default_term) {
                candidates.push(bound);
            }
            let radius = forbidden.len().saturating_add(2).min(64);
            for n in 0..=radius {
                candidates.push(BigRational::from_integer(BigInt::from(n)));
                if n != 0 {
                    candidates.push(BigRational::from_integer(BigInt::from(-(n as i64))));
                }
            }
            candidates.retain(|value| !forbidden.iter().any(|blocked| blocked == value));
            candidates.dedup();

            let before = model.clone();
            let mut accepted = false;
            for candidate in candidates {
                *model = before.clone();
                let value = EvalValue::Rational(candidate);
                if !Self::insert_completed_value(&self.ctx.terms, model, default_term, &value) {
                    continue;
                }
                if self.completed_gap_model_accepted(model) {
                    accepted = true;
                    repaired += 1;
                    break;
                }
            }
            if !accepted {
                *model = before;
                super::eval_memo_clear();
            }
        }
        repaired
    }

    /// Run opaque array-default completion on the current candidate model
    /// before either SAT-validation entry reaches its strict gate.
    ///
    /// Both validation funnels can be entered before output completion, so the
    /// output-only hook above is too late to prevent a stale extracted default
    /// from degrading a valid SAT result.  The underlying completion remains
    /// snapshot-and-retract and gate-verified; this wrapper only installs the
    /// accepted candidate early enough for the unchanged validation pipeline
    /// to inspect it.
    pub(in crate::executor) fn complete_opaque_array_defaults_gate_verified(&mut self) {
        let Some(mut model) = self.last_model.take() else {
            return;
        };
        let repaired = self.complete_opaque_array_default_disequalities(&mut model);
        if repaired > 0 {
            self.last_model_validated = false;
            self.last_statistics
                .set_int("model_completion.opaque_array_defaults", repaired as u64);
        }
        self.last_model = Some(model);
    }

    /// Gate-verified, retracting completion of String-sorted GAP variables, run
    /// from the IN-LOOP validation entry [`Self::finalize_sat_model_validation`]
    /// (the strings solver validates there and downgrades BEFORE the outer
    /// `emit_sat_verdict` sweep, so the constrained-gap pass would otherwise
    /// never see a string model).
    ///
    /// A `(str.len x) = N`-pinned string variable, and the substr/concat
    /// reduction SKOLEMS bridged to it (`(= (str.substr x 0 3) sk_res)`,
    /// `x = sk_pre ++ skt ++ sk_suf`), print as the default `""` — whose length
    /// 0 violates the proxy and whose absent value makes the reduced bridge
    /// equalities unevaluable, degrading a genuine SAT to Unknown. This collects
    /// those String-sorted vars (user vars AND reduction skolems reachable from
    /// the reduced assertions) that still evaluate to `Unknown`, and completes
    /// them through [`Self::complete_constrained_gaps`] — the SAME snapshot-and-
    /// RETRACT pass the outer sweep uses. Every candidate is re-checked by the
    /// strict oracles + independent gate; ANY refutation retracts the whole
    /// completion, so this can only turn a today-Unknown string model into a
    /// GATE-VALIDATED SAT — never a wrong SAT and never a sat→unknown
    /// regression (a refuted completion restores the pre-completion model and
    /// the pipeline proceeds exactly as before).
    ///
    /// Scoped to OUTER solves (`pivot_enum_depth == 0`): inner pivot-enum solves
    /// run against a swapped, lowered assertion set where "occurs in the
    /// assertions" is not reliable (#inner-assertion-swap); the outer solve
    /// re-validates every accepted candidate anyway.
    pub(in crate::executor) fn complete_string_gaps_gate_verified(&mut self) {
        if self.pivot_enum_depth > 0 {
            return;
        }
        let Some(mut model) = self.last_model.take() else {
            return;
        };
        // Cheap early-out for non-string problems: no string theory model means
        // no string variable can have been left unpinned by string reduction.
        if model.string_model.is_none() {
            self.last_model = Some(model);
            return;
        }
        let mut gap_vars: Vec<TermId> = self
            .collect_occurring_vars(&[])
            .into_iter()
            .filter(|&v| {
                matches!(self.ctx.terms.get(v), TermData::Var(..))
                    && matches!(self.ctx.terms.sort(v), Sort::String)
                    && matches!(self.evaluate_term(&model, v), EvalValue::Unknown)
            })
            .collect();
        if gap_vars.is_empty() {
            self.last_model = Some(model);
            return;
        }
        // Deterministic order (stable pad-char ordinals, reproducible completion).
        gap_vars.sort_by_key(|t| t.index());
        let filled = self.complete_constrained_gaps(&mut model, &gap_vars);
        if filled > 0 {
            // Mirror the gate-accepted String witnesses into the string model's
            // `values` map so the downstream string-witness materializer
            // (`materialize_string_witnesses`, which reads `string_model.values`
            // — NOT `completed_values`) and `(get-model)` read the SAME concrete
            // values the strict + independent gate just validated. Without this
            // the materializer independently re-pads a user string var (e.g.
            // `x = "aaa"`) that clashes with the substr/concat skolem values this
            // pass DERIVED from `x`, spuriously failing closed (#str-gap).
            // Fill-only (`or_insert`): a solver-assigned string value is never
            // overwritten.
            let string_fills: Vec<(TermId, String)> = gap_vars
                .iter()
                .filter_map(|&v| match model.completed_values.get(&v) {
                    Some(EvalValue::String(s)) => Some((v, s.clone())),
                    _ => None,
                })
                .collect();
            if let Some(sm) = model.string_model.as_mut() {
                for (v, s) in string_fills {
                    sm.values.entry(v).or_insert(s);
                }
            }
            self.last_statistics
                .set_int("model_completion.string_gaps", filled as u64);
        }
        self.last_model = Some(model);
    }

    /// Complete every DECLARED arity>0 FUNCTION that occurs in no assertion
    /// (and no `check_sat_assuming` assumption) with a canonical constant
    /// interpretation, so `(get-model)` prints its `define-fun` and
    /// `(get-value ((g ..)))` answers from it — Z3 parity for unconstrained
    /// functions (`(define-fun g ((x!0 S)) T <default>)`), and the function
    /// counterpart of [`Self::complete_unconstrained_constants_for_output`].
    ///
    /// A function that occurs in NO assertion is UNCONSTRAINED by the formula:
    /// any total interpretation is a valid witness, so the canonical constant
    /// body (the sort default) is legitimate model completion, not a fabricated
    /// value over a real constraint. The interpretation is stored as an EMPTY
    /// [`ay_euf::FunctionTable`] in `model.euf_model.function_tables`, exactly
    /// the shape the printers already treat as "constant else body"
    /// (`format_function_table` / `uf_unlisted_point_value` render it as
    /// `format_default_value(result_sort)`).
    ///
    /// ORDERING — runs AFTER the strict + independent model-validation gates,
    /// unlike the constant sweep which runs before them. The gates read
    /// `model.euf_model.is_some()` as EUF verification evidence (`euf_backed`
    /// in the validation pipeline), so materializing an otherwise-absent
    /// `euf_model` before validation would WEAKEN those gates. Because an
    /// unconstrained function appears in no assertion, it can never change any
    /// gate verdict, so completing it after the gates is verdict-neutral yet
    /// still lets the printers read a real interpretation
    /// (#no-fabricated-model-values). Fill-only: a function whose name occurs
    /// in an assertion (its table is owned by EUF model extraction) or that
    /// already has a table is left untouched. Idempotent.
    ///
    /// MUST be called at the OUTER check-sat level only (same rationale as the
    /// constant sweep): inner theory dispatch swaps/lowers `ctx.assertions`, so
    /// "occurs in no assertion" is not evidence of unconstrainedness there.
    pub(in crate::executor) fn complete_unconstrained_functions_for_output(
        &mut self,
        extra_roots: &[TermId],
    ) {
        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return;
        }
        let Some(mut model) = self.last_model.take() else {
            // Trivially-SAT (no theory model): the output paths build a fresh
            // `completed_default_model()`, which populates the same empty
            // function tables — nothing to complete here.
            return;
        };
        let occurring = self.collect_occurring_function_names(extra_roots);
        // A problem-DEFINED symbol (define-fun/-rec) is NOT unconstrained: its
        // interpretation is fixed by the problem text. Its applications are
        // macro-expanded at elaboration, so the name never occurs as an App
        // head — without this filter the sweep fabricated an empty table for
        // it, which the printer rendered as a WRONG constant body (e.g.
        // `min/max = 0.0` on QF_LRA blending/12.smt2) (#mv-defined-fun-emit).
        let mut names: Vec<String> = self
            .ctx
            .symbol_iter()
            .filter(|(name, info)| {
                !info.arg_sorts.is_empty()
                    && !self.is_dt_internal_symbol(name)
                    && !self.ctx.is_defined_fun(name)
            })
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();
        names.sort();
        names.dedup();

        let mut filled = 0usize;
        for name in names {
            if occurring.contains(&name) {
                // Occurs in an assertion — its table is owned by EUF model
                // extraction (the partially-constrained case). Never fabricate
                // over a real constraint.
                continue;
            }
            let euf_model = model.euf_model.get_or_insert_with(Default::default);
            // Fill-only: an existing table (constrained function) is authoritative.
            euf_model.function_tables.entry(name).or_default();
            filled += 1;
        }
        if filled > 0 {
            tracing::debug!(
                filled,
                "model completion: defaulted unconstrained declared functions"
            );
            self.last_statistics
                .set_int("model_completion.unconstrained_functions", filled as u64);
        }
        self.last_model = Some(model);
    }

    /// The set of function/UF names that appear as APPLICATION heads anywhere in
    /// the current (original) assertions and `extra_roots` — including
    /// quantifier bodies, triggers, let bindings. Used as the conservative
    /// "possibly constrained" set for the unconstrained-function sweep: a
    /// function applied anywhere in an assertion is never completed by that
    /// sweep (its interpretation must come from EUF model extraction).
    fn collect_occurring_function_names(&self, extra_roots: &[TermId]) -> HashSet<String> {
        let terms = &self.ctx.terms;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut names: HashSet<String> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        stack.extend_from_slice(extra_roots);
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            match terms.get(tid) {
                TermData::App(sym, args) => {
                    if !args.is_empty() {
                        names.insert(sym.name().to_string());
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, t)| *t));
                    stack.push(*body);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                _ => {}
            }
        }
        names
    }

    /// Gate-verified candidate completion for declared constants that occur in
    /// assertions but have no value in the model (see
    /// [`Self::complete_unconstrained_constants_for_output`]).
    ///
    /// Values are DERIVED where possible (asserted defining equalities, then
    /// assertion bounds), defaulted otherwise, in up to two dependency rounds
    /// (deriving `v` from `(= (select a i) v)` needs `i` pinned first). The
    /// completed model is then re-checked by `verify_model_strict` and the
    /// independent gate: any refutation RETRACTS every candidate, restoring
    /// the pre-candidate model, so a wrong guess can never ship — the sat
    /// verdict and the printed values behave exactly as if no candidate had
    /// been tried. Returns the number of committed candidate values.
    fn complete_constrained_gaps(&mut self, model: &mut Model, gap_vars: &[TermId]) -> usize {
        if gap_vars.is_empty() {
            return 0;
        }
        let snapshot = model.clone();

        // Try candidate strategies in order; keep the FIRST whose completed
        // model the strict oracles + independent gate accept. Every strategy is
        // gate-validated, so an accepted completion is a VALID witness (never a
        // wrong model). The SortDefault retry after the assertion-Derived one is
        // the #array-completion-order fix (seed 21453): the derived value can be
        // an assertion bound / equality that is NOT the binding constraint and
        // that FALSIFIES the formula under the rest of the (array) model. The
        // old single-attempt code retracted such a candidate and left the gap
        // var UNPINNED — then `(get-model)` re-derived that very refuted value at
        // print time and shipped an invalid witness. Retrying with the sort
        // default recovers the genuinely-sat query with a VALID completion (e.g.
        // `i2 = 0` where the derived `i2 = -2` was refuted) instead of a wrong
        // model or a needless Unknown.
        for strategy in [GapStrategy::Derived, GapStrategy::SortDefault] {
            *model = snapshot.clone();
            super::eval_memo_clear();
            let filled = self.fill_constrained_gap_vars(model, gap_vars, strategy);
            if filled == 0 {
                continue;
            }
            if self.completed_gap_model_accepted(model) {
                tracing::debug!(
                    candidates = filled,
                    strategy = ?strategy,
                    "model completion: constrained-gap candidates verified and committed"
                );
                return filled;
            }
            tracing::debug!(
                candidates = filled,
                strategy = ?strategy,
                "model completion: constrained-gap candidates refuted — trying next strategy"
            );
        }

        // W3: both all-or-nothing strategies were refuted. Retry per variable,
        // retracting only the variables the gates actually reject.
        //
        // COMPLETENESS REQUIREMENT (#w3-partial-completion): the result is
        // committed ONLY when every gap variable ended up filled. A PARTIAL
        // completion is strictly worse than none for the downstream consumers:
        // `complete_string_gaps_gate_verified` mirrors the accepted values into
        // `string_model.values`, and `materialize_string_witnesses` then
        // re-derives the REMAINING variables against those pinned values and
        // fails closed when they clash — turning a file that solved via the
        // untouched path into Unknown (observed on
        // `slent_kaluza_568_sink.smt2`). Requiring a total fill keeps the
        // increment purely additive: either the per-variable ordering found a
        // complete completion the all-or-nothing pass could not, or nothing
        // changes at all.
        if string_witness::str_witness_w3() {
            *model = snapshot.clone();
            super::eval_memo_clear();
            let filled = self.fill_gap_vars_per_variable(model, gap_vars);
            if filled == gap_vars.len() && self.completed_gap_model_accepted(model) {
                tracing::debug!(
                    candidates = filled,
                    "model completion: per-variable constrained-gap completion verified and committed"
                );
                return filled;
            }
        }

        *model = snapshot;
        super::eval_memo_clear();
        0
    }

    /// Fill each still-Unknown gap variable with a candidate value chosen by
    /// `strategy`, returning how many were filled. Fill-only: a variable that
    /// already resolves to a value is left untouched.
    fn fill_constrained_gap_vars(
        &self,
        model: &mut Model,
        gap_vars: &[TermId],
        strategy: GapStrategy,
    ) -> usize {
        let mut filled = 0usize;
        for _round in 0..2 {
            let mut progress = false;
            for (ord, &var) in gap_vars.iter().enumerate() {
                if !matches!(self.evaluate_term(model, var), EvalValue::Unknown) {
                    continue;
                }
                let sort = self.ctx.terms.sort(var).clone();
                let value = self.gap_candidate_value(model, var, ord, &sort, strategy);
                let Some(value) = value else {
                    continue;
                };
                if Self::insert_completed_value(&self.ctx.terms, model, var, &value) {
                    filled += 1;
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }
        filled
    }

    /// The candidate value `strategy` chooses for a single gap variable, or
    /// `None` when the strategy has nothing to offer for that sort.
    ///
    /// Extracted from [`Self::fill_constrained_gap_vars`] so the per-variable
    /// retract pass (W3) can reuse the EXACT same candidate derivation instead
    /// of duplicating it.
    fn gap_candidate_value(
        &self,
        model: &Model,
        var: TermId,
        ord: usize,
        sort: &Sort,
        strategy: GapStrategy,
    ) -> Option<EvalValue> {
        match strategy {
            // Derive from the recorded substitution RHS / the asserted
            // defining equality first, then from assertion bounds; only a
            // genuinely underdetermined variable falls back to the sort
            // default.
            GapStrategy::Derived => {
                let mut value = self
                    .recorded_var_substitutions
                    .get(&var)
                    .copied()
                    .map(|rhs| self.evaluate_term(model, rhs))
                    .filter(|v| !matches!(v, EvalValue::Unknown));
                if value.is_none() {
                    value = self
                        .extract_value_from_asserted_equalities(model, var)
                        .filter(|v| !matches!(v, EvalValue::Unknown));
                }
                if value.is_none() {
                    value = match *sort {
                        Sort::Int => self
                            .extract_int_from_assertion_bounds(var)
                            .map(|v| EvalValue::Rational(BigRational::from(v))),
                        Sort::Real => self
                            .extract_real_from_assertion_bounds(var)
                            .map(EvalValue::Rational),
                        // A Seq gap with `(seq.len s) = N` / `(seq.nth s i)`
                        // constraints: derive the witness those constraints
                        // pin (unconstrained cells complete to the element
                        // default), so the sequence value EXISTS in the
                        // gate-checked model instead of being reconstructed
                        // at print time (#no-fabricated-model-values).
                        Sort::Seq(_) => self
                            .reconstruct_seq_from_len_nth(model, var)
                            .filter(|v| !matches!(v, EvalValue::Unknown)),
                        // A String gap with `(str.len s) = N` and/or a
                        // SAT-true defining equality: derive the witness
                        // those constraints pin (from a defining equality
                        // first, else pad to the model length), exactly
                        // parallel to the Seq arm above. Without this the
                        // gap defaults to `""` (below), which VIOLATES any
                        // `(str.len s) = N > 0` and re-feeds to Unknown —
                        // the substr-equals-whole / length-pinned probes.
                        Sort::String => self
                            .reconstruct_string_from_len_or_equalities(model, var, ord)
                            .filter(|v| !matches!(v, EvalValue::Unknown)),
                        _ => None,
                    };
                }
                value.or_else(|| self.unconstrained_default_value(sort))
            }
            // Ignore the assertion-derived value entirely — a refuted
            // Derived attempt has already shown it falsifies the model —
            // and use the canonical sort default directly.
            GapStrategy::SortDefault => self.unconstrained_default_value(sort),
        }
    }

    /// W3 (default ON, `AY_STR_WITNESS=0` kill switch): PER-VARIABLE retracting
    /// completion, run only after BOTH all-or-nothing strategies were refuted.
    ///
    /// The pre-existing pass fills every gap variable, gate-checks ONCE, and on
    /// any refutation throws the WHOLE completion away — so a single bad
    /// variable discards the correct values derived for all the others and the
    /// model degrades to Unknown. This commits variables one at a time and
    /// gate-checks after each: a variable whose value makes some assertion
    /// definitively false is retracted IMMEDIATELY, retried with the other
    /// strategy, and left unfilled if that also fails, while the accepted
    /// prefix stays.
    ///
    /// SOUNDNESS: unchanged. Every intermediate model is checked by the SAME
    /// `completed_gap_model_accepted` (strict oracles + independent gate), the
    /// caller re-checks the final model, and a still-unfilled variable simply
    /// evaluates to `Unknown` exactly as it did before this pass ran. Ordering
    /// is the deterministic `gap_vars` order, so the result is reproducible.
    ///
    /// Runs only when both prior strategies failed, so it can never change an
    /// outcome the existing pass already accepted — it can only convert a
    /// would-be Unknown.
    fn fill_gap_vars_per_variable(&mut self, model: &mut Model, gap_vars: &[TermId]) -> usize {
        // Each variable costs up to two full gate checks; bound the work.
        const MAX_PER_VAR_GAPS: usize = 32;
        if gap_vars.len() > MAX_PER_VAR_GAPS {
            return 0;
        }
        let deadline = Instant::now() + Duration::from_secs(2);
        let mut filled = 0usize;
        for _round in 0..2 {
            let mut progress = false;
            for (ord, &var) in gap_vars.iter().enumerate() {
                if Instant::now() >= deadline {
                    return filled;
                }
                if !matches!(self.evaluate_term(model, var), EvalValue::Unknown) {
                    continue;
                }
                let sort = self.ctx.terms.sort(var).clone();
                let before = model.clone();
                for strategy in [GapStrategy::Derived, GapStrategy::SortDefault] {
                    let Some(value) = self.gap_candidate_value(model, var, ord, &sort, strategy)
                    else {
                        continue;
                    };
                    if !Self::insert_completed_value(&self.ctx.terms, model, var, &value) {
                        continue;
                    }
                    super::eval_memo_clear();
                    if self.completed_gap_model_accepted(model) {
                        filled += 1;
                        progress = true;
                        break;
                    }
                    // Refuted: retract JUST this variable and try the next
                    // strategy for it (the accepted prefix is preserved).
                    *model = before.clone();
                    super::eval_memo_clear();
                }
            }
            if !progress {
                break;
            }
        }
        filled
    }

    /// Reconstruct a String-variable witness from either a SAT-true defining
    /// string equality or the LIA/string length model, for the model-output
    /// (gate-verified candidate) path only. Parallel to
    /// [`Self::reconstruct_seq_from_len_nth`].
    ///
    /// Used when a String-sorted gap variable has no direct string-theory model
    /// entry and no defining `(= s (str.++ ...))` value the earlier
    /// `GapStrategy::Derived` steps could resolve, so [`Self::evaluate_term`]
    /// yields `Unknown`. The bare default in that case is `""` — length 0 —
    /// which VIOLATES any `(str.len s) = N > 0` constraint (re-feeds to Unknown).
    /// Two sound sources, in order:
    ///
    /// * (a) a SAT-assigned-TRUE string equality atom `(= var other)` /
    ///   `(= other var)` whose OTHER side already evaluates to a concrete string
    ///   — this captures the reduction-internal clause-literal equalities
    ///   (`x = sk_pre ++ skt ++ sk_suf`, `substr = skt`) that pin the witness
    ///   once the skolems have values, beyond the top-level asserted equalities
    ///   the caller already tried via `extract_value_from_asserted_equalities`;
    /// * (b) padding to the length the LIA/string model assigns `(str.len var)`
    ///   with a per-variable DISTINCT filler character (so two length-equal vars
    ///   constrained to differ get different witnesses — a blind uniform pad
    ///   would falsify `(not (= a b))` and be retracted to Unknown).
    ///
    /// Returns `None` (degrade to the `""` default / documented gap) when no
    /// defining equality resolves and no concrete non-negative length under a
    /// sanity cap is available.
    ///
    /// A substitution KEY is NEVER reconstructed here — it is DEFINED by its RHS
    /// and completed by the substitution fixpoint (Phase 2 of
    /// `complete_model_for_validation`); padding it would latch a value the
    /// fill-only fixpoint could no longer overwrite, mirroring the deliberate
    /// key-skip at the top of that pass (#substitution-key-skip).
    ///
    /// EVERY produced value is a CANDIDATE only:
    /// [`Self::complete_constrained_gaps`] re-checks the completed model with the
    /// strict oracles + independent gate and RETRACTS all candidates on any
    /// refutation, so a wrong filler can never ship — it degrades to Unknown.
    fn reconstruct_string_from_len_or_equalities(
        &self,
        model: &Model,
        var: TermId,
        ord: usize,
    ) -> Option<EvalValue> {
        // Only meaningful for an actual String-sorted variable.
        if !matches!(self.ctx.terms.get(var), TermData::Var(..)) {
            return None;
        }
        // Substitution keys are DEFINED by their RHS (Phase 2). Never
        // derive/pad one here or the fill-only fixpoint can no longer set the
        // correct value (#substitution-key-skip).
        if self.recorded_var_substitutions.contains_key(&var) {
            return None;
        }
        // (a) Derive from a SAT-true defining string equality whose other side
        //     is already concrete.
        if let Some(s) = self.derive_string_from_sat_true_equalities(model, var) {
            return Some(EvalValue::String(s));
        }
        // (a2) W1 (default ON, `AY_STR_WITNESS=0` kill switch): CONTENT-POSITIVE
        //      construction from the variable's `str.in_re` memberships as the
        //      SAT model assigns them. The uniform pad in (b) can only emit the
        //      pad letter, so a length-pinned + language-constrained variable is
        //      always refuted there; the derivative witness search emits exactly
        //      the characters the regex classes demand. Same candidate status as
        //      every other branch — `complete_constrained_gaps` re-checks and
        //      RETRACTS on refutation, so this can only convert to a
        //      gate-validated SAT, never mis-answer.
        if string_witness::str_witness_w1() {
            if let Some(s) = self.derive_string_from_sat_regex_memberships(model, var) {
                return Some(EvalValue::String(s));
            }
        }
        // (b) Pad to the model length with a per-variable distinct filler. A
        //     wrong pad (e.g. against a self-referential substr constraint, or a
        //     concat parent whose pieces disagree) makes an assertion evaluate
        //     definitively false, so `complete_constrained_gaps` RETRACTS the
        //     whole completion — degrading to Unknown, never a wrong SAT.
        let n = self.string_len_model_value(model, var)?;
        // Sanity cap mirrors the seq/ground reconstruction caps.
        if n > 4096 {
            return None;
        }
        let ch = Self::gap_pad_char(ord);
        Some(EvalValue::String(std::iter::repeat_n(ch, n).collect()))
    }

    /// Derive `var`'s string witness from a SAT-assigned-TRUE string equality
    /// atom `(= var other)` / `(= other var)` whose OTHER side already evaluates
    /// to a concrete string. Scans ALL `=` applications (not just top-level
    /// assertions) so reduction-internal clause-literal equalities are seen.
    ///
    /// The atom MUST be assigned true by the SAT model: an atom the solver never
    /// decided is absent from `term_to_var`, so [`Self::term_value`] yields
    /// `None` and the atom is skipped — a stale/undecided polarity is never
    /// assumed (the reviewers' step-2 caveat). Even so the value is only a
    /// gate-checked candidate, so a wrong read degrades to Unknown.
    fn derive_string_from_sat_true_equalities(&self, model: &Model, var: TermId) -> Option<String> {
        // String-sorted variable only (the caller already guarantees this).
        if !matches!(self.ctx.terms.sort(var), Sort::String) {
            return None;
        }
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            let TermData::App(sym, args) = self.ctx.terms.get(tid) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let other = if args[0] == var {
                args[1]
            } else if args[1] == var {
                args[0]
            } else {
                continue;
            };
            // The equality must be committed TRUE by the SAT model; an undecided
            // atom (absent from `term_to_var`) yields `None` and is skipped.
            if self.term_value(&model.sat_model, &model.term_to_var, tid) != Some(true) {
                continue;
            }
            if let EvalValue::String(s) = self.evaluate_term(model, other) {
                return Some(s);
            }
        }
        None
    }

    /// W1 (default ON, `AY_STR_WITNESS=0` kill switch): construct `var`'s witness from the
    /// `str.in_re` memberships the SAT model assigns it, via the exact
    /// derivative search [`ay_strings::we_regex::find_witness`].
    ///
    /// The membership polarities come from the SAT ASSIGNMENT (see
    /// [`Self::harvest_sat_regex_memberships`]), so reduction-internal and
    /// disjunctively-chosen memberships are seen — not only top-level syntactic
    /// conjuncts. The target length is the SAME `(str.len var)` model value the
    /// uniform pad (b) uses, so the constructed witness agrees with the LIA
    /// proxy by construction; when no concrete length resolves, any length the
    /// search finds is admissible.
    ///
    /// Returns `None` when the variable has no decided membership, when no
    /// exact translation exists, or when the bounded search finds nothing —
    /// in every case the caller falls through to the pre-existing pad, so the
    /// flags-off behavior is preserved exactly.
    ///
    /// GATE STATUS: candidate only. `complete_constrained_gaps` re-runs the
    /// strict oracles + the independent gate over the completed model and
    /// retracts every candidate on any refutation.
    fn derive_string_from_sat_regex_memberships(
        &self,
        model: &Model,
        var: TermId,
    ) -> Option<String> {
        let regexes = self.harvest_sat_regex_memberships(model, var);
        if regexes.is_empty() {
            return None;
        }
        let exact_len = self.string_len_model_value(model, var);
        if exact_len.is_some_and(|n| n > string_witness::MAX_WITNESS_CONSTRUCT_LEN) {
            return None;
        }
        ay_strings::we_regex::find_witness(&regexes, exact_len)
    }

    /// Concrete model length of `str_var`: the non-negative integer value of
    /// some `(str.len str_var)` term, read non-circularly via
    /// [`Self::lookup_term_value`] (LIA/theory models + asserted length
    /// equalities). `None` when no such term resolves to a concrete length.
    /// Parallel to `seq_len_model_value`.
    fn string_len_model_value(&self, model: &Model, str_var: TermId) -> Option<usize> {
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(tid) {
                if name == "str.len" && args.len() == 1 && args[0] == str_var {
                    if let EvalValue::Rational(r) = self.lookup_term_value(model, tid) {
                        if r.is_integer() && r.numer().sign() != num_bigint::Sign::Minus {
                            if let Some(n) = r.numer().to_usize() {
                                return Some(n);
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// A deterministic per-gap-variable filler character for length padding.
    /// Distinct ordinals map to distinct printable ASCII letters, so two
    /// length-equal string gap vars constrained to DIFFER receive different
    /// witnesses (a uniform filler would falsify `(not (= a b))` and be
    /// retracted). Cycles A-Z then a-z; ordinals past 52 reuse a letter (still
    /// sound — the gate retracts any resulting collision, degrading to Unknown).
    fn gap_pad_char(ord: usize) -> char {
        const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        ALPHABET[ord % ALPHABET.len()] as char
    }

    /// Whether the strict oracles AND the independent model-check gate accept
    /// the just-completed `model` as a valid SAT witness. Installs the model
    /// temporarily (both checks read `last_result`/`last_model`) and restores.
    fn completed_gap_model_accepted(&mut self, model: &mut Model) -> bool {
        use ay_model_check::GateVerdict;
        self.last_model = Some(std::mem::replace(model, Model::empty()));
        let prev_result = self.last_result.clone();
        self.last_result = Some(SolveResult::Sat);
        let strict_reject = self.verify_model_strict().is_some();
        let gate_reject = matches!(
            self.confirm_sat_with_independent_gate(),
            GateVerdict::ModelViolates { .. }
        );
        self.last_result = prev_result;
        *model = self.last_model.take().expect("installed above");
        !(strict_reject || gate_reject)
    }

    /// The canonical completion default for an UNCONSTRAINED variable of a
    /// given sort, or `None` for sorts whose completion is owned elsewhere:
    /// datatypes (the dt model prints the canonical constructor) and arrays
    /// (the store-chain witness renderer completes unwritten cells).
    ///
    /// The concrete choices deliberately match the (removed) print-time
    /// defaults so genuinely-unconstrained variables print exactly as before —
    /// but the value now EXISTS in the model before validation
    /// (#no-fabricated-model-values).
    pub(in crate::executor) fn unconstrained_default_value(
        &self,
        sort: &Sort,
    ) -> Option<EvalValue> {
        match sort {
            Sort::Bool => Some(EvalValue::Bool(false)),
            Sort::Int | Sort::Real => Some(EvalValue::Rational(BigRational::zero())),
            Sort::BitVec(bv) => Some(EvalValue::BitVec {
                value: BigInt::zero(),
                width: bv.width,
            }),
            Sort::String => Some(EvalValue::String(String::new())),
            Sort::RegLan => Some(EvalValue::Element("re.none".to_string())),
            Sort::FloatingPoint(eb, sb) => {
                Some(EvalValue::Fp(FpModelValue::PosZero { eb: *eb, sb: *sb }))
            }
            Sort::Seq(_) => Some(EvalValue::Seq(Vec::new())),
            Sort::Uninterpreted(name) => {
                if name == "RoundingMode" {
                    // FIXED 5-element FP domain (#P0.2 symbolic RoundingMode):
                    // an `@RoundingMode!0` token is not a valid value of the
                    // sort (z3 rejects a model carrying it). Any concrete mode
                    // is a valid completion for an unconstrained RM constant;
                    // use the IEEE default.
                    return Some(EvalValue::Element("roundNearestTiesToEven".to_string()));
                }
                if self.datatype_sort_name(sort).is_some() {
                    // Datatype-sorted: the dt model resolves the canonical
                    // constructor at print time; an `@Sort!0` element here
                    // would leak a skolem into the witness.
                    None
                } else {
                    Some(EvalValue::Element(format!("@{name}!0")))
                }
            }
            // Arrays, inline datatype sorts, and future sorts: completion is
            // owned by their dedicated model machinery.
            _ => None,
        }
    }

    /// A fully-completed model for the trivially-SAT query paths
    /// (`last_result == Sat` with `last_model == None`: preprocessing reduced
    /// the formula to `true`, so EVERY declared constant AND function is
    /// unconstrained and any assignment/interpretation is a valid witness).
    /// `(get-model)` / `(get-value)` / `(get-objectives)` borrow this instead
    /// of an empty dummy model, so the values they print exist in a model
    /// rather than being fabricated at print time (#no-fabricated-model-values).
    pub(in crate::executor) fn completed_default_model(&self) -> Model {
        let mut model = Model::empty();
        let mut consts: Vec<TermId> = self
            .ctx
            .symbol_iter()
            .filter(|(name, info)| {
                info.arg_sorts.is_empty()
                    && info.term.is_some()
                    && !self.is_dt_internal_symbol(name)
            })
            .filter_map(|(_, info)| info.term)
            .collect();
        consts.sort_by_key(|t| t.index());
        consts.dedup();
        for var in consts {
            let sort = self.ctx.terms.sort(var);
            if let Some(default) = self.unconstrained_default_value(sort) {
                model.completed_values.insert(var, default);
            } else if let Sort::Array(array_sort) = sort {
                model
                    .array_model
                    .get_or_insert_with(Default::default)
                    .array_values
                    .insert(
                        var,
                        ArrayInterpretation {
                            default: Some(self.canonical_default_value(&array_sort.element_sort)),
                            stores: Vec::new(),
                            index_sort: Some(array_sort.index_sort.clone()),
                            element_sort: Some(array_sort.element_sort.clone()),
                        },
                    );
            }
        }
        // Every DECLARED arity>0 function is likewise unconstrained here, so give
        // each a canonical constant interpretation (an empty function table the
        // printers render as `format_default_value(result_sort)`) — the function
        // counterpart of the constant defaults above, and Z3 parity for
        // `(get-model)` / `(get-value ((g ..)))` on trivially-SAT queries.
        // Problem-DEFINED symbols are excluded: their interpretation is fixed
        // by the problem, never a completion default (#mv-defined-fun-emit).
        let mut fns: Vec<String> = self
            .ctx
            .symbol_iter()
            .filter(|(name, info)| {
                !info.arg_sorts.is_empty()
                    && !self.is_dt_internal_symbol(name)
                    && !self.ctx.is_defined_fun(name)
            })
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();
        fns.sort();
        fns.dedup();
        if !fns.is_empty() {
            let euf_model = model.euf_model.get_or_insert_with(Default::default);
            for name in fns {
                euf_model.function_tables.entry(name).or_default();
            }
        }
        model
    }

    /// Every `TermData::Var` reachable from the current assertions and
    /// `extra_roots` — INCLUDING quantifier bodies, triggers, and let
    /// bindings. Used as the conservative "possibly constrained" set for the
    /// unconstrained-constant sweep: a variable occurring anywhere in an
    /// assertion is never defaulted by that sweep.
    fn collect_occurring_vars(&self, extra_roots: &[TermId]) -> HashSet<TermId> {
        let terms = &self.ctx.terms;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut vars: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        stack.extend_from_slice(extra_roots);
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            match terms.get(tid) {
                TermData::Var(_, _) => {
                    vars.insert(tid);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, t)| *t));
                    stack.push(*body);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                _ => {}
            }
        }
        vars
    }

    /// Whether a substitution-target term reads an array variable that was
    /// itself eliminated by substitution, i.e. contains `(select v _)` with
    /// `v ∈ substituted`.
    ///
    /// Such a target cannot be trusted from the raw BV model: after `v` is
    /// substituted away its orphaned `select(v, _)` term keeps whatever
    /// unconstrained bits the bit-blaster left, so the BV-lane recovery may
    /// have assigned the depending variable a stale value. The array-aware
    /// evaluator resolves the read through the reconstructed array
    /// interpretation instead, so completion re-derives (overrides) those
    /// variables rather than treating their stale value as authoritative.
    /// (#array-subst-store-target)
    /// Per-call visited set: the term store is a hash-consed DAG; without it
    /// this walk is once-per-tree-PATH -- exponential in sharing depth (the
    /// DAG->tree pathology; it consumed the whole post-solve completion phase
    /// on a 30M-clause BMC instance). Sound: `any`/`||` short-circuit on the
    /// first `true`, so a continued-past node evaluated `false`, fixed for
    /// this (term table, substituted) pair.
    fn target_reads_substituted_array(
        terms: &ay_core::TermStore,
        term: TermId,
        substituted: &HashSet<TermId>,
    ) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        Self::target_reads_substituted_array_inner(terms, term, substituted, &mut visited)
    }

    fn target_reads_substituted_array_inner(
        terms: &ay_core::TermStore,
        term: TermId,
        substituted: &HashSet<TermId>,
        visited: &mut HashSet<TermId>,
    ) -> bool {
        if !visited.insert(term) {
            return false;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "select" && args.len() == 2 && substituted.contains(&args[0]) {
                    return true;
                }
                args.iter().any(|&a| {
                    Self::target_reads_substituted_array_inner(terms, a, substituted, visited)
                })
            }
            TermData::Not(inner) => {
                Self::target_reads_substituted_array_inner(terms, *inner, substituted, visited)
            }
            TermData::Ite(c, t, e) => {
                Self::target_reads_substituted_array_inner(terms, *c, substituted, visited)
                    || Self::target_reads_substituted_array_inner(terms, *t, substituted, visited)
                    || Self::target_reads_substituted_array_inner(terms, *e, substituted, visited)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, t)| {
                    Self::target_reads_substituted_array_inner(terms, *t, substituted, visited)
                }) || Self::target_reads_substituted_array_inner(terms, *body, substituted, visited)
            }
            _ => false,
        }
    }

    /// Whether `term` reads a `select` over a DATATYPE/uninterpreted-ELEMENT
    /// array (the `select`'s own result sort is `Uninterpreted`). The BV/Bool
    /// recovery lane (`recover_substituted_bv_bool_values`) runs at bv-model
    /// construction time, BEFORE the EUF model is populated, and cannot fold a
    /// datatype-selector-over-array read (e.g. `(fld_rhs (select a i))`), so it
    /// leaves a STALE BV-lane default (0). Now that the full model (EUF) is
    /// available, the array-aware `evaluate_term` — with the committed-element
    /// `select` fallback (#g4-dt-ce-select) — CAN resolve it, so such a target
    /// must be re-derived even if the stale value is non-Unknown. SOUND:
    /// `evaluate_term` reads only committed theory-model values and fails closed
    /// to Unknown (the value then stays as-is and validation degrades), so the
    /// override only ever replaces a stale value with the committed-model value,
    /// never fabricates one.
    fn target_reads_datatype_element_array(terms: &ay_core::TermStore, term: TermId) -> bool {
        match terms.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.sort(term), Sort::Uninterpreted(_))
                {
                    return true;
                }
                args.iter()
                    .any(|&a| Self::target_reads_datatype_element_array(terms, a))
            }
            TermData::Not(inner) => Self::target_reads_datatype_element_array(terms, *inner),
            TermData::Ite(c, t, e) => {
                Self::target_reads_datatype_element_array(terms, *c)
                    || Self::target_reads_datatype_element_array(terms, *t)
                    || Self::target_reads_datatype_element_array(terms, *e)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, t)| Self::target_reads_datatype_element_array(terms, *t))
                    || Self::target_reads_datatype_element_array(terms, *body)
            }
            _ => false,
        }
    }

    /// Whether `term` structurally references any `TermData::Var` in `set`.
    /// Used to grow the datatype-dependent closure: a substituted var whose def
    /// mentions a var that (transitively) reads a datatype-element array must
    /// itself be re-derived once that array read is resolved (#g4-dt-ce-select).
    fn term_references_var_in_set(
        terms: &ay_core::TermStore,
        term: TermId,
        set: &HashSet<TermId>,
    ) -> bool {
        if set.contains(&term) {
            return true;
        }
        match terms.get(term) {
            TermData::App(_, args) => args
                .iter()
                .any(|&a| Self::term_references_var_in_set(terms, a, set)),
            TermData::Not(inner) => Self::term_references_var_in_set(terms, *inner, set),
            TermData::Ite(c, t, e) => {
                Self::term_references_var_in_set(terms, *c, set)
                    || Self::term_references_var_in_set(terms, *t, set)
                    || Self::term_references_var_in_set(terms, *e, set)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, t)| Self::term_references_var_in_set(terms, *t, set))
                    || Self::term_references_var_in_set(terms, *body, set)
            }
            _ => false,
        }
    }

    /// Collect the free variables of the current (original) assertions for
    /// the sorts completion can default (Bool/Int/Real).
    ///
    /// Quantifier bodies are intentionally NOT traversed: bound variables in
    /// them are `TermData::Var` nodes indistinguishable from free variables
    /// without scope tracking, and defaulting a bound variable would be
    /// meaningless. `Let` bodies are also skipped (lets are expanded before
    /// solving; defensive only).
    fn collect_assertion_free_vars(&self) -> Vec<TermId> {
        let terms = &self.ctx.terms;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut vars = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            match terms.get(tid) {
                TermData::Var(_, _) => {
                    if matches!(terms.sort(tid), Sort::Bool | Sort::Int | Sort::Real) {
                        vars.push(tid);
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                // Skip quantifier and let bodies (see doc comment).
                _ => {}
            }
        }
        // Deterministic order for reproducible completion.
        vars.sort_by_key(|t| t.index());
        vars
    }

    /// Record variable substitutions discovered by a preprocessing pass so
    /// model completion can replay them at finalize time.
    pub(in crate::executor) fn record_var_substitutions(
        &mut self,
        var_subst: &crate::preprocess::VariableSubstitution,
    ) {
        for (&from, &to) in var_subst.substitutions() {
            self.recorded_var_substitutions.insert(from, to);
        }
    }
}

#[cfg(test)]
mod equality_carrier_completion_tests {
    use super::{Executor, Model};
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use ay_frontend::parse;
    use ay_seq::SeqModel;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn completed_seq(model: &Model, term: ay_core::TermId) -> &Vec<super::EvalValue> {
        match model.completed_values.get(&term) {
            Some(super::EvalValue::Seq(elems)) => elems,
            other => panic!("expected concrete completed sequence, got {other:?}"),
        }
    }

    fn declared_seq_var(exec: &mut Executor, name: &str, sort: Sort) -> ay_core::TermId {
        let term = exec.ctx.terms.mk_var(name, sort.clone());
        exec.ctx.register_symbol(name.to_string(), term, sort);
        term
    }

    #[test]
    fn nested_sat_true_sequence_equality_gets_one_model_class_without_bv() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = declared_seq_var(&mut exec, "seq-class-x", seq_int.clone());
        let y = declared_seq_var(&mut exec, "seq-class-y", seq_int.clone());
        let z = declared_seq_var(&mut exec, "seq-class-z", seq_int);
        let equal = exec.ctx.terms.mk_eq(x, y);
        let guard = exec.ctx.terms.mk_var("seq-class-guard", Sort::Bool);
        let nested = exec.ctx.terms.mk_or(vec![equal, guard]);
        let distinct = exec.ctx.terms.mk_distinct(vec![x, z]);
        exec.self_check_authored_assertions = Some(vec![nested, distinct]);
        assert!(exec.ctx.assertions.is_empty());

        let mut model = Model::empty();
        model.sat_model = vec![true];
        model.term_to_var.insert(equal, 0);
        assert!(model.bv_model.is_none());

        exec.complete_uninterpreted_sort_model(&mut model, &[]);

        assert_eq!(completed_seq(&model, x), completed_seq(&model, y));
        assert_ne!(completed_seq(&model, x), completed_seq(&model, z));
        assert!(model.euf_model.as_ref().is_none_or(|euf| {
            [x, y, z].iter().all(|term| {
                !euf.term_values
                    .get(term)
                    .is_some_and(|v| v.starts_with("@ay-seq"))
            })
        }));
    }

    #[test]
    fn nested_sat_false_sequence_equality_does_not_merge_classes() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = declared_seq_var(&mut exec, "seq-false-x", seq_int.clone());
        let y = declared_seq_var(&mut exec, "seq-false-y", seq_int);
        let equal = exec.ctx.terms.mk_eq(x, y);
        let guard = exec.ctx.terms.mk_var("seq-false-guard", Sort::Bool);
        let nested = exec.ctx.terms.mk_or(vec![equal, guard]);
        exec.ctx.assertions.push(nested);

        let mut model = Model::empty();
        model.sat_model = vec![false];
        model.term_to_var.insert(equal, 0);

        exec.complete_uninterpreted_sort_model(&mut model, &[]);

        assert_ne!(
            completed_seq(&model, x),
            completed_seq(&model, y),
            "a nested equality assigned false must not merge its operands"
        );
    }

    #[test]
    fn sequence_completion_reuses_an_existing_model_class() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = declared_seq_var(&mut exec, "seq-existing-x", seq_int.clone());
        let y = declared_seq_var(&mut exec, "seq-existing-y", seq_int);
        let equal = exec.ctx.terms.mk_eq(x, y);
        exec.ctx.assertions.push(equal);

        let mut model = Model::empty();
        let mut euf = ay_euf::EufModel::default();
        euf.term_values.insert(x, "model-class-7".to_string());
        model.euf_model = Some(euf);

        exec.complete_uninterpreted_sort_model(&mut model, &[]);

        assert_eq!(completed_seq(&model, x), completed_seq(&model, y));
        assert!(matches!(
            model.euf_model.as_ref().and_then(|euf| euf.term_values.get(&x)),
            Some(value) if value == "model-class-7"
        ));
    }

    #[test]
    fn conflicting_concrete_sequences_forced_equal_do_not_fill_missing_member() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = declared_seq_var(&mut exec, "seq-conflict-x", seq_int.clone());
        let y = declared_seq_var(&mut exec, "seq-conflict-y", seq_int.clone());
        let missing = declared_seq_var(&mut exec, "seq-conflict-missing", seq_int);
        let xy = exec.ctx.terms.mk_eq(x, y);
        let ym = exec.ctx.terms.mk_eq(y, missing);
        exec.ctx.assertions.extend([xy, ym]);

        let mut model = Model::empty();
        let mut values = HashMap::default();
        values.insert(x, Vec::new());
        values.insert(y, vec!["7".to_string()]);
        model.seq_model = Some(SeqModel { values });

        exec.complete_uninterpreted_sort_model(&mut model, &[]);

        assert!(
            !model.completed_values.contains_key(&missing),
            "a conflicting concrete class must remain unresolved and fail closed"
        );
    }

    #[test]
    fn concrete_sequence_class_is_propagated_without_an_opaque_identity() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let concrete = declared_seq_var(&mut exec, "seq-concrete", seq_int.clone());
        let missing = declared_seq_var(&mut exec, "seq-missing", seq_int);
        let equal = exec.ctx.terms.mk_eq(concrete, missing);
        exec.ctx.assertions.push(equal);

        let mut model = Model::empty();
        let mut values = HashMap::default();
        values.insert(concrete, vec!["11".to_string()]);
        model.seq_model = Some(SeqModel { values });

        exec.complete_uninterpreted_sort_model(&mut model, &[]);

        assert_eq!(
            completed_seq(&model, concrete),
            completed_seq(&model, missing)
        );
        assert_eq!(completed_seq(&model, missing).len(), 1);
        assert!(model.euf_model.as_ref().is_none_or(|euf| {
            !euf.term_values
                .get(&missing)
                .is_some_and(|v| v.starts_with("@ay-seq"))
        }));
    }

    #[test]
    fn native_sequence_term_anchors_class_but_is_never_completed() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = declared_seq_var(&mut exec, "seq-native-anchor-x", seq_int.clone());
        let seven = exec.ctx.terms.mk_int(BigInt::from(7));
        let unit =
            exec.ctx
                .terms
                .mk_app(Symbol::Named("seq.unit".to_string()), vec![seven], seq_int);
        let equal = exec.ctx.terms.mk_eq(x, unit);
        exec.ctx.assertions.push(equal);

        let mut model = Model::empty();
        exec.complete_uninterpreted_sort_model(&mut model, &[]);

        assert_eq!(completed_seq(&model, x).len(), 1);
        assert_eq!(
            completed_seq(&model, x)[0],
            super::EvalValue::Rational(BigRational::from_integer(BigInt::from(7)))
        );
        assert!(
            !model.completed_values.contains_key(&unit),
            "native seq.unit is a semantic class anchor, never a completion target"
        );
    }

    #[test]
    fn opaque_uninterpreted_elements_do_not_become_public_sequence_witnesses() {
        let mut exec = Executor::new();
        let elem = Sort::Uninterpreted("SeqElem".to_string());
        let seq = Sort::Seq(Box::new(elem));
        let x = declared_seq_var(&mut exec, "seq-uninterp-x", seq.clone());
        let y = declared_seq_var(&mut exec, "seq-uninterp-y", seq);
        let distinct = exec.ctx.terms.mk_distinct(vec![x, y]);
        exec.ctx.assertions.push(distinct);

        let mut model = Model::empty();
        exec.complete_uninterpreted_sort_model(&mut model, &[]);

        assert!(model.completed_values.get(&x).is_none());
        assert!(model.completed_values.get(&y).is_none());
        assert_eq!(
            exec.last_statistics
                .get_int("model_completion.sequence_budget_or_value_blocked"),
            Some(1)
        );
    }

    #[test]
    fn sequence_completion_cell_budget_has_exact_fail_closed_boundary() {
        // Lengths 0..63 consume 2016 cells in class representatives and 2016
        // more in per-term completed values: 4032 <= the 4096-cell budget.
        // Adding class 64 would consume 4160 total cells and must commit none.
        for (classes, should_complete) in [(64usize, true), (65usize, false)] {
            let mut exec = Executor::new();
            let seq = Sort::Seq(Box::new(Sort::Int));
            let vars: Vec<_> = (0..classes)
                .map(|idx| {
                    declared_seq_var(
                        &mut exec,
                        &format!("seq-budget-{classes}-{idx}"),
                        seq.clone(),
                    )
                })
                .collect();
            let distinct = exec.ctx.terms.mk_distinct(vars.clone());
            exec.ctx.assertions.push(distinct);
            let mut model = Model::empty();

            exec.complete_uninterpreted_sort_model(&mut model, &[]);

            assert_eq!(
                vars.iter()
                    .all(|term| model.completed_values.contains_key(term)),
                should_complete,
                "unexpected completion decision for {classes} classes"
            );
            if !should_complete {
                assert!(vars
                    .iter()
                    .all(|term| !model.completed_values.contains_key(term)));
                assert_eq!(
                    exec.last_statistics
                        .get_int("model_completion.sequence_budget_or_value_blocked"),
                    Some(1)
                );
            }
        }
    }

    #[test]
    fn equality_only_sequence_model_and_values_round_trip_without_opaque_tokens() {
        let input = "\
(set-logic QF_SEQ)\n\
(set-option :produce-models true)\n\
(declare-const x (Seq Int))\n\
(declare-const y (Seq Int))\n\
(declare-const z (Seq Int))\n\
(assert (= x y))\n\
(assert (distinct x z))\n\
(check-sat)\n\
(get-model)\n\
(get-value (x y z))";
        let commands = parse(input).expect("valid sequence equality query");
        let mut exec = Executor::new();
        exec.set_self_check(true);
        let outputs = exec.execute_all(&commands).expect("query executes");
        assert_eq!(outputs.first().map(String::as_str), Some("sat"));

        let model = outputs.get(1).expect("get-model output");
        let values = outputs.get(2).expect("get-value output");
        assert!(!model.contains("@ay-seq"), "opaque class leaked: {model}");
        assert!(!values.contains("@ay-seq"), "opaque class leaked: {values}");
        assert!(model.contains("(define-fun x () (Seq Int)"));
        assert!(model.contains("(define-fun y () (Seq Int)"));
        assert!(model.contains("(define-fun z () (Seq Int)"));

        // Re-feed the emitted definitions as an ordinary SMT-LIB query. This
        // checks both syntax and semantics: the concrete model must still make
        // x=y and x!=z true, and its get-value answers must match the original.
        let definitions = model
            .strip_prefix("(model\n")
            .and_then(|body| body.strip_suffix("\n)"))
            .expect("canonical model response");
        let replay = format!(
            "(set-logic QF_SEQ)\n{definitions}\n\
             (assert (= x y))\n\
             (assert (distinct x z))\n\
             (check-sat)\n\
             (get-value (x y z))"
        );
        let replay_commands = parse(&replay).expect("emitted model reparses");
        let mut replay_exec = Executor::new();
        let replay_outputs = replay_exec
            .execute_all(&replay_commands)
            .expect("emitted model re-executes");
        assert_eq!(replay_outputs.first().map(String::as_str), Some("sat"));
        assert_eq!(replay_outputs.get(1), Some(values));
    }

    #[test]
    fn sequence_semantic_builtins_cannot_be_repaired_into_sat() {
        let cases = [
            "(assert (= (seq.len (seq.unit 7)) 0))",
            "(assert (distinct (seq.++ (seq.unit 1) (seq.unit 2)) \
                               (seq.++ (seq.unit 1) (seq.unit 2))))",
            "(assert (distinct (seq.extract (seq.unit 1) 0 1) (seq.unit 1)))",
        ];
        for assertion in cases {
            let input = format!("(set-logic QF_SEQ)\n{assertion}\n(check-sat)");
            let commands = parse(&input).expect("valid adversarial sequence query");
            let mut exec = Executor::new();
            exec.set_self_check(true);
            let outputs = exec.execute_all(&commands).expect("query executes");
            assert_ne!(
                outputs.first().map(String::as_str),
                Some("sat"),
                "false native-sequence assertion was repaired into sat: {assertion}"
            );
        }
    }
}

#[cfg(test)]
mod gap_pad_char_tests {
    use super::Executor;

    /// The pad-char generator underpins the disequality-pad soundness of the
    /// `Sort::String` `GapStrategy::Derived` arm: two length-equal string gap
    /// vars constrained to DIFFER must receive different fillers so a blind
    /// uniform pad can't falsify `(not (= a b))`. Distinct ordinals within one
    /// alphabet cycle MUST map to distinct printable letters.
    #[test]
    fn distinct_ordinals_give_distinct_pad_chars() {
        let n = 52; // A-Z then a-z, one full cycle
        let chars: Vec<char> = (0..n).map(Executor::gap_pad_char).collect();
        for c in &chars {
            assert!(
                c.is_ascii_alphabetic(),
                "pad char must be a printable ASCII letter, got {c:?}"
            );
        }
        let mut sorted = chars.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            n,
            "the first {n} ordinals must yield {n} DISTINCT pad chars (no collision within a cycle)"
        );
        // Deterministic anchors (stable witnesses across redeploys).
        assert_eq!(Executor::gap_pad_char(0), 'A');
        assert_eq!(Executor::gap_pad_char(1), 'B');
        // Wraps around after the alphabet is exhausted (still sound — the gate
        // retracts any resulting collision).
        assert_eq!(Executor::gap_pad_char(52), Executor::gap_pad_char(0));
    }
}

#[cfg(test)]
mod uf_table_conflict_discard_tests {
    use crate::executor::model::Model;
    use crate::executor::Executor;

    fn executor_with_conflicted_uf_model() -> Executor {
        let mut exec = Executor::new();
        let mut model = Model::empty();
        let mut euf = ay_euf::EufModel::default();
        euf.function_table_conflicts.insert("f".to_string());
        model.euf_model = Some(euf);
        exec.last_model = Some(model);
        exec.last_model_validated = true;
        exec
    }

    /// #uflia-cong-repair-arm handoff: discarding a conflicted-UF-table model
    /// on the UFLIA lane must ARM the reactive congruence-repair re-solve.
    /// The discard runs BEFORE the independent gate, so without arming here
    /// the gate site that normally triggers the retry never sees the model
    /// and a genuine SAT dies as a final "No model available" Unknown
    /// (mathsat Hash hash_sat_07_05, default mode).
    #[test]
    fn uf_table_conflict_discard_arms_uflia_congruence_retry() {
        let mut exec = executor_with_conflicted_uf_model();
        exec.uflia_congruence_lane = true;

        exec.complete_unconstrained_constants_for_output(&[]);

        assert!(
            exec.last_model.is_none(),
            "conflicted model must be discarded"
        );
        assert!(!exec.last_model_validated);
        assert!(
            exec.uflia_congruence_gate_rejected,
            "UFLIA-lane discard must arm the congruence-repair re-solve"
        );
    }

    /// Off the UFLIA lane the discard stays inert: no other theory's
    /// conflicted table may arm the (UFLIA-specific) repair retry.
    #[test]
    fn uf_table_conflict_discard_does_not_arm_outside_uflia_lane() {
        let mut exec = executor_with_conflicted_uf_model();
        exec.uflia_congruence_lane = false;

        exec.complete_unconstrained_constants_for_output(&[]);

        assert!(exec.last_model.is_none());
        assert!(!exec.uflia_congruence_gate_rejected);
    }
}
