// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Propagation replay entry point, indexes, and candidate planning.
// Textually included by `proof_propagated_rewrite.rs` to preserve method paths.

impl Executor {
    /// Mint provenance for the 1→N re-flatten of an `and`-headed assertion.
    ///
    /// Top-level propagation can reduce a guarded branch to its surviving
    /// conjunction, after which variable substitution rewrites it and the
    /// pipeline flattens it into individual assertions. Before this record,
    /// those new conjunct units were never replay candidates and were demoted
    /// to premiseless `trust` (30 of 31 units on the measured dillig12_m
    /// clause-1 shape).
    ///
    /// A record is only a hint that `after` lies on an `and` path beneath
    /// `before`. Replay re-finds that path in the term store and emits the
    /// existing `and_pos` plus `th_resolution` projection chain, which the
    /// strict checker independently validates. A false record cannot license
    /// a step and falls through to fail-closed demotion.
    pub(in crate::executor) fn extend_propagated_value_provenance_from_reflatten(
        &mut self,
        pairs: &[(TermId, TermId)],
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() || pairs.is_empty() {
            return;
        }
        let rewrites: Vec<_> = pairs
            .iter()
            .filter(|(before, after)| before != after)
            .map(
                |&(before, after)| crate::preprocess::PropagatedRewriteRecord {
                    before,
                    after,
                    stamp: 1,
                },
            )
            .collect();
        if rewrites.is_empty() {
            return;
        }
        self.merge_propagation_records(PropagationRecords {
            rewrites,
            ..PropagationRecords::default()
        });
    }

    /// Derive propagation-rewritten assumptions from their authored roots
    /// before the demotion pass turns unsupported assumptions into `trust`.
    pub(in crate::executor) fn derive_propagated_value_assumptions(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) {
        let candidate_budget = array_units::ArrayReplayBudget::new(self);
        self.derive_propagated_value_assumptions_with_candidates(
            proof,
            problem_assertions,
            &|work, bytes| candidate_budget.charge(work, bytes),
        );
    }

    // The extra envelope covers discovery only. Existing candidate planners
    // retain their per-plan bound; this is not a whole scalar-L1 lifetime cap.
    fn derive_propagated_value_assumptions_with_candidates(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
        candidate_progress: &dyn Fn(usize, usize) -> bool,
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled()
            || (self.propagated_value_provenance.rewrites.is_empty()
                && self.propagated_value_provenance.array_units.is_empty())
        {
            return;
        }
        let array_active = !self.propagated_value_provenance.array_units.is_empty();
        if array_active && self.term_memory_exceeded() {
            return;
        }
        let array_budget = array_active.then(|| array_units::ArrayReplayBudget::new(self));
        let array_progress =
            |work, bytes| array_budget.as_ref().is_none_or(|b| b.charge(work, bytes));
        if !array_progress(0, 0) {
            return;
        }
        if array_active
            && array_units::prepay_indexes(
                problem_assertions.len(),
                &self.propagated_value_provenance,
                &array_progress,
            )
            .is_none()
        {
            return;
        }
        let problem_set = problem_assertions.iter().copied().collect();
        let (record_by_after, entry_by_expr) = self.propagation_replay_indexes();
        let Some(candidates) = Self::propagation_replay_candidates(
            &self.ctx.terms,
            proof,
            &problem_set,
            &record_by_after,
            &self.propagated_value_provenance.array_units,
            &array_progress,
            candidate_progress,
        ) else {
            return;
        };
        if candidates.is_empty() || !candidate_progress(0, 0) {
            return;
        }
        let planned = self.plan_propagation_candidates(
            candidates,
            &problem_set,
            problem_assertions,
            &record_by_after,
            &entry_by_expr,
            &array_progress,
        );
        if !candidate_progress(0, 0)
            || (array_active && (!array_progress(0, 0) || self.term_memory_exceeded()))
        {
            return;
        }
        if !planned.shared_conclusions.is_empty() || !planned.solo.is_empty() {
            if array_active
                && array_units::prepay_splice(proof, &planned, &array_progress).is_none()
            {
                return;
            }
            // This bounded existing splice moves payloads; it does not clone
            // arbitrary certificates. A final stop observation never licenses
            // the resulting proof as a verdict: publication still checks it.
            if !candidate_progress(0, 0) {
                return;
            }
            splice::splice_propagated_plans(proof, planned);
            if array_active {
                array_progress(0, 0);
            }
        }
    }

    fn propagation_replay_indexes(
        &self,
    ) -> (
        HashMap<TermId, (TermId, u32)>,
        HashMap<TermId, (TermId, TermId, u32)>,
    ) {
        let mut record_by_after = HashMap::default();
        for record in &self.propagated_value_provenance.rewrites {
            if record.before != record.after {
                record_by_after
                    .entry(record.after)
                    .or_insert((record.before, record.stamp));
            }
        }
        let mut entry_by_expr = HashMap::default();
        for entry in &self.propagated_value_provenance.entries {
            entry_by_expr.entry(entry.expr).or_insert((
                entry.value,
                entry.source_assertion,
                entry.stamp,
            ));
        }
        (record_by_after, entry_by_expr)
    }

    fn propagation_replay_candidates(
        terms: &TermStore,
        proof: &Proof,
        problem_set: &HashSet<TermId>,
        record_by_after: &HashMap<TermId, (TermId, u32)>,
        array_units: &[ArrayUnitDerivation],
        progress: &dyn Fn(usize, usize) -> bool,
        candidate_progress: &dyn Fn(usize, usize) -> bool,
    ) -> Option<Vec<(usize, TermId)>> {
        let descendants =
            match replay_candidates::and_descendants(terms, record_by_after, &|work, bytes| {
                progress(work, bytes) && candidate_progress(work, bytes)
            }) {
                Ok(descendants) => descendants,
                // Discovery is optional: a local shape/work refusal must not
                // suppress historical direct-record or array-unit candidates.
                Err(replay_candidates::CensusDecline::BoundedMiss) => HashSet::default(),
                // Never poll again or retry after a witnessed resource stop.
                Err(replay_candidates::CensusDecline::Stopped) => return None,
            };
        if !progress(0, 0) || !candidate_progress(0, 0) {
            return None;
        }
        let active = !array_units.is_empty();
        let mut candidates = Vec::new();
        for (index, step) in proof.steps.iter().enumerate() {
            if active && !progress(1, 0) {
                return None;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if problem_set.contains(term) {
                continue;
            }
            let mut found = record_by_after.contains_key(term) || descendants.contains(term);
            if !found {
                for unit in array_units {
                    if !progress(1, 0) {
                        return None;
                    }
                    if unit.term() == *term {
                        found = true;
                        break;
                    }
                }
            }
            if found {
                // Prepay amortized vector growth; there is no auxiliary unit
                // hash index whose allocation precedes the caller's meter.
                if active && !progress(1, 2 * std::mem::size_of::<(usize, TermId)>()) {
                    return None;
                }
                candidates.push((index, *term));
            }
        }
        Some(candidates)
    }

    fn plan_propagation_candidates(
        &mut self,
        candidates: Vec<(usize, TermId)>,
        problem_set: &HashSet<TermId>,
        problem_roots: &[TermId],
        record_by_after: &HashMap<TermId, (TermId, u32)>,
        entry_by_expr: &HashMap<TermId, (TermId, TermId, u32)>,
        array_progress: &dyn Fn(usize, usize) -> bool,
    ) -> splice::PlannedPropagationChains {
        // Share the licensing prefix across non-constant candidates. A failed
        // candidate rolls its partial chain back, and each attempt receives
        // the historical full node budget.
        //
        // Every plan runs with the constant-array read leg OFF first. A target
        // whose attempt deferred such a read is retried ALONE with the leg on
        // (`PlanCx::const_array_reads`), so neither the shared chain nor its
        // memo ever holds a leg-closed step another candidate could reuse.
        let const_array_reads = self.ctx.datatype_iter().next().is_none();
        let array_units = self.propagated_value_provenance.array_units.as_slice();
        let plan_cx = |const_array_reads: bool| {
            PlanCx::new(
                problem_set,
                problem_roots,
                record_by_after,
                entry_by_expr,
                &[],
                false,
            )
            .with_array_units(array_units, array_progress)
            .with_const_array_reads(const_array_reads)
        };
        let mut shared = plan_cx(false);
        let mut shared_conclusions = HashMap::default();
        let mut solo = HashMap::default();
        for (index, term) in candidates {
            let constant_target =
                matches!(self.ctx.terms.get(term), TermData::Const(Constant::Bool(_)));
            let mut planner = PropagationChainPlanner {
                terms: &mut self.ctx.terms,
            };
            let deferred = if constant_target {
                // Constant targets stay isolated so a shared memo cannot
                // bypass their explicit refusal rule.
                let mut cx = plan_cx(false).with_constant_target(term);
                if let Some(conclusion) = planner.plan_derive_clause(&mut cx, term) {
                    solo.insert(index, (cx.chain, conclusion));
                    continue;
                }
                cx.deferred_const_array_read()
            } else {
                shared.budget = PLAN_NODE_BUDGET;
                shared.const_array_read_deferred = false;
                let mark = shared.mark();
                if let Some(conclusion) = planner.plan_derive_clause(&mut shared, term) {
                    shared_conclusions.insert(index, conclusion);
                    continue;
                }
                shared.rollback(mark);
                shared.deferred_const_array_read()
            };
            if const_array_reads && deferred {
                let mut cx = plan_cx(true);
                if constant_target {
                    cx = cx.with_constant_target(term);
                }
                if let Some(conclusion) = planner.plan_derive_clause(&mut cx, term) {
                    solo.insert(index, (cx.chain, conclusion));
                }
            }
        }
        splice::PlannedPropagationChains {
            shared_chain: shared.chain,
            shared_conclusions,
            solo,
        }
    }
}
