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
        if !crate::quant_unit_authority::quant_unit_authority_enabled()
            || self.propagated_value_provenance.rewrites.is_empty()
        {
            return;
        }
        let problem_set = problem_assertions.iter().copied().collect();
        let (record_by_after, entry_by_expr) = self.propagation_replay_indexes();
        let candidates = Self::propagation_replay_candidates(proof, &problem_set, &record_by_after);
        if candidates.is_empty() {
            return;
        }
        let planned = self.plan_propagation_candidates(
            candidates,
            &problem_set,
            problem_assertions,
            &record_by_after,
            &entry_by_expr,
        );
        if !planned.shared_conclusions.is_empty() || !planned.solo.is_empty() {
            splice::splice_propagated_plans(proof, planned);
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
        proof: &Proof,
        problem_set: &HashSet<TermId>,
        record_by_after: &HashMap<TermId, (TermId, u32)>,
    ) -> Vec<(usize, TermId)> {
        proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                let ProofStep::Assume(term) = step else {
                    return None;
                };
                if problem_set.contains(term) || !record_by_after.contains_key(term) {
                    return None;
                }
                Some((index, *term))
            })
            .collect()
    }

    fn plan_propagation_candidates(
        &mut self,
        candidates: Vec<(usize, TermId)>,
        problem_set: &HashSet<TermId>,
        problem_roots: &[TermId],
        record_by_after: &HashMap<TermId, (TermId, u32)>,
        entry_by_expr: &HashMap<TermId, (TermId, TermId, u32)>,
    ) -> splice::PlannedPropagationChains {
        // Share the licensing prefix across non-constant candidates. A failed
        // candidate rolls its partial chain back, and each attempt receives
        // the historical full node budget.
        let mut shared = PlanCx::new(
            problem_set,
            problem_roots,
            record_by_after,
            entry_by_expr,
            &[],
            false,
        );
        let mut shared_conclusions = HashMap::default();
        let mut solo = HashMap::default();
        for (index, term) in candidates {
            let constant_target =
                matches!(self.ctx.terms.get(term), TermData::Const(Constant::Bool(_)));
            if constant_target {
                // Constant targets stay isolated so a shared memo cannot
                // bypass their explicit refusal rule.
                let mut cx = PlanCx::new(
                    problem_set,
                    problem_roots,
                    record_by_after,
                    entry_by_expr,
                    &[],
                    false,
                )
                .with_constant_target(term);
                let mut planner = PropagationChainPlanner {
                    terms: &mut self.ctx.terms,
                };
                if let Some(conclusion) = planner.plan_derive_clause(&mut cx, term) {
                    solo.insert(index, (cx.chain, conclusion));
                }
            } else {
                shared.budget = PLAN_NODE_BUDGET;
                let mark = shared.mark();
                let mut planner = PropagationChainPlanner {
                    terms: &mut self.ctx.terms,
                };
                match planner.plan_derive_clause(&mut shared, term) {
                    Some(conclusion) => {
                        shared_conclusions.insert(index, conclusion);
                    }
                    None => shared.rollback(mark),
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
