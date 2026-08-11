// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Watched-literal falsification handling for `PbPropagator`: the
//! `notify_falsified*` family and unwatched-replacement scanning that keep
//! each constraint's two-watched invariant. Extracted from `propagation.rs`;
//! these remain methods on [`super::PbPropagator`].

use super::*;

impl PbPropagator {
    /// Watch-result handling that also queues propagating/conflicting
    /// constraints.
    ///
    /// `notify_falsified` keeps only the FIRST propagation per falsification
    /// event; every other constraint whose check reports `Propagated` here
    /// would historically be dropped and re-discovered only by the caller's
    /// next full constraint scan. Queueing the constraint index instead lets
    /// the event-driven fixpoint drivers (`propagate_all`,
    /// `drive_to_fixpoint`) re-check exactly these constraints without the
    /// O(constraints) rescan (P2d). The first propagation is queued too: its
    /// consumer re-checks the same constraint anyway (idempotent `Ok`), and
    /// callers that discard the returned result (e.g. `decide`, whose search
    /// loop re-propagates immediately afterwards) then cannot lose it.
    /// `Conflict` results are queued for the same reason: a caller that
    /// discards a conflict (again `decide`) historically relied on the next
    /// full scan to re-detect it; the queued re-check reproduces that.
    fn handle_watch_result_queueing(
        &mut self,
        cid: usize,
        result: PropResult,
        advance: bool,
        cursor: &mut usize,
        first_propagation: &mut Option<PropResult>,
    ) -> Option<PropResult> {
        if matches!(
            result,
            PropResult::Propagated(..) | PropResult::Conflict(..)
        ) {
            self.queue_pending_check(cid);
        }
        handle_watch_result(result, advance, cursor, first_propagation)
    }

    /// Handles a literal becoming false: examines all constraints watching it.
    ///
    /// For each constraint, if the falsified literal is in the watched set:
    /// 1. Reduce slack by its coefficient
    /// 2. Try to swap in a non-false unwatched literal
    /// 3. If no swap: check for conflict or propagation
    pub(super) fn notify_falsified(&mut self, falsified_lit: Lit) -> PropResult {
        let Some(watch_idx) = lit_index(falsified_lit) else {
            return PropResult::Ok;
        };
        if watch_idx >= self.watches.len() {
            return PropResult::Ok;
        }

        // COUNTING PRE-PASS (soundness): decrement EVERY counting constraint that
        // watches `falsified_lit` before the main propagation loop runs. Counting
        // slack is trusted exactly (no lazy rescan fallback), so it must reflect
        // this falsification unconditionally — even if the main loop aborts early
        // on a conflict before reaching a given counting constraint. The main
        // loop's counting branch then only CHECKS (it does not decrement again).
        // Non-counting constraints keep the watched scheme's early-abort
        // behavior, since their checks fall back to an exact rescan and tolerate
        // a momentarily stale cached slack.
        self.decrement_counting_watches(watch_idx, falsified_lit);

        let mut first_propagation: Option<PropResult> = None;
        let mut cursor = 0usize;
        while cursor < self.watches[watch_idx].len() {
            let cid = self.watches[watch_idx][cursor];
            if !self.constraints[cid].active {
                self.watches[watch_idx].swap_remove(cursor);
                continue;
            }

            if self.constraints[cid].shape == ConstraintShape::Clause {
                match self.notify_falsified_clause(watch_idx, cursor, cid, falsified_lit) {
                    TernaryNotify::Advance => cursor += 1,
                    TernaryNotify::Stay => {}
                    TernaryNotify::Return { result, advance } => {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            advance,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                    }
                }
                continue;
            }

            if self.constraints[cid].shape == ConstraintShape::TernaryClause {
                match self.notify_falsified_ternary_clause(watch_idx, cursor, cid, falsified_lit) {
                    TernaryNotify::Advance => cursor += 1,
                    TernaryNotify::Stay => {}
                    TernaryNotify::Return { result, advance } => {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            advance,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                    }
                }
                continue;
            }

            if self.constraints[cid].shape == ConstraintShape::UnitCardinality {
                match self.notify_falsified_unit_cardinality(watch_idx, cursor, cid, falsified_lit)
                {
                    TernaryNotify::Advance => cursor += 1,
                    TernaryNotify::Stay => {}
                    TernaryNotify::Return { result, advance } => {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            advance,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                    }
                }
                continue;
            }

            if self.constraints[cid].counting {
                // Slack was already decremented in the pre-pass; only check.
                if self.counting_lit_coeff(cid, falsified_lit) == 0 {
                    cursor += 1;
                    continue;
                }
                let result = self.check_counting_propagation(cid);
                if !matches!(result, PropResult::Ok) {
                    if let Some(stop) = self.handle_watch_result_queueing(
                        cid,
                        result,
                        true,
                        &mut cursor,
                        &mut first_propagation,
                    ) {
                        return stop;
                    }
                    continue;
                }
                cursor += 1;
                continue;
            }

            // Find the falsified literal in the watched region. Duplicate
            // literals are legal after normalization, so accumulate every
            // watched occurrence that became false under this assignment.
            let watch_end = self.constraints[cid].watch_end;
            let mut found_idx = None;
            let mut falsified_watched_coeff = 0i128;
            for i in 0..watch_end {
                if self.constraints[cid].terms[i].lit == falsified_lit {
                    if found_idx.is_none() {
                        found_idx = Some(i);
                    }
                    falsified_watched_coeff = falsified_watched_coeff
                        .saturating_add(self.constraints[cid].terms[i].coeff);
                }
            }

            let Some(watched_idx) = found_idx else {
                // Literal is not in the watched region. For full-visibility
                // rows this is a REAL event: an unwatched falsification can
                // flip the exact slack with no watched-slack change, so run a
                // full (exact) check without touching cached slack (P2d).
                // Otherwise it is a harmless stale watch entry (possible
                // after backtrack + rebuild). Never adjust slack here.
                if self.constraints[cid].watch_all {
                    let result = self.check_propagation(cid);
                    if !matches!(result, PropResult::Ok) {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            true,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                        continue;
                    }
                }
                cursor += 1;
                continue;
            };

            let falsified_coeff = self.constraints[cid].terms[watched_idx].coeff;

            // Try to find a non-false unwatched literal to swap in.
            let replacement =
                self.weighted_unwatched_replacement_preserving_invariant(cid, falsified_coeff);

            if let WeightedReplacement::Swap(candidate_idx) = replacement {
                // Swap: move falsified literal out of watched set, bring
                // candidate in. Update watch lists incrementally.
                let candidate_lit = self.constraints[cid].terms[candidate_idx].lit;
                let candidate_coeff = self.constraints[cid].terms[candidate_idx].coeff;
                let old_max_watched_coeff = self.constraints[cid].max_watched_coeff;
                let old_max_unwatched_coeff = self.constraints[cid].max_unwatched_coeff;

                // Swap the terms.
                self.swap_constraint_terms(cid, watched_idx, candidate_idx);

                // The falsified term is now at candidate_idx (unwatched region).
                // The new term is at watched_idx (watched region).
                // Update watched_sum: remove falsified coeff, add candidate coeff.
                self.constraints[cid].watched_sum = self.constraints[cid]
                    .watched_sum
                    .saturating_sub(falsified_coeff)
                    .saturating_add(candidate_coeff);

                self.update_weighted_swap_coefficient_bounds(
                    cid,
                    watched_idx,
                    old_max_watched_coeff,
                    old_max_unwatched_coeff,
                    falsified_coeff,
                    candidate_coeff,
                );
                self.advance_weighted_replacement_scan_hint(cid, candidate_idx);

                let retained_old_watch = self.replace_watch_after_swap(
                    watch_idx,
                    cursor,
                    cid,
                    falsified_lit,
                    candidate_lit,
                );

                self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
                self.adjust_slack_for_non_false_watch(cid, candidate_coeff);
                // The swap changed slack and possibly `max_watched_coeff`:
                // re-evaluate blindness (P2d).
                self.arm_watch_all_if_blind(cid);

                // Even after a successful swap, check for propagation: the new
                // slack might still force some watched literals.
                let result = self.check_propagation(cid);
                if !matches!(result, PropResult::Ok) {
                    if let Some(stop) = self.handle_watch_result_queueing(
                        cid,
                        result,
                        retained_old_watch,
                        &mut cursor,
                        &mut first_propagation,
                    ) {
                        return stop;
                    }
                    continue;
                }
                if retained_old_watch {
                    cursor += 1;
                }
            } else {
                // No swap possible. The falsified literal stays in the watched
                // set but is false: if the settled slack leaves a watched
                // literal propagatable, arm full visibility so future
                // unwatched falsifications / un-falsifications stay
                // observable (P2d).
                self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
                self.arm_watch_all_if_blind(cid);

                let result = if matches!(replacement, WeightedReplacement::NoNonFalse) {
                    self.check_weighted_no_unwatched_non_false(cid)
                } else {
                    self.check_propagation(cid)
                };
                if !matches!(result, PropResult::Ok) {
                    // The falsified literal remains watched, so advance the cursor.
                    if let Some(stop) = self.handle_watch_result_queueing(
                        cid,
                        result,
                        true,
                        &mut cursor,
                        &mut first_propagation,
                    ) {
                        return stop;
                    }
                    continue;
                }
                cursor += 1;
            }
        }

        first_propagation.unwrap_or(PropResult::Ok)
    }

    /// Decrements the cached slack of every counting constraint watching
    /// `falsified_lit` for this falsification, recording a falsified-watch event
    /// for each (for backtrack repair). Idempotent within one falsification: a
    /// given `(falsified_lit, cid)` is decremented at most once because the
    /// literal becomes false exactly once between assign and unassign, and this
    /// runs once per `notify_falsified`. Non-counting constraints are untouched.
    fn decrement_counting_watches(&mut self, watch_idx: usize, falsified_lit: Lit) {
        let mut i = 0usize;
        while i < self.watches[watch_idx].len() {
            let cid = self.watches[watch_idx][i];
            i += 1;
            let Some(constraint) = self.constraints.get(cid) else {
                continue;
            };
            if !constraint.active || !constraint.counting {
                continue;
            }
            let falsified_coeff = self.counting_lit_coeff(cid, falsified_lit);
            if falsified_coeff == 0 {
                continue;
            }
            self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_coeff);
        }
    }

    pub(super) fn notify_falsified_interruptible<F>(
        &mut self,
        falsified_lit: Lit,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return self.interrupted_after_assignment();
        }

        let Some(watch_idx) = lit_index(falsified_lit) else {
            return PropResult::Ok;
        };
        if watch_idx >= self.watches.len() {
            return PropResult::Ok;
        }

        // Counting pre-pass (see `notify_falsified`): decrement every counting
        // constraint watching `falsified_lit` before the main loop, so their
        // trusted-exact slack reflects this falsification even if the loop aborts
        // early on a conflict. On interrupt the propagator rebuilds slack from
        // scratch, so the pre-pass decrements are harmless there.
        self.decrement_counting_watches(watch_idx, falsified_lit);

        let mut first_propagation: Option<PropResult> = None;
        let mut impacted_budget = STOP_POLL_INTERVAL;
        let mut cursor = 0usize;
        while cursor < self.watches[watch_idx].len() {
            if should_interrupt(should_stop, &mut impacted_budget) {
                return self.interrupted_after_assignment();
            }
            let cid = self.watches[watch_idx][cursor];
            if !self.constraints[cid].active {
                self.watches[watch_idx].swap_remove(cursor);
                continue;
            }

            if self.constraints[cid].shape == ConstraintShape::Clause {
                match self.notify_falsified_clause_interruptible(
                    watch_idx,
                    cursor,
                    cid,
                    falsified_lit,
                    should_stop,
                ) {
                    TernaryNotify::Advance => cursor += 1,
                    TernaryNotify::Stay => {}
                    TernaryNotify::Return { result, advance } => {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            advance,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                    }
                }
                continue;
            }

            if self.constraints[cid].shape == ConstraintShape::TernaryClause {
                match self.notify_falsified_ternary_clause(watch_idx, cursor, cid, falsified_lit) {
                    TernaryNotify::Advance => cursor += 1,
                    TernaryNotify::Stay => {}
                    TernaryNotify::Return { result, advance } => {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            advance,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                    }
                }
                continue;
            }

            if self.constraints[cid].shape == ConstraintShape::UnitCardinality {
                match self.notify_falsified_unit_cardinality_interruptible(
                    watch_idx,
                    cursor,
                    cid,
                    falsified_lit,
                    should_stop,
                ) {
                    TernaryNotify::Advance => cursor += 1,
                    TernaryNotify::Stay => {}
                    TernaryNotify::Return { result, advance } => {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            advance,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                    }
                }
                continue;
            }

            if self.constraints[cid].counting {
                // Slack was already decremented in the pre-pass; only check.
                if self.counting_lit_coeff(cid, falsified_lit) == 0 {
                    cursor += 1;
                    continue;
                }
                let result = self.check_counting_propagation(cid);
                if !matches!(result, PropResult::Ok) {
                    if let Some(stop) = self.handle_watch_result_queueing(
                        cid,
                        result,
                        true,
                        &mut cursor,
                        &mut first_propagation,
                    ) {
                        return stop;
                    }
                    continue;
                }
                cursor += 1;
                continue;
            }

            let watch_end = self.constraints[cid].watch_end;
            let mut found_idx = None;
            let mut falsified_watched_coeff = 0i128;
            let mut watched_budget = STOP_POLL_INTERVAL;
            for i in 0..watch_end {
                if should_interrupt(should_stop, &mut watched_budget) {
                    return self.interrupted_after_assignment();
                }
                if self.constraints[cid].terms[i].lit == falsified_lit {
                    if found_idx.is_none() {
                        found_idx = Some(i);
                    }
                    falsified_watched_coeff = falsified_watched_coeff
                        .saturating_add(self.constraints[cid].terms[i].coeff);
                }
            }

            let Some(watched_idx) = found_idx else {
                // See the non-interruptible variant: full-visibility rows get
                // a real exact check on unwatched falsifications (P2d).
                if self.constraints[cid].watch_all {
                    let result = self.check_propagation_interruptible(cid, should_stop);
                    if !matches!(result, PropResult::Ok) {
                        if let Some(stop) = self.handle_watch_result_queueing(
                            cid,
                            result,
                            true,
                            &mut cursor,
                            &mut first_propagation,
                        ) {
                            return stop;
                        }
                        continue;
                    }
                }
                cursor += 1;
                continue;
            };

            let falsified_coeff = self.constraints[cid].terms[watched_idx].coeff;

            let replacement = match self
                .weighted_unwatched_replacement_preserving_invariant_interruptible(
                    cid,
                    falsified_coeff,
                    should_stop,
                ) {
                Ok(replacement) => replacement,
                Err(()) => return self.interrupted_after_assignment(),
            };

            if let WeightedReplacement::Swap(candidate_idx) = replacement {
                let candidate_lit = self.constraints[cid].terms[candidate_idx].lit;
                let candidate_coeff = self.constraints[cid].terms[candidate_idx].coeff;
                let old_max_watched_coeff = self.constraints[cid].max_watched_coeff;
                let old_max_unwatched_coeff = self.constraints[cid].max_unwatched_coeff;

                self.swap_constraint_terms(cid, watched_idx, candidate_idx);
                self.constraints[cid].watched_sum = self.constraints[cid]
                    .watched_sum
                    .saturating_sub(falsified_coeff)
                    .saturating_add(candidate_coeff);

                self.update_weighted_swap_coefficient_bounds(
                    cid,
                    watched_idx,
                    old_max_watched_coeff,
                    old_max_unwatched_coeff,
                    falsified_coeff,
                    candidate_coeff,
                );
                self.advance_weighted_replacement_scan_hint(cid, candidate_idx);
                let retained_old_watch = self.replace_watch_after_swap(
                    watch_idx,
                    cursor,
                    cid,
                    falsified_lit,
                    candidate_lit,
                );
                self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
                self.adjust_slack_for_non_false_watch(cid, candidate_coeff);
                // See the non-interruptible variant (P2d).
                self.arm_watch_all_if_blind(cid);

                let result = self.check_propagation_interruptible(cid, should_stop);
                if !matches!(result, PropResult::Ok) {
                    if let Some(stop) = self.handle_watch_result_queueing(
                        cid,
                        result,
                        retained_old_watch,
                        &mut cursor,
                        &mut first_propagation,
                    ) {
                        return stop;
                    }
                    continue;
                }
                if retained_old_watch {
                    cursor += 1;
                }
            } else {
                // See the non-interruptible variant: arm full visibility when
                // the settled slack is blind (P2d).
                self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
                self.arm_watch_all_if_blind(cid);
                let result = if matches!(replacement, WeightedReplacement::NoNonFalse) {
                    self.check_weighted_no_unwatched_non_false_interruptible(cid, should_stop)
                } else {
                    self.check_propagation_interruptible(cid, should_stop)
                };
                if !matches!(result, PropResult::Ok) {
                    // The falsified literal remains watched, so advance the cursor.
                    if let Some(stop) = self.handle_watch_result_queueing(
                        cid,
                        result,
                        true,
                        &mut cursor,
                        &mut first_propagation,
                    ) {
                        return stop;
                    }
                    continue;
                }
                cursor += 1;
            }
        }

        first_propagation.unwrap_or(PropResult::Ok)
    }

    fn notify_falsified_clause(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        falsified_lit: Lit,
    ) -> TernaryNotify {
        debug_assert_eq!(self.constraints[cid].shape, ConstraintShape::Clause);

        let Some((watched_idx, falsified_watched_coeff)) =
            self.find_watched_falsified_occurrence(cid, falsified_lit)
        else {
            // Full-visibility rows treat an unwatched falsification as a real
            // event (exact re-check, no slack adjustment); see P2d notes.
            return self.watch_all_clause_notify(cid);
        };

        if let Some(candidate_idx) = self.first_non_false_clause_replacement(cid) {
            self.swap_clause_watch(
                watch_idx,
                cursor,
                cid,
                watched_idx,
                candidate_idx,
                falsified_lit,
                falsified_watched_coeff,
            );

            if self.clause_watched_region_has_two_non_false(cid) {
                return TernaryNotify::Stay;
            }

            let result = self.check_clause_propagation(cid);
            return if matches!(result, PropResult::Ok) {
                TernaryNotify::Stay
            } else {
                TernaryNotify::Return {
                    result,
                    advance: false,
                }
            };
        }

        // No non-false replacement: the falsified literal is stuck in the
        // watched region — arm full visibility (P2d).
        self.arm_watch_all(cid);
        self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
        let result = self.check_clause_propagation(cid);
        if matches!(result, PropResult::Ok) {
            TernaryNotify::Advance
        } else {
            TernaryNotify::Return {
                result,
                advance: true,
            }
        }
    }

    /// Full-visibility notification for a Clause-shaped row whose falsified
    /// literal lies outside the watched region: run the exact value-based
    /// clause check (no slack bookkeeping). Non-armed rows skip (stale watch
    /// entry).
    fn watch_all_clause_notify(&mut self, cid: usize) -> TernaryNotify {
        if !self.constraints[cid].watch_all {
            return TernaryNotify::Advance;
        }
        let result = self.check_clause_propagation(cid);
        if matches!(result, PropResult::Ok) {
            TernaryNotify::Advance
        } else {
            TernaryNotify::Return {
                result,
                advance: true,
            }
        }
    }

    fn notify_falsified_clause_interruptible<F>(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        falsified_lit: Lit,
        should_stop: &mut F,
    ) -> TernaryNotify
    where
        F: FnMut() -> bool,
    {
        debug_assert_eq!(self.constraints[cid].shape, ConstraintShape::Clause);

        let Some((watched_idx, falsified_watched_coeff)) =
            self.find_watched_falsified_occurrence(cid, falsified_lit)
        else {
            // See `watch_all_clause_notify` (P2d).
            return self.watch_all_clause_notify(cid);
        };

        let replacement =
            match self.first_non_false_clause_replacement_interruptible(cid, should_stop) {
                Ok(replacement) => replacement,
                Err(()) => {
                    return TernaryNotify::Return {
                        result: self.interrupted_after_assignment(),
                        advance: true,
                    }
                }
            };

        if let Some(candidate_idx) = replacement {
            self.swap_clause_watch(
                watch_idx,
                cursor,
                cid,
                watched_idx,
                candidate_idx,
                falsified_lit,
                falsified_watched_coeff,
            );

            if self.clause_watched_region_has_two_non_false(cid) {
                return TernaryNotify::Stay;
            }

            let result = self.check_clause_propagation_interruptible(cid, should_stop);
            return if matches!(result, PropResult::Ok) {
                TernaryNotify::Stay
            } else {
                TernaryNotify::Return {
                    result,
                    advance: false,
                }
            };
        }

        // See the non-interruptible variant: stuck false watch arms full
        // visibility (P2d).
        self.arm_watch_all(cid);
        self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
        let result = self.check_clause_propagation_interruptible(cid, should_stop);
        if matches!(result, PropResult::Ok) {
            TernaryNotify::Advance
        } else {
            TernaryNotify::Return {
                result,
                advance: true,
            }
        }
    }

    fn find_watched_falsified_occurrence(
        &self,
        cid: usize,
        falsified_lit: Lit,
    ) -> Option<(usize, i128)> {
        let watch_end = self.constraints[cid].watch_end;
        let mut found_idx = None;
        let mut falsified_watched_coeff = 0i128;
        for i in 0..watch_end {
            if self.constraints[cid].terms[i].lit == falsified_lit {
                if found_idx.is_none() {
                    found_idx = Some(i);
                }
                falsified_watched_coeff =
                    falsified_watched_coeff.saturating_add(self.constraints[cid].terms[i].coeff);
            }
        }
        found_idx.map(|idx| (idx, falsified_watched_coeff))
    }

    fn first_non_false_clause_replacement(&self, cid: usize) -> Option<usize> {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Clause);

        for candidate_idx in constraint.watch_end..constraint.terms.len() {
            let candidate = constraint.terms[candidate_idx];
            if self.assignment.value(candidate.lit) != LitValue::False {
                return Some(candidate_idx);
            }
        }

        None
    }

    fn first_non_false_clause_replacement_interruptible<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> Result<Option<usize>, ()>
    where
        F: FnMut() -> bool,
    {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Clause);

        let mut candidate_budget = STOP_POLL_INTERVAL;
        for candidate_idx in constraint.watch_end..constraint.terms.len() {
            if should_interrupt(should_stop, &mut candidate_budget) {
                return Err(());
            }
            let candidate = constraint.terms[candidate_idx];
            if self.assignment.value(candidate.lit) != LitValue::False {
                return Ok(Some(candidate_idx));
            }
        }

        Ok(None)
    }

    fn swap_clause_watch(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        watched_idx: usize,
        candidate_idx: usize,
        falsified_lit: Lit,
        falsified_watched_coeff: i128,
    ) {
        let candidate_lit = self.constraints[cid].terms[candidate_idx].lit;

        self.swap_constraint_terms(cid, watched_idx, candidate_idx);
        self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
        self.adjust_slack_for_non_false_watch(cid, 1);

        // Full-visibility rows keep every entry (P2d); see
        // `replace_watch_after_swap`.
        if self.constraints[cid].watch_all
            || self.constraints[cid].terms[..self.constraints[cid].watch_end]
                .iter()
                .any(|term| term.lit == falsified_lit)
        {
            self.add_watch(candidate_lit, cid);
        } else {
            self.watches[watch_idx].swap_remove(cursor);
            self.add_watch(candidate_lit, cid);
        }
    }

    fn notify_falsified_unit_cardinality(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        falsified_lit: Lit,
    ) -> TernaryNotify {
        debug_assert_eq!(
            self.constraints[cid].shape,
            ConstraintShape::UnitCardinality
        );

        let Some((watched_idx, falsified_watched_coeff)) =
            self.find_watched_falsified_occurrence(cid, falsified_lit)
        else {
            // See `watch_all_unit_cardinality_notify` (P2d).
            return self.watch_all_unit_cardinality_notify(cid);
        };

        let replacement = self.strongest_non_false_unwatched_replacement(cid);
        if let Some(candidate_idx) = replacement {
            let retained_old_watch = self.swap_unit_cardinality_watch(
                watch_idx,
                cursor,
                cid,
                watched_idx,
                candidate_idx,
                falsified_lit,
                falsified_watched_coeff,
            );
            if self.unit_cardinality_has_sufficient_watched_slack(cid) {
                #[cfg(test)]
                self.record_unit_cardinality_watch_shortcut();
                return if retained_old_watch {
                    TernaryNotify::Advance
                } else {
                    TernaryNotify::Stay
                };
            }

            let result = self.check_unit_cardinality_propagation(cid);
            return if matches!(result, PropResult::Ok) {
                if retained_old_watch {
                    TernaryNotify::Advance
                } else {
                    TernaryNotify::Stay
                }
            } else {
                TernaryNotify::Return {
                    result,
                    advance: retained_old_watch,
                }
            };
        }

        // No non-false replacement: stuck false watch arms full visibility
        // (P2d).
        self.arm_watch_all(cid);
        self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
        let result = self.check_unit_cardinality_no_unwatched_non_false(cid);
        if matches!(result, PropResult::Ok) {
            TernaryNotify::Advance
        } else {
            TernaryNotify::Return {
                result,
                advance: true,
            }
        }
    }

    /// Full-visibility notification for a UnitCardinality row whose falsified
    /// literal lies outside the watched region: run the exact count-based
    /// check (no slack bookkeeping). Non-armed rows skip (stale watch entry).
    fn watch_all_unit_cardinality_notify(&mut self, cid: usize) -> TernaryNotify {
        if !self.constraints[cid].watch_all {
            return TernaryNotify::Advance;
        }
        let result = self.check_unit_cardinality_propagation(cid);
        if matches!(result, PropResult::Ok) {
            TernaryNotify::Advance
        } else {
            TernaryNotify::Return {
                result,
                advance: true,
            }
        }
    }

    fn notify_falsified_unit_cardinality_interruptible<F>(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        falsified_lit: Lit,
        should_stop: &mut F,
    ) -> TernaryNotify
    where
        F: FnMut() -> bool,
    {
        debug_assert_eq!(
            self.constraints[cid].shape,
            ConstraintShape::UnitCardinality
        );

        let Some((watched_idx, falsified_watched_coeff)) =
            self.find_watched_falsified_occurrence(cid, falsified_lit)
        else {
            // See `watch_all_unit_cardinality_notify` (P2d).
            return self.watch_all_unit_cardinality_notify(cid);
        };

        let replacement =
            match self.strongest_non_false_unwatched_replacement_interruptible(cid, should_stop) {
                Ok(replacement) => replacement,
                Err(()) => {
                    return TernaryNotify::Return {
                        result: self.interrupted_after_assignment(),
                        advance: true,
                    }
                }
            };

        if let Some(candidate_idx) = replacement {
            let retained_old_watch = self.swap_unit_cardinality_watch(
                watch_idx,
                cursor,
                cid,
                watched_idx,
                candidate_idx,
                falsified_lit,
                falsified_watched_coeff,
            );
            if self.unit_cardinality_has_sufficient_watched_slack(cid) {
                #[cfg(test)]
                self.record_unit_cardinality_watch_shortcut();
                return if retained_old_watch {
                    TernaryNotify::Advance
                } else {
                    TernaryNotify::Stay
                };
            }

            let result = self.check_unit_cardinality_propagation_interruptible(cid, should_stop);
            return if matches!(result, PropResult::Ok) {
                if retained_old_watch {
                    TernaryNotify::Advance
                } else {
                    TernaryNotify::Stay
                }
            } else {
                TernaryNotify::Return {
                    result,
                    advance: retained_old_watch,
                }
            };
        }

        // See the non-interruptible variant: stuck false watch arms full
        // visibility (P2d).
        self.arm_watch_all(cid);
        self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
        let result = self.check_unit_cardinality_no_unwatched_non_false(cid);
        if matches!(result, PropResult::Ok) {
            TernaryNotify::Advance
        } else {
            TernaryNotify::Return {
                result,
                advance: true,
            }
        }
    }

    fn swap_unit_cardinality_watch(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        watched_idx: usize,
        candidate_idx: usize,
        falsified_lit: Lit,
        falsified_watched_coeff: i128,
    ) -> bool {
        let candidate_lit = self.constraints[cid].terms[candidate_idx].lit;
        let candidate_coeff = self.constraints[cid].terms[candidate_idx].coeff;
        debug_assert_eq!(candidate_coeff, 1);

        self.swap_constraint_terms(cid, watched_idx, candidate_idx);
        self.constraints[cid].watched_sum = self.constraints[cid]
            .watched_sum
            .saturating_sub(1)
            .saturating_add(candidate_coeff);
        debug_assert_eq!(self.constraints[cid].max_watched_coeff, 1);
        debug_assert_eq!(self.constraints[cid].max_unwatched_coeff, 1);
        let retained_old_watch =
            self.replace_watch_after_swap(watch_idx, cursor, cid, falsified_lit, candidate_lit);
        self.adjust_slack_for_falsified_watch(cid, falsified_lit, falsified_watched_coeff);
        self.adjust_slack_for_non_false_watch(cid, candidate_coeff);
        retained_old_watch
    }

    fn notify_falsified_ternary_clause(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        falsified_lit: Lit,
    ) -> TernaryNotify {
        debug_assert_eq!(self.constraints[cid].shape, ConstraintShape::TernaryClause);
        debug_assert_eq!(self.constraints[cid].terms.len(), 3);
        debug_assert_eq!(self.constraints[cid].watch_end, 2);

        let watched_idx = match (
            self.constraints[cid].terms[0].lit == falsified_lit,
            self.constraints[cid].terms[1].lit == falsified_lit,
        ) {
            (true, _) => 0,
            (false, true) => 1,
            // Unwatched (third-literal) falsification: a real event for
            // full-visibility rows (P2d); otherwise a stale watch entry.
            (false, false) => {
                if !self.constraints[cid].watch_all {
                    return TernaryNotify::Advance;
                }
                let result = self.check_ternary_clause_propagation(cid);
                return if matches!(result, PropResult::Ok) {
                    TernaryNotify::Advance
                } else {
                    TernaryNotify::Return {
                        result,
                        advance: true,
                    }
                };
            }
        };

        let candidate_lit = self.constraints[cid].terms[2].lit;
        let candidate_value = self.assignment.value(candidate_lit);
        if candidate_value == LitValue::False {
            // The falsified watch cannot be replaced (third literal false):
            // arm full visibility (P2d).
            self.arm_watch_all(cid);
        }
        if candidate_value != LitValue::False {
            let other_watched_lit = self.constraints[cid].terms[1 - watched_idx].lit;
            self.swap_constraint_terms(cid, watched_idx, 2);
            if self.constraints[cid].watch_all {
                // Full-visibility rows keep every entry (P2d): the swapped-out
                // literal's future falsifications must stay observable. The
                // retained entry means the cursor must advance, which the
                // `watch_all` third-literal path handles on revisit.
                self.add_watch(candidate_lit, cid);
                let result = self.check_ternary_clause_propagation(cid);
                return if matches!(result, PropResult::Ok) {
                    TernaryNotify::Advance
                } else {
                    TernaryNotify::Return {
                        result,
                        advance: true,
                    }
                };
            }
            self.watches[watch_idx].swap_remove(cursor);
            self.add_watch(candidate_lit, cid);

            if candidate_value == LitValue::True
                || self.assignment.value(other_watched_lit) != LitValue::False
            {
                return TernaryNotify::Stay;
            }

            let result = self.check_ternary_clause_propagation(cid);
            return if matches!(result, PropResult::Ok) {
                TernaryNotify::Stay
            } else {
                TernaryNotify::Return {
                    result,
                    advance: false,
                }
            };
        }

        let result = self.check_ternary_clause_propagation(cid);
        if matches!(result, PropResult::Ok) {
            TernaryNotify::Advance
        } else {
            TernaryNotify::Return {
                result,
                advance: true,
            }
        }
    }

    fn interrupted_after_assignment(&mut self) -> PropResult {
        self.needs_rebuild = true;
        PropResult::Interrupted
    }

    pub(super) fn strongest_non_false_unwatched_replacement(&self, cid: usize) -> Option<usize> {
        let constraint = &self.constraints[cid];
        let mut replacement = None;
        let mut replacement_coeff = 0i128;

        for candidate_idx in constraint.watch_end..constraint.terms.len() {
            #[cfg(test)]
            self.record_unwatched_replacement_candidate();

            let candidate = constraint.terms[candidate_idx];
            if replacement.is_some() && candidate.coeff <= replacement_coeff {
                continue;
            }
            #[cfg(test)]
            self.record_unwatched_replacement_value_check();
            if self.assignment.value(candidate.lit) == LitValue::False {
                continue;
            }
            if replacement.is_none() || candidate.coeff > replacement_coeff {
                replacement = Some(candidate_idx);
                replacement_coeff = candidate.coeff;
                if replacement_coeff == constraint.max_unwatched_coeff {
                    break;
                }
            }
        }

        replacement
    }

    fn weighted_unwatched_replacement_preserving_invariant(
        &self,
        cid: usize,
        falsified_coeff: i128,
    ) -> WeightedReplacement {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        let required_coeff = self.minimum_weighted_swap_candidate_coeff(cid, falsified_coeff);
        let scan_start = self.weighted_replacement_scan_start(cid);
        let mut saw_non_false = false;
        let mut best_non_false_coeff = 0i128;

        if let Some(candidate_idx) = self.weighted_replacement_in_range(
            constraint,
            scan_start..constraint.terms.len(),
            required_coeff,
            &mut saw_non_false,
            &mut best_non_false_coeff,
        ) {
            return WeightedReplacement::Swap(candidate_idx);
        }
        if scan_start > constraint.watch_end {
            if let Some(candidate_idx) = self.weighted_replacement_in_range(
                constraint,
                constraint.watch_end..scan_start,
                required_coeff,
                &mut saw_non_false,
                &mut best_non_false_coeff,
            ) {
                return WeightedReplacement::Swap(candidate_idx);
            }
        }

        if saw_non_false {
            WeightedReplacement::InsufficientNonFalse
        } else {
            WeightedReplacement::NoNonFalse
        }
    }

    pub(super) fn strongest_non_false_unwatched_replacement_interruptible<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> Result<Option<usize>, ()>
    where
        F: FnMut() -> bool,
    {
        let constraint = &self.constraints[cid];
        let mut replacement = None;
        let mut replacement_coeff = 0i128;
        let mut candidate_budget = STOP_POLL_INTERVAL;

        for candidate_idx in constraint.watch_end..constraint.terms.len() {
            if should_interrupt(should_stop, &mut candidate_budget) {
                return Err(());
            }
            #[cfg(test)]
            self.record_unwatched_replacement_candidate();

            let candidate = constraint.terms[candidate_idx];
            if replacement.is_some() && candidate.coeff <= replacement_coeff {
                continue;
            }
            #[cfg(test)]
            self.record_unwatched_replacement_value_check();
            if self.assignment.value(candidate.lit) == LitValue::False {
                continue;
            }
            if replacement.is_none() || candidate.coeff > replacement_coeff {
                replacement = Some(candidate_idx);
                replacement_coeff = candidate.coeff;
                if replacement_coeff == constraint.max_unwatched_coeff {
                    break;
                }
            }
        }

        Ok(replacement)
    }

    fn weighted_unwatched_replacement_preserving_invariant_interruptible<F>(
        &self,
        cid: usize,
        falsified_coeff: i128,
        should_stop: &mut F,
    ) -> Result<WeightedReplacement, ()>
    where
        F: FnMut() -> bool,
    {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        let required_coeff = self.minimum_weighted_swap_candidate_coeff(cid, falsified_coeff);
        let scan_start = self.weighted_replacement_scan_start(cid);
        let mut saw_non_false = false;
        let mut best_non_false_coeff = 0i128;
        let mut candidate_budget = STOP_POLL_INTERVAL;

        if let Some(candidate_idx) = self.weighted_replacement_in_range_interruptible(
            constraint,
            scan_start..constraint.terms.len(),
            required_coeff,
            &mut saw_non_false,
            &mut best_non_false_coeff,
            should_stop,
            &mut candidate_budget,
        )? {
            return Ok(WeightedReplacement::Swap(candidate_idx));
        }
        if scan_start > constraint.watch_end {
            if let Some(candidate_idx) = self.weighted_replacement_in_range_interruptible(
                constraint,
                constraint.watch_end..scan_start,
                required_coeff,
                &mut saw_non_false,
                &mut best_non_false_coeff,
                should_stop,
                &mut candidate_budget,
            )? {
                return Ok(WeightedReplacement::Swap(candidate_idx));
            }
        }

        Ok(if saw_non_false {
            WeightedReplacement::InsufficientNonFalse
        } else {
            WeightedReplacement::NoNonFalse
        })
    }

    fn weighted_replacement_scan_start(&self, cid: usize) -> usize {
        let constraint = &self.constraints[cid];
        if constraint.weighted_replacement_scan_hint > constraint.watch_end
            && constraint.weighted_replacement_scan_hint < constraint.terms.len()
        {
            constraint.weighted_replacement_scan_hint
        } else {
            constraint.watch_end
        }
    }

    fn advance_weighted_replacement_scan_hint(&mut self, cid: usize, candidate_idx: usize) {
        let constraint = &mut self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        debug_assert!(candidate_idx >= constraint.watch_end);

        let next_idx = candidate_idx.saturating_add(1);
        constraint.weighted_replacement_scan_hint = if next_idx < constraint.terms.len() {
            next_idx
        } else {
            constraint.watch_end
        };
    }

    fn weighted_replacement_in_range(
        &self,
        constraint: &PropConstraint,
        range: std::ops::Range<usize>,
        required_coeff: i128,
        saw_non_false: &mut bool,
        best_non_false_coeff: &mut i128,
    ) -> Option<usize> {
        for candidate_idx in range {
            #[cfg(test)]
            self.record_unwatched_replacement_candidate();

            let candidate = constraint.terms[candidate_idx];
            if *saw_non_false && candidate.coeff <= *best_non_false_coeff {
                continue;
            }
            #[cfg(test)]
            self.record_unwatched_replacement_value_check();
            if self.assignment.value(candidate.lit) == LitValue::False {
                continue;
            }

            *saw_non_false = true;
            *best_non_false_coeff = candidate.coeff;
            if candidate.coeff >= required_coeff {
                return Some(candidate_idx);
            }
        }

        None
    }

    fn weighted_replacement_in_range_interruptible<F>(
        &self,
        constraint: &PropConstraint,
        range: std::ops::Range<usize>,
        required_coeff: i128,
        saw_non_false: &mut bool,
        best_non_false_coeff: &mut i128,
        should_stop: &mut F,
        candidate_budget: &mut usize,
    ) -> Result<Option<usize>, ()>
    where
        F: FnMut() -> bool,
    {
        for candidate_idx in range {
            if should_interrupt(should_stop, candidate_budget) {
                return Err(());
            }
            #[cfg(test)]
            self.record_unwatched_replacement_candidate();

            let candidate = constraint.terms[candidate_idx];
            if *saw_non_false && candidate.coeff <= *best_non_false_coeff {
                continue;
            }
            #[cfg(test)]
            self.record_unwatched_replacement_value_check();
            if self.assignment.value(candidate.lit) == LitValue::False {
                continue;
            }

            *saw_non_false = true;
            *best_non_false_coeff = candidate.coeff;
            if candidate.coeff >= required_coeff {
                return Ok(Some(candidate_idx));
            }
        }

        Ok(None)
    }

    fn minimum_weighted_swap_candidate_coeff(&self, cid: usize, falsified_coeff: i128) -> i128 {
        let constraint = &self.constraints[cid];
        let max_unwatched_after_swap_upper_bound =
            constraint.max_unwatched_coeff.max(falsified_coeff);
        let required = constraint
            .degree
            .saturating_add(max_unwatched_after_swap_upper_bound)
            .saturating_sub(constraint.watched_sum.saturating_sub(falsified_coeff));
        required.max(0)
    }
}
