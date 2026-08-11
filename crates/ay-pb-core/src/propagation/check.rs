// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-constraint conflict/propagation checking for `PbPropagator`
//! (clause / unit-cardinality / weighted shapes, scalar + native paths).
//! Extracted from `propagation.rs`; these remain methods on
//! [`super::PbPropagator`].

use super::*;

impl PbPropagator {
    /// Checks a single constraint for conflict or propagation based on current slack.
    pub(super) fn check_propagation(&self, cid: usize) -> PropResult {
        match self.constraints[cid].shape {
            ConstraintShape::Clause => return self.check_clause_propagation(cid),
            ConstraintShape::TernaryClause => return self.check_ternary_clause_propagation(cid),
            ConstraintShape::UnitCardinality => {
                return self.check_unit_cardinality_propagation(cid)
            }
            ConstraintShape::Weighted => {}
        }

        if self.constraints[cid].counting {
            return self.check_counting_propagation(cid);
        }

        if self.native_code_helper_validation_enabled {
            self.record_native_helper_scalar_fallback();
        }

        #[cfg(test)]
        self.record_weighted_check();

        let slack = if self.weighted_has_sufficient_watched_slack(cid) {
            #[cfg(test)]
            self.record_weighted_slack_shortcut();
            return PropResult::Ok;
        } else {
            self.exact_weighted_slack(cid)
        };

        if slack < 0 {
            return PropResult::Conflict(self.conflict_reason(cid), cid);
        }

        for term in &self.constraints[cid].terms {
            if term.coeff > slack && self.assignment.value(term.lit) == LitValue::Unassigned {
                return PropResult::Propagated(
                    term.lit,
                    self.propagation_reason(cid, term.lit),
                    cid,
                );
            }
        }

        PropResult::Ok
    }

    /// Counting (RoundingSat-style) propagation for `Weighted` counting
    /// constraints: O(1)-amortized using the incrementally-maintained exact
    /// `slack` field instead of an O(terms) `exact_weighted_slack` rescan.
    ///
    /// For a counting constraint `watch_end == terms.len()`, so
    /// `constraint.slack == sum(coeff of non-false terms) - degree`, which is
    /// exactly the value `exact_weighted_slack` would recompute. This method
    /// therefore yields the SAME conflict/propagation decisions as the watched
    /// path, only faster. The propagation scan relies on the terms staying in
    /// descending-coefficient order (counting constraints never swap), so once a
    /// term has `coeff <= slack` every later term does too and the scan stops.
    pub(super) fn check_counting_propagation(&self, cid: usize) -> PropResult {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        debug_assert!(constraint.counting);
        debug_assert_eq!(constraint.watch_end, constraint.terms.len());
        // SOUNDNESS INVARIANT: the incrementally-maintained counting slack must
        // always equal the slack recomputed exactly from scratch. This is the
        // differential check the keystone hangs on; it runs in debug builds on
        // every counting check.
        debug_assert_eq!(
            constraint.slack,
            self.exact_weighted_slack(cid),
            "counting slack diverged from exact slack for cid {cid}"
        );

        if self.native_code_helper_validation_enabled {
            self.record_native_helper_scalar_fallback();
        }

        #[cfg(test)]
        self.record_weighted_check();

        let slack = constraint.slack;

        if slack < 0 {
            return PropResult::Conflict(self.conflict_reason(cid), cid);
        }

        // Terms are sorted descending by coefficient and never reordered for a
        // counting constraint, so the first `coeff <= slack` ends the scan: no
        // later term can have `coeff > slack`.
        for term in &constraint.terms {
            if term.coeff <= slack {
                break;
            }
            if self.assignment.value(term.lit) == LitValue::Unassigned {
                return PropResult::Propagated(
                    term.lit,
                    self.propagation_reason(cid, term.lit),
                    cid,
                );
            }
        }

        PropResult::Ok
    }

    pub(super) fn check_propagation_interruptible<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return PropResult::Interrupted;
        }

        match self.constraints[cid].shape {
            ConstraintShape::Clause => {
                return self.check_clause_propagation_interruptible(cid, should_stop)
            }
            ConstraintShape::TernaryClause => return self.check_ternary_clause_propagation(cid),
            ConstraintShape::UnitCardinality => {
                return self.check_unit_cardinality_propagation_interruptible(cid, should_stop);
            }
            ConstraintShape::Weighted => {}
        }

        if self.constraints[cid].counting {
            // Counting propagation is O(1)-amortized; no interruption needed.
            return self.check_counting_propagation(cid);
        }

        if self.native_code_helper_validation_enabled {
            self.record_native_helper_scalar_fallback();
        }

        #[cfg(test)]
        self.record_weighted_check();

        let slack = if self.weighted_has_sufficient_watched_slack(cid) {
            #[cfg(test)]
            self.record_weighted_slack_shortcut();
            return PropResult::Ok;
        } else {
            match self.exact_weighted_slack_interruptible(cid, should_stop) {
                Some(slack) => slack,
                None => return PropResult::Interrupted,
            }
        };

        if slack < 0 {
            return PropResult::Conflict(self.conflict_reason(cid), cid);
        }

        let mut poll_budget = STOP_POLL_INTERVAL;
        for term in &self.constraints[cid].terms {
            if should_interrupt(should_stop, &mut poll_budget) {
                return PropResult::Interrupted;
            }
            if term.coeff > slack && self.assignment.value(term.lit) == LitValue::Unassigned {
                return PropResult::Propagated(
                    term.lit,
                    self.propagation_reason(cid, term.lit),
                    cid,
                );
            }
        }

        PropResult::Ok
    }

    pub(super) fn check_weighted_no_unwatched_non_false(&self, cid: usize) -> PropResult {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        debug_assert!(constraint.terms[constraint.watch_end..]
            .iter()
            .all(|term| self.assignment.value(term.lit) == LitValue::False));

        // A counting constraint has an empty unwatched region (it always reaches
        // this no-replacement path). Use the O(1)-amortized exact-slack scan.
        if constraint.counting {
            return self.check_counting_propagation(cid);
        }

        if self.native_code_helper_validation_enabled {
            self.record_native_helper_scalar_fallback();
        }

        #[cfg(test)]
        {
            self.record_weighted_check();
            self.record_weighted_no_replacement_shortcut();
        }

        if self.weighted_has_sufficient_watched_slack(cid) {
            #[cfg(test)]
            self.record_weighted_slack_shortcut();
            return PropResult::Ok;
        }

        if constraint.slack < 0 {
            return PropResult::Conflict(self.conflict_reason(cid), cid);
        }

        for term in &constraint.terms[..constraint.watch_end] {
            if term.coeff > constraint.slack
                && self.assignment.value(term.lit) == LitValue::Unassigned
            {
                return PropResult::Propagated(
                    term.lit,
                    self.propagation_reason(cid, term.lit),
                    cid,
                );
            }
        }

        PropResult::Ok
    }

    pub(super) fn check_weighted_no_unwatched_non_false_interruptible<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return PropResult::Interrupted;
        }

        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        debug_assert!(constraint.terms[constraint.watch_end..]
            .iter()
            .all(|term| self.assignment.value(term.lit) == LitValue::False));

        if constraint.counting {
            return self.check_counting_propagation(cid);
        }

        if self.native_code_helper_validation_enabled {
            self.record_native_helper_scalar_fallback();
        }

        #[cfg(test)]
        {
            self.record_weighted_check();
            self.record_weighted_no_replacement_shortcut();
        }

        if self.weighted_has_sufficient_watched_slack(cid) {
            #[cfg(test)]
            self.record_weighted_slack_shortcut();
            return PropResult::Ok;
        }

        if constraint.slack < 0 {
            return PropResult::Conflict(self.conflict_reason(cid), cid);
        }

        let mut poll_budget = STOP_POLL_INTERVAL;
        for term in &constraint.terms[..constraint.watch_end] {
            if should_interrupt(should_stop, &mut poll_budget) {
                return PropResult::Interrupted;
            }
            if term.coeff > constraint.slack
                && self.assignment.value(term.lit) == LitValue::Unassigned
            {
                return PropResult::Propagated(
                    term.lit,
                    self.propagation_reason(cid, term.lit),
                    cid,
                );
            }
        }

        PropResult::Ok
    }

    pub(super) fn check_clause_propagation(&self, cid: usize) -> PropResult {
        #[cfg(test)]
        self.record_clause_check();

        if self.clause_watched_region_has_two_non_false(cid) {
            #[cfg(test)]
            self.record_clause_watch_shortcut();
            return PropResult::Ok;
        }

        let mut unassigned_lit = None;
        let mut false_lits = ReasonBuf::new();

        for term in &self.constraints[cid].terms {
            match self.assignment.value(term.lit) {
                LitValue::True => return PropResult::Ok,
                LitValue::Unassigned => {
                    if unassigned_lit.is_some() {
                        return PropResult::Ok;
                    }
                    unassigned_lit = Some(term.lit);
                }
                LitValue::False => false_lits.push_false(term.lit),
            }
        }

        if let Some(lit) = unassigned_lit {
            PropResult::Propagated(lit, false_lits.into_propagation_reason(lit), cid)
        } else {
            PropResult::Conflict(false_lits.into_reason(), cid)
        }
    }

    pub(super) fn check_clause_propagation_interruptible<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        #[cfg(test)]
        self.record_clause_check();

        if self.clause_watched_region_has_two_non_false(cid) {
            #[cfg(test)]
            self.record_clause_watch_shortcut();
            return PropResult::Ok;
        }

        let mut unassigned_lit = None;
        let mut false_lits = ReasonBuf::new();
        let mut poll_budget = STOP_POLL_INTERVAL;

        for term in &self.constraints[cid].terms {
            if should_interrupt(should_stop, &mut poll_budget) {
                return PropResult::Interrupted;
            }
            match self.assignment.value(term.lit) {
                LitValue::True => return PropResult::Ok,
                LitValue::Unassigned => {
                    if unassigned_lit.is_some() {
                        return PropResult::Ok;
                    }
                    unassigned_lit = Some(term.lit);
                }
                LitValue::False => false_lits.push_false(term.lit),
            }
        }

        if let Some(lit) = unassigned_lit {
            PropResult::Propagated(lit, false_lits.into_propagation_reason(lit), cid)
        } else {
            PropResult::Conflict(false_lits.into_reason(), cid)
        }
    }

    pub(super) fn check_ternary_clause_propagation(&self, cid: usize) -> PropResult {
        #[cfg(test)]
        self.record_clause_check();

        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::TernaryClause);
        debug_assert_eq!(constraint.terms.len(), 3);

        if constraint.watch_end == 2 {
            let first = self.assignment.value(constraint.terms[0].lit);
            let second = self.assignment.value(constraint.terms[1].lit);
            if first != LitValue::False && second != LitValue::False {
                #[cfg(test)]
                self.record_clause_watch_shortcut();
                return PropResult::Ok;
            }
        }

        let mut unassigned_lit = None;
        let mut false_lits = ReasonBuf::new();
        for term in &constraint.terms {
            match self.assignment.value(term.lit) {
                LitValue::True => return PropResult::Ok,
                LitValue::Unassigned => {
                    if unassigned_lit.is_some() {
                        return PropResult::Ok;
                    }
                    unassigned_lit = Some(term.lit);
                }
                // A 3-literal clause has distinct literals, so de-duplication is a
                // no-op here; this matches the old plain `push` ordering.
                LitValue::False => false_lits.push_false(term.lit),
            }
        }

        if let Some(lit) = unassigned_lit {
            PropResult::Propagated(lit, false_lits.into_propagation_reason(lit), cid)
        } else {
            PropResult::Conflict(false_lits.into_reason(), cid)
        }
    }

    pub(super) fn clause_watched_region_has_two_non_false(&self, cid: usize) -> bool {
        let constraint = &self.constraints[cid];
        if constraint.shape != ConstraintShape::Clause || constraint.watch_end < 2 {
            return false;
        }

        let mut non_false = 0usize;
        for term in &constraint.terms[..constraint.watch_end] {
            if self.assignment.value(term.lit) != LitValue::False {
                non_false += 1;
                if non_false == 2 {
                    return true;
                }
            }
        }
        false
    }

    pub(super) fn check_unit_cardinality_propagation(&self, cid: usize) -> PropResult {
        if self.should_try_native_code_helper() {
            match self.unit_cardinality_native_code_helper(cid) {
                NativeHelperAttempt::Evaluated { result, source } => {
                    self.record_native_helper_evaluation();
                    let scalar = self.check_unit_cardinality_propagation_scalar(cid);
                    return self.validated_native_code_helper_result(result, scalar, source);
                }
                NativeHelperAttempt::TrustedNativeOk => {
                    self.record_native_helper_evaluation();
                    self.record_native_helper_native_apply_confirmation();
                    return PropResult::Ok;
                }
                NativeHelperAttempt::Fallback => {
                    self.record_native_helper_evaluation();
                    self.record_native_helper_scalar_fallback();
                    return self.check_unit_cardinality_propagation_scalar(cid);
                }
                NativeHelperAttempt::Interrupted => return PropResult::Interrupted,
            }
        }

        if self.native_code_helper_validation_enabled && self.native_code_helper_deopted.get() {
            self.record_native_helper_scalar_fallback();
        }

        self.check_unit_cardinality_propagation_scalar(cid)
    }

    fn check_unit_cardinality_propagation_scalar(&self, cid: usize) -> PropResult {
        #[cfg(test)]
        self.record_unit_cardinality_check();

        if self.unit_cardinality_has_sufficient_watched_slack(cid) {
            #[cfg(test)]
            self.record_unit_cardinality_slack_shortcut();
            return PropResult::Ok;
        }

        #[cfg(test)]
        self.record_unit_cardinality_full_scan();

        let constraint = &self.constraints[cid];
        let mut non_false_count = 0i128;
        let mut first_unassigned = None;
        let mut false_lits = ReasonBuf::new();

        for term in &constraint.terms {
            #[cfg(test)]
            self.record_unit_cardinality_scan_term();

            match self.assignment.value(term.lit) {
                LitValue::True => {
                    non_false_count = non_false_count.saturating_add(1);
                    if non_false_count > constraint.degree {
                        return PropResult::Ok;
                    }
                }
                LitValue::Unassigned => {
                    non_false_count = non_false_count.saturating_add(1);
                    if non_false_count > constraint.degree {
                        return PropResult::Ok;
                    }
                    if first_unassigned.is_none() {
                        first_unassigned = Some(term.lit);
                    }
                }
                LitValue::False => false_lits.push_false(term.lit),
            }
        }

        if non_false_count < constraint.degree {
            return PropResult::Conflict(false_lits.into_reason(), cid);
        }

        if non_false_count == constraint.degree {
            if let Some(lit) = first_unassigned {
                return PropResult::Propagated(lit, false_lits.into_propagation_reason(lit), cid);
            }
        }

        PropResult::Ok
    }

    pub(super) fn check_unit_cardinality_propagation_interruptible<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if self.should_try_native_code_helper() {
            match self.unit_cardinality_native_code_helper_interruptible(cid, should_stop) {
                NativeHelperAttempt::Evaluated { result, source } => {
                    if matches!(result, PropResult::Interrupted) {
                        return result;
                    }
                    self.record_native_helper_evaluation();
                    let scalar = self
                        .check_unit_cardinality_propagation_interruptible_scalar(cid, should_stop);
                    if matches!(scalar, PropResult::Interrupted) {
                        return scalar;
                    }
                    return self.validated_native_code_helper_result(result, scalar, source);
                }
                NativeHelperAttempt::TrustedNativeOk => {
                    if should_stop() {
                        return PropResult::Interrupted;
                    }
                    self.record_native_helper_evaluation();
                    self.record_native_helper_native_apply_confirmation();
                    return PropResult::Ok;
                }
                NativeHelperAttempt::Fallback => {
                    self.record_native_helper_evaluation();
                    self.record_native_helper_scalar_fallback();
                    return self
                        .check_unit_cardinality_propagation_interruptible_scalar(cid, should_stop);
                }
                NativeHelperAttempt::Interrupted => return PropResult::Interrupted,
            }
        }

        if self.native_code_helper_validation_enabled && self.native_code_helper_deopted.get() {
            self.record_native_helper_scalar_fallback();
        }

        self.check_unit_cardinality_propagation_interruptible_scalar(cid, should_stop)
    }

    fn check_unit_cardinality_propagation_interruptible_scalar<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        #[cfg(test)]
        self.record_unit_cardinality_check();

        if self.unit_cardinality_has_sufficient_watched_slack(cid) {
            #[cfg(test)]
            self.record_unit_cardinality_slack_shortcut();
            return PropResult::Ok;
        }

        #[cfg(test)]
        self.record_unit_cardinality_full_scan();

        let constraint = &self.constraints[cid];
        let mut non_false_count = 0i128;
        let mut first_unassigned = None;
        let mut false_lits = ReasonBuf::new();
        let mut poll_budget = STOP_POLL_INTERVAL;

        for term in &constraint.terms {
            if should_interrupt(should_stop, &mut poll_budget) {
                return PropResult::Interrupted;
            }
            #[cfg(test)]
            self.record_unit_cardinality_scan_term();

            match self.assignment.value(term.lit) {
                LitValue::True => {
                    non_false_count = non_false_count.saturating_add(1);
                    if non_false_count > constraint.degree {
                        return PropResult::Ok;
                    }
                }
                LitValue::Unassigned => {
                    non_false_count = non_false_count.saturating_add(1);
                    if non_false_count > constraint.degree {
                        return PropResult::Ok;
                    }
                    if first_unassigned.is_none() {
                        first_unassigned = Some(term.lit);
                    }
                }
                LitValue::False => false_lits.push_false(term.lit),
            }
        }

        if non_false_count < constraint.degree {
            return PropResult::Conflict(false_lits.into_reason(), cid);
        }

        if non_false_count == constraint.degree {
            if let Some(lit) = first_unassigned {
                return PropResult::Propagated(lit, false_lits.into_propagation_reason(lit), cid);
            }
        }

        PropResult::Ok
    }
}
