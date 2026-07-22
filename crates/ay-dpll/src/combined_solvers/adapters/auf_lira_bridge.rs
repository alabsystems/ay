// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen bridge methods for AUFLIRA combined solver.
//!
//! Cross-sort propagation, interface bridge evaluation, subsolver
//! checking, and fixpoint handling. The struct definition, constructor,
//! and `TheorySolver` trait impl are in `auf_lira.rs`.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Constant, SplitRequest, TermData, TermId, TheoryLit, TheoryResult, TheorySolver};
use ay_lra::Bound;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::auf_lira::{
    AufLiraCrossSortTrailEntry, AufLiraSolver, PropagationKind, SubsolverCheckResult,
};
use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, discover_model_equality, drain_equalities_for_propagation,
    forward_non_sat, propagate_array_index_info, propagate_equalities_to, triage_lia_result,
    triage_lra_result_deferred,
};
use crate::combined_solvers::interface_bridge::{
    evaluate_arith_term_with_reasons, evaluate_real_arith_term_with_reasons,
    lia_get_int_value_with_reasons, lra_get_real_value_with_reasons,
};

impl AufLiraSolver<'_> {
    fn integer_lower_bound(bound: &Bound) -> BigInt {
        if bound.strict {
            bound.value.floor() + BigInt::from(1)
        } else {
            bound.value.ceil()
        }
    }

    fn integer_upper_bound(bound: &Bound) -> BigInt {
        if bound.strict {
            bound.value.ceil() - BigInt::from(1)
        } else {
            bound.value.floor()
        }
    }

    fn collect_bound_reasons(lower: &Bound, upper: &Bound) -> Vec<TheoryLit> {
        let mut reasons = Vec::new();
        for (term, val) in lower.reason_pairs() {
            if !term.is_sentinel() {
                reasons.push(TheoryLit::new(term, val));
            }
        }
        for (term, val) in upper.reason_pairs() {
            if !term.is_sentinel() && !reasons.iter().any(|r| r.term == term) {
                reasons.push(TheoryLit::new(term, val));
            }
        }
        reasons
    }

    fn exact_integer_reasons(
        value: &BigInt,
        lower: Option<&Bound>,
        upper: Option<&Bound>,
    ) -> Option<Vec<TheoryLit>> {
        let (lower, upper) = (lower?, upper?);
        let min_value = Self::integer_lower_bound(lower);
        let max_value = Self::integer_upper_bound(upper);
        if min_value != *value || max_value != *value {
            return None;
        }
        let reasons = Self::collect_bound_reasons(lower, upper);
        if reasons.is_empty() {
            None
        } else {
            Some(reasons)
        }
    }

    fn choose_cross_sort_split_value(
        lower: Option<&Bound>,
        upper: Option<&Bound>,
        fallback_value: &BigRational,
    ) -> BigRational {
        if let (Some(lower), Some(upper)) = (lower, upper) {
            let lo = Self::integer_lower_bound(lower);
            let hi = Self::integer_upper_bound(upper);
            if lo < hi {
                return BigRational::from((lo + hi) / BigInt::from(2));
            }
        }

        fallback_value.clone()
    }

    /// Returns `Ok((lia_is_unknown, lra_is_unknown, deferred_lia, deferred_lra))` or early-returns a conflict.
    ///
    /// Cross-sort propagation (#5955) runs at N-O loop level after sub-solver checks.
    ///
    /// #7448: Use triage_lra_result_deferred instead of triage_lra_result.
    /// triage_lra_result early-returns NeedModelEquality/NeedDisequalitySplit,
    /// which skips cross-sort propagation entirely. For Big-M patterns
    /// like (* 1000000.0 (to_real phase)), LRA discovers model equalities
    /// before cross-sort can bridge LIA's integer bounds to LRA. Without
    /// deferral, the loop cycles NeedModelEquality → encode → re-check
    /// without ever propagating phase's integrality, producing Unknown.
    pub(super) fn check_subsolvers(&mut self) -> SubsolverCheckResult {
        // LIA: defer splits to fixpoint so cross-sort, EUF, and interface bridge
        // propagation all run before the split escapes to the pipeline (#7448).
        // Without deferral, LIA NeedSplit bypasses all N-O propagation channels,
        // causing the outer split loop to oscillate on cross-sort variables.
        let lia_result = self.lia.check();
        let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
        let (deferred_lia_result, lia_early) = triage_lia_result(lia_result);
        if let Some(early) = lia_early {
            return Err(Box::new(early));
        }

        // LRA: continue N-O loop on Unknown — EUF/LIA equalities may help (#4945).
        //
        // #7448: Use triage_lra_result_deferred instead of triage_lra_result.
        // Deferring NeedModelEquality/NeedDisequalitySplit allows cross-sort
        // propagation to bridge LIA's integer bounds to LRA before the split
        // escapes to the pipeline.
        let lra_result = self.lra.check();
        let lra_is_unknown = matches!(&lra_result, TheoryResult::Unknown);
        let (deferred_lra_result, lra_early) = triage_lra_result_deferred(lra_result);
        if let Some(early) = lra_early {
            return Err(Box::new(early));
        }

        // EUF consistency check before cross-theory propagation.
        let euf_check = self.euf.check();
        if let Some(result) = forward_non_sat(euf_check) {
            return Err(Box::new(result));
        }

        Ok((
            lia_is_unknown,
            lra_is_unknown,
            deferred_lia_result,
            deferred_lra_result,
        ))
    }

    pub(super) fn propagate_theory_equalities(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Result<(usize, usize, usize, usize), Box<TheoryResult>> {
        let lia_eq_count = propagate_equalities_to(
            &mut self.lia,
            &mut self.euf,
            debug,
            "AUFLIRA-LIA",
            iteration,
        )
        .map_err(Box::new)?;
        let lra_eq_count = propagate_equalities_to(
            &mut self.lra,
            &mut self.euf,
            debug,
            "AUFLIRA-LRA",
            iteration,
        )
        .map_err(Box::new)?;
        let euf_to_arith_count = self
            .propagate_euf_arith_facts(debug, iteration)
            .map_err(Box::new)?;

        // Include disequality counts in the EUF→arith totals so the fixpoint
        // convergence check sees new information flow (#8455, #8469).
        Ok((lia_eq_count, lra_eq_count, euf_to_arith_count, 0))
    }

    fn propagate_euf_arith_facts(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Result<usize, TheoryResult> {
        let eq_result =
            drain_equalities_for_propagation(&mut self.euf, debug, "AUFLIRA-EUF", iteration)?;
        let mut count = 0;

        for eq in eq_result.equalities {
            match (self.terms.sort(eq.lhs), self.terms.sort(eq.rhs)) {
                (ay_core::Sort::Int, ay_core::Sort::Int) => {
                    self.lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                    count += 1;
                }
                (ay_core::Sort::Real, ay_core::Sort::Real) => {
                    if self.real_equality_is_lia_relevant(eq.lhs, eq.rhs) {
                        self.lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                    }
                    self.lra.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                    count += 1;
                }
                _ => {}
            }
        }

        for diseq in eq_result.disequalities {
            match (self.terms.sort(diseq.lhs), self.terms.sort(diseq.rhs)) {
                (ay_core::Sort::Int, ay_core::Sort::Int) => {
                    self.lia
                        .assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
                    count += 1;
                }
                (ay_core::Sort::Real, ay_core::Sort::Real) => {
                    if self.real_equality_is_lia_relevant(diseq.lhs, diseq.rhs) {
                        self.lia
                            .assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
                    }
                    self.lra
                        .assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
                    count += 1;
                }
                _ => {}
            }
        }

        Ok(count)
    }

    fn real_equality_is_lia_relevant(&self, lhs: TermId, rhs: TermId) -> bool {
        self.term_mentions_to_real(lhs)
            || self.term_mentions_to_real(rhs)
            || (!self.term_mentions_array_sort(lhs)
                && !self.term_mentions_array_sort(rhs)
                && (self.term_mentions_int_sort(lhs) || self.term_mentions_int_sort(rhs)))
    }

    fn term_mentions_to_real(&self, term: TermId) -> bool {
        let mut stack = vec![term];
        while let Some(current) = stack.pop() {
            if let TermData::App(sym, args) = self.terms.get(current) {
                if sym.name() == "to_real" {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
        }
        false
    }

    fn term_mentions_array_sort(&self, term: TermId) -> bool {
        let mut stack = vec![term];
        while let Some(current) = stack.pop() {
            if matches!(self.terms.sort(current), ay_core::Sort::Array(_)) {
                return true;
            }
            if let TermData::App(_, args) = self.terms.get(current) {
                stack.extend(args.iter().copied());
            }
        }
        false
    }

    fn term_mentions_int_sort(&self, term: TermId) -> bool {
        let mut stack = vec![term];
        while let Some(current) = stack.pop() {
            if matches!(self.terms.sort(current), ay_core::Sort::Int) {
                return true;
            }
            if let TermData::App(_, args) = self.terms.get(current) {
                stack.extend(args.iter().copied());
            }
        }
        false
    }

    /// Evaluate Int-sorted interface terms under LIA model and propagate to EUF (#5227).
    pub(super) fn propagate_int_interface_bridge(&mut self, debug: bool) -> usize {
        let lia = &self.lia;
        let (new_eqs, _speculative) = self.interface.evaluate_and_propagate(
            self.terms,
            &|t| lia_get_int_value_with_reasons(lia, t),
            debug,
            "AUFLIRA",
        );
        let count = new_eqs.len();
        for eq in &new_eqs {
            self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            self.lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
        }
        count
    }

    /// Evaluate Real-sorted interface terms under LRA model and propagate to EUF (#5227).
    pub(super) fn propagate_real_interface_bridge(&mut self, debug: bool) -> usize {
        let lra = &self.lra;
        let (new_eqs, _speculative) = self.interface.evaluate_and_propagate_real(
            self.terms,
            &|t| lra_get_real_value_with_reasons(lra, t),
            debug,
            "AUFLIRA",
        );
        let count = new_eqs.len();
        for eq in &new_eqs {
            self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
        }
        count
    }

    pub(super) fn propagate_array_index_relations(&mut self) -> Result<bool, Box<TheoryResult>> {
        let mut array_progress = false;
        {
            let terms = self.terms;
            let lia = &self.lia;
            // #read-congruence-quantified-scope: the LIRA bridge keeps the
            // read-congruence pair obligations unconditionally (`true`) — it
            // predates the quantified-pipeline scoping and no regression is
            // attributed to it; only `TheoryCombiner`-routed AUF solves thread
            // the executor's flag.
            if let Some(result) = propagate_array_index_info(
                terms,
                &mut self.arrays,
                &mut self.euf,
                |t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_arith_term_with_reasons(
                        terms,
                        &|var| lia_get_int_value_with_reasons(lia, var),
                        t,
                        &mut reasons,
                    )?;
                    Some((value, reasons))
                },
                true,
            ) {
                match result {
                    TheoryResult::Sat => array_progress = true,
                    other => return Err(Box::new(other)),
                }
            }
        }
        {
            let terms = self.terms;
            let lra = &self.lra;
            if let Some(result) = propagate_array_index_info(
                terms,
                &mut self.arrays,
                &mut self.euf,
                |t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_real_arith_term_with_reasons(
                        terms,
                        &|var| lra_get_real_value_with_reasons(lra, var),
                        t,
                        &mut reasons,
                    )?;
                    Some((value, reasons))
                },
                true,
            ) {
                match result {
                    TheoryResult::Sat => array_progress = true,
                    other => return Err(Box::new(other)),
                }
            }
        }
        Ok(array_progress)
    }

    /// Propagate LIA integer values to LRA for shared variables (#5955).
    ///
    /// Ported from `LiraSolver::propagate_cross_sort_values` (#4915, #5947).
    /// Returns `(propagation_count, optional_split_request)`.
    pub(super) fn propagate_cross_sort_values(
        &mut self,
        debug: bool,
    ) -> (usize, Option<TheoryResult>) {
        let lia_lra = self.lia.lra_solver();
        let lra_vars = self.lra.term_to_var();
        let to_int_term_ids: HashSet<TermId> = self
            .lra
            .to_int_terms()
            .iter()
            .filter_map(|(to_int_var, _)| self.lra.var_term_id(*to_int_var))
            .collect();
        // #6217: When to_int terms exist, suppress cross-sort splits to avoid
        // conflict with floor axiom handling in propagate_to_int_values.
        let has_to_int = !self.lra.to_int_terms().is_empty();

        let mut to_propagate: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();
        let mut to_propagate_bounds: Vec<(TermId, Option<Bound>, Option<Bound>)> = Vec::new();
        let mut need_split: Option<(TermId, BigRational)> = None;

        for (&term, _) in lia_lra.term_to_var() {
            // Only propagate for Int-sorted terms that also appear in a literal
            // actually asserted to the Real side (#6198, ported from #6290).
            if !matches!(self.terms.sort(term), ay_core::Sort::Int) {
                continue;
            }
            // #8790: `(to_int x)` is owned by the Real side's floor-axiom
            // propagation. Splitting it here can create non-converging
            // integer-style branches over an auxiliary Real term.
            if to_int_term_ids.contains(&term) {
                continue;
            }
            if !self.asserted_real_int_terms.contains(&term) || !lra_vars.contains_key(&term) {
                continue;
            }
            if let Some((value, reasons)) = lia_lra.get_value_with_reasons(term) {
                if !value.is_integer() {
                    continue;
                }
                let bounds = lia_lra.get_bounds(term);
                let key = value.to_integer();
                let tight_reasons = if reasons.is_empty() {
                    bounds.as_ref().and_then(|(lower, upper)| {
                        Self::exact_integer_reasons(&key, lower.as_ref(), upper.as_ref())
                    })
                } else {
                    Some(reasons.clone())
                };
                let wants_tight = tight_reasons.is_some();
                let new_kind = if wants_tight {
                    PropagationKind::Tight
                } else {
                    PropagationKind::Bounds
                };
                let prev_kind = self
                    .propagated_cross_sort
                    .get(&(term, key.clone()))
                    .copied();
                match prev_kind {
                    Some(PropagationKind::Tight) => continue,
                    Some(PropagationKind::Bounds) if !wants_tight => continue,
                    _ => {}
                }
                self.propagated_cross_sort
                    .insert((term, key.clone()), new_kind);
                self.cross_sort_trail
                    .push(AufLiraCrossSortTrailEntry::Propagated(
                        term,
                        key.clone(),
                        prev_kind,
                    ));
                if let Some(tight_reasons) = tight_reasons {
                    to_propagate.push((term, value, tight_reasons));
                } else {
                    // #5947 soundness fix: bounds not tight. Propagate individual
                    // bounds (not the value) and request a split.
                    if let Some((lower, upper)) = bounds {
                        if lower.is_none() && upper.is_none() {
                            // No direct bounds are available to forward to LRA.
                            // Only request the fallback split when the simplex
                            // tableau has implied bounds that the branch can
                            // refine; otherwise the same split repeats without
                            // progress.
                            if !has_to_int
                                && lia_lra.has_implied_bounds(term)
                                && need_split.is_none()
                            {
                                need_split = Some((
                                    term,
                                    Self::choose_cross_sort_split_value(None, None, &value),
                                ));
                            }
                            continue;
                        }
                        // When both bounds already pin the integer value exactly,
                        // bounds-only propagation is enough and no split can refine it.
                        let interval_is_singleton = match (lower.as_ref(), upper.as_ref()) {
                            (Some(lo_b), Some(up_b)) => {
                                Self::integer_lower_bound(lo_b) == key
                                    && Self::integer_upper_bound(up_b) == key
                            }
                            _ => false,
                        };
                        let split_value = Self::choose_cross_sort_split_value(
                            lower.as_ref(),
                            upper.as_ref(),
                            &value,
                        );
                        to_propagate_bounds.push((term, lower, upper));
                        if !has_to_int && !interval_is_singleton && need_split.is_none() {
                            need_split = Some((term, split_value));
                        }
                    }
                }
            }
        }

        let count = to_propagate.len() + to_propagate_bounds.len();
        self.apply_cross_sort_propagations(to_propagate, to_propagate_bounds, debug);
        let split = need_split.map(|s| Self::make_cross_sort_split(s.0, s.1, debug));
        (count, split)
    }

    /// Apply collected cross-sort propagations to LRA.
    fn apply_cross_sort_propagations(
        &mut self,
        tight: Vec<(TermId, BigRational, Vec<TheoryLit>)>,
        bounds: Vec<(TermId, Option<Bound>, Option<Bound>)>,
        debug: bool,
    ) {
        for (term, value, reasons) in tight {
            if debug {
                safe_eprintln!(
                    "[N-O AUFLIRA] Cross-sort value: term {:?} = {} ({} reasons)",
                    term,
                    value,
                    reasons.len()
                );
            }
            self.lra.assert_tight_bound(term, &value, &reasons);
        }
        for (term, lower, upper) in bounds {
            if debug {
                safe_eprintln!(
                    "[N-O AUFLIRA] Cross-sort bounds: term {:?} lower={} upper={}",
                    term,
                    lower.is_some(),
                    upper.is_some()
                );
            }
            self.lra
                .assert_cross_sort_bounds(term, lower.as_ref(), upper.as_ref());
        }
    }

    /// Handle fixpoint: final result after N-O convergence.
    /// Returns `Some(result)` to return from check, `None` to continue the N-O loop.
    pub(super) fn handle_fixpoint(
        &mut self,
        debug: bool,
        lia_is_unknown: bool,
        lra_is_unknown: bool,
        deferred_lia_result: Option<TheoryResult>,
        deferred_lra_result: Option<TheoryResult>,
        pending_cross_sort_split: Option<TheoryResult>,
    ) -> Option<TheoryResult> {
        if lia_is_unknown || lra_is_unknown {
            return Some(TheoryResult::Unknown);
        }
        // #7448: return deferred LIA results (NeedSplit, NeedDisequalitySplit)
        // at fixpoint, after cross-sort, EUF, and interface bridge propagation
        // have all had a chance to run. Without deferral, LIA NeedSplit bypasses
        // all N-O propagation channels, causing the outer split loop to oscillate.
        if let Some(lia_deferred) = deferred_lia_result {
            return Some(lia_deferred);
        }
        // #5947: shared Int vars must be split before speculative LRA model
        // equalities. Otherwise the equality round-trip can short-circuit the
        // split loop and leave the Real side with only loose cross-sort bounds.
        if let Some(split) = pending_cross_sort_split {
            return Some(split);
        }
        // #7448: return deferred LRA results (NeedModelEquality,
        // NeedDisequalitySplit, NeedExpressionSplit) at fixpoint,
        // after cross-sort propagation has had a chance to run.
        if let Some(lra_deferred) = deferred_lra_result {
            return Some(lra_deferred);
        }
        // Model equality discovery for non-convex theory combination (#4906).
        // #7462: Use evaluate_arith_term_with_reasons (recursive expression
        // evaluation) instead of lia_get_int_value_with_reasons (direct variable
        // lookup). Without recursive evaluation, compound expressions like (+ p 3)
        // that are arguments to UF applications cannot be evaluated, so two UF
        // args that simplify to the same value (e.g., p+3=5 and q+1=5) are never
        // grouped together, and the pairwise bridge misses the equality.
        // Int-sorted terms via LIA:
        {
            let lia = &self.lia;
            let terms = self.terms;
            if let Some(model_eq) = discover_model_equality(
                self.interface.sorted_arith_terms().into_iter(),
                self.terms,
                &self.euf,
                &|t| {
                    let mut reasons = Vec::new();
                    evaluate_arith_term_with_reasons(
                        terms,
                        &|var| lia_get_int_value_with_reasons(lia, var),
                        t,
                        &mut reasons,
                    )
                },
                &[ay_core::Sort::Int],
                debug,
                "AUFLIRA",
            ) {
                return Some(model_eq);
            }
        }
        // Real-sorted terms via LRA:
        {
            let lra = &self.lra;
            let terms = self.terms;
            if let Some(model_eq) = discover_model_equality(
                self.interface.sorted_arith_terms().into_iter(),
                self.terms,
                &self.euf,
                &|t| {
                    let mut reasons = Vec::new();
                    evaluate_real_arith_term_with_reasons(
                        terms,
                        &|var| lra_get_real_value_with_reasons(lra, var),
                        t,
                        &mut reasons,
                    )
                },
                &[ay_core::Sort::Real],
                debug,
                "AUFLIRA",
            ) {
                return Some(model_eq);
            }
        }
        // Deferred array checks at fixpoint (#6282 Packet 2).
        let final_result = self.arrays.final_check();
        if let Some(result) = forward_non_sat(final_result) {
            return Some(result);
        }
        assert_fixpoint_convergence(
            "AUFLIRA",
            &mut [
                &mut self.lia,
                &mut self.lra,
                &mut self.euf,
                &mut self.arrays,
            ],
        );
        Some(TheoryResult::Sat)
    }

    /// Build a split request for a non-tight shared variable (#5947).
    pub(super) fn make_cross_sort_split(
        term: TermId,
        value: BigRational,
        debug: bool,
    ) -> TheoryResult {
        let int_val = value.to_integer();
        let half = BigRational::new(1.into(), 2.into());
        let split_point = value + &half;
        if debug {
            safe_eprintln!(
                "[N-O AUFLIRA] Requesting split on shared var {:?} at {}",
                term,
                split_point
            );
        }
        TheoryResult::NeedSplit(SplitRequest {
            variable: term,
            value: split_point,
            floor: int_val.clone(),
            ceil: int_val + BigInt::from(1),
        })
    }

    pub(super) fn record_asserted_real_int_term(&mut self, term: TermId) {
        if self.asserted_real_int_terms.insert(term) {
            self.cross_sort_trail
                .push(AufLiraCrossSortTrailEntry::AssertedRealIntTerm(term));
        }
    }

    /// Track Int-sorted terms that occur in literals routed to the Real solver.
    /// Mirrors LiraSolver::track_asserted_real_int_terms (#6290).
    pub(super) fn track_asserted_real_int_terms(&mut self, literal: TermId) {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![literal];

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }

            if matches!(self.terms.sort(term), ay_core::Sort::Int)
                && !matches!(self.terms.get(term), TermData::Const(Constant::Int(_)))
            {
                self.record_asserted_real_int_term(term);
            }

            stack.extend(self.terms.children(term));
        }
    }
}
