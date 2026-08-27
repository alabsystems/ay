// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy-reason routing shared by normal and early-drain propagation lanes.

use ay_core::{TermId, TheoryPropagation, TheorySolver};
use ay_sat::SolverContext;

use super::*;

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn resolve_lazy_propagation(
        &mut self,
        propagation: TheoryPropagation,
        ctx: &dyn SolverContext,
    ) -> LazyResolution {
        let Some(reason_data) = propagation.reason_data else {
            return LazyResolution::Materialized(propagation);
        };
        let Some(literal) =
            self.term_to_literal(propagation.literal.term, propagation.literal.value)
        else {
            return LazyResolution::Skip;
        };
        if let Some(value) = ctx.value(literal.variable()) {
            if value != propagation.literal.value {
                return self.materialize_lazy_propagation(propagation, reason_data);
            }
            self.feedback_assigned_propagation(
                propagation.literal.term,
                propagation.literal.value,
                FeedbackLane::Deferred,
            );
            return LazyResolution::Skip;
        }
        let guarded_euf_token = reason_data & ay_euf::EUF_LAZY_MAGIC_MASK == ay_euf::EUF_LAZY_MAGIC
            && self.is_ite_guarded_term(propagation.literal.term);
        if guarded_euf_token {
            return self.materialize_lazy_propagation(propagation, reason_data);
        }
        LazyResolution::Deliver {
            theory_literal: propagation.literal,
            sat_literal: literal,
            reason_data,
        }
    }

    fn materialize_lazy_propagation(
        &mut self,
        mut propagation: TheoryPropagation,
        reason_data: u64,
    ) -> LazyResolution {
        if let Some(reason) = self
            .theory
            .explain_propagation(propagation.literal.term, reason_data)
        {
            propagation.reason = reason;
            propagation.reason_data = None;
            LazyResolution::Materialized(propagation)
        } else {
            self.theory
                .mark_propagation_rejected(propagation.literal.term, reason_data);
            LazyResolution::Skip
        }
    }

    pub(super) fn feedback_assigned_propagation(
        &mut self,
        term: TermId,
        value: bool,
        lane: FeedbackLane,
    ) {
        self.eager_stats.props_already_assigned += 1;
        if Self::prop_feedback_enabled(lane) && self.is_ite_guarded_term(term) {
            self.theory.assert_literal(term, value);
            self.eager_stats.props_fed_back += 1;
        }
    }

    fn prop_feedback_enabled(lane: FeedbackLane) -> bool {
        static MAIN_NO_FEEDBACK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        static SHARED_NO_FEEDBACK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let disabled =
            match lane {
                FeedbackLane::MainEager => MAIN_NO_FEEDBACK
                    .get_or_init(|| ay_core::theory_disable_flags().no_prop_feedback),
                FeedbackLane::Deferred => SHARED_NO_FEEDBACK
                    .get_or_init(|| ay_core::theory_disable_flags().no_prop_feedback),
            };
        !*disabled
    }

    pub(super) fn is_ite_guarded_term(&self, term: TermId) -> bool {
        self.term_to_var.get(&term).is_some_and(|&variable| {
            let index = variable as usize;
            let word = index / 64;
            word < self.ite_guarded_bitset.len()
                && (self.ite_guarded_bitset[word] >> (index % 64)) & 1 != 0
        })
    }
}
