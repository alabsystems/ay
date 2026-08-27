// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager DPLL(T) propagation.
//!
//! The SAT callback is intentionally an orchestration layer. Each child module
//! owns one phase and documents its fail-closed boundary. The phase order is
//! load-bearing: stop checks and pending axioms precede trail ingestion, and the
//! theory check precedes delivery. Materialized conflicts and propagations
//! receive structural and semantic verification. Direct lazy deliveries retain
//! the established opaque, theory-owned reason-token boundary instead of
//! manufacturing a clause in this callback.

use ay_core::{TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};
use ay_sat::{ExtPropagateResult, Literal, SolverContext};

use super::TheoryExtension;

mod axioms;
mod batching;
mod check_result;
mod conflict;
mod farkas_conflict;
mod propagation;
mod propagation_lazy;
mod propagation_verify;
mod trail;

/// Maximum number of expensive full-state conflict guards per solve.
const FULL_STATE_GUARD_BUDGET: u64 = 32;

/// Campaign-only propagation instrumentation gate (#qfax-t3-atom-space).
static PROP_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Data shared by the ordered phases of one SAT propagation callback.
struct PropagationRound<'ctx> {
    ctx: &'ctx dyn SolverContext,
    trail: &'ctx [Literal],
    sat_level: u32,
    started_at: Option<ay_core::time::Instant>,
    asserted_atoms: usize,
    pushed_scope: bool,
}

impl<'ctx> PropagationRound<'ctx> {
    fn new<T: TheorySolver>(
        extension: &TheoryExtension<'_, T>,
        ctx: &'ctx dyn SolverContext,
    ) -> Self {
        let trail = ctx.trail();
        let sat_level = ctx.decision_level();
        let started_at = extension
            .diagnostic_trace
            .is_some()
            .then(ay_core::time::Instant::now);
        Self {
            ctx,
            trail,
            sat_level,
            started_at,
            asserted_atoms: 0,
            pushed_scope: false,
        }
    }
}

/// A phase either advances with typed state or completes the SAT callback.
enum PhaseOutcome<T> {
    Continue(T),
    Complete(ExtPropagateResult),
}

/// Stable diagnostic labels emitted after the theory check.
#[derive(Clone, Copy)]
enum CheckLabel {
    Sat,
    Unknown,
    InlineLemmas,
    Split,
    StaleSplit,
    StaleModelEquality,
    StaleModelEqualities,
}

impl CheckLabel {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unknown => "unknown",
            Self::InlineLemmas => "inline_lemmas",
            Self::Split => "split",
            Self::StaleSplit => "sat(stale-split)",
            Self::StaleModelEquality => "sat(stale-model-eq)",
            Self::StaleModelEqualities => "sat(stale-model-eqs)",
        }
    }
}

/// Whether a bound-refinement handoff must stop the current SAT solve.
#[derive(Clone, Copy, Eq, PartialEq)]
enum RefinementHandoff {
    Continue,
    Stop,
}

/// Preserve the independently cached feedback gates of the original lanes.
#[derive(Clone, Copy)]
enum FeedbackLane {
    MainEager,
    Deferred,
}

impl RefinementHandoff {
    const fn requested(self) -> bool {
        matches!(self, Self::Stop)
    }
}

/// Output retained after handling a non-conflicting `TheoryResult`.
struct CheckPhase {
    label: CheckLabel,
    inline_clauses: Vec<Vec<Literal>>,
    refinement_handoff: RefinementHandoff,
}

impl CheckPhase {
    fn new() -> Self {
        Self {
            label: CheckLabel::Sat,
            inline_clauses: Vec::new(),
            refinement_handoff: RefinementHandoff::Continue,
        }
    }
}

/// Clauses and lazy/eager propagation records accumulated for SAT delivery.
struct PropagationBatch {
    clauses: Vec<Vec<Literal>>,
    eager: Vec<(Vec<Literal>, Literal)>,
    lazy: Vec<(Literal, u64)>,
}

impl PropagationBatch {
    fn with_clauses(clauses: Vec<Vec<Literal>>) -> Self {
        Self {
            clauses,
            eager: Vec::new(),
            lazy: Vec::new(),
        }
    }

    fn len(&self) -> usize {
        self.clauses.len() + self.eager.len() + self.lazy.len()
    }
}

/// Result of resolving a lazy theory propagation.
enum LazyResolution {
    Skip,
    Deliver {
        theory_literal: TheoryLit,
        sat_literal: Literal,
        reason_data: u64,
    },
    Materialized(TheoryPropagation),
}

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Run one eager theory-propagation callback without changing phase order.
    pub(super) fn propagate_impl(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.eager_stats.propagate_calls += 1;
        if let Some(result) = self.propagation_guard_result() {
            return result;
        }
        if let Some(result) = self.take_pending_axiom_result() {
            return result;
        }

        let mut round = PropagationRound::new(self, ctx);
        self.align_theory_scope(&mut round);
        self.feed_new_assignments(&mut round);
        match self.prepare_bcp_check(&round) {
            PhaseOutcome::Continue(()) => {}
            PhaseOutcome::Complete(result) => return result,
        }

        let check_result = self.run_bcp_theory_check();
        let check = match self.handle_bcp_check_result(check_result, &round) {
            PhaseOutcome::Continue(check) => check,
            PhaseOutcome::Complete(result) => return result,
        };
        self.deliver_theory_propagations(&round, check)
    }

    fn run_bcp_theory_check(&mut self) -> TheoryResult {
        if self.disable_theory_check || crate::theory_debug_flags::no_bcp_theory_check() {
            TheoryResult::Sat
        } else {
            self.total_bcp_checks += 1;
            self.theory.check_during_propagate()
        }
    }
}
