// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane's ground oracle: one disposable `Executor` per question.
//!
//! Each query runs on an UNPRUNED clone of the enclosing context (so target
//! `TermId`s minted in the outer store keep their meaning in the probe, exactly
//! like `probe_finite_witness_values`), under the caller's interrupt and a
//! deadline no later than the lane's. Only rational and Boolean values for
//! the requested targets cross back. NO AUTHORITY CROSSES THIS BOUNDARY: the
//! search treats every answer as a hint (module docs of
//! `crate::cegqi::lra_nested`).

use ay_core::time::Instant;
use ay_core::{TermId, TermStore};

use super::super::model::EvalValue;
use super::super::Executor;
use crate::cegqi::lra_nested::{OracleAnswer, OracleValue, QlraHost};
use crate::ematching::contains_quantifier;
use crate::executor_types::SolveResult;

/// How a probe decides its query.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum OracleRoute {
    /// A full public `check_sat` on the probe (M1).
    PublicCheckSat,
    /// `solve_for_category(QfLra)` directly: no public pipeline, gates or
    /// certification — the plan's §5 oracle. The answer is a hint either way.
    DirectQfLra,
}

/// The executor-backed [`QlraHost`].
pub(super) struct ExecutorQlraHost<'a> {
    executor: &'a mut Executor,
    deadline: Instant,
    route: OracleRoute,
}

impl<'a> ExecutorQlraHost<'a> {
    pub(super) fn new(executor: &'a mut Executor, deadline: Instant) -> Self {
        Self::with_route(executor, deadline, OracleRoute::PublicCheckSat)
    }

    pub(super) fn with_route(
        executor: &'a mut Executor,
        deadline: Instant,
        route: OracleRoute,
    ) -> Self {
        Self {
            executor,
            deadline,
            route,
        }
    }

    fn remaining_ms(&self) -> u64 {
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        u64::try_from(remaining.as_millis()).unwrap_or(u64::MAX)
    }
}

impl QlraHost for ExecutorQlraHost<'_> {
    fn terms(&mut self) -> &mut TermStore {
        &mut self.executor.ctx.terms
    }

    fn check(&mut self, assertions: &[TermId], targets: &[TermId]) -> OracleAnswer {
        let budget_ms = self.remaining_ms();
        if budget_ms == 0 {
            return OracleAnswer::Unknown;
        }
        self.executor
            .qlra_oracle_check(assertions, targets, budget_ms, self.route)
    }

    fn should_stop(&self) -> bool {
        Instant::now() >= self.deadline || (self.executor.make_should_stop())()
    }
}

fn oracle_value(value: EvalValue) -> Option<OracleValue> {
    match value {
        EvalValue::Rational(r) => Some(OracleValue::Rat(r)),
        EvalValue::Bool(b) => Some(OracleValue::Bool(b)),
        _ => None,
    }
}

impl Executor {
    /// Decide the quantifier-free conjunction `assertions` on a disposable
    /// probe and read `targets` from its model.
    fn qlra_oracle_check(
        &mut self,
        assertions: &[TermId],
        targets: &[TermId],
        budget_ms: u64,
        route: OracleRoute,
    ) -> OracleAnswer {
        if self.should_abort_theory_loop()
            || !self.qpf_probe_preflight()
            || assertions
                .iter()
                .any(|&term| contains_quantifier(&self.ctx.terms, term))
        {
            return OracleAnswer::Unknown;
        }
        let Some(probe_ctx) = self.isolated_probe_context(assertions) else {
            return OracleAnswer::Unknown;
        };
        let mut probe = self.qpf_probe_executor(probe_ctx, budget_ms);
        probe.original_problem_had_quantifiers = false;
        probe.incremental_mode = false;
        probe.qlra_lane.probe_lra_no_implied_bounds = route == OracleRoute::DirectQfLra;
        probe.begin_public_solve(false);
        probe.bind_unsat_query_assumptions(&[]);
        let solved = match route {
            OracleRoute::PublicCheckSat => probe.check_sat(),
            OracleRoute::DirectQfLra => {
                probe.solve_for_category(crate::logic_detection::LogicCategory::QfLra)
            }
        };
        let answer = match solved {
            Ok(SolveResult::Sat) => match probe.last_model.as_ref() {
                Some(model) => OracleAnswer::Sat(
                    targets
                        .iter()
                        .map(|&target| oracle_value(probe.evaluate_term(model, target)))
                        .collect(),
                ),
                None => OracleAnswer::Unknown,
            },
            Ok(SolveResult::Unsat(_)) => OracleAnswer::Unsat,
            _ => OracleAnswer::Unknown,
        };
        drop(probe);
        answer
    }
}
