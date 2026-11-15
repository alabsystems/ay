// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-rule validation whose search is bounded by counted work.
//!
//! A fixed wall budget per rule makes a `Safe` verdict depend on the host: a
//! clause check that needs a second of CPU settles inside 1.5 s on an idle
//! machine and not on a loaded one, and the already-found model is refused.
//! Under a counted allowance every rule's executor runs draw on one allowance
//! of work (`smt::executor_work`: CDCL conflicts plus split-loop round trips,
//! entered as the work ceiling and grant the executor polls), so an executor
//! search that does not settle stops at the same count on every host.
//!
//! The count does not see every phase of an executor run. Preprocessing,
//! encoding, proof bookkeeping and certification's work outside its SAT
//! searches charge no conflict (`smt::executor_work`), and a search reads the
//! ceiling only at its stop polls. Measured while ay-sat reported conflicts at
//! its restarts only, with the deadline as a rule's only wall: a 128-bit
//! factorisation transition counted 2,597 units and was still in LRAT
//! bookkeeping at the 120 s deadline, and a proof-mode LIA query clause
//! counted 4,070 in 28-58 s. So each rule keeps a wall, as a
//! liveness backstop only: what a verification retry may take, a quarter of
//! what remains until the solve deadline, at least 2 s and at most 30 s
//! (`current_verify_retry_timeout`). That is wide enough that load does not
//! cut a rule whose checks settle (on the pre-fix model-checker-consumer realloc VC, rules
//! took up to 5.1 s at load 24, against a fixed 1.5 s). And a rule that cannot
//! be settled leaves three quarters of the time to the caller's later stages.
//! The solve deadline stays the outer backstop.

use std::time::Duration;

use super::super::{InvariantModel, PdrSolver};
use crate::smt::executor_work::{ExecutorWork, ScopedExecutorWork};

/// The work allowance each rule gets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RuleWork {
    /// Work units (conflicts plus round trips) the rule's executor runs may
    /// spend together.
    pub(crate) units: u64,
    /// Split-loop round trips they may spend together.
    pub(crate) round_trips: u64,
    /// The widest internal pre-slice a check takes before its executor.
    pub(crate) internal_slice: Duration,
}

/// How `verify_model_impl` bounds its clause checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::pdr::verification) enum PerRule {
    /// One wall budget (or none) shared by every clause.
    Shared,
    /// The wall budget starts again at every clause.
    Wall,
    /// Every clause gets this work allowance, and a wall that follows the
    /// solve deadline ([`PdrSolver::open_rule_allotment`]).
    Counted(RuleWork),
}

/// Work allowance of one rule when the adaptive portfolio validates a
/// translated `Safe` model on the original clauses
/// (`validate_preprocessed_safe_model`). It replaces a fixed 1.5 s per rule.
///
/// A census of what valid rules need, with room. The model-checker-consumer realloc VC,
/// before cc2c626b4 substituted its definitions away, has three rules (of 90)
/// that need 1,330, 3,661 and 4,120 units. An allowance of 1,024 refused that
/// valid model at the 3,661-unit rule; 8,192 admits it. No rule the CHC suites
/// validate here spends more than 328 units, and none makes more than two
/// round trips (measured when ay-sat reported conflicts at its restarts only,
/// which missed each solve's conflicts after its last one). A search reads
/// the ceiling at its stop polls, so a run overshoots the allowance before it
/// stops. One unit costs from well under a millisecond (bit-blast search) to
/// 7-14 ms (proof-mode LIA). So the count is not a time equivalent, and the
/// rule's wall bounds what it does not see. The internal pre-slice keeps the
/// quarter of 1.5 s a first check had.
/// Wider, a check the internal loop cannot settle would wait up to 2 s for its
/// executor.
pub(crate) const PREPROCESSED_SAFE_RULE_WORK: RuleWork = RuleWork {
    units: 8_192,
    round_trips: 256,
    internal_slice: Duration::from_millis(375),
};

impl PdrSolver {
    /// Per-rule validation of a translated `Safe` model on the original
    /// clauses at the adaptive boundary: every rule gets
    /// [`PREPROCESSED_SAFE_RULE_WORK`], under `deadline`.
    pub(crate) fn verify_model_at_preprocessed_safe_boundary(
        &mut self,
        model: &InvariantModel,
        deadline: ay_core::time::Instant,
    ) -> bool {
        self.verify_model_per_rule_counted(model, PREPROCESSED_SAFE_RULE_WORK, deadline)
    }

    /// Per-rule validation whose search is bounded by `work`:
    /// [`verify_model_per_rule`](Self::verify_model_per_rule) with every
    /// rule's executor runs drawing on one allowance of `work`, and every
    /// rule's wall following `deadline` ([`Self::open_rule_allotment`]).
    ///
    /// A rule whose checks spend the allowance, or its wall, without settling
    /// is refused, exactly as an expired wall budget refused it. The allowance
    /// only decides when the checks give up, never what they prove.
    pub(crate) fn verify_model_per_rule_counted(
        &mut self,
        model: &InvariantModel,
        work: RuleWork,
        deadline: ay_core::time::Instant,
    ) -> bool {
        self.solve_deadline = Some(
            self.solve_deadline
                .map_or(deadline, |current| current.min(deadline)),
        );
        self.verify_model_impl(model, None, false, PerRule::Counted(work))
            .is_none()
    }

    /// Open one rule's allotment. A wall budget restarts its clock. A counted
    /// allowance installs a fresh executor allowance (lifted when the returned
    /// scope drops). The rule's wall, and its first check's timeout, become
    /// what a verification retry may take now: a quarter of what remains until
    /// the solve deadline, at least 2 s, at most 30 s.
    pub(in crate::pdr::verification) fn open_rule_allotment(
        &self,
        per_rule: PerRule,
        budget: &mut Option<Duration>,
        budget_start: &mut Option<ay_core::time::Instant>,
        verify_timeout: &mut Duration,
    ) -> Option<ScopedExecutorWork> {
        match per_rule {
            PerRule::Shared => None,
            PerRule::Wall => {
                *budget_start = budget.map(|_| ay_core::time::Instant::now());
                None
            }
            PerRule::Counted(work) => {
                let wall = self.current_verify_retry_timeout(None, None);
                *budget = Some(wall);
                *budget_start = Some(ay_core::time::Instant::now());
                *verify_timeout = wall;
                Some(ScopedExecutorWork::install(ExecutorWork {
                    units: work.units,
                    round_trips: work.round_trips,
                    internal_slice: work.internal_slice,
                }))
            }
        }
    }
}

#[cfg(test)]
#[path = "counted_tests.rs"]
mod tests;
