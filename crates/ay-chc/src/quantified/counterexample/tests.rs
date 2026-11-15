// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::QuantifiedChcCounterexample;
use crate::quantified::{
    QuantifiedChcProblem, QuantifiedChcResult, QuantifiedHornClause, UniversalPremise,
};
use crate::smt::{ScopedSmtDeadline, SmtContext, SmtValue};
use crate::{
    CancellationToken, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause,
};
use ay_core::time::Instant;
use ntest::timeout;
use std::sync::Arc;
use std::time::Duration;

mod authority;
mod deep;
mod fixtures;
mod functions;
mod nested;
mod paths;
mod trees;
mod wide;

const TERM_BUDGET: usize = 128 * 1024 * 1024;

/// The search's own window where a test pins what the search reaches (see
/// `deep::search` and `require_searched_unsafe`), sized for the work on the
/// host's slowest core under contention rather than inherited from the
/// production split of a `solve`. `exploration::clock::tests` pins that this
/// window absorbs a slower core that the quarter of a 60 s solve does not.
pub(super) const SEARCH_WINDOW: Duration = Duration::from_secs(90);

fn remaining(deadline: Instant) -> Duration {
    deadline.saturating_duration_since(Instant::now())
}

fn require_unsafe(
    problem: &QuantifiedChcProblem,
    deadline: Instant,
    cancellation: &CancellationToken,
) -> QuantifiedChcCounterexample {
    match problem.solve(
        remaining(deadline).min(Duration::from_secs(45)),
        Some(TERM_BUDGET),
        cancellation,
    ) {
        QuantifiedChcResult::Unsafe(evidence) => evidence,
        other => panic!("concrete original path must have checked SAT evidence: {other:?}"),
    }
}

/// The counterexample search itself, for a source with one original
/// derivation, decided by counts rather than by `solve`'s split of the wall.
///
/// `solve` hands the search a quarter of its remaining wall
/// (`solve::counterexample_deadline`): 11.25 s under `require_unsafe`'s 45 s
/// cap, and that quarter is the search's wall backstop, which a loaded host
/// spends before the one SAT probe finishes. Here the counts decide. The
/// generator emits the source's derivations and then reports `Exhausted` (a
/// count of cursor steps, the same on every host), and the dovetail then
/// hands the one pending candidate the whole remaining envelope
/// (`exploration::policy`, `exhausted && count == 1`), so its probe ends on
/// the native solver's own deterministic budgets: its instantiation round
/// caps and the default ground budget per SAT solve. `SEARCH_WINDOW` is only
/// the hang backstop, and a search it ended panics as could-not-run, never as
/// a missing counterexample.
fn require_searched_unsafe(
    problem: &QuantifiedChcProblem,
    backstop: Instant,
    cancellation: &CancellationToken,
) -> QuantifiedChcCounterexample {
    let until = Instant::now() + remaining(backstop).min(SEARCH_WINDOW);
    let _window = ScopedSmtDeadline::install_until(until);
    match super::search(problem, until, Some(TERM_BUDGET), cancellation) {
        Some(evidence) => evidence,
        None => {
            require_before(until, "the counterexample search");
            panic!("concrete original path must have checked SAT evidence")
        }
    }
}

/// Panic as could-not-run once `backstop` has passed: then the clock, not
/// the counts, may have ended `phase`, and its answer is not a verdict.
fn require_before(backstop: Instant, phase: &str) {
    assert!(
        Instant::now() < backstop,
        "COULD NOT RUN: {phase} reached its hang backstop before its counts decided"
    );
}

fn op(operation: ChcOp, arguments: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operation, arguments.into_iter().map(Arc::new).collect())
}
