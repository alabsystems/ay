// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-wide memory of bounded counterexample replays that failed.
//!
//! Every Unsafe validation builds a fresh verifier, so a per-verifier memo
//! forgets a failed replay the moment the verifier is dropped. When several
//! engines rediscover the same witness-less counterexample, or the adaptive
//! layer re-validates what the portfolio already tried, the same fruitless
//! replay was paid again each time (trex02: five 10 s replays, 53% of the
//! wall; the development design notes at `9598c4206`).
//!
//! An entry records the problem, the depth hint, and the budget the attempt
//! demonstrably had: `min(nominal budget, elapsed + MIN_REPLAY_BUDGET)`,
//! since the replay stops once less than `MIN_REPLAY_BUDGET` remains and an
//! enclosing deadline may have cut it shorter than its nominal budget. A new
//! request is skipped only when it is dominated: same problem, depth hint at
//! least as deep (the replay starts deeper), budget at most the recorded one.
//!
//! Soundness: skipping returns "not confirmed", the fail-closed answer.

use super::BmcSolver;
use crate::pdr::Counterexample;
use crate::{CancellationToken, ChcProblem};
use std::sync::Mutex;
use std::time::Duration;

impl BmcSolver {
    /// Replay-confirm an engine-claimed Unsafe by bounded BMC on `problem`
    /// (see [`BmcSolver::replay_confirm_unsafe_on_problem_unmemoized`] for
    /// the acceptance contract), skipping a replay dominated by one that
    /// already failed: same problem, depth hint at least as deep, budget at
    /// most what the failed attempt actually had. Skipping can only withhold
    /// a confirmation, never grant one.
    pub(crate) fn replay_confirm_unsafe_on_problem(
        problem: &ChcProblem,
        depth_hint: usize,
        budget: Duration,
        cancellation_token: Option<CancellationToken>,
        verbose: bool,
    ) -> Option<Counterexample> {
        // Closed under an effort (`BmcSolver::closed_under_effort`), before the
        // process-wide memo below is read or written: a run's answer must not
        // depend on what the process replayed before it.
        if Self::closed_under_effort() {
            return None;
        }
        if budget < MIN_REPLAY_BUDGET {
            return None;
        }
        if dominated(problem, depth_hint, budget) {
            tracing::debug!(
                "cex-replay: skipped (depth hint {depth_hint}, budget {budget:?}): an equally \
                 hard replay already failed on this problem"
            );
            return None;
        }
        let started = ay_core::time::Instant::now();
        let confirmed = Self::replay_confirm_unsafe_on_problem_unmemoized(
            problem,
            depth_hint,
            budget,
            cancellation_token.clone(),
            verbose,
        );
        let cancelled = cancellation_token
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled);
        if confirmed.is_none() && !cancelled {
            record(problem, depth_hint, budget, started.elapsed());
        }
        confirmed
    }
}

/// Below this the replay does not start (and it stops once less remains).
const MIN_REPLAY_BUDGET: Duration = Duration::from_millis(250);

/// Distinct failed replays kept (oldest evicted first).
const CAPACITY: usize = 8;

struct FailedReplay {
    fingerprint: u64,
    problem: ChcProblem,
    depth_hint: usize,
    budget: Duration,
}

static FAILED: Mutex<Vec<FailedReplay>> = Mutex::new(Vec::new());

fn with_memo<T>(f: impl FnOnce(&mut Vec<FailedReplay>) -> T) -> T {
    let mut guard = FAILED
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    f(&mut guard)
}

/// Whether a replay of `problem` at `depth_hint` with `budget` is no easier
/// than one that already failed.
fn dominated(problem: &ChcProblem, depth_hint: usize, budget: Duration) -> bool {
    let fingerprint = problem.shallow_fingerprint();
    with_memo(|memo| {
        memo.iter().any(|failed| {
            failed.fingerprint == fingerprint
                && failed.depth_hint <= depth_hint
                && budget <= failed.budget
                && failed.problem.structurally_equal(problem)
        })
    })
}

/// Remember that a replay of `problem` at `depth_hint` failed after
/// `elapsed` of its nominal `budget`.
fn record(problem: &ChcProblem, depth_hint: usize, budget: Duration, elapsed: Duration) {
    let had = budget.min(elapsed.saturating_add(MIN_REPLAY_BUDGET));
    if had < MIN_REPLAY_BUDGET {
        return;
    }
    let fingerprint = problem.shallow_fingerprint();
    let evicted = with_memo(|memo| {
        if let Some(failed) = memo.iter_mut().find(|failed| {
            failed.fingerprint == fingerprint
                && failed.depth_hint == depth_hint
                && failed.problem.structurally_equal(problem)
        }) {
            failed.budget = failed.budget.max(had);
            return None;
        }
        memo.push(FailedReplay {
            fingerprint,
            problem: problem.clone(),
            depth_hint,
            budget: had,
        });
        (memo.len() > CAPACITY).then(|| memo.remove(0))
    });
    // Tear the evicted problem down outside the lock, without deep recursion.
    if let Some(evicted) = evicted {
        evicted.problem.iterative_drop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    fn problem(bound: i64) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("MemoP", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(bound))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    fn only_dominated_requests_on_the_same_problem_are_skipped() {
        // A bound no other test uses, so the process-wide memo is ours.
        let failed = problem(918_273);
        record(&failed, 6, Duration::from_secs(10), Duration::from_secs(10));
        assert!(dominated(&failed, 6, Duration::from_secs(10)));
        assert!(
            dominated(&failed, 9, Duration::from_secs(4)),
            "deeper and poorer"
        );
        assert!(
            !dominated(&failed, 3, Duration::from_secs(10)),
            "shallower start"
        );
        assert!(
            !dominated(&failed, 6, Duration::from_secs(20)),
            "better funded"
        );
        assert!(
            !dominated(&problem(918_274), 6, Duration::from_secs(1)),
            "other problem"
        );
    }

    #[test]
    fn a_replay_cut_short_records_only_the_time_it_had() {
        let failed = problem(918_275);
        record(&failed, 4, Duration::from_secs(10), Duration::from_secs(2));
        assert!(dominated(&failed, 4, Duration::from_secs(2)));
        assert!(!dominated(&failed, 4, Duration::from_secs(5)));
    }
}
