// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::UniversalPremise;
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

mod conservation;
mod functions;

fn fixture() -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("p", vec![]);
    let q = declarations.declare_predicate("q", vec![]);
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::new(vec![], Some(ChcExpr::Bool(true))),
                    ClauseHead::Predicate(p, vec![]),
                ),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::new(vec![(p, vec![])], None),
                    ClauseHead::Predicate(q, vec![]),
                ),
                vec![UniversalPremise::new(
                    ChcVar::new("i", ChcSort::BitVec(1)),
                    ChcExpr::Bool(true),
                )],
            ),
            QuantifiedHornClause::new(
                HornClause::new(ClauseBody::new(vec![(q, vec![])], None), ClauseHead::False),
                vec![],
            ),
        ],
    )
    .unwrap()
}

fn control(token: &CancellationToken) -> Control<'_> {
    Control::new(Instant::now() + Duration::from_secs(60), token)
}

#[test]
fn expired_overflow_and_precancelled_batches_return_no_prefix() {
    let source = fixture();
    let token = CancellationToken::new();
    assert!(source.query_obligations(Duration::ZERO, &token).is_err());
    assert!(source.query_obligations(Duration::MAX, &token).is_err());
    token.cancel();
    assert!(source
        .query_obligations(Duration::from_secs(60), &token)
        .is_err());
    token.reset();
    assert_eq!(
        source
            .query_obligations(Duration::from_secs(60), &token)
            .unwrap()
            .len(),
        1
    );
}

#[test]
fn each_enumeration_poll_refuses_whole_batch_and_same_attempt_stays_stopped() {
    let source = fixture();
    let token = CancellationToken::new();
    let live = control(&token);
    let original = source.source_smtlib().to_owned();
    let expected = enumerate_checked(&source, &live).unwrap();
    let calls = live.calls.get();
    assert!(calls > 20 && calls < 2_000);
    for ordinal in 1..=calls {
        let stopped = control(&token);
        stopped.stop_at.set(Some(ordinal));
        assert!(
            enumerate_checked(&source, &stopped).is_err(),
            "poll {ordinal}"
        );
        assert_eq!(stopped.calls.get(), ordinal);
        stopped.stop_at.set(None);
        assert!(enumerate_checked(&source, &stopped).is_err());
        assert_eq!(stopped.calls.get(), ordinal);
        assert_eq!(source.source_smtlib(), original);
    }
    let retry = enumerate_checked(&source, &control(&token)).unwrap();
    assert_eq!(retry[0].id(), expected[0].id());
}

#[test]
fn cumulative_copy_limit_refuses_before_unbounded_slice_cloning() {
    let token = CancellationToken::new();
    let control = control(&token);
    assert!(control.charge(0, 64 * 1024 * 1024).is_ok());
    assert!(control.charge(0, 1).is_err());
    assert!(control.charge(0, 0).is_err());
    let fresh = self::control(&token);
    assert!(fresh.charge(8_000_000, 0).is_ok());
    assert!(fresh.charge(1, 0).is_err());
    assert!(fresh.poll().is_err());
}

#[test]
fn observed_token_cancellation_is_sticky_across_reset() {
    let token = CancellationToken::new();
    let control = control(&token);
    token.cancel();
    assert!(control.poll().is_err());
    token.reset();
    assert!(control.poll().is_err());
    assert!(self::control(&token).poll().is_ok());
}

#[test]
fn enclosing_deadline_refuses_even_with_a_fresh_local_budget() {
    let source = fixture();
    let token = CancellationToken::new();
    {
        let _scope = crate::smt::ScopedSmtDeadline::install_until(Instant::now());
        assert!(source
            .query_obligations(Duration::from_secs(60), &token)
            .is_err());
    }
    assert!(source
        .query_obligations(Duration::from_secs(60), &token)
        .is_ok());
}

#[test]
fn complete_two_row_batch_obeys_exact_cumulative_allowance_and_retries() {
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::new(vec![], Some(ChcExpr::Bool(false))),
                    ClauseHead::False,
                ),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::new(vec![], Some(ChcExpr::Bool(true))),
                    ClauseHead::False,
                ),
                vec![],
            ),
        ],
    )
    .unwrap();
    let token = CancellationToken::new();
    let live = control(&token);
    let rows = enumerate_checked(&source, &live).unwrap();
    assert_eq!(rows.len(), 2);
    let bytes = live.bytes_used();
    assert!(bytes > source.source_smtlib().len());
    let exact = Control::with_limits(&token, 8_000_000, bytes);
    assert_eq!(enumerate_checked(&source, &exact).unwrap().len(), 2);
    let short = Control::with_limits(&token, 8_000_000, bytes - 1);
    assert!(enumerate_checked(&source, &short).is_err());
    assert!(short.poll().is_err());
    assert_eq!(
        enumerate_checked(&source, &control(&token)).unwrap()[1].id(),
        rows[1].id()
    );
}

#[test]
fn marker_fanout_refuses_the_complete_plan_before_materializing_any_slices() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error", vec![]);
    let definition = QuantifiedHornClause::new(
        HornClause::new(
            ClauseBody::new(vec![], Some(ChcExpr::Bool(false))),
            ClauseHead::Predicate(error, vec![]),
        ),
        vec![],
    );
    let mut clauses = vec![definition; 1_025];
    for _ in 0..4 {
        clauses.push(QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody::new(vec![(error, vec![])], None),
                ClauseHead::False,
            ),
            vec![],
        ));
    }
    let source = QuantifiedChcProblem::new(declarations, clauses).unwrap();
    let token = CancellationToken::new();
    let stopped = control(&token);
    assert!(plan::plans(&source, &stopped).is_err());
    assert!(stopped.poll().is_err());
    assert!(source
        .query_obligations(Duration::from_secs(60), &token)
        .is_err());
    assert_eq!(source.source_problem().clauses().len(), 1_029);
}
