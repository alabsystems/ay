// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Supplementary typed-lowering controls, never substitutes for the three R23 originals.

use super::*;
use crate::quantified::QuantifiedChcCompleteResult;
use crate::CancellationToken;
use ay_core::time::Instant;
use ay_model_check::ModelValue;
use ntest::timeout;
use std::time::Duration;

const WALL: Duration = Duration::from_secs(20);
const TERMS: usize = 128 * 1024 * 1024;

// ModelValue intentionally has no global PartialEq; these fixtures require
// exact scalar variant, bit width, and arbitrary-precision integer identity.
fn assert_scalar_eq(actual: &ModelValue, expected: &ModelValue) {
    match (actual, expected) {
        (ModelValue::Bool(actual), ModelValue::Bool(expected)) => assert_eq!(actual, expected),
        (
            ModelValue::BitVec {
                width: actual_width,
                value: actual_value,
            },
            ModelValue::BitVec {
                width: expected_width,
                value: expected_value,
            },
        ) => {
            assert_eq!(actual_width, expected_width, "bit-vector width");
            assert_eq!(actual_value, expected_value, "bit-vector integer payload");
        }
        _ => panic!("expected matching Bool or BitVec model values"),
    }
}

fn read(name: &str, index: u64) -> Arc<ChcExpr> {
    op(
        ChcOp::Select,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new(name, array()))),
            scalar(index.into(), 64),
        ],
    )
}

fn eq(left: Arc<ChcExpr>, value: u128) -> Arc<ChcExpr> {
    op(ChcOp::Eq, vec![left, scalar(value, 8)])
}

fn problem(
    premise: UniversalPremise,
    seed: Arc<ChcExpr>,
    query: Arc<ChcExpr>,
) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let written = declarations.declare_predicate("Written", vec![array()]);
    let result = ChcExpr::Var(ChcVar::new("w", array()));
    let fact = HornClause::fact(seed.as_ref().clone(), written, vec![result.clone()]);
    let body = ClauseBody::predicates_only(vec![(written, vec![result])]);
    let body = ClauseBody {
        constraint: Some(query.as_ref().clone()),
        ..body
    };
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(fact, vec![premise]),
            QuantifiedHornClause::new(HornClause::query(body), vec![]),
        ],
    )
    .unwrap()
}

fn copy() -> UniversalPremise {
    UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Copy {
            source: ChcVar::new("s", array()),
            source_lower: scalar(0, 64),
        },
    )
    .unwrap()
}

fn copy_seed() -> Arc<ChcExpr> {
    op(ChcOp::And, vec![eq(read("d", 0), 7), eq(read("s", 0), 9)])
}

fn assert_safe(problem: QuantifiedChcProblem, end: Instant) {
    let token = CancellationToken::new();
    let QuantifiedChcCompleteResult::Safe(evidence) = problem.solve_with_complete_trace(
        end.saturating_duration_since(Instant::now()),
        Some(TERMS),
        &token,
    ) else {
        panic!("typed original-source Safe with all quantified premises required");
    };
    assert_eq!(evidence.source_smtlib(), problem.source_smtlib());
    assert!(evidence.recheck(
        &problem,
        end.saturating_duration_since(Instant::now()),
        &token
    ));
    assert!(Instant::now() < end);
}

fn assert_unsafe(problem: QuantifiedChcProblem, end: Instant, index: u64, value: u64) {
    let token = CancellationToken::new();
    let QuantifiedChcCompleteResult::Unsafe(trace) = problem.solve_with_complete_trace(
        end.saturating_duration_since(Instant::now()),
        Some(TERMS),
        &token,
    ) else {
        panic!("typed full original same-assignment Unsafe required");
    };
    assert_eq!(trace.source_smtlib(), problem.source_smtlib());
    assert!(trace.replay_obligation().contains("(forall "));
    let query = trace
        .bindings()
        .iter()
        .find(|binding| binding.occurrence() == 1)
        .unwrap();
    let crate::quantified::QuantifiedChcCompleteValue::FunctionalArray(array) = query.value()
    else {
        panic!("full function, not sampled cells");
    };
    let expected = ay_model_check::ModelValue::bitvec(value.into(), 8);
    let key = ay_model_check::ModelValue::bitvec(index.into(), 64);
    assert_scalar_eq(
        &array
            .read_with_stop(&key, &mut 100_000, &mut || {
                token.is_cancelled() || Instant::now() >= end
            })
            .unwrap(),
        &expected,
    );
    assert!(trace.recheck(
        &problem,
        end.saturating_duration_since(Instant::now()),
        &token
    ));
    assert!(Instant::now() < end);
}

#[test]
#[timeout(30000)]
fn typed_copy_proves_the_untouched_lane_with_one_twenty_second_end() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let problem = problem(
        copy(),
        copy_seed(),
        op(ChcOp::Not, vec![eq(read("w", 0), 7)]),
    );
    assert_safe(problem, end);
}

#[test]
#[timeout(30000)]
fn typed_copy_proves_the_written_lane_with_one_twenty_second_end() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let problem = problem(
        copy(),
        copy_seed(),
        op(ChcOp::Not, vec![eq(read("w", 1), 9)]),
    );
    assert_safe(problem, end);
}

#[test]
#[timeout(30000)]
fn typed_copy_refutes_stale_lane_only_with_a_complete_original_witness() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    assert_unsafe(problem(copy(), copy_seed(), eq(read("w", 1), 9)), end, 1, 9);
}

#[test]
#[timeout(30000)]
fn typed_partial_fill_proves_written_lane_and_full_unsigned_frame() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let premise = UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Fill(scalar(9, 8)),
    )
    .unwrap();
    let wrong = op(
        ChcOp::Or,
        vec![
            op(ChcOp::Not, vec![eq(read("w", 0), 7)]),
            op(ChcOp::Not, vec![eq(read("w", 1), 9)]),
        ],
    );
    assert_safe(problem(premise, eq(read("d", 0), 7), wrong), end);
}

#[test]
#[timeout(30000)]
fn typed_partial_fill_requires_whole_array_unsafe_not_sampled_reads() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let premise = UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Fill(scalar(9, 8)),
    )
    .unwrap();
    assert_unsafe(
        problem(premise, eq(read("d", 0), 7), eq(read("w", 1), 9)),
        end,
        1,
        9,
    );
}

#[test]
#[timeout(30000)]
fn typed_overlapping_copy_uses_the_pre_write_source_snapshot_in_unsafe_replay() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let premise = UniversalPremise::array_range_write(
        binder(),
        request(1, 4),
        ArrayRangeValue::Copy {
            source: ChcVar::new("d", array()),
            source_lower: scalar(0, 64),
        },
    )
    .unwrap();
    let seed = op(ChcOp::And, vec![eq(read("d", 0), 9), eq(read("d", 1), 7)]);
    assert_unsafe(problem(premise, seed, eq(read("w", 2), 7)), end, 2, 7);
}

#[test]
#[timeout(30000)]
fn typed_empty_and_reversed_fill_ranges_preserve_the_destination_under_one_end() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    for (lo, hi) in [(0, 0), (9, 3)] {
        let premise = UniversalPremise::array_range_write(
            binder(),
            request(lo, hi),
            ArrayRangeValue::Fill(scalar(9, 8)),
        )
        .unwrap();
        assert_safe(
            problem(
                premise,
                eq(read("d", 0), 7),
                op(ChcOp::Not, vec![eq(read("w", 0), 7)]),
            ),
            end,
        );
    }
}

#[test]
#[timeout(30000)]
fn typed_full_domain_fill_covers_the_maximum_bv64_index() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let mut write = request(0, 0);
    write.range = ArrayRange::Full;
    let premise =
        UniversalPremise::array_range_write(binder(), write, ArrayRangeValue::Fill(scalar(9, 8)))
            .unwrap();
    assert_safe(
        problem(
            premise,
            Arc::new(ChcExpr::Bool(true)),
            op(ChcOp::Not, vec![eq(read("w", u64::MAX), 9)]),
        ),
        end,
    );
}
