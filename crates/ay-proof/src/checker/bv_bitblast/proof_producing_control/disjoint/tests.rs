// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Continuation tests do not establish theorem validity: accepting spies are
//! test-only. Native wrappers still use the independent compact validator.

use super::*;
use crate::checker::bv_bitblast::disjoint::Shape as DisjointShape;
use crate::checker::bv_bitblast::proof_producing_control::outside_frame;
use std::cell::Cell;

mod controls;
mod fixtures;
use fixtures::{fixture, Fixture, Route, Value};

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn limits(deadline: Instant) -> BvExprProofLimits {
    let mut limits = producer_limits::counted_limits_until(deadline);
    // Odd values expose floor division at both stages, not merely equality
    // for an even preset. All other caps and both deadlines stay untouched.
    limits.max_estimated_gate_work = 101;
    limits.max_expansion_work = 103;
    limits.resolution.validation.max_work = 105;
    limits.resolution.max_conflicts = Some(107);
    limits.resolution.max_decisions = Some(109);
    limits
}

fn halve(limits: &mut BvExprProofLimits) {
    limits.max_estimated_gate_work /= 2;
    limits.max_expansion_work /= 2;
    limits.resolution.validation.max_work /= 2;
    limits.resolution.max_conflicts = limits.resolution.max_conflicts.map(|n| n / 2);
    limits.resolution.max_decisions = limits.resolution.max_decisions.map(|n| n / 2);
}

fn lower<F>(
    fixture: &Fixture,
    route: Route,
    limits: &mut BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
    prove: &mut F,
) -> Result<BvExpr, Failure>
where
    F: FnMut(
        &BvExpr,
        &BvExpr,
        &BvExprProofLimits,
        &BvBlastValidateLimits,
        &mut dyn FnMut() -> bool,
    ) -> Result<(), BvExprExportError>,
{
    let terms = &fixture.terms;
    match route {
        Route::Disjoint | Route::Combined => {
            let shape = DisjointShape::recognize(terms, &[fixture.clause]).unwrap();
            lower_with_prover(terms, shape, limits, deadline, poll, prove)
        }
        Route::Outside => {
            let shape = outside_frame::Shape::recognize(terms, &[fixture.clause]).unwrap();
            outside_frame::lower_with_disjoint_and_prover(
                terms, shape, limits, deadline, poll, None, prove,
            )
        }
    }
}

fn expected_disjoint(fixture: &Fixture, deadline: Instant) -> BvExpr {
    let shape = DisjointShape::recognize(&fixture.terms, &[fixture.clause]).unwrap();
    let mut lowerer = ProofProducingLowerer::new(&fixture.terms, deadline);
    let [a, b, c] = shape.guards.map(|id| lowerer.lower_bool(id).unwrap());
    let guard = BvExpr::and(a, BvExpr::and(b, c));
    let a = lowerer.lower_bv(shape.spans[0].start).unwrap().0;
    let b = lowerer.lower_bv(shape.spans[1].start).unwrap().0;
    let i = BvExpr::leaf("disjoint_offset_a", shape.width);
    let j = BvExpr::leaf("disjoint_offset_b", shape.width);
    let in_a = BvExpr::Ult(
        Box::new(i.clone()),
        Box::new(BvExpr::const_val(shape.spans[0].length, shape.width)),
    );
    let in_b = BvExpr::Ult(
        Box::new(j.clone()),
        Box::new(BvExpr::const_val(shape.spans[1].length, shape.width)),
    );
    BvExpr::not(BvExpr::and(
        BvExpr::and(guard, in_a),
        BvExpr::and(in_b, BvExpr::eq(BvExpr::add(i, a), BvExpr::add(j, b))),
    ))
}

fn expected_outside(fixture: &Fixture, deadline: Instant) -> BvExpr {
    let shape = outside_frame::Shape::recognize(&fixture.terms, &[fixture.clause]).unwrap();
    let mut lowerer = ProofProducingLowerer::new(&fixture.terms, deadline);
    let guard = lowerer.lower_bool(shape.guard).unwrap();
    let outside = lowerer.lower_bool(shape.outside).unwrap();
    let start = lowerer.lower_bv(shape.start).unwrap().0;
    let observe = lowerer.lower_bv(shape.observe).unwrap().0;
    let offset = BvExpr::leaf("outside_frame_offset", shape.width);
    BvExpr::not(BvExpr::and(
        BvExpr::and(guard, outside),
        BvExpr::and(
            BvExpr::Ult(
                Box::new(offset.clone()),
                Box::new(BvExpr::const_val(shape.length, shape.width)),
            ),
            BvExpr::eq(observe, BvExpr::add(start, offset)),
        ),
    ))
}

#[test]
fn source_queries_truth_and_split_limits_reach_one_continuation_in_order() {
    for route in [Route::Disjoint, Route::Outside, Route::Combined] {
        let fixture = fixture(route, Value::Valid);
        let deadline = deadline();
        let mut actual = limits(deadline);
        let mut expected = actual.clone();
        let queries = match route {
            Route::Disjoint => vec![expected_disjoint(&fixture, deadline)],
            Route::Outside => vec![expected_outside(&fixture, deadline)],
            Route::Combined => vec![
                expected_disjoint(&fixture, deadline),
                expected_outside(&fixture, deadline),
            ],
        };
        let before = fixture.terms.entries_snapshot();
        let mut calls = 0;
        let result = lower(
            &fixture,
            route,
            &mut actual,
            deadline,
            &mut || Ok(()),
            &mut |query, truth, proof, replay, poll| {
                assert_eq!(query, &queries[calls]);
                assert_eq!(truth, &BvExpr::const_val(1, 1));
                halve(&mut expected);
                assert_eq!(format!("{proof:?}"), format!("{expected:?}"));
                let mut expected_replay = proof_replay_limits(&expected);
                expected_replay.max_work /= 2;
                assert_eq!(format!("{replay:?}"), format!("{expected_replay:?}"));
                assert!(poll());
                calls += 1;
                Ok(())
            },
        );
        assert!(result.is_ok());
        assert_eq!(calls, queries.len());
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        assert_eq!(fixture.terms.entries_snapshot(), before);
        assert!(!fixture
            .terms
            .strict_bv_semantics_validated(&[fixture.clause]));
    }
}

#[test]
fn optional_search_caps_and_original_deadlines_are_not_replaced() {
    let fixture = fixture(Route::Combined, Value::Valid);
    let deadline = deadline();
    let replay_deadline = deadline.checked_sub(Duration::from_secs(1)).unwrap();
    let mut limits = limits(deadline);
    limits.resolution.validation.deadline = Some(replay_deadline);
    limits.resolution.max_conflicts = None;
    limits.resolution.max_decisions = Some(1);
    let mut calls = 0;
    assert!(lower(
        &fixture,
        Route::Combined,
        &mut limits,
        deadline,
        &mut || Ok(()),
        &mut |_, _, proof, replay, _| {
            assert_eq!(proof.resolution.deadline, Some(deadline));
            assert_eq!(proof.resolution.validation.deadline, Some(replay_deadline));
            assert_eq!(replay.deadline, Some(replay_deadline));
            assert_eq!(proof.resolution.max_conflicts, None);
            assert_eq!(proof.resolution.max_decisions, Some(0));
            calls += 1;
            Ok(())
        },
    )
    .is_ok());
    assert_eq!(calls, 2);
}

#[test]
fn accepting_prerequisites_does_not_skip_overwritten_operand_validation() {
    for (route, count) in [
        (Route::Disjoint, 1),
        (Route::Outside, 1),
        (Route::Combined, 2),
    ] {
        let fixture = fixture(route, Value::OverwrittenMalformed);
        let deadline = deadline();
        let mut calls = 0;
        let result = lower(
            &fixture,
            route,
            &mut limits(deadline),
            deadline,
            &mut || Ok(()),
            &mut |_, _, _, _, _| {
                calls += 1;
                Ok(())
            },
        );
        assert!(matches!(result, Err(Failure::Rejected(_))));
        assert_eq!(calls, count);
    }
}
