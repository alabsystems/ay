// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn prerequisite_refusal_never_reaches_payload_or_later_theorem() {
    for route in [Route::Disjoint, Route::Outside, Route::Combined] {
        // The malformed payload must not replace the prerequisite's error.
        let fixture = fixture(route, Value::OverwrittenMalformed);
        let deadline = deadline();
        for error in [
            BvExprExportError::NoRefutation,
            BvExprExportError::Cancelled,
        ] {
            let failed = Cell::new(false);
            let mut calls = 0;
            let result = lower(
                &fixture,
                route,
                &mut limits(deadline),
                deadline,
                &mut || {
                    assert!(!failed.get(), "work continued after prerequisite refusal");
                    Ok(())
                },
                &mut |_, _, _, _, _| {
                    calls += 1;
                    failed.set(true);
                    Err(error.clone())
                },
            );
            assert_eq!(calls, 1);
            let expected = match &error {
                BvExprExportError::Cancelled => Failure::Cancelled,
                _ => {
                    let theorem = match route {
                        Route::Outside => "outside-frame",
                        Route::Disjoint | Route::Combined => "disjointness",
                    };
                    Failure::Rejected(format!("free-offset {theorem} theorem: {error}"))
                }
            };
            assert_eq!(result, Err(expected));
        }
    }
}

#[test]
fn combined_second_refusal_stops_before_conditional_payload_validation() {
    let fixture = fixture(Route::Combined, Value::OverwrittenMalformed);
    let deadline = deadline();
    let mut actual = limits(deadline);
    let mut expected = actual.clone();
    halve(&mut expected);
    halve(&mut expected);
    let failed = Cell::new(false);
    let mut calls = 0;
    let result = lower(
        &fixture,
        Route::Combined,
        &mut actual,
        deadline,
        &mut || {
            assert!(!failed.get(), "payload polled after second theorem refusal");
            Ok(())
        },
        &mut |_, _, _, _, poll| {
            calls += 1;
            assert!(poll());
            if calls == 1 {
                Ok(())
            } else {
                failed.set(true);
                Err(BvExprExportError::SolverUnknown)
            }
        },
    );
    assert_eq!(calls, 2);
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!(
        result,
        Err(Failure::Rejected(format!(
            "free-offset outside-frame theorem: {}",
            BvExprExportError::SolverUnknown
        )))
    );
}

#[test]
fn each_lowering_and_continuation_poll_stops_the_same_chain() {
    for route in [Route::Disjoint, Route::Outside, Route::Combined] {
        let fixture = fixture(route, Value::Valid);
        let deadline = deadline();
        let mut polls = 0;
        let mut prove = |_: &BvExpr,
                         _: &BvExpr,
                         _: &BvExprProofLimits,
                         _: &BvBlastValidateLimits,
                         poll: &mut dyn FnMut() -> bool| {
            if poll() {
                Ok(())
            } else {
                Err(BvExprExportError::Cancelled)
            }
        };
        assert!(lower(
            &fixture,
            route,
            &mut limits(deadline),
            deadline,
            &mut || {
                polls += 1;
                Ok(())
            },
            &mut prove,
        )
        .is_ok());
        assert!(polls > 1);
        for stop in 1..=polls {
            let mut calls = 0;
            let result = lower(
                &fixture,
                route,
                &mut limits(deadline),
                deadline,
                &mut || {
                    calls += 1;
                    if calls == stop {
                        Err(ProofCheckError::ResourceLimit)
                    } else {
                        Ok(())
                    }
                },
                &mut prove,
            );
            assert_eq!(result, Err(Failure::Cancelled));
            assert_eq!(calls, stop, "callback was called again after its refusal");
        }
    }
}

#[test]
fn expired_source_deadline_never_invokes_prerequisite_or_splits_limits() {
    for route in [Route::Disjoint, Route::Outside, Route::Combined] {
        let fixture = fixture(route, Value::Valid);
        let deadline = Instant::now() - Duration::from_secs(1);
        let mut actual = limits(deadline);
        let expected = format!("{actual:?}");
        let mut calls = 0;
        let result = lower(
            &fixture,
            route,
            &mut actual,
            deadline,
            &mut || Ok(()),
            &mut |_, _, _, _, _| {
                calls += 1;
                Ok(())
            },
        );
        assert!(result.is_err());
        assert_eq!(calls, 0);
        assert_eq!(format!("{actual:?}"), expected);
    }
}

#[test]
fn returned_expression_still_contains_an_unproved_sibling() {
    let mut fixture = fixture(Route::Outside, Value::Valid);
    let shape = outside_frame::Shape::recognize(&fixture.terms, &[fixture.clause]).unwrap();
    let sibling = fixture.terms.mk_var("not_a_theorem", Sort::Bool);
    let conjunction =
        fixture
            .terms
            .mk_app(Symbol::named("and"), &[shape.property, sibling], Sort::Bool);
    let negative = fixture.terms.mk_not_raw(conjunction);
    let root = fixture
        .terms
        .mk_app(Symbol::named("and"), &[shape.guard, negative], Sort::Bool);
    fixture.clause = fixture.terms.mk_not_raw(root);
    let deadline = deadline();
    let mut calls = 0;
    let result = lower(
        &fixture,
        Route::Outside,
        &mut limits(deadline),
        deadline,
        &mut || Ok(()),
        &mut |_, _, _, _, _| {
            calls += 1;
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(calls, 1);
    // Only the selected property is replaced. The root still needs the final
    // proof in prove_and_replay; prerequisite success is not clause acceptance.
    let mut lowerer = ProofProducingLowerer::new(&fixture.terms, deadline);
    lowerer.memo.insert(
        shape.property,
        ProofProducingExpr::Bool(BvExpr::const_val(1, 1)),
    );
    lowerer.memo_node_counts.insert(shape.property, 1);
    assert_eq!(result, BvExpr::not(lowerer.lower_bool(root).unwrap()));
    assert!(format!("{result:?}").contains(&format!("proof_bool_{}", sibling.0)));
}
