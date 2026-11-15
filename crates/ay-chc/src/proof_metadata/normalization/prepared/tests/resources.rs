// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_total_and_one_short_work_or_storage_have_sticky_original_refusal() {
    let problem = fixture();
    let (units, bytes) = totals(&problem);
    let end = Instant::now() + Duration::from_secs(20);
    consume(&owner_at(end, units, bytes, Arc::new(|| false)), &problem).unwrap();
    for original in [
        owner_at(end, units - 1, bytes, Arc::new(|| false)),
        owner_at(end, units, bytes - 1, Arc::new(|| false)),
    ] {
        assert!(consume(&original, &problem).is_err());
        assert!(original.check().is_err());
        assert!(consume(&original.clone(), &problem).is_err());
    }
}

#[test]
fn repeated_consumption_uses_one_original_grant_across_retained_clones() {
    let problem = fixture();
    let (units, bytes) = totals(&problem);
    let original = owner(units * 2, bytes * 2, Arc::new(|| false));
    let retained = original.clone();
    consume(&original, &problem).unwrap();
    consume(&retained, &problem).unwrap();
    assert!(consume(&retained, &problem).is_err());
    assert!(original.check().is_err());
}

#[test]
fn unused_datatype_declaration_is_refused_without_legacy_fallback() {
    let mut problem = ChcProblem::new();
    problem.add_datatype_def("D".to_string(), vec![("Ctor".to_string(), Vec::new())]);
    let original = quiet_owner();
    let result =
        original.with_work(
            |work| match prepare_normalized_chc_input_with_work(&problem, work) {
                Err(error) => {
                    assert_eq!(
                        error,
                        QueryError::Invalid("datatype-bearing normalized input is unsupported")
                    );
                    Err(error)
                }
                Ok(value) => value.with_input(|_, _, _| panic!("unsupported declaration admitted")),
            },
        );
    assert!(result.is_err() && original.check().is_err());
    assert_eq!(
        super::super::super::input(&problem),
        super::super::super::text::normalized_input(
            &problem,
            &mut super::super::super::AlwaysContinue
        )
        .unwrap()
    );
}

#[test]
fn hidden_datatype_sort_in_an_unchosen_descendant_is_refused() {
    let datatype = ChcSort::Datatype {
        name: "D".to_string(),
        constructors: crate::ChcDtConstructors::new(Vec::new()),
    };
    let mut problem = ChcProblem::new();
    let hidden = ChcExpr::FuncApp(
        "hidden".to_string(),
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(datatype)),
        Vec::new(),
    );
    raw(
        &mut problem,
        HornClause::query(ClauseBody::constraint(ChcExpr::Op(
            ChcOp::Ite,
            vec![
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(hidden),
            ],
        ))),
    );
    let original = quiet_owner();
    assert!(original
        .with_work(
            |work| prepare_normalized_chc_input_with_work(&problem, work)?
                .with_input(|_, _, _| Ok(()))
        )
        .is_err());
    assert!(original.check().is_err());
}

struct CaptureDrop(Arc<AtomicBool>);
impl Drop for CaptureDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[test]
fn callback_capture_cleanup_precedes_final_original_observer_poll() {
    let dropped = Arc::new(AtomicBool::new(false));
    let observer = dropped.clone();
    let original = owner(
        1_000_000,
        1_000_000,
        Arc::new(move || observer.load(Ordering::SeqCst)),
    );
    let capture = CaptureDrop(dropped.clone());
    let problem = ChcProblem::new();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&problem, work)?.with_input(move |_, _, _| {
            assert!(!capture.0.load(Ordering::SeqCst));
            let _retain_whole_capture = &capture;
            Ok(())
        })
    });
    assert!(dropped.load(Ordering::SeqCst));
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    dropped.store(false, Ordering::SeqCst);
    assert_eq!(
        original.check(),
        Err(OriginalAdmissionError::ObserverStopped)
    );
}

#[test]
fn original_callback_reset_cannot_revive_after_consumption_stop() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observer = stopped.clone();
    let original = owner(
        1_000_000,
        1_000_000,
        Arc::new(move || observer.load(Ordering::SeqCst)),
    );
    let problem = ChcProblem::new();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&problem, work)?.with_input(|_, _, _| {
            stopped.store(true, Ordering::SeqCst);
            Ok(())
        })
    });
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    stopped.store(false, Ordering::SeqCst);
    assert!(consume(&original.clone(), &problem).is_err());
}

#[test]
fn one_original_end_expiring_during_callback_refuses_after_cleanup() {
    let end = Instant::now() + Duration::from_millis(100);
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        end,
        Arc::new(|| false),
    );
    let dropped = Arc::new(AtomicBool::new(false));
    let capture = CaptureDrop(dropped.clone());
    let entered = Arc::new(AtomicBool::new(false));
    let callback_entered = entered.clone();
    let problem = ChcProblem::new();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&problem, work)?.with_input(move |_, _, _| {
            callback_entered.store(true, Ordering::SeqCst);
            let _retain_whole_capture = &capture;
            while Instant::now() < end {
                std::thread::yield_now();
            }
            Ok(())
        })
    });
    assert!(dropped.load(Ordering::SeqCst));
    assert!(entered.load(Ordering::SeqCst));
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            ay_core::original_query::StopReason::Deadline
        )))
    );
    assert!(original.check().is_err());
}

#[test]
fn caller_error_and_caught_panic_latch_without_a_replacement_adapter() {
    let problem = ChcProblem::new();
    let end = Instant::now() + Duration::from_secs(20);
    let original = owner_at(end, 20_000_000, 128 * 1024 * 1024, Arc::new(|| false));
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&problem, work)?
            .with_input(|_, _, _| Err(QueryError::Invalid("caller refused")))
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Invalid(
            "caller refused"
        )))
    );
    assert!(consume(&original, &problem).is_err());
    let panic_owner = owner_at(end, 20_000_000, 128 * 1024 * 1024, Arc::new(|| false));
    let result = panic_owner.with_work(|work| {
        prepare_normalized_chc_input_with_work(&problem, work)?
            .with_input(|_, _, _| panic!("callback fixture"))
    });
    assert_eq!(result, Err(OriginalAdmissionError::OperationPanicked));
    assert!(panic_owner.check().is_err());
}

#[test]
fn checked_capacity_overflow_refuses_before_storage_and_remains_sticky() {
    let original = quiet_owner();
    let result = original.with_work(|work| {
        let mut values: Vec<u8> = Vec::new();
        bytes::reserve(&mut values, usize::MAX, &mut Borrowed(work))
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert!(original.check().is_err());
}
