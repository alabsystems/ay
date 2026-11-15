// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn test_meter() -> CheckedRefutationMeter {
    let mut limits = ResolutionValidationLimits::unbounded();
    limits.max_work = MAX_SCREEN_WORK;
    limits.max_bytes = MAX_SCREEN_BYTES;
    CheckedRefutationMeter::new(limits, None, None).unwrap()
}

#[test]
fn sparse_dense_search_and_original_model_check_agree() {
    let low = Literal::positive(Variable::new(3));
    let high = Literal::positive(Variable::new(1 << 29));
    let clause = [low, high];
    let units = [low.negated(), high];
    assert!(mapped_originals_satisfiable(&[&clause], &units, &mut test_meter(), None).unwrap());
    assert!(!mapped_originals_satisfiable(
        &[&clause],
        &[low.negated(), high.negated()],
        &mut test_meter(),
        None
    )
    .unwrap());
    let variables = [3, 1 << 29];
    assert!(model_satisfies(
        &[false, true],
        &variables,
        &[&clause],
        &units,
        &mut test_meter()
    )
    .unwrap());
    assert!(!model_satisfies(
        &[true, false],
        &variables,
        &[&clause],
        &units,
        &mut test_meter()
    )
    .unwrap());
    assert!(!model_satisfies(&[], &variables, &[&clause], &units, &mut test_meter()).unwrap());
    assert!(!model_satisfies(&[false, true], &variables, &[&[]], &[], &mut test_meter()).unwrap());
}

#[test]
fn repeated_literals_are_priced_before_dense_vector_growth() {
    let literal = Literal::positive(Variable::new(1));
    let wide = vec![literal; 128];
    let mut meter = test_meter();
    meter.limits.max_work = 128; // one clause visit + 128 requested slots
    assert!(matches!(
        dense_variables(&[&wide], &[], &mut meter),
        Err(ScreenFailure::Decline)
    ));
    let mut meter = test_meter();
    let dense = dense_variables(&[&wide], &[], &mut meter).unwrap();
    assert_eq!(dense, vec![1]);
    let remaining = meter.remaining_validation_limits().unwrap();
    assert!(MAX_SCREEN_WORK - remaining.max_work > wide.len() as u64);
    assert_eq!(
        MAX_SCREEN_BYTES - remaining.max_bytes,
        dense.capacity() * size_of::<u32>()
    );
    let too_wide = vec![literal; MAX_SCREEN_LITERALS + 1];
    let mut meter = test_meter();
    assert!(matches!(
        dense_variables(&[&too_wide], &[], &mut meter),
        Err(ScreenFailure::Decline)
    ));
    assert_eq!(
        meter.remaining_validation_limits().unwrap().max_bytes,
        MAX_SCREEN_BYTES
    );
}

#[test]
fn sparse_shape_limits_decline_without_authority_or_namespace_allocation() {
    let literals: Vec<_> = (0..=MAX_SCREEN_VARIABLES)
        .map(|index| Literal::positive(Variable::new(index as u32 * 100)))
        .collect();
    assert!(matches!(
        dense_variables(&[&literals], &[], &mut test_meter()),
        Err(ScreenFailure::Decline)
    ));
    let repeated_clause: &[Literal] = &literals[..1];
    let clauses = vec![repeated_clause; MAX_SCREEN_CLAUSES + 1];
    let mut meter = test_meter();
    assert!(matches!(
        dense_variables(&clauses, &[], &mut meter),
        Err(ScreenFailure::Decline)
    ));
    assert_eq!(
        meter.remaining_validation_limits().unwrap().max_bytes,
        MAX_SCREEN_BYTES
    );
}

#[test]
fn callback_and_sat_recorded_stops_survive_recovered_controls() {
    let flag = Arc::new(AtomicBool::new(false));
    let mut meter =
        CheckedRefutationMeter::new(test_meter().limits, Some(flag.clone()), None).unwrap();
    let stop = SatStop::new(&mut meter);
    flag.store(true, Ordering::Relaxed);
    assert!(stop.should_stop());
    flag.store(false, Ordering::Relaxed);
    assert!(stop.should_stop());
    assert!(matches!(
        stop.finish(None),
        Err(ScreenFailure::CallerStop(
            ResolutionValidationError::Cancelled
        ))
    ));
    let mut meter = test_meter();
    let stop = SatStop::new(&mut meter);
    stop.meter.borrow_mut().limits.deadline = Some(ay_core::time::Instant::now());
    assert!(stop.should_stop());
    stop.meter.borrow_mut().limits.deadline = None;
    assert!(matches!(
        stop.finish(None),
        Err(ScreenFailure::CallerStop(
            ResolutionValidationError::DeadlineExceeded
        ))
    ));
    for deadline in [false, true] {
        let mut solver = ay_sat::Solver::new(1);
        let interrupt = Arc::new(AtomicBool::new(!deadline));
        solver.set_interrupt_handle(Some(interrupt.clone()));
        if deadline {
            solver.set_solve_deadline(Some(ay_core::time::Instant::now()));
        }
        assert!(solver
            .solve_interruptible(|| false)
            .into_inner()
            .is_unknown());
        let reason = solver.last_unknown_reason();
        interrupt.store(false, Ordering::Relaxed);
        solver.set_solve_deadline(None);
        let expected = if deadline {
            ResolutionValidationError::DeadlineExceeded
        } else {
            ResolutionValidationError::Cancelled
        };
        let mut meter = test_meter();
        let stop = SatStop::new(&mut meter);
        assert!(
            matches!(stop.finish(reason), Err(ScreenFailure::CallerStop(error)) if error == expected)
        );
    }
    // Local callback exhaustion also appears Interrupted to SAT, but is not a
    // caller stop and must not prohibit the ordinary complete proof builder.
    let mut meter = test_meter();
    meter.limits.max_work = 0;
    let stop = SatStop::new(&mut meter);
    assert!(stop.should_stop());
    assert!(matches!(
        stop.finish(Some(ay_sat::SatUnknownReason::Interrupted)),
        Err(ScreenFailure::Decline)
    ));
    assert!(SatStop::new(&mut test_meter())
        .finish(Some(ay_sat::SatUnknownReason::ResourceBudget))
        .is_ok());
}
