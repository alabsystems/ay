// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn unmappable_executor() -> Executor {
    let p = Literal::positive(Variable::new(0));
    let bit = Literal::positive(Variable::new(1));
    screened_executor(2, &[vec![p], vec![bit], vec![bit.negated()]], false).0
}

#[test]
fn local_work_and_byte_exhaustion_skip_only_the_optional_screen() {
    let executor = unmappable_executor();
    for (work, bytes) in [(0, MAX_SCREEN_BYTES), (MAX_SCREEN_WORK, 0), (8, 64)] {
        let mut limits = screen_limits(&executor);
        limits.max_work = work;
        limits.max_bytes = bytes;
        assert!(reject_with_limits(&executor, limits).is_ok());
    }
    assert!(matches!(
        reject_unmappable_refutation(&executor),
        Err(CheckedSatRefutationError::UnmappableRefutation { variable: 1, .. })
    ));

    // The other direction is an actual positive sidecar, not just a None screen.
    let p = Literal::positive(Variable::new(0));
    let bit = Literal::positive(Variable::new(1));
    let (mut mapped, _) = screened_executor(2, &[vec![bit, p], vec![p], vec![p.negated()]], true);
    let mut limits = screen_limits(&mapped);
    limits.max_work = 0;
    assert!(reject_with_limits(&mapped, limits).is_ok());
    assert!(CheckedSatRefutation::build(&mut mapped).is_ok());
}

#[test]
fn caller_interrupt_deadline_and_memory_refuse_before_conversion() {
    let mut executor = unmappable_executor();
    let flag = Arc::new(AtomicBool::new(true));
    executor.solve_interrupt = Some(flag.clone());
    assert!(matches!(
        CheckedSatRefutation::build(&mut executor),
        Err(CheckedSatRefutationError::CertificationResource(
            ResolutionValidationError::Cancelled
        ))
    ));
    flag.store(false, Ordering::Relaxed);
    executor.set_deadline(Some(ay_core::time::Instant::now()));
    assert!(matches!(
        CheckedSatRefutation::build(&mut executor),
        Err(CheckedSatRefutationError::CertificationResource(
            ResolutionValidationError::DeadlineExceeded
        ))
    ));
    executor.set_deadline(None);
    // The existing memory API explicitly treats unavailable RSS as no reading.
    if crate::memory::current_memory_bytes() > 0 {
        for limit in [0, 1] {
            executor.set_memory_limit(Some(limit));
            assert!(matches!(
                CheckedSatRefutation::build(&mut executor),
                Err(CheckedSatRefutationError::CertificationResource(
                    ResolutionValidationError::Cancelled
                ))
            ));
        }
    }
    executor.set_memory_limit(None);
    assert!(matches!(
        reject_unmappable_refutation(&executor),
        Err(CheckedSatRefutationError::UnmappableRefutation { variable: 1, .. })
    ));
}

#[test]
fn partition_scratch_depends_on_trace_not_declared_namespace() {
    let executor = unmappable_executor();
    let mut ordinary_meter = CheckedRefutationMeter::unbounded();
    let mut inputs = ScreenInputs::gather(&executor, &mut ordinary_meter).unwrap();
    let mut first_meter =
        CheckedRefutationMeter::new(screen_limits(&executor), None, None).unwrap();
    let ordinary = inputs.partition_originals(&mut first_meter).unwrap();
    let first_remaining = first_meter.remaining_validation_limits().unwrap();
    // This changes only the private screen's declared namespace, not a solver
    // or proof certificate. No allocation proportional to this value is valid.
    inputs.sat_num_vars = usize::MAX;
    let mut sparse_meter =
        CheckedRefutationMeter::new(screen_limits(&executor), None, None).unwrap();
    let sparse = inputs.partition_originals(&mut sparse_meter).unwrap();
    let sparse_remaining = sparse_meter.remaining_validation_limits().unwrap();
    assert_eq!(ordinary.first_unmappable, sparse.first_unmappable);
    assert_eq!(ordinary.mappable, sparse.mappable);
    assert_eq!(first_remaining.max_bytes, sparse_remaining.max_bytes);
    assert_eq!(first_remaining.max_work, sparse_remaining.max_work);
}

#[test]
fn structural_selector_order_and_allocation_admission_remain_fail_closed() {
    let executor = unmappable_executor();
    let map = executor.last_var_to_term.as_ref().unwrap();
    let neg = |v| Literal::negative(Variable::new(v));
    let mut meter = CheckedRefutationMeter::unbounded();
    assert!(validate_scope_assumptions(&[neg(2), neg(3)], map, 4, &mut meter).is_ok());
    for selectors in [
        vec![neg(3), neg(2)],
        vec![neg(2), neg(2)],
        vec![neg(0)],
        vec![neg(4)],
        vec![neg(2).negated()],
    ] {
        assert!(validate_scope_assumptions(&selectors, map, 4, &mut meter).is_err());
    }
    assert!(matches!(
        screen_vec::<u64>(usize::MAX, &mut meter),
        Err(ScreenFailure::Decline)
    ));
    let mut limits = screen_limits(&executor);
    limits.max_bytes = 7;
    let mut small = CheckedRefutationMeter::new(limits, None, None).unwrap();
    assert!(matches!(
        screen_vec::<u64>(1, &mut small),
        Err(ScreenFailure::Decline)
    ));
    let mut admitted = CheckedRefutationMeter::new(screen_limits(&executor), None, None).unwrap();
    let buffer = screen_vec::<u64>(1, &mut admitted).unwrap();
    assert!(buffer.capacity() >= 1);
    assert_eq!(
        MAX_SCREEN_BYTES - admitted.remaining_validation_limits().unwrap().max_bytes,
        buffer.capacity() * size_of::<u64>()
    );
    // Exercise the same excess-capacity admission used by screen_vec without
    // assuming that a particular allocator over-reserves try_reserve_exact.
    let mut tight_limits = screen_limits(&executor);
    tight_limits.max_bytes = 8;
    let mut tight = CheckedRefutationMeter::new(tight_limits, None, None).unwrap();
    tight.charge(1, 8).unwrap();
    assert!(matches!(
        charge_capacity_excess::<u64>(2, 1, &mut tight),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
}
