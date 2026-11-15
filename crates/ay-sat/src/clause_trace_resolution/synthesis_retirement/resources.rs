// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[test]
fn synthesis_retirement_every_transient_stop_and_work_boundary_is_terminal() {
    let fixture = fixture(3, 3, 16);
    let run = |stop_at: usize, allowance: u64| {
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = allowance;
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            let hints = synthesize(&fixture, &[pos(0)], &[], &mut meter)?;
            assert_eq!(hints, Some(fixture.expected[0].clone()));
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        (result, calls.get())
    };
    let (complete, polls) = run(usize::MAX, u64::MAX);
    let work = complete.unwrap();
    assert!(polls > 5);
    for stop_at in 1..=polls {
        let (result, calls) = run(stop_at, u64::MAX);
        assert_eq!(result, Err(ResolutionValidationError::Cancelled));
        assert_eq!(calls, stop_at, "observed stop cannot restart a later phase");
    }
    assert_eq!(run(usize::MAX, work).0, Ok(work));
    for allowance in 0..work {
        assert!(matches!(
            run(usize::MAX, allowance).0,
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                ..
            })
        ));
    }
}

#[test]
fn synthesis_retirement_clear_is_chunked_and_cannot_admit_after_a_stop() {
    let run = |stop_at: usize, allowance: u64| {
        let mut bytes = vec![0; CONTROL_POLL_INTERVAL + 1];
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = allowance;
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            let mut retired =
                SynthesisRetirement::new(&mut bytes, 8 * CONTROL_POLL_INTERVAL, 1, &mut meter)?;
            retired.mark(0, &mut meter)?;
            retired.mark(8 * CONTROL_POLL_INTERVAL, &mut meter)?;
            assert_eq!(retired.0[0], 1);
            assert_eq!(retired.0[CONTROL_POLL_INTERVAL], 1);
            retired.clear(&mut meter)?;
            assert!(bytes.iter().all(|&byte| byte == 0));
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        // On an error this one-shot buffer is discarded, never used as cone
        // marks. A later row starts with its own zeroed admitted allocation.
        (result, calls.get())
    };
    let (complete, polls) = run(usize::MAX, u64::MAX);
    let work = complete.unwrap();
    assert_eq!(work, CONTROL_POLL_INTERVAL as u64 + 6);
    assert!(polls >= 7);
    for stop_at in 1..=polls {
        let (result, calls) = run(stop_at, u64::MAX);
        assert_eq!(result, Err(ResolutionValidationError::Cancelled));
        assert_eq!(calls, stop_at);
    }
    assert_eq!(run(usize::MAX, work).0, Ok(work));
    assert!(matches!(
        run(usize::MAX, work - 1).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
}

#[test]
fn synthesis_retirement_preserves_byte_admission_and_expired_deadlines() {
    let fixture = fixture(3, 3, 7);
    let admitted = planned_synthesis_scratch_bytes(fixture.num_vars, 0).unwrap();
    let run = |bytes: usize, deadline: Option<Instant>| {
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.deadline = deadline;
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop)?;
        synthesize_rup_hints(
            &fixture.originals,
            &fixture.derived,
            &[pos(0)],
            &[],
            fixture.num_vars,
            usize::MAX,
            0,
            bytes,
            &mut meter,
        )
    };
    assert_eq!(
        run(admitted, None).unwrap(),
        Some(fixture.expected[0].clone())
    );
    assert!(matches!(
        run(admitted - 1, None),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    assert_eq!(
        run(admitted, Some(Instant::now())),
        Err(ResolutionValidationError::DeadlineExceeded)
    );

    let mut bytes = [1u8; 1];
    let mut expired = ResolutionValidationLimits::unbounded();
    expired.deadline = Some(Instant::now());
    let mut stop = || panic!("deadline is checked before the cancellation callback");
    let mut meter = ConversionMeter {
        limits: &expired,
        should_stop: &mut stop,
        work: 0,
        attribution: WorkAttribution::default(),
    };
    assert_eq!(
        SynthesisRetirement(&mut bytes).clear(&mut meter),
        Err(ResolutionValidationError::DeadlineExceeded)
    );
    assert_eq!(
        bytes,
        [1],
        "failed cleanup cannot advance to cone admission"
    );
}

#[test]
fn synthesis_retirement_seed_shortcuts_and_malformed_sources_stay_fail_closed() {
    let fixture = fixture(3, 3, 7);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    for (target, premises) in [
        (vec![pos(0), neg(0)], vec![]),
        (vec![], vec![pos(0), neg(0)]),
        (vec![pos(0)], vec![pos(0)]),
    ] {
        assert_eq!(
            synthesize(&fixture, &target, &premises, &mut meter).unwrap(),
            Some(vec![])
        );
    }
    assert!(matches!(
        synthesize(&fixture, &[pos(99)], &[], &mut meter),
        Err(ResolutionValidationError::Invalid(
            ResolutionDagValidateError::VarOutOfRange { .. }
        ))
    ));
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![pos(0), pos(99)], true);
    trace.add_clause(2, vec![pos(0)], true);
    trace.add_clause(3, vec![neg(0)], true);
    trace.add_clause_with_hints(4, vec![], false, vec![2, 3]);
    assert!(
        validate_clause_trace_resolution(&trace, 2, &limits).is_err(),
        "whole-source admission still checks an otherwise satisfied malformed tail"
    );
}
