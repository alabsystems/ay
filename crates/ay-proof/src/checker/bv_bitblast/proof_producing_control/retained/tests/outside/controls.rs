// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn both_frames_and_wrapper_share_one_exact_or_one_short_work_grant() {
    let (terms, clause) = fixture(Source::Valid);
    let bytes = capture_bytes(&terms, clause).value;
    for operation in [Operation::Capture, Operation::Replay] {
        let end = deadline();
        let (proof, gates) = limits(end);
        let wire = wire_limits(end);
        let run = |grant| {
            invoke(
                operation,
                &terms,
                clause,
                &bytes,
                &proof,
                &gates,
                &wire,
                WorkAllowance::new(grant, end),
                &mut || true,
            )
        };
        let usage = run(GRANT).unwrap();
        let exact = total(usage);
        let largest = [
            usage.producer_validation,
            usage.retained_prefix,
            usage.gates,
            usage.dag,
            usage.wire,
        ]
        .into_iter()
        .max()
        .unwrap();
        assert!(largest > 0 && largest < exact);
        assert_eq!(run(exact).unwrap(), usage);
        for grant in [0, largest, exact - 1] {
            assert!(
                run(grant).is_err(),
                "{operation:?}: grant={grant}, exact={exact}"
            );
        }
    }
}

#[test]
fn wire_caps_count_both_frames_and_all_role_wrapper_bytes() {
    let (terms, clause) = fixture(Source::Valid);
    let bytes = capture_bytes(&terms, clause).value;
    let end = deadline();
    let (proof, gates) = limits(end);
    let pair = wire::pair::decode(&bytes, &wire_limits(end), &proof, &gates, &mut || true)
        .result
        .unwrap();
    assert!(bytes.len() > pair[0].len() + pair[1].len());
    let payloads = pair.map(|frame| {
        wire::decode(frame, &wire_limits(end), &proof, &gates, &mut || true)
            .result
            .unwrap()
    });
    let rows = payloads.iter().map(|p| p.rows.len()).sum::<usize>();
    let literals = payloads
        .iter()
        .flat_map(|p| &p.rows)
        .map(|r| r.literals.len())
        .sum::<usize>();
    let hints = payloads
        .iter()
        .flat_map(|p| &p.rows)
        .map(|r| r.hints.len())
        .sum::<usize>();
    assert!(rows > 1 && hints > 0);
    for operation in [Operation::Capture, Operation::Replay] {
        let mut exact = wire_limits(end);
        exact.max_json_bytes = bytes.len();
        exact.max_rows = rows;
        exact.max_literals = literals;
        exact.max_hints = hints;
        invoke(
            operation,
            &terms,
            clause,
            &bytes,
            &proof,
            &gates,
            &exact,
            WorkAllowance::new(GRANT, end),
            &mut || true,
        )
        .unwrap();
        for cap in 0..6 {
            let mut short = exact;
            match cap {
                0 => short.max_json_bytes -= 1,
                1 => short.max_rows -= 1,
                2 if literals > 0 => short.max_literals -= 1,
                2 => continue,
                3 => short.max_hints -= 1,
                4 => short.max_storage_bytes = 0,
                5 => short.max_work = 0,
                _ => unreachable!(),
            }
            assert!(
                invoke(
                    operation,
                    &terms,
                    clause,
                    &bytes,
                    &proof,
                    &gates,
                    &short,
                    WorkAllowance::new(GRANT, end),
                    &mut || true,
                )
                .is_err(),
                "{operation:?}: cap={cap}"
            );
        }
    }
}

#[test]
fn entry_interior_and_final_callback_stops_cannot_publish_a_pair() {
    let (terms, clause) = fixture(Source::Valid);
    let bytes = capture_bytes(&terms, clause).value;
    let before = terms.entries_snapshot();
    for operation in [Operation::Capture, Operation::Replay] {
        let end = deadline();
        let (proof, gates) = limits(end);
        let wire = wire_limits(end);
        let calls = Cell::new(0);
        let run = |stop_at| {
            calls.set(0);
            invoke(
                operation,
                &terms,
                clause,
                &bytes,
                &proof,
                &gates,
                &wire,
                WorkAllowance::new(GRANT, end),
                &mut || {
                    calls.set(calls.get() + 1);
                    calls.get() != stop_at
                },
            )
        };
        run(0).unwrap();
        let total = calls.get();
        assert!(total > 10);
        // Sample decisive boundaries; do not repeat SAT search O(polls) times.
        for stop_at in [1, total / 2, total] {
            let producers = producer_test_counter::count();
            assert!(
                matches!(
                    run(stop_at),
                    Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
                ),
                "{operation:?}: stop_at={stop_at}"
            );
            assert_eq!(calls.get(), stop_at);
            if matches!(operation, Operation::Replay) || stop_at == 1 {
                assert_eq!(producer_test_counter::count(), producers);
            }
        }
    }
    assert_eq!(terms.entries_snapshot(), before);
}

#[test]
fn every_original_deadline_constrains_the_two_frame_operation_before_polling() {
    let (terms, clause) = fixture(Source::Valid);
    let past = Instant::now() - Duration::from_secs(1);
    let calls = producer_test_counter::count();
    for operation in [Operation::Capture, Operation::Replay] {
        for expired in 0..5 {
            let end = deadline();
            let (mut proof, mut gates) = limits(end);
            let mut wire = wire_limits(end);
            let credit_end = if expired == 0 { past } else { end };
            match expired {
                1 => wire.deadline = past,
                2 => proof.resolution.deadline = Some(past),
                3 => proof.resolution.validation.deadline = Some(past),
                4 => gates.deadline = Some(past),
                _ => {}
            }
            assert!(matches!(
                invoke(
                    operation,
                    &terms,
                    clause,
                    b"",
                    &proof,
                    &gates,
                    &wire,
                    WorkAllowance::new(GRANT, credit_end),
                    &mut || panic!("an expired source clock must refuse before callbacks"),
                ),
                Err(MeteredBridgeError::Bridge(BridgeError::Deadline))
            ));
        }
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn invalid_pair_cleanup_retains_a_transient_cancellation() {
    let (terms, clause) = fixture(Source::Valid);
    let end = deadline();
    let (proof, gates) = limits(end);
    let wire = wire_limits(end);
    let calls = Cell::new(0);
    let run = |stop_at| {
        calls.set(0);
        invoke(
            Operation::Replay,
            &terms,
            clause,
            b"[",
            &proof,
            &gates,
            &wire,
            WorkAllowance::new(GRANT, end),
            &mut || {
                calls.set(calls.get() + 1);
                calls.get() != stop_at
            },
        )
    };
    assert!(run(0).is_err());
    let last = calls.get();
    assert!(last > 2);
    let producers = producer_test_counter::count();
    assert!(matches!(
        run(last),
        Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
    ));
    assert_eq!(calls.get(), last);
    assert_eq!(producer_test_counter::count(), producers);
}
