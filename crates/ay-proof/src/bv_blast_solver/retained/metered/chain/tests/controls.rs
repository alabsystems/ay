// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn caught_precheck_and_wire_errors_poison_the_whole_child() {
    let (mut proof, gates, wire) = limits();
    let (lhs, rhs) = source(0);
    proof.resolution.max_conflicts = None;
    let calls = producer_test_counter::count();
    let result = run(
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true,
        |chain| {
            assert!(matches!(
                chain.capture_one(&lhs, &rhs, &proof, &gates),
                Err(MeteredError::Proof(BvExprExportError::Malformed(_)))
            ));
            assert!(matches!(
                chain.capture_one(&lhs, &rhs, &proof, &gates),
                Err(MeteredError::Work(WorkError::Refused))
            ));
            Ok(())
        },
    );
    assert!(matches!(
        result,
        Err(MeteredError::Work(WorkError::Refused))
    ));
    assert_eq!(producer_test_counter::count(), calls);
    let (proof, _, _) = limits();
    let result = run(
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true,
        |chain| {
            assert!(matches!(
                chain.replay_one(&lhs, &rhs, b"null", &proof, &gates),
                Err(MeteredError::Wire(_))
            ));
            assert!(matches!(
                chain.capture_one(&lhs, &rhs, &proof, &gates),
                Err(MeteredError::Work(WorkError::Refused))
            ));
            Ok(())
        },
    );
    assert!(matches!(
        result,
        Err(MeteredError::Work(WorkError::Refused))
    ));
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn every_chain_capture_and_replay_poll_is_terminal_including_cleanup() {
    let frames = capture_many::<2>(1_000_000).unwrap().value;
    for capturing in [true, false] {
        let invoke = |poll: &mut dyn FnMut() -> bool| {
            let (mut proof, gates, wire) = limits();
            if !capturing {
                no_search(&mut proof);
            }
            run(&proof, &gates, &wire, allowance(1_000_000), poll, |chain| {
                let mut output = [Vec::new(), Vec::new()];
                for index in 0..2 {
                    let (lhs, rhs) = source(index);
                    if capturing {
                        output[index] = chain.capture_one(&lhs, &rhs, &proof, &gates)?;
                    } else {
                        chain.replay_one(&lhs, &rhs, &frames[index], &proof, &gates)?;
                    }
                }
                Ok(output)
            })
        };
        let count = Cell::new(0);
        invoke(&mut || {
            count.set(count.get() + 1);
            true
        })
        .unwrap();
        assert!(count.get() > 10);
        for stop in 1..=count.get() {
            let seen = Cell::new(0);
            assert!(
                invoke(&mut || {
                    seen.set(seen.get() + 1);
                    seen.get() != stop
                })
                .is_err(),
                "capture={capturing}, poll={stop}"
            );
            assert_eq!(seen.get(), stop);
        }
    }
}

#[test]
fn caught_child_callback_panics_cannot_resume_even_at_post_payload_cleanup() {
    let frames = capture_many::<2>(1_000_000).unwrap().value;
    let (mut proof, gates, wire) = limits();
    no_search(&mut proof);
    let (lhs, rhs) = source(0);
    let calls = Cell::new(0);
    let last_child_poll = Cell::new(0);
    run(
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || {
            calls.set(calls.get() + 1);
            true
        },
        |chain| {
            chain.replay_one(&lhs, &rhs, &frames[0], &proof, &gates)?;
            last_child_poll.set(calls.get());
            Ok(())
        },
    )
    .unwrap();
    // Final child poll lies OUTSIDE every Ledger::phase and after the payload
    // has dropped. Also exercise a parser/phase callback panic.
    for panic_at in [2, last_child_poll.get()] {
        let seen = Cell::new(0);
        let result = run(
            &proof,
            &gates,
            &wire,
            allowance(1_000_000),
            &mut || {
                seen.set(seen.get() + 1);
                assert_ne!(seen.get(), panic_at, "test callback panic");
                true
            },
            |chain| {
                assert!(catch_unwind(AssertUnwindSafe(
                    || chain.replay_one(&lhs, &rhs, &frames[0], &proof, &gates)
                ))
                .is_err());
                assert!(matches!(
                    chain.replay_one(&lhs, &rhs, &frames[0], &proof, &gates),
                    Err(MeteredError::Work(WorkError::Refused))
                ));
                Ok(())
            },
        );
        assert!(result.is_err());
        assert_eq!(seen.get(), panic_at);
    }
}

#[test]
fn child_deadlines_only_shorten_and_expired_child_cannot_enter_producer() {
    let (proof, gates, wire) = limits();
    let end = wire.deadline - Duration::from_secs(1);
    for field in 0..3 {
        let mut child = proof.clone();
        let mut child_gates = gates;
        match field {
            0 => child.resolution.deadline = Some(end),
            1 => child.resolution.validation.deadline = Some(end),
            2 => child_gates.deadline = Some(end),
            _ => unreachable!(),
        }
        let (lhs, rhs) = source(0);
        run(
            &proof,
            &gates,
            &wire,
            allowance(1_000_000),
            &mut || true,
            |chain| {
                drop(chain.capture_one(&lhs, &rhs, &child, &child_gates)?);
                assert_eq!(chain.end, end);
                drop(chain.capture_one(&lhs, &rhs, &proof, &gates)?);
                assert_eq!(chain.end, end);
                Ok(())
            },
        )
        .unwrap();
        child.resolution.deadline = Some(Instant::now() - Duration::from_secs(1));
        let before = producer_test_counter::count();
        assert!(run(
            &proof,
            &gates,
            &wire,
            allowance(1_000_000),
            &mut || true,
            |chain| { chain.capture_one(&lhs, &rhs, &child, &child_gates) }
        )
        .is_err());
        assert_eq!(producer_test_counter::count(), before);
    }
}

#[test]
fn odd_child_caps_and_zero_caps_remain_independent_of_abundant_credit() {
    let (proof, gates, wire) = limits();
    let mut child = proof.clone();
    let mut child_gates = gates;
    child.resolution.validation.max_work = 101 / 2;
    child_gates.max_work = 101 / 4;
    let (got, got_gates) = limits::child(&proof, &gates, &child, &child_gates, wire.deadline);
    assert_eq!(got.resolution.validation.max_work, 50);
    assert_eq!(got_gates.max_work, 25);
    let (lhs, rhs) = source(0);
    child_gates.max_work = 0;
    let result = run(
        &proof,
        &gates,
        &wire,
        allowance(u64::MAX),
        &mut || true,
        |chain| chain.capture_one(&lhs, &rhs, &proof, &child_gates),
    );
    assert!(result.is_err());
    child.resolution.validation.max_work = 0;
    assert!(run(
        &proof,
        &gates,
        &wire,
        allowance(u64::MAX),
        &mut || true,
        |chain| { chain.capture_one(&lhs, &rhs, &child, &gates) }
    )
    .is_err());
}

#[test]
fn failure_cleanup_stop_dominates_wire_error_and_drops_closure_success() {
    let (proof, gates, wire) = limits();
    let (lhs, rhs) = source(0);
    let failed = Cell::new(false);
    let dropped = Cell::new(false);
    struct Witness<'a>(&'a Cell<bool>);
    impl Drop for Witness<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    let result = run(
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || {
            if failed.get() {
                assert!(dropped.get());
                false
            } else {
                true
            }
        },
        |chain| {
            assert!(chain
                .replay_one(&lhs, &rhs, b"null", &proof, &gates)
                .is_err());
            failed.set(true);
            Ok(Witness(&dropped))
        },
    );
    assert!(matches!(
        result,
        Err(MeteredError::Proof(BvExprExportError::Cancelled))
    ));
    assert!(dropped.get());
}
