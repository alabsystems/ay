// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[derive(Clone, Copy)]
enum Refusal {
    Json,
    Shape,
    Writer,
}

fn refuse(fixture: &Fixture, case: Refusal, poll: &mut dyn FnMut() -> bool) -> WireOutcome<()> {
    match case {
        Refusal::Writer => {
            let out = encode(
                &payload(),
                &fixture.wire,
                &fixture.proof,
                &fixture.gates,
                poll,
            );
            WireOutcome {
                result: out.result.map(drop),
                usage: out.usage,
            }
        }
        Refusal::Json | Refusal::Shape => {
            let mut bytes = JSON.to_vec();
            let index = match case {
                Refusal::Json => bytes.len() - 1,
                _ => bytes.len() - 2,
            };
            bytes[index] = match case {
                Refusal::Json => b']',
                _ => b'4',
            };
            let out = decode(&bytes, &fixture.wire, &fixture.proof, &fixture.gates, poll);
            WireOutcome {
                result: out.result.map(drop),
                usage: out.usage,
            }
        }
    }
}

#[test]
fn json_shape_and_writer_failures_observe_the_final_cleanup_callback() {
    for case in [Refusal::Json, Refusal::Shape, Refusal::Writer] {
        let mut fixture = Fixture::new();
        if matches!(case, Refusal::Writer) {
            let out = fixture.encode(&payload());
            out.result.unwrap();
            fixture.wire.max_work = u64::try_from(out.usage.charged_work - 1).unwrap();
        }
        let mut calls = 0;
        let first = refuse(&fixture, case, &mut || {
            calls += 1;
            true
        });
        assert!(matches!(
            first.result,
            Err(WireError::InvalidJson | WireError::InvalidPayload(_) | WireError::Limit { .. })
        ));
        assert_eq!(first.usage.returned_owned_bytes, 0);
        assert!(calls > 10);
        let total = calls;
        calls = 0;
        let stopped = refuse(&fixture, case, &mut || {
            calls += 1;
            calls != total
        });
        assert_eq!(stopped.result, Err(WireError::Cancelled));
        assert_eq!(calls, total);
        assert_eq!(
            stopped.usage, first.usage,
            "cleanup does not refund charges"
        );
    }
}

struct Dropped<'a>(&'a Cell<bool>);

impl Drop for Dropped<'_> {
    fn drop(&mut self) {
        self.0.set(true);
    }
}

#[test]
fn failure_cleanup_precedes_external_observation_and_never_revives_errors() {
    let fixture = Fixture::new();
    let dropped = Cell::new(false);
    let mut calls = 0;
    let out: WireOutcome<()> = run(
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || {
            calls += 1;
            if calls == 2 {
                assert!(dropped.get());
                false
            } else {
                true
            }
        },
        |control| {
            let _owner = Dropped(&dropped);
            control.fail(WireError::InvalidPayload("test refusal"))
        },
    );
    assert_eq!(out.result, Err(WireError::Cancelled));
    assert_eq!(calls, 2);
    let out: WireOutcome<()> = run(
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || true,
        |control| {
            control.limits.deadline = Instant::now();
            control.fail(WireError::InvalidJson)
        },
    );
    assert_eq!(out.result, Err(WireError::Deadline));
    let out: WireOutcome<()> = run(
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || true,
        |control| control.fail(WireError::InvalidJson),
    );
    assert_eq!(out.result, Err(WireError::InvalidJson));
}

#[test]
fn a_success_stopped_at_final_boundary_drops_its_owner_before_return() {
    let fixture = Fixture::new();
    let dropped = Cell::new(false);
    let mut calls = 0;
    let out = run(
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || {
            calls += 1;
            assert!(!dropped.get());
            calls != 2
        },
        |_control| Ok(Dropped(&dropped)),
    );
    assert!(matches!(out.result, Err(WireError::Cancelled)));
    assert!(dropped.get());
    assert_eq!(calls, 2, "sticky cleanup check must not retry the callback");
    assert_eq!(out.usage.returned_owned_bytes, 0);
}
