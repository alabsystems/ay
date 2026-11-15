// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Framing controls only: fake inner objects are never proof authority.

use super::*;

struct Fixture {
    wire: WireLimits,
    proof: BvExprProofLimits,
    gates: BvBlastValidateLimits,
}

impl Fixture {
    fn new() -> Self {
        let end = Instant::now() + Duration::from_secs(60);
        Self {
            wire: WireLimits {
                max_json_bytes: 4096,
                max_rows: 100,
                max_literals: 1000,
                max_hints: 1000,
                max_work: 100_000,
                max_storage_bytes: 1024 * 1024,
                deadline: end,
            },
            proof: BvExprProofLimits::conservative_external(end, 100),
            gates: BvBlastValidateLimits {
                deadline: Some(end),
                max_vars: 4096,
                max_bit_lemmas: 4096,
                max_clauses: 16000,
                max_clause_literals: 64,
                max_original_literals: 64000,
                max_resolution_steps: 100,
                max_derived_literals: 10000,
                max_work: 100_000,
            },
        }
    }

    fn encode(&self, plan: FrameSet, frames: &[&[u8]]) -> WireOutcome<Vec<u8>> {
        encode_frames(
            plan,
            frames,
            &self.wire,
            &self.proof,
            &self.gates,
            &mut || true,
        )
    }

    fn decode<'a>(&self, plan: FrameSet, bytes: &'a [u8]) -> WireOutcome<[&'a [u8]; 3]> {
        decode_frames(
            plan,
            bytes,
            &self.wire,
            &self.proof,
            &self.gates,
            &mut || true,
        )
    }
}

fn outside() -> &'static [u8] {
    br#"[{"outside_free_offset":{}},{"final_clause":{"x":1}}]"#
}

#[test]
fn every_closed_role_plan_has_exact_order_and_borrows_inner_objects() {
    let fixture = Fixture::new();
    let frames: [&[u8]; 3] = [b"{}", br#"{"x":1}"#, br#"{"y":2}"#];
    for plan in [FrameSet::Outside, FrameSet::Disjoint, FrameSet::Combined] {
        let encoded = fixture.encode(plan, &frames[..plan.frame_count()]);
        let bytes = encoded.result.unwrap();
        let length = plan.overhead()
            + frames[..plan.frame_count()]
                .iter()
                .map(|frame| frame.len())
                .sum::<usize>();
        assert_eq!(bytes.len(), length);
        assert_eq!(
            encoded.usage.returned_owned_bytes,
            size_of::<Vec<u8>>() + bytes.capacity()
        );
        let decoded = fixture.decode(plan, &bytes);
        let value = decoded.result.unwrap();
        assert_eq!(&value[..plan.frame_count()], &frames[..plan.frame_count()]);
        for frame in &value[..plan.frame_count()] {
            let offset = frame.as_ptr() as usize - bytes.as_ptr() as usize;
            assert!(offset + frame.len() <= bytes.len());
        }
        assert_eq!(decoded.usage.returned_owned_bytes, 0);
        assert_eq!(decoded.usage.peak_storage_bytes, bytes.len());
        for other in [FrameSet::Outside, FrameSet::Disjoint, FrameSet::Combined] {
            if other != plan {
                assert!(fixture.decode(other, &bytes).result.is_err());
            }
        }
    }
    assert_eq!(FrameSet::Outside.overhead(), OVERHEAD);
    assert_eq!(
        fixture
            .encode(FrameSet::Outside, &frames[..2])
            .result
            .unwrap(),
        outside()
    );
}

#[test]
fn fixed_frame_counts_roles_object_shapes_and_trailing_bytes_are_required() {
    let fixture = Fixture::new();
    for bad in [
        br#"[]"#.as_slice(),
        br#"[{"outside_free_offset":{}}]"#,
        br#"[{"final_clause":{}},{"outside_free_offset":{}}]"#,
        br#"[{"outside_free_offset":{}},{"final_clause":{}},{"final_clause":{}}]"#,
        br#"[{"outside_free_offset":{},"extra":{}},{"final_clause":{}}]"#,
        br#"[{"outside_free_offset ":{}},{"final_clause":{}}]"#,
        br#"[{"\u006futside_free_offset":{}},{"final_clause":{}}]"#,
        br#"[{"outside_free_offset":[]},{"final_clause":{}}]"#,
        br#"[{"outside_free_offset":{}},{"final_clause":{}}]0"#,
    ] {
        assert!(
            fixture.decode(FrameSet::Outside, bad).result.is_err(),
            "{bad:?}"
        );
    }
    for count in [0, 1, 3] {
        let frames = [b"{}".as_slice(); 3];
        assert_eq!(
            fixture.encode(FrameSet::Outside, &frames[..count]).result,
            Err(WireError::InvalidPayload("frame count"))
        );
    }
    let spaced = b" \n [ { \"outside_free_offset\" : {} }, { \"final_clause\" : {} } ] \t";
    assert!(fixture.decode(FrameSet::Outside, spaced).result.is_ok());
}

#[test]
fn inner_depth_four_is_exact_and_strings_do_not_change_nesting() {
    let fixture = Fixture::new();
    let depth_four = br#"{"a":[[[0]]],"text":"}]\"[[["}"#;
    let bytes = fixture
        .encode(FrameSet::Outside, &[depth_four, b"{}"])
        .result
        .unwrap();
    let frames = fixture.decode(FrameSet::Outside, &bytes).result.unwrap();
    assert_eq!(frames[0], depth_four);
    for bad in [br#"{"a":[[[[0]]]]}"#.as_slice(), br#"{"a":[0}}"#] {
        let bytes = fixture
            .encode(FrameSet::Outside, &[bad, b"{}"])
            .result
            .unwrap();
        assert_eq!(
            fixture.decode(FrameSet::Outside, &bytes).result,
            Err(WireError::InvalidJson)
        );
    }
    // Splitting alone does not validate inner JSON or confer wire authority.
    let bytes = fixture
        .encode(FrameSet::Outside, &[b"{garbage}", b"{}"])
        .result
        .unwrap();
    let frames = fixture.decode(FrameSet::Outside, &bytes).result.unwrap();
    assert!(super::super::decode(
        frames[0],
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || true,
    )
    .result
    .is_err());
}

#[test]
fn framing_work_json_and_storage_grants_are_exact_and_not_renewed() {
    let mut fixture = Fixture::new();
    let plan = FrameSet::Outside;
    let frames: [&[u8]; 2] = [b"{}", br#"{"x":1}"#];
    let baseline = fixture.encode(plan, &frames);
    let bytes = baseline.result.unwrap();
    fixture.wire.max_json_bytes = plan.overhead();
    fixture.wire.max_work = baseline.usage.charged_work.try_into().unwrap();
    fixture.wire.max_storage_bytes = baseline.usage.peak_storage_bytes;
    assert!(fixture.encode(plan, &frames).result.is_ok());
    fixture.wire.max_work -= 1;
    assert!(fixture.encode(plan, &frames).result.is_err());
    fixture.wire.max_work += 1;
    fixture.wire.max_json_bytes -= 1;
    assert!(fixture.encode(plan, &frames).result.is_err());
    fixture.wire.max_json_bytes += 1;
    fixture.wire.max_storage_bytes = size_of::<Vec<u8>>() + bytes.len() - 1;
    assert!(fixture.encode(plan, &frames).result.is_err());

    let mut fixture = Fixture::new();
    let decoded = fixture.decode(plan, &bytes);
    assert!(decoded.result.is_ok());
    fixture.wire.max_json_bytes = bytes.len();
    fixture.wire.max_storage_bytes = bytes.len();
    fixture.wire.max_work = decoded.usage.charged_work.try_into().unwrap();
    assert!(fixture.decode(plan, &bytes).result.is_ok());
    fixture.wire.max_work -= 1;
    assert!(fixture.decode(plan, &bytes).result.is_err());
    fixture.wire.max_work += 1;
    fixture.wire.max_storage_bytes -= 1;
    assert!(fixture.decode(plan, &bytes).result.is_err());
    fixture.wire.max_storage_bytes += 1;
    fixture.wire.max_json_bytes -= 1;
    assert!(fixture.decode(plan, &bytes).result.is_err());
}

#[test]
fn every_small_encode_and_decode_callback_stop_publishes_nothing() {
    let fixture = Fixture::new();
    for encode in [false, true] {
        let mut total = 0;
        let mut poll = || {
            total += 1;
            true
        };
        let success = if encode {
            super::encode(
                [b"{}", br#"{"x":1}"#],
                &fixture.wire,
                &fixture.proof,
                &fixture.gates,
                &mut poll,
            )
            .result
            .map(|_| ())
        } else {
            decode(
                outside(),
                &fixture.wire,
                &fixture.proof,
                &fixture.gates,
                &mut poll,
            )
            .result
            .map(|_| ())
        };
        success.unwrap();
        assert!(total >= 3);
        for stop in 1..=total {
            let mut calls = 0;
            let mut poll = || {
                calls += 1;
                calls != stop
            };
            let (result, usage) = if encode {
                let outcome = super::encode(
                    [b"{}", br#"{"x":1}"#],
                    &fixture.wire,
                    &fixture.proof,
                    &fixture.gates,
                    &mut poll,
                );
                (outcome.result.map(|_| ()), outcome.usage)
            } else {
                let outcome = decode(
                    outside(),
                    &fixture.wire,
                    &fixture.proof,
                    &fixture.gates,
                    &mut poll,
                );
                (outcome.result.map(|_| ()), outcome.usage)
            };
            assert_eq!(result, Err(WireError::Cancelled));
            assert_eq!(usage.returned_owned_bytes, 0);
            assert_eq!(calls, stop, "a transient refusal cannot be reset");
        }
    }
}

#[test]
fn cleanup_stop_overrides_invalid_shape_without_reviving_the_operation() {
    let fixture = Fixture::new();
    let mut total = 0;
    assert!(decode(
        b"[]",
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || {
            total += 1;
            true
        }
    )
    .result
    .is_err());
    assert!(total >= 3);
    let mut calls = 0;
    let outcome = decode(
        b"[]",
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || {
            calls += 1;
            calls != total
        },
    );
    assert_eq!(outcome.result, Err(WireError::Cancelled));
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
    assert_eq!(calls, total);
}

#[test]
fn every_original_deadline_is_a_minimum_and_absence_is_not_renewed() {
    for index in 0..4 {
        let mut fixture = Fixture::new();
        let expired = Instant::now() - Duration::from_secs(1);
        match index {
            0 => fixture.wire.deadline = expired,
            1 => fixture.proof.resolution.deadline = Some(expired),
            2 => fixture.proof.resolution.validation.deadline = Some(expired),
            3 => fixture.gates.deadline = Some(expired),
            _ => unreachable!(),
        }
        let mut calls = 0;
        let result = decode(
            outside(),
            &fixture.wire,
            &fixture.proof,
            &fixture.gates,
            &mut || {
                calls += 1;
                true
            },
        );
        assert_eq!(result.result, Err(WireError::Deadline));
        assert_eq!(calls, 0);
    }
    let mut fixture = Fixture::new();
    fixture.proof.resolution.deadline = None;
    assert_eq!(
        fixture.decode(FrameSet::Outside, outside()).result,
        Err(WireError::MissingDeadline)
    );
}
