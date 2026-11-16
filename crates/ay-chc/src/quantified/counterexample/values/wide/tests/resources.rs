// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn one_million_bit_limit_preserves_the_high_bit_and_rejects_larger_widths() {
    let width = crate::MAX_BITVECTOR_WIDTH;
    let value = (BigUint::from(1u8) << (width - 1) as usize) + BigUint::from(1u8);
    let registry = registry();
    let sort = ChcSort::BitVec(width);
    let decoded = decoded(&model(&value, width), &sort, &registry).unwrap();
    let SmtValue::BigBitVec(actual, recorded) = &decoded else {
        panic!("wide carrier")
    };
    assert_eq!(actual.as_ref(), &value);
    assert_eq!(*recorded, width);
    let rendered = text(&decoded, &sort, &registry).unwrap();
    assert_eq!(rendered.len(), width as usize + 2);
    assert!(rendered.starts_with("#b1") && rendered.ends_with('1'));
    assert!(rendered.as_bytes()[3..rendered.len() - 1]
        .iter()
        .all(|byte| *byte == b'0'));
    for width in [0, width + 1, u32::MAX] {
        assert!(super::decoded(
            &model(&BigUint::from(0u8), width),
            &ChcSort::BitVec(width),
            &registry
        )
        .is_none());
        assert!(text(
            &SmtValue::BigBitVec(Arc::new(BigUint::from(0u8)), width),
            &ChcSort::BitVec(width),
            &registry
        )
        .is_none());
    }
}

#[test]
fn binary_output_precharge_refuses_before_reserving_or_writing_any_prefix() {
    let width = crate::MAX_BITVECTOR_WIDTH;
    let value = BigUint::from(0u8);
    let output_bytes = (width as usize + 2) * 2;
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut codec = Codec::new(&control);
    codec.decoded_bytes = MAX_OUTPUT - output_bytes + 1;
    assert!(codec.write_big_bitvec(&value, width, width).is_none());
    assert_eq!(codec.text, "");
    assert_eq!(codec.text.capacity(), 0);
    let mut codec = Codec::new(&control);
    codec.decoded_bytes = MAX_OUTPUT - output_bytes;
    assert!(codec.write_big_bitvec(&value, width, width).is_some());
    assert_eq!(codec.decoded_bytes, MAX_OUTPUT);
    assert_eq!(codec.text.len(), width as usize + 2);
    // Shared budget accounts for work plus output before reserve as well.
    let control = SourceControl::new(deadline(), &token);
    let work = (width as usize).div_ceil(64) * 64;
    control
        .bytes(64 * 1024 * 1024 - work - output_bytes + 1)
        .unwrap();
    let mut codec = Codec::new(&control);
    assert!(codec.write_big_bitvec(&value, width, width).is_none());
    assert_eq!(codec.text, "");
    assert_eq!(codec.text.capacity(), 0);
    assert!(control.poll().is_none());
}

#[test]
fn bigint_clone_has_an_exact_local_precharge_and_zero_is_width_independent() {
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let width = 136;
    let value = (BigInt::from(1u8) << 135usize) + BigInt::from(7u8);
    let cost = (3 * 8 + std::mem::size_of::<BigUint>() + 2 * std::mem::size_of::<usize>()) * 2;
    let mut codec = Codec::new(&control);
    codec.decoded_bytes = MAX_OUTPUT - cost + 1;
    assert!(codec.decode_bitvec(&value, width, width).is_none());
    let mut codec = Codec::new(&control);
    codec.decoded_bytes = MAX_OUTPUT - cost;
    assert!(codec.decode_bitvec(&value, width, width).is_some());
    assert_eq!(codec.decoded_bytes, MAX_OUTPUT);
    let mut narrow = Codec::new(&control);
    let mut widest = Codec::new(&control);
    assert!(narrow.decode_bitvec(&BigInt::from(0), 129, 129).is_some());
    assert!(widest
        .decode_bitvec(
            &BigInt::from(0),
            crate::MAX_BITVECTOR_WIDTH,
            crate::MAX_BITVECTOR_WIDTH
        )
        .is_some());
    assert_eq!(narrow.decoded_bytes, widest.decoded_bytes);
}

#[test]
fn wide_shared_refusal_and_observed_cancellation_require_a_fresh_attempt() {
    let token = CancellationToken::new();
    let registry = registry();
    let sort = ChcSort::BitVec(136);
    let value = model(&(BigUint::from(1u8) << 135usize), 136);
    let control = SourceControl::new(deadline(), &token);
    token.cancel();
    assert!(decode(&value, &sort, &registry, &control).is_none());
    token.reset();
    assert!(decode(&value, &sort, &registry, &control).is_none());
    let fresh = SourceControl::new(deadline(), &token);
    let concrete = decode(&value, &sort, &registry, &fresh).unwrap();
    assert!(literal(&concrete, &sort, &registry, &fresh).is_some());
    let exhausted = SourceControl::new(deadline(), &token);
    assert!(exhausted.bytes(usize::MAX).is_none());
    assert!(literal(&concrete, &sort, &registry, &exhausted).is_none());
    assert!(decode(&value, &sort, &registry, &exhausted).is_none());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(literal(&concrete, &sort, &registry, &expired).is_none());
}
