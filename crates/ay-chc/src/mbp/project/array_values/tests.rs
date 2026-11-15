// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, NodeLabel};
use num_bigint::BigUint;
use num_traits::One;
use std::sync::atomic::{AtomicUsize, Ordering};

fn array_case(sort: ChcSort, value: SmtValue) -> (ChcVar, SmtValue) {
    (
        ChcVar::new(
            "numeric_array",
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(sort)),
        ),
        SmtValue::ConstArray(Box::new(value)),
    )
}

fn height(expr: &ChcExpr) -> usize {
    match expr {
        ChcExpr::Op(_, args) => 1 + args.iter().map(|arg| height(arg)).max().unwrap_or(0),
        ChcExpr::ConstArray(_, value) => 1 + height(value),
        _ => 0,
    }
}

fn default_expr(expr: &ChcExpr) -> &ChcExpr {
    let ChcExpr::ConstArray(_, value) = expr else {
        panic!("typed const array expected")
    };
    value
}

#[test]
fn balanced_bv_conversion_preserves_partial_and_odd_high_chunks() {
    // Three, five and seven chunks must retain an odd high block across rounds.
    for width in [
        129,
        255,
        256,
        257,
        513,
        769,
        16_385,
        crate::MAX_BITVECTOR_WIDTH,
    ] {
        let number = (BigUint::one() << (width - 1) as usize)
            + (BigUint::one() << (width / 2) as usize)
            + BigUint::from(3u8);
        let (var, value) = array_case(
            ChcSort::BitVec(width),
            SmtValue::BigBitVec(Arc::new(number.clone()), width),
        );
        let expr = model_value(&var, Some(&value)).expect("full supported width admitted");
        assert_eq!(expr.sort(), var.sort);
        let evaluated =
            crate::expr::evaluate::evaluate_expr(default_expr(&expr), &Default::default())
                .expect("balanced literal evaluates");
        assert_eq!(evaluated.bitvec_to_biguint(), Some((number, width)));
        let levels = usize::BITS as usize
            - (width as usize)
                .div_ceil(128)
                .saturating_sub(1)
                .leading_zeros() as usize;
        assert_eq!(height(&expr), levels + 1);
    }
}

#[test]
fn balanced_signed_integer_conversion_preserves_three_five_and_seven_limbs() {
    for bits in [128usize, 129, 191, 256, 257, 384, 4097] {
        let magnitude =
            (BigInt::one() << bits) + (BigInt::one() << (bits / 2)) + BigInt::from(37u8);
        for number in [magnitude.clone(), -magnitude] {
            let (var, value) = array_case(ChcSort::Int, SmtValue::BigInt(Arc::new(number.clone())));
            let expr = model_value(&var, Some(&value)).expect("balanced integer admitted");
            assert_eq!(expr.sort(), var.sort);
            assert_eq!(
                crate::expr::evaluate::eval_int_big(default_expr(&expr), &Default::default()),
                Some(number),
            );
            assert!(height(&expr) < 32, "no Horner spine");
        }
    }
}

#[test]
fn narrow_bv_reads_only_low_limbs_of_an_enormous_noncanonical_payload() {
    let number = (BigUint::one() << 8_000_000usize) + BigUint::from(0x1abu32);
    let (var, value) = array_case(ChcSort::BitVec(8), SmtValue::BigBitVec(Arc::new(number), 8));
    let owner = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(5)));
    let _entered = owner.enter();
    let expr = model_value(&var, Some(&value)).expect("only four small conversion units");
    assert_eq!(default_expr(&expr), &ChcExpr::BitVec(0xab, 8));
    assert_eq!(owner.ticks(), 4);
}

#[test]
fn numeric_work_uses_original_guard_and_exact_limit_does_not_fallback() {
    let (var, value) = array_case(
        ChcSort::BitVec(769),
        SmtValue::BigBitVec(Arc::new((BigUint::one() << 768usize) + BigUint::one()), 769),
    );
    let run = |limit| {
        let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(limit));
        let _entered = guard.enter();
        let result = model_value_or_default(&var, Some(&value));
        (result, guard.ticks())
    };
    let (healthy, work) = run(None);
    assert!(healthy.is_some());
    assert!(work > 7);
    let (same, spent) = run(Some(work + 1));
    assert_eq!(same, healthy);
    assert_eq!(spent, work);
    for limit in [3, work / 2, work] {
        assert!(
            run(Some(limit)).0.is_none(),
            "no renewed default after count stop"
        );
    }

    let original = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(4)));
    let entered = original.enter();
    let mut owner = Owner::capture();
    drop(entered);
    let replacement = Guard::new();
    let _entered = replacement.enter();
    assert!(owner.literal(&var.sort, &value, 0).is_none());
    assert!(original.ticks() >= 4);
    assert_eq!(replacement.ticks(), 0);
    assert!(owner.default(&var.sort, 0).is_none());
}

#[test]
fn numeric_conversion_stops_at_every_original_callback_poll() {
    let cases = [
        array_case(
            ChcSort::Int,
            SmtValue::BigInt(Arc::new(-(BigInt::one() << 257usize))),
        ),
        array_case(
            ChcSort::BitVec(257),
            SmtValue::BigBitVec(Arc::new(BigUint::one() << 256usize), 257),
        ),
    ];
    for (var, value) in cases {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let entered = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }));
        assert!(model_value_or_default(&var, Some(&value)).is_some());
        drop(entered);
        let total = calls.load(Ordering::SeqCst);
        assert!(total > 8, "inner construction must cooperate");
        for stop_at in 0..total {
            let calls = Arc::new(AtomicUsize::new(0));
            let observed = Arc::clone(&calls);
            let _entered = enter_check_stop(Arc::new(move || {
                observed.fetch_add(1, Ordering::SeqCst) == stop_at
            }));
            assert!(model_value_or_default(&var, Some(&value)).is_none());
            assert_eq!(calls.load(Ordering::SeqCst), stop_at + 1);
        }
    }
}

#[test]
fn numeric_candidate_allocation_is_finite_even_without_a_guard() {
    let number = BigInt::one() << 6_000_000usize;
    let (var, value) = array_case(ChcSort::Int, SmtValue::BigInt(Arc::new(number)));
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let _entered = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        false
    }));
    assert!(model_value_or_default(&var, Some(&value)).is_none());
    assert_eq!(
        calls.load(Ordering::SeqCst),
        4,
        "refuse before numeric buffers"
    );
}

#[test]
fn numeric_height_and_credit_are_cumulative_with_the_enclosing_array() {
    let number = SmtValue::BigBitVec(Arc::new(BigUint::one() << 256usize), 257);
    let mut owner = Owner::capture();
    assert!(owner
        .literal(&ChcSort::BitVec(257), &number, MAX_DEPTH - 2)
        .is_some());
    assert!(owner
        .literal(&ChcSort::BitVec(257), &number, MAX_DEPTH - 1)
        .is_none());
    assert!(owner.default(&ChcSort::Bool, 0).is_none());

    let mut owner = Owner::capture();
    let (var, value) = array_case(ChcSort::BitVec(257), number);
    let initial = owner.remaining;
    assert!(owner.literal(&var.sort, &value, 0).is_some());
    let work = initial - owner.remaining;
    owner.remaining = work - 1;
    assert!(owner.literal(&var.sort, &value, 0).is_none());
    assert!(owner.default(&var.sort, 0).is_none());
}

#[test]
fn unsupported_bv_sorts_stay_symbolic_in_keys_and_default_elements() {
    for width in [0, crate::MAX_BITVECTOR_WIDTH + 1, u32::MAX] {
        let (element, value) = array_case(ChcSort::BitVec(width), SmtValue::BitVec(0, width));
        assert!(model_value_or_default(&element, Some(&value)).is_none());
        assert!(model_value_or_default(&element, None).is_none());
        let key = ChcVar::new(
            "bad_key",
            ChcSort::Array(Box::new(ChcSort::BitVec(width)), Box::new(ChcSort::Bool)),
        );
        assert!(model_value_or_default(&key, None).is_none());
    }
    let maximum = ChcVar::new(
        "full_width",
        ChcSort::Array(
            Box::new(ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH)),
            Box::new(ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH)),
        ),
    );
    let expr = model_value_or_default(&maximum, None).expect("both full-width sorts supported");
    assert_eq!(expr.sort(), maximum.sort);
}
