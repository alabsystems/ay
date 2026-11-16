// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Leaf-only controls: test RawValue parsing stands in for prior input admission.

use super::*;
use crate::bundle::retained::{control, RawValue, TransportOutcome};
use ay_core::time::Instant;
use serde::{Deserialize, Serialize};
use std::{cell::Cell, time::Duration};

#[derive(Debug, Serialize, Deserialize)]
#[serde(transparent)]
struct LegacyInteger(#[serde(with = "ay_core::serde_bignum::bigint")] BigInt);

#[derive(Debug, Serialize, Deserialize)]
#[serde(transparent)]
struct LegacyBigRatio(#[serde(with = "ay_core::serde_bignum::bigrational")] BigRational);

#[derive(Debug, Serialize, Deserialize)]
#[serde(transparent)]
struct LegacyRatio64(#[serde(with = "ay_core::serde_bignum::rational64")] Rational64);

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn raw(text: &str) -> RawSlice<'_> {
    RawSlice::from_raw(serde_json::from_str::<&RawValue>(text).unwrap())
}

fn checked<'a, T>(
    text: &'a str,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> TransportOutcome<T> {
    control::run(deadline(), &mut |_, _| true, |control| {
        decode(raw(text), control)
    })
}

#[test]
fn bigint_wire_parity_preserves_sign_normalization_and_all_word_boundaries() {
    for sign in [-1, 0, 1] {
        for words in [
            "[]",
            "[0]",
            "[0,0,0,0,0,0,0,0,0]",
            "[1]",
            "[4294967295]",
            "[0,1]",
            "[1,0,1]",
            "[4294967295,4294967295,4294967295]",
            "[1,2,3,4,5,6,7,8,9]",
            "[1,0,0,0,0,0,0,0,0]",
        ] {
            let text = format!("[{sign},{words}]");
            let expected: LegacyInteger = serde_json::from_str(&text).unwrap();
            let actual = checked(&text, bigint).result.unwrap();
            assert_eq!(actual, expected.0, "{text}");
            assert_eq!(
                serde_json::to_vec(&LegacyInteger(actual)).unwrap(),
                serde_json::to_vec(&expected).unwrap(),
                "{text}"
            );
        }
    }
}

#[test]
fn malformed_sign_tuple_and_limb_types_match_incumbent_refusal() {
    for text in [
        "null",
        "{}",
        "[]",
        "[1]",
        "[1,[],0]",
        "[2,[]]",
        "[-2,[]]",
        "[128,[]]",
        "[-129,[]]",
        "[-0,[]]",
        "[1.0,[]]",
        "[1e0,[]]",
        "[true,[]]",
        "[\"1\",[]]",
        "[1,null]",
        "[1,{}]",
        "[1,[null]]",
        "[1,[true]]",
        "[1,[-1]]",
        "[1,[-0]]",
        "[1,[1.0]]",
        "[1,[1e0]]",
        "[1,[4294967296]]",
        "[1,[18446744073709551616]]",
        "[1,[\"1\"]]",
        "[0,[1,false]]",
        "[0,[4294967296]]",
        "[0,[1,[],0]]",
    ] {
        assert!(
            serde_json::from_str::<LegacyInteger>(text).is_err(),
            "{text}"
        );
        let outcome = checked(text, bigint);
        assert!(outcome.result.is_err(), "{text}");
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn invalid_sign_precedes_limb_ownership_but_no_sign_still_validates_every_limb() {
    let invalid = checked("[2,[1,2,3,false]]", bigint);
    assert_eq!(
        invalid.result,
        Err(TransportError::InvalidShape("invalid bigint sign"))
    );
    assert_eq!(invalid.usage.charged_bytes, 0);
    let zero = checked("[0,[1,2,3,false]]", bigint);
    assert!(zero.result.is_err());
    assert!(zero.usage.charged_bytes >= 4 * size_of::<u32>());
    assert_eq!(
        checked("[0,[4294967295,1]]", bigint).result,
        Ok(BigInt::ZERO)
    );
}

#[test]
fn tuple_shape_prepass_may_refuse_extra_arity_before_invalid_sign() {
    let text = "[2,[false],0]";
    // Both readers refuse; the controlled reader intentionally does not
    // promise the incumbent's streaming sign-before-limbs diagnostic order.
    assert!(serde_json::from_str::<LegacyInteger>(text).is_err());
    let outcome = checked(text, bigint);
    assert_eq!(
        outcome.result,
        Err(TransportError::InvalidShape("long sequence"))
    );
    assert_eq!(outcome.usage.charged_bytes, 0);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn ratio_shape_prepass_may_refuse_extra_arity_before_invalid_numerator() {
    let text = "[[2,[false]],[1,[0]],0]";
    // Outer shape admission precedes typed numerator decoding here. This is
    // refusal parity, not a claim that the two dynamic diagnostics match.
    assert!(serde_json::from_str::<LegacyBigRatio>(text).is_err());
    let outcome = checked(text, big_rational);
    assert_eq!(
        outcome.result,
        Err(TransportError::InvalidShape("long sequence"))
    );
    assert_eq!(outcome.usage.charged_bytes, 0);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn big_ratios_keep_unreduced_terms_and_negative_denominators() {
    for text in [
        "[[1,[2]],[1,[4]]]",
        "[[-1,[6]],[-1,[8]]]",
        "[[0,[99]],[-1,[7]]]",
        "[[1,[0,0]],[-1,[0,1,0]]]",
        "[[1,[4294967295,1]],[-1,[9,0,0]]]",
    ] {
        let expected: LegacyBigRatio = serde_json::from_str(text).unwrap();
        let actual = checked(text, big_rational).result.unwrap();
        // Ratio equality alone would hide reduction or denominator-sign changes.
        assert_eq!(actual.numer(), expected.0.numer(), "{text}");
        assert_eq!(actual.denom(), expected.0.denom(), "{text}");
        assert_eq!(
            serde_json::to_vec(&LegacyBigRatio(actual)).unwrap(),
            serde_json::to_vec(&expected).unwrap()
        );
    }
}

#[test]
fn ratio64_preserves_raw_i64_extremes_without_arithmetic() {
    for text in [
        "[2,4]",
        "[-6,-8]",
        "[0,-7]",
        "[-9223372036854775808,-1]",
        "[9223372036854775807,-9223372036854775808]",
    ] {
        let expected: LegacyRatio64 = serde_json::from_str(text).unwrap();
        let outcome = checked(text, rational64);
        let actual = outcome.result.unwrap();
        assert_eq!(actual.numer(), expected.0.numer());
        assert_eq!(actual.denom(), expected.0.denom());
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn ratios_refuse_zero_denominators_and_malformed_fields_in_source_order() {
    for text in [
        "[]",
        "[1,2]",
        "[[1,[1]]]",
        "[[1,[1]],[1,[1]],0]",
        "[[1,[1]],[1,[]]]",
        "[[1,[1]],[-1,[0,0]]]",
        "[[1,[1]],[0,[99]]]",
        "[[1,[1]],[1,[false]]]",
    ] {
        assert!(serde_json::from_str::<LegacyBigRatio>(text).is_err());
        assert!(checked(text, big_rational).result.is_err());
    }
    for text in [
        "[]",
        "[1]",
        "[1,2,3]",
        "[1,0]",
        "[1,-0]",
        "[1,1.0]",
        "[1,9223372036854775808]",
        "[null,-1]",
    ] {
        assert!(serde_json::from_str::<LegacyRatio64>(text).is_err());
        assert!(checked(text, rational64).result.is_err());
    }
    let invalid = checked("[[2,[false]],[1,[0]]]", big_rational);
    assert_eq!(
        invalid.result,
        Err(TransportError::InvalidShape("invalid bigint sign"))
    );
    assert_eq!(invalid.usage.charged_bytes, 0);
}

#[test]
fn pinned_hidden_allocation_counts_digit_pairs_and_excludes_zero_magnitudes() {
    for count in [1_usize, 2, 3, 7, 8, 9] {
        let words = vec![1_u32; count];
        let text = format!("[1,{}]", serde_json::to_string(&words).unwrap());
        let mut reservations = Vec::new();
        let outcome = control::run(
            deadline(),
            &mut |_, bytes| {
                if bytes != 0 {
                    reservations.push(bytes);
                }
                true
            },
            |control| bigint(raw(&text), control),
        );
        assert!(outcome.result.is_ok());
        #[cfg(target_pointer_width = "64")]
        let hidden = 8 * count.div_ceil(2).max(4);
        #[cfg(not(target_pointer_width = "64"))]
        let hidden = 4 * count.max(4);
        assert_eq!(reservations, [count * 4, hidden]);
        assert_eq!(outcome.usage.charged_bytes, count * 4 + hidden);
    }
    for text in ["[0,[1,2,3]]", "[1,[0,0,0]]", "[-1,[0,0,0]]"] {
        let outcome = checked(text, bigint);
        assert_eq!(outcome.result, Ok(BigInt::ZERO));
        assert_eq!(outcome.usage.charged_bytes, 3 * size_of::<u32>());
    }
    assert_eq!(checked("[1,[]]", bigint).usage.charged_bytes, 0);
}

#[test]
fn trailing_zero_trim_preserves_temporary_capacity_but_avoids_hidden_shrink() {
    let text = "[1,[1,0,0,0,0,0,0,0,0]]";
    let outcome = checked(text, bigint);
    assert_eq!(outcome.result, Ok(BigInt::from(1)));
    #[cfg(target_pointer_width = "64")]
    let hidden = 32;
    #[cfg(not(target_pointer_width = "64"))]
    let hidden = 16;
    assert_eq!(outcome.usage.charged_bytes, 9 * size_of::<u32>() + hidden);
    let zeros = checked("[1,[0,0,0,0,0,0,0,0,0]]", bigint);
    assert_eq!(zeros.usage.charged_bytes, 9 * size_of::<u32>());
}

#[test]
fn exact_and_short_work_storage_and_cumulative_two_number_controls() {
    let text = "[[1,[1,2,0]],[-1,[3,4,5]]]";
    let baseline = checked(text, big_rational);
    assert!(baseline.result.is_ok());
    let (work, bytes) = (baseline.usage.charged_work, baseline.usage.charged_bytes);
    for (limit_work, limit_bytes, accept) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let outcome = control::run(deadline(), &mut |_, _| true, |control| {
            control.constrain(limit_work as u64, limit_bytes)?;
            big_rational(raw(text), control)
        });
        assert_eq!(outcome.result.is_ok(), accept);
        if !accept {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
    let outcome = control::run(deadline(), &mut |_, _| true, |control| {
        control.constrain(work as u64, bytes)?;
        let first = big_rational(raw(text), control)?;
        let second = big_rational(raw(text), control)?;
        Ok((first, second))
    });
    assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
}

#[test]
fn every_success_and_partial_failure_checkpoint_refuses_without_restart() {
    for text in [
        "[[1,[1,2,0]],[-1,[3,4,5]]]",
        "[[1,[1]],[1,[0,0]]]",
        "[[1,[1]],[0,[1,false]]]",
    ] {
        let calls = Cell::new(0);
        let baseline = control::run(
            deadline(),
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            |control| big_rational(raw(text), control),
        );
        assert_eq!(
            baseline.result.is_ok(),
            serde_json::from_str::<LegacyBigRatio>(text).is_ok()
        );
        let total = calls.get();
        assert!(total > 10);
        for stop in 1..=total {
            calls.set(0);
            let outcome = control::run(
                deadline(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| big_rational(raw(text), control),
            );
            assert_eq!(outcome.result, Err(TransportError::Refused));
            assert_eq!(calls.get(), stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(outcome.usage, baseline.usage);
            }
        }
    }
}

#[test]
fn original_deadline_sticky_error_and_caught_callback_panic_cannot_publish() {
    let expired = control::run(
        Instant::now().checked_sub(Duration::from_secs(1)).unwrap(),
        &mut |_, _| -> bool { panic!("expired before progress") },
        |control| bigint(raw("[1,[1]]"), control),
    );
    assert_eq!(expired.result, Err(TransportError::Deadline));
    assert_eq!(expired.usage.charged_bytes, 0);
    let sticky = control::run(deadline(), &mut |_, _| true, |control| {
        let error = bigint(raw("[2,[]]"), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(bigint(raw("[1,[1]]"), control), Err(error));
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(
        sticky.result,
        Err(TransportError::InvalidShape(_))
    ));
    let panicked = Cell::new(false);
    let outcome = control::run(
        deadline(),
        &mut |_, bytes| {
            assert!(
                bytes <= 4 || panicked.replace(true),
                "construction admission"
            );
            true
        },
        |control| {
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                bigint(raw("[1,[1]]"), control)
            }));
            assert!(caught.is_err());
            assert_eq!(
                bigint(raw("[1,[1]]"), control),
                Err(TransportError::Refused)
            );
            Ok(())
        },
    );
    assert_eq!(outcome.result, Err(TransportError::Refused));
}
