// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bundle::retained::{control, TransportOutcome};
use ay_core::time::Instant;
use serde_json::value::RawValue;
use std::{cell::Cell, time::Duration};

fn end() -> Instant {
    Instant::now() + Duration::from_secs(30)
}
fn raw(text: &str) -> RawSlice<'_> {
    RawSlice::from_raw(serde_json::from_str::<&RawValue>(text).unwrap())
}
fn checked<'a, T>(
    text: &'a str,
    read: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> TransportOutcome<T> {
    control::run(end(), &mut |_, _| true, |control| read(raw(text), control))
}

// Test-only introspection reads the actual serde table, not a duplicate list
// of every unit tag. No arbitrary type decoder is exposed by production.
struct Registry<'a>(&'a mut Option<&'static [&'static str]>);
impl<'de> Deserializer<'de> for Registry<'_> {
    type Error = Error;
    fn deserialize_any<V: de::Visitor<'de>>(self, _: V) -> Result<V::Value, Error> {
        Err(Error::unsupported())
    }
    fn deserialize_enum<V: de::Visitor<'de>>(
        self,
        _: &'static str,
        variants: &'static [&'static str],
        _: V,
    ) -> Result<V::Value, Error> {
        *self.0 = Some(variants);
        Err(Error::unsupported())
    }
    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct identifier ignored_any
    }
}

fn unit_parity<T>(
    read: impl Fn(RawSlice<'_>, &mut Control<'_>) -> Result<T, TransportError>,
) -> (usize, usize)
where
    T: for<'de> Deserialize<'de> + PartialEq + fmt::Debug,
{
    let mut names = None;
    assert!(T::deserialize(Registry(&mut names)).is_err());
    let (mut units, mut payloads) = (0, 0);
    for name in names.unwrap() {
        let quoted = serde_json::to_string(name).unwrap();
        let expected = serde_json::from_str::<T>(&quoted);
        let actual = checked(&quoted, &read);
        assert_eq!(actual.result.is_ok(), expected.is_ok(), "{name}");
        assert_eq!(actual.result.ok(), expected.ok(), "{name}");
        let object = format!("{{{quoted}:null}}");
        let expected = serde_json::from_str::<T>(&object);
        let actual = checked(&object, &read);
        assert_eq!(actual.result.is_ok(), expected.is_ok(), "{object}");
        if expected.is_ok() {
            units += 1;
        } else {
            payloads += 1;
        }
        assert_eq!(actual.result.ok(), expected.ok(), "{object}");
    }
    (units, payloads)
}

#[test]
fn every_current_unit_in_all_four_serde_registries_matches_string_and_object_null() {
    // Each registry is discovered from the owning enum. Verify every variant's
    // decoding behavior without freezing counts as new variants are added.
    assert!(unit_parity(bv_gate).0 > 0);
    assert!(unit_parity(fp_operation).0 > 0);
    assert!(unit_parity(theory_unit).0 > 0);
    assert!(unit_parity(alethe_unit).0 > 0);
}

#[test]
fn escaped_names_use_existing_variant_names_without_accepting_numeric_identifiers() {
    for text in [r#""\u0041dd""#, r#"{"A\u0064d":null}"#] {
        assert_eq!(
            checked(text, bv_gate).result.unwrap(),
            serde_json::from_str::<BvGateType>(text).unwrap()
        );
        assert_eq!(
            checked(text, fp_operation).result.unwrap(),
            serde_json::from_str::<FpOp>(text).unwrap()
        );
    }
    assert_eq!(
        checked(r#""Bv\u0042itBlast""#, theory_unit).result,
        Ok(TheoryLemmaKind::BvBitBlast)
    );
    assert_eq!(
        checked(r#"{"Resol\u0075tion":null}"#, alethe_unit).result,
        Ok(AletheRule::Resolution)
    );
    for text in [
        "0",
        "1",
        "null",
        "true",
        "[]",
        "{}",
        r#""0""#,
        r#"{"0":null}"#,
        r#""Unknown""#,
    ] {
        assert!(serde_json::from_str::<BvGateType>(text).is_err());
        assert!(checked(text, bv_gate).result.is_err());
    }
}

#[test]
fn wrong_unit_payloads_duplicates_and_invalid_surrogates_refuse() {
    for text in [
        r#"{"Add":false}"#,
        r#"{"Add":0}"#,
        r#"{"Add":[]}"#,
        r#"{"Add":{}}"#,
        r#"{"Add":""}"#,
        r#"{"Add":null,"Add":null}"#,
        r#"{"Add":null,"Sub":null}"#,
        r#""\ud800""#,
        r#"{"\udc00":null}"#,
    ] {
        assert!(serde_json::from_str::<FpOp>(text).is_err());
        assert!(checked(text, fp_operation).result.is_err());
    }
    let unknown = format!("\"{}\"", "X".repeat(4096));
    let outcome = checked(&unknown, theory_unit);
    assert!(matches!(
        outcome.result,
        Err(TransportError::Limit {
            resource: "encoded field name bytes",
            ..
        })
    ));
    assert_eq!(outcome.usage.charged_bytes, 0);
}

#[test]
fn valid_nonunit_enum_payloads_decline_without_entering_their_decoders() {
    for text in [
        r#"{"AndPos":0}"#,
        r#"{"OrPos":4294967295}"#,
        r#"{"Custom":"owned"}"#,
    ] {
        assert!(serde_json::from_str::<AletheRule>(text).is_ok());
        let result = checked(text, alethe_unit);
        assert!(matches!(
            result.result,
            Err(TransportError::InvalidShape("expected a unit enum variant"))
        ));
        // Only the variant name is owned; Custom's body is not deserialized.
        assert!(result.usage.charged_bytes <= "Custom".len());
    }
    for text in [
        r#"{"BvBitBlastGate":{"gate_type":"Add","width":8}}"#,
        r#"{"ArraySelectStore":[true]}"#,
        r#"{"FpToBv":{"operation":"Add"}}"#,
        r#"{"FpClassification":{"operation":"IsNaN"}}"#,
    ] {
        assert!(serde_json::from_str::<TheoryLemmaKind>(text).is_ok());
        assert!(matches!(
            checked(text, theory_unit).result,
            Err(TransportError::InvalidShape("expected a unit enum variant"))
        ));
    }
}

#[derive(Debug)]
struct PayloadBomb;
impl<'de> Deserialize<'de> for PayloadBomb {
    fn deserialize<D: Deserializer<'de>>(_: D) -> Result<Self, D::Error> {
        panic!("payload seed must never be entered")
    }
}
#[allow(dead_code)]
#[derive(Debug, Deserialize)]
enum FutureShape {
    Unit,
    Newtype(PayloadBomb),
    Tuple(PayloadBomb, PayloadBomb),
    Record { owned: PayloadBomb },
}

#[test]
fn future_owned_variants_fail_before_newtype_tuple_or_struct_payload_visitors() {
    for text in [
        r#"{"Newtype":"owner"}"#,
        r#"{"Tuple":[1,2]}"#,
        r#"{"Record":{"owned":1}}"#,
    ] {
        let result = checked(text, decode::<FutureShape>);
        assert!(matches!(
            result.result,
            Err(TransportError::InvalidShape("expected a unit enum variant"))
        ));
    }
    assert!(matches!(
        checked(r#""Unit""#, decode::<FutureShape>).result,
        Ok(FutureShape::Unit)
    ));
}

#[test]
fn fixed_serde_error_never_formats_visitor_diagnostics() {
    struct DisplayBomb;
    impl fmt::Display for DisplayBomb {
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            panic!("diagnostic allocation/formatting")
        }
    }
    let error = <Error as de::Error>::custom(DisplayBomb);
    assert!(matches!(error.0, TransportError::InvalidShape(_)));
}

#[test]
fn exact_work_metadata_storage_and_one_short_or_zero_limits_are_enforced() {
    let text = r#"{"\u0041dd":null}"#;
    let full = checked(text, bv_gate);
    assert_eq!(full.result, Ok(BvGateType::Add));
    let (work, bytes) = (full.usage.charged_work, full.usage.charged_bytes);
    assert!(work > text.len() && bytes >= 8);
    for (max_work, max_bytes, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let outcome = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(max_work as u64, max_bytes)?;
            bv_gate(raw(text), control)
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
}

#[test]
fn every_success_and_malformed_payload_callback_refuses_through_final_cleanup() {
    for (text, accepted) in [(r#""Add""#, true), (r#"{"Add":[]}"#, false)] {
        let calls = Cell::new(0);
        let full = control::run(
            end(),
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            |control| bv_gate(raw(text), control),
        );
        assert_eq!(full.result.is_ok(), accepted);
        let total = calls.get();
        assert!(total > 10);
        for stop in 1..=total {
            calls.set(0);
            let result = control::run(
                end(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| bv_gate(raw(text), control),
            );
            assert_eq!(result.result, Err(TransportError::Refused));
            assert_eq!(calls.get(), stop);
            assert_eq!(result.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(result.usage, full.usage);
            }
        }
    }
}

#[test]
fn original_deadline_and_caught_progress_panic_are_terminal() {
    let result = control::run(
        Instant::now().checked_sub(Duration::from_secs(1)).unwrap(),
        &mut |_, _| -> bool { panic!("expired") },
        |control| bv_gate(raw(r#""Add""#), control),
    );
    assert_eq!(result.result, Err(TransportError::Deadline));
    assert_eq!(result.usage.charged_work, 0);
    let calls = Cell::new(0);
    let result = control::run(
        end(),
        &mut |_, bytes| {
            calls.set(calls.get() + 1);
            assert!(bytes == 0, "name admission");
            true
        },
        |control| {
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                bv_gate(raw(r#""Add""#), control)
            }));
            assert!(caught.is_err());
            let before = calls.get();
            assert_eq!(
                bv_gate(raw(r#""Add""#), control),
                Err(TransportError::Refused)
            );
            assert_eq!(calls.get(), before);
            Ok(())
        },
    );
    assert_eq!(result.result, Err(TransportError::Refused));
}

#[test]
fn nonunit_failure_cannot_fall_back_or_renew_a_shared_grant() {
    let result = control::run(end(), &mut |_, _| true, |control| {
        let error = alethe_unit(raw(r#"{"Custom":"x"}"#), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(alethe_unit(raw(r#""Resolution""#), control), Err(error));
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(
        result.result,
        Err(TransportError::InvalidShape(_))
    ));
    let full = checked(r#""Add""#, bv_gate);
    let result = control::run(end(), &mut |_, _| true, |control| {
        control.constrain(full.usage.charged_work as u64, full.usage.charged_bytes)?;
        bv_gate(raw(r#""Add""#), control)?;
        bv_gate(raw(r#""Add""#), control)
    });
    assert!(matches!(result.result, Err(TransportError::Limit { .. })));
}
