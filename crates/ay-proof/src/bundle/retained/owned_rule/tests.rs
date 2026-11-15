// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only RawValue parsing stands for prior input admission. Decoding a
//! rule's representation does not authorize its use in a proof.

use super::{alethe, theory};
use crate::bundle::retained::{
    control::{self, Control},
    owned_values::RawSlice,
    TransportError, TransportOutcome,
};
use ay_core::time::Instant;
use serde::{de::DeserializeOwned, Serialize};
use serde_json::value::RawValue;
use std::{fmt::Debug, time::Duration};

type Decoder<T> = fn(RawSlice<'_>, &mut Control<'_>) -> Result<T, TransportError>;
const WORK: u64 = 1_000_000;
const STORAGE: usize = 1024 * 1024;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn attempt<T>(
    text: &str,
    decode: Decoder<T>,
    work: u64,
    bytes: usize,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> TransportOutcome<T> {
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    control::run(deadline, progress, |control| {
        control.constrain(work, bytes)?;
        decode(RawSlice::from_raw(raw), control)
    })
}

fn checked<T>(text: &str, decode: Decoder<T>) -> TransportOutcome<T> {
    attempt(text, decode, WORK, STORAGE, end(), &mut |_, _| true)
}

fn accepts<T: DeserializeOwned + Serialize + Debug + PartialEq>(text: &str, decode: Decoder<T>) {
    let expected: T = serde_json::from_str(text).unwrap();
    let actual = checked(text, decode).result.unwrap();
    assert_eq!(actual, expected, "{text}");
    assert_eq!(
        serde_json::to_vec(&actual).unwrap(),
        serde_json::to_vec(&expected).unwrap(),
        "{text}"
    );
}

fn rejects<T: DeserializeOwned>(text: &str, decode: Decoder<T>) {
    assert!(serde_json::from_str::<T>(text).is_err(), "{text}");
    let outcome = checked(text, decode);
    assert!(outcome.result.is_err(), "{text}");
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn all_three_alethe_payload_variants_match_existing_serde() {
    for text in [
        r#"{"AndPos":0}"#,
        r#"{"AndPos":4294967295}"#,
        r#"{"OrPos":0}"#,
        r#"{"OrPos":4294967295}"#,
        r#"{"Custom":""}"#,
        r#"{"Custom":"λ\u0000\uD83D\uDE00"}"#,
        r#"{"And\u0050os":7}"#,
        r#"{"\u0043ustom":"\"\\\/\n"}"#,
    ] {
        accepts(text, alethe);
    }
}

#[test]
fn all_four_theory_payloads_accept_exact_object_and_sequence_forms() {
    for text in [
        r#"{"BvBitBlastGate":{"gate_type":"Add","width":8}}"#,
        r#"{"BvBitBlastGate":["Variable",0]}"#,
        r#"{"BvBitBlastGate":{"width":4294967295,"gate_type":"Mul"}}"#,
        r#"{"ArraySelectStore":{"index_eq":true}}"#,
        r#"{"ArraySelectStore":[false]}"#,
        r#"{"FpToBv":{"operation":"Add"}}"#,
        r#"{"FpToBv":["FromFp"]}"#,
        r#"{"FpClassification":{"operation":"IsNaN"}}"#,
        r#"{"FpClassification":["StructuralEq"]}"#,
        r#"{"BvBitBlast\u0047ate":{"gate\u005ftype":"E\u0071","w\u0069dth":8}}"#,
        r#"{"ArraySelectStore":{"index\u005feq":false}}"#,
        r#"{"Fp\u0054oBv":{"oper\u0061tion":"Neg"}}"#,
    ] {
        accepts(text, theory);
    }
}

#[test]
fn finite_field_linear_payload_is_bounded_in_both_decoders() {
    accepts(r#"{"FiniteFieldLinear":[5,1,0,0,0,0,0,0]}"#, theory);
    rejects(r#"{"FiniteFieldLinear":[1,1,1,1,1,1,1,1,1]}"#, theory);
    rejects(r#"{"FiniteFieldLinear":[-1,1,0,0,0,0,0,0]}"#, theory);
    rejects(r#"{"FiniteFieldLinear":[256,1,0,0,0,0,0,0]}"#, theory);
    accepts(
        r#"{"FiniteFieldLinearWide":[4294967290,1,0,0,0,0,0,0]}"#,
        theory,
    );
    rejects(
        r#"{"FiniteFieldLinearWide":[4294967296,1,0,0,0,0,0,0]}"#,
        theory,
    );
    rejects(r#"{"FiniteFieldLinearWide":[1,1,1,1,1,1,1,1,1]}"#, theory);
    rejects(r#"{"FiniteFieldLinearWide":[-1,1,0,0,0,0,0,0]}"#, theory);
}

#[test]
fn unit_routes_keep_string_and_object_null_forms_without_becoming_payloads() {
    for name in ["True", "False", "And", "Or", "FpToBv", "FreshDefEq"] {
        accepts(&format!(r#""{name}""#), alethe);
        accepts(&format!(r#"{{"{name}":null}}"#), alethe);
        rejects(&format!(r#"{{"{name}":[]}}"#), alethe);
    }
    for name in [
        "EufTransitive",
        "BvBitBlast",
        "BoolTautology",
        "Generic",
        "IntCgCutChain",
    ] {
        accepts(&format!(r#""{name}""#), theory);
        accepts(&format!(r#"{{"{name}":null}}"#), theory);
        rejects(&format!(r#"{{"{name}":false}}"#), theory);
    }
    accepts(r#""\u0054rue""#, alethe);
    accepts(r#"{"Euf\u0054ransitive":null}"#, theory);
}

#[test]
fn every_nested_bv_gate_tag_uses_its_existing_wire_name_in_both_unit_forms() {
    for gate in [
        "And",
        "Or",
        "Xor",
        "Not",
        "Add",
        "Mul",
        "Neg",
        "Shl",
        "Lshr",
        "Ashr",
        "Eq",
        "Ult",
        "Concat",
        "Extract",
        "ZeroExtend",
        "SignExtend",
        "Udiv",
        "Urem",
        "Const",
        "Variable",
        "Ite",
    ] {
        accepts(&format!(r#"{{"BvBitBlastGate":["{gate}",0]}}"#), theory);
        accepts(
            &format!(
                r#"{{"BvBitBlastGate":{{"gate_type":{{"{gate}":null}},"width":4294967295}}}}"#
            ),
            theory,
        );
    }
}

#[test]
fn every_nested_fp_operation_is_transport_accepted_in_both_theory_payloads() {
    for operation in [
        "Add",
        "Sub",
        "Mul",
        "Div",
        "Sqrt",
        "Neg",
        "Abs",
        "Fma",
        "Eq",
        "Lt",
        "Le",
        "Gt",
        "Ge",
        "ToReal",
        "FromReal",
        "ToSbv",
        "ToUbv",
        "FromSbv",
        "FromUbv",
        "RoundToIntegral",
        "Min",
        "Max",
        "Rem",
        "IsNaN",
        "IsInfinite",
        "IsZero",
        "IsNormal",
        "IsSubnormal",
        "IsPositive",
        "IsNegative",
        "StructuralEq",
        "ToIeeeBv",
        "FromFp",
    ] {
        for kind in ["FpToBv", "FpClassification"] {
            // Whether an operation is suitable for this lemma is a later
            // checker obligation, not a narrower wire-enum grammar.
            accepts(&format!(r#"{{"{kind}":["{operation}"]}}"#), theory);
            accepts(
                &format!(r#"{{"{kind}":{{"operation":{{"{operation}":null}}}}}}"#),
                theory,
            );
        }
    }
}

#[test]
fn unknown_and_multiple_top_tags_never_discard_payload_or_unit_neighbors() {
    for text in [
        r#"{"AndPos":0,"True":null}"#,
        r#"{"True":null,"AndPos":0}"#,
        r#"{"Custom":"x","unknown":null}"#,
        r#"{"unknown":null,"Custom":"x"}"#,
        r#"{"AndPos":0,"AndPos":1}"#,
        r#"{"True":null,"False":null}"#,
        r#"{"True":null,"True":null}"#,
        r#"{"OrPos":0,"Or\u0050os":1}"#,
        r#"{"True":null,"unknown":0}"#,
    ] {
        rejects(text, alethe);
    }
    for text in [
        r#"{"ArraySelectStore":[true],"Generic":null}"#,
        r#"{"Generic":null,"ArraySelectStore":[true]}"#,
        r#"{"FpToBv":["Add"],"unknown":null}"#,
        r#"{"unknown":null,"FpToBv":["Add"]}"#,
        r#"{"BvBitBlastGate":["Add",8],"BvBitBlastGate":["Mul",8]}"#,
        r#"{"EufReflexive":null,"Generic":null}"#,
        r#"{"Generic":null,"Generic":null}"#,
        r#"{"Generic":null,"unknown":0}"#,
    ] {
        rejects(text, theory);
    }
}

#[test]
fn malformed_alethe_payloads_and_numeric_variant_indices_refuse() {
    for text in [
        "null",
        "true",
        "0",
        "[]",
        "{}",
        r#""Unknown""#,
        r#"{"0":null}"#,
        r#""AndPos""#,
        r#""OrPos""#,
        r#""Custom""#,
        r#"{"AndPos":null}"#,
        r#"{"OrPos":[0]}"#,
        r#"{"Custom":null}"#,
        r#"{"Custom":0}"#,
        r#"{"Custom":["x"]}"#,
        r#"{"Custom":"\uD800"}"#,
        r#"{"\uDC00":0}"#,
    ] {
        rejects(text, alethe);
    }
    for value in ["-0", "-1", "1.0", "1e0", "4294967296", "true", r#""1""#] {
        for name in ["AndPos", "OrPos"] {
            rejects(&format!(r#"{{"{name}":{value}}}"#), alethe);
        }
    }
}

#[test]
fn theory_struct_fields_are_required_exact_and_unknown_or_duplicate_rejecting() {
    for text in [
        "null",
        "0",
        "[]",
        "{}",
        r#""Unknown""#,
        r#"{"0":null}"#,
        r#""BvBitBlastGate""#,
        r#""ArraySelectStore""#,
        r#""FpToBv""#,
        r#""FpClassification""#,
        r#"{"BvBitBlastGate":null}"#,
        r#"{"BvBitBlastGate":[]}"#,
        r#"{"BvBitBlastGate":["Add"]}"#,
        r#"{"BvBitBlastGate":["Add",8,0]}"#,
        r#"{"BvBitBlastGate":{"width":8}}"#,
        r#"{"BvBitBlastGate":{"gate_type":"Add"}}"#,
        r#"{"BvBitBlastGate":{"gate_type":"Add","width":8,"extra":0}}"#,
        r#"{"BvBitBlastGate":{"gate_type":"Add","width":8,"w\u0069dth":9}}"#,
        r#"{"ArraySelectStore":{}}"#,
        r#"{"ArraySelectStore":[true,false]}"#,
        r#"{"ArraySelectStore":{"index_eq":true,"index_eq":false}}"#,
        r#"{"FpToBv":{}}"#,
        r#"{"FpToBv":[]}"#,
        r#"{"FpToBv":["Add","Sub"]}"#,
        r#"{"FpToBv":{"operation":"Add","extra":0}}"#,
        r#"{"FpClassification":{"operation":"IsNaN","oper\u0061tion":"IsZero"}}"#,
        r#"{"FpClassification":null}"#,
    ] {
        rejects(text, theory);
    }
}

#[test]
fn theory_nested_enums_and_scalar_ranges_refuse_without_cross_route_fallback() {
    for value in ["-0", "-1", "1.0", "1e0", "4294967296", "null", r#""8""#] {
        rejects(&format!(r#"{{"BvBitBlastGate":["Add",{value}]}}"#), theory);
    }
    for value in ["0", "null", "[]", r#""true""#] {
        rejects(&format!(r#"{{"ArraySelectStore":[{value}]}}"#), theory);
    }
    for value in [
        "0",
        "null",
        r#""Bogus""#,
        r#"{"Add":[]}"#,
        r#"{"Add":null,"Mul":null}"#,
        r#""\uD800""#,
    ] {
        rejects(&format!(r#"{{"BvBitBlastGate":[{value},8]}}"#), theory);
        rejects(&format!(r#"{{"FpToBv":[{value}]}}"#), theory);
        rejects(&format!(r#"{{"FpClassification":[{value}]}}"#), theory);
    }
}

#[test]
fn long_unicode_custom_payload_is_not_limited_by_static_variant_name_length() {
    let name = "λ\0😀\"\\".repeat(2048);
    let encoded = serde_json::to_string(&name).unwrap();
    let text = format!(r#"{{"Custom":{encoded}}}"#);
    accepts(&text, alethe);
    let outcome = checked(&text, alethe);
    assert!(outcome.result.is_ok());
    assert!(outcome.usage.charged_bytes >= encoded.len() - 2);
}

fn boundaries<T: Debug + PartialEq>(text: &str, decode: Decoder<T>) {
    let full = checked(text, decode);
    assert!(full.result.is_ok());
    let (work, bytes) = (full.usage.charged_work as u64, full.usage.charged_bytes);
    assert!(work > 1 && bytes > 0);
    let exact = attempt(text, decode, work, bytes, end(), &mut |_, _| true);
    assert_eq!(exact.result, full.result);
    assert_eq!(exact.usage, full.usage);
    for (work, bytes) in [(work - 1, bytes), (work, bytes - 1), (0, bytes), (work, 0)] {
        let short = attempt(text, decode, work, bytes, end(), &mut |_, _| true);
        assert!(matches!(short.result, Err(TransportError::Limit { .. })));
        assert_eq!(short.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn exact_and_one_short_budgets_cover_both_payload_and_unit_routes() {
    boundaries(r#"{"Custom":"\u03bb"}"#, alethe);
    boundaries(r#"{"AndPos":3}"#, alethe);
    boundaries(r#""True""#, alethe);
    boundaries(r#"{"BvBitBlastGate":[{"Add":null},8]}"#, theory);
    boundaries(r#"{"FpClassification":{"operation":"IsNaN"}}"#, theory);
    boundaries(r#"{"Generic":null}"#, theory);
}

fn checkpoints<T: Debug + PartialEq + DeserializeOwned>(text: &str, decode: Decoder<T>) {
    let mut total = 0;
    let full = attempt(text, decode, WORK, STORAGE, end(), &mut |_, _| {
        total += 1;
        true
    });
    assert_eq!(full.result.is_ok(), serde_json::from_str::<T>(text).is_ok());
    assert!(total > 2);
    for stop in 1..=total {
        let mut calls = 0;
        let stopped = attempt(text, decode, WORK, STORAGE, end(), &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert_eq!(
            stopped.result,
            Err(TransportError::Refused),
            "{text} at {stop}"
        );
        assert_eq!(calls, stop);
        assert_eq!(stopped.usage.returned_owned_bytes, 0);
        if stop == total {
            assert_eq!(stopped.usage, full.usage);
        }
    }
}

#[test]
fn every_success_and_failure_cleanup_callback_is_terminal_on_both_routes() {
    for text in [
        r#"{"AndPos":1}"#,
        r#"{"OrPos":2}"#,
        r#"{"Custom":"x"}"#,
        r#""True""#,
        r#"{"Custom":"\uD800"}"#,
    ] {
        checkpoints(text, alethe);
    }
    for text in [
        r#"{"BvBitBlastGate":["Add",8]}"#,
        r#"{"ArraySelectStore":[false]}"#,
        r#"{"FpToBv":["Add"]}"#,
        r#"{"FpClassification":["IsNaN"]}"#,
        r#"{"Generic":null}"#,
        r#"{"BvBitBlastGate":["Add",null]}"#,
        r#"{"ArraySelectStore":[true],"Generic":null}"#,
    ] {
        checkpoints(text, theory);
    }
}

fn no_renewal<T: Debug + PartialEq>(text: &str, decode: Decoder<T>) {
    let full = checked(text, decode);
    assert!(full.result.is_ok());
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    for (work, bytes) in [
        (full.usage.charged_work as u64, STORAGE),
        (WORK, full.usage.charged_bytes),
    ] {
        let outcome = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(work, bytes)?;
            drop(decode(RawSlice::from_raw(raw), control)?);
            let error = decode(RawSlice::from_raw(raw), control).unwrap_err();
            assert!(matches!(error, TransportError::Limit { .. }));
            let usage = control.usage;
            assert_eq!(decode(RawSlice::from_raw(raw), control), Err(error));
            assert_eq!(control.usage, usage);
            Ok(())
        });
        assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
    }
}

#[test]
fn repeated_decodes_do_not_renew_work_or_metadata_and_payload_storage() {
    no_renewal(r#"{"Custom":"owned"}"#, alethe);
    no_renewal(r#"{"BvBitBlastGate":["Add",8]}"#, theory);
    no_renewal(r#""True""#, alethe);
    no_renewal(r#""Generic""#, theory);
}

fn terminal<T: Debug + PartialEq>(invalid: &str, valid: &str, decode: Decoder<T>) {
    for text in [invalid, valid] {
        let expired = attempt(
            text,
            decode,
            WORK,
            STORAGE,
            Instant::now() - Duration::from_secs(1),
            &mut |_, _| -> bool { panic!("expired before callback") },
        );
        assert_eq!(expired.result, Err(TransportError::Deadline));
        assert_eq!(expired.usage.charged_work, 0);
        assert_eq!(expired.usage.charged_bytes, 0);
    }
    let bad: &RawValue = serde_json::from_str(invalid).unwrap();
    let good: &RawValue = serde_json::from_str(valid).unwrap();
    let outcome = control::run(end(), &mut |_, _| true, |control| {
        let error = decode(RawSlice::from_raw(bad), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(decode(RawSlice::from_raw(good), control), Err(error));
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(outcome.result.is_err());
}

#[test]
fn original_deadline_and_caught_payload_errors_cannot_restart_as_unit_decoding() {
    terminal(r#"{"AndPos":null}"#, r#""True""#, alethe);
    terminal(r#"{"FpToBv":["Unknown"]}"#, r#""Generic""#, theory);
    terminal(r#"{"True":false}"#, r#"{"Custom":"x"}"#, alethe);
    terminal(
        r#"{"Generic":false}"#,
        r#"{"ArraySelectStore":[true]}"#,
        theory,
    );
}
