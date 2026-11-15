// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed-leaf compatibility only. Test RawValue parsing stands in for prior
//! whole-input admission; accepted transport is not an accepted proof/store.

use super::{constant, read};
use crate::bundle::retained::{
    control::{self, Control},
    owned_values::RawSlice,
    TransportError, TransportOutcome,
};
use ay_core::{time::Instant, Constant, TermData};
use serde_json::value::RawValue;
use std::{cell::Cell, time::Duration};

const MIXED: &str = r#"{"Forall":[[["λ",{"Array":[{"BitVec":[0]},{"Seq":"Char"}]}],["q","Bool"]],4294967295,[[0,4294967295],[],[3,3]]]}"#;

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

fn accepts_term(text: &str) {
    let expected: TermData = serde_json::from_str(text).unwrap();
    let actual = checked(text, read).result.unwrap();
    assert_eq!(actual, expected, "{text}");
    // RationalWrapper's Eq alone can hide raw numerator/denominator changes.
    assert_eq!(
        serde_json::to_vec(&actual).unwrap(),
        serde_json::to_vec(&expected).unwrap(),
        "{text}"
    );
}

fn accepts_constant(text: &str) {
    let expected: Constant = serde_json::from_str(text).unwrap();
    let actual = checked(text, constant).result.unwrap();
    assert_eq!(actual, expected, "{text}");
    assert_eq!(
        serde_json::to_vec(&actual).unwrap(),
        serde_json::to_vec(&expected).unwrap(),
        "{text}"
    );
    accepts_term(&format!(r#"{{"Const":{text}}}"#));
}

#[test]
fn all_eight_term_variants_match_existing_serde_values_and_wire_bytes() {
    for text in [
        r#"{"Const":{"Bool":true}}"#,
        r#"{"Var":["x",7]}"#,
        r#"{"App":[{"Named":"bvadd"},[2,3,2]]}"#,
        r#"{"Let":[[["x",2],["y",3]],4]}"#,
        r#"{"Not":1}"#,
        r#"{"Ite":[1,2,3]}"#,
        r#"{"Forall":[[["x","Int"]],2,[[3,4],[5]]]}"#,
        r#"{"Exists":[[["x",{"BitVec":{"width":8}}]],2,[[3],[]]]}"#,
    ] {
        accepts_term(text);
    }
}

#[test]
fn all_five_constant_variants_preserve_unreduced_rationals_and_normalized_integers() {
    for text in [
        r#"{"Bool":false}"#,
        r#"{"Int":[-1,[4294967295,2,0,0]]}"#,
        r#"{"Int":[0,[4294967295,1]]}"#,
        r#"{"Rational":[[1,[2]],[-1,[4]]]}"#,
        r#"{"Rational":[[0,[99]],[-1,[7]]]}"#,
        r#"{"BitVec":{"value":[1,[255]],"width":8}}"#,
        r#"{"String":"é∑😀\n\u0000"}"#,
    ] {
        accepts_constant(text);
    }
}

#[test]
fn bitvector_constant_struct_accepts_exact_positional_and_reordered_forms() {
    for text in [
        r#"{"BitVec":[[1,[9]],4]}"#,
        r#"{"BitVec":{"width":4,"value":[1,[9]]}}"#,
        r#"{"Bit\u0056ec":{"w\u0069dth":4,"val\u0075e":[-1,[9]]}}"#,
    ] {
        accepts_constant(text);
    }
}

#[test]
fn binders_triggers_let_names_and_indexed_symbols_keep_order_duplicates_and_escapes() {
    for text in [
        MIXED,
        r#"{"Exists":[[["",{"Datatype":["D",[["C",[]]]]}],["","Bool"]],0,[[],[0,0],[]]]}"#,
        r#"{"Forall":[[],0,[]]}"#,
        r#"{"Exists":[[],0,[[]]]}"#,
        r#"{"Let":[[["\u03bb",4294967295],["λ",0],["\u0000",1]],4294967295]}"#,
        r#"{"Let":[[],0]}"#,
        r#"{"App":[{"Indexed":["extract",[31,0,31]]},[0,0,4294967295]]}"#,
        r#"{"App":[{"Named":""},[]]}"#,
        r#"{"V\u0061r":["\uD83D\uDE00\"\\",1]}"#,
    ] {
        accepts_term(text);
    }
}

#[test]
fn transport_accepts_width_zero_noncanonical_magnitudes_and_maximum_term_ids() {
    for text in [
        r#"{"BitVec":{"value":[-1,[4294967295,1]],"width":0}}"#,
        r#"{"BitVec":[[1,[4294967295]],4294967295]}"#,
        r#"{"Int":[-1,[0,0,0]]}"#,
    ] {
        accepts_constant(text);
    }
    for text in [
        r#"{"Var":["",4294967295]}"#,
        r#"{"Not":4294967295}"#,
        r#"{"Ite":[4294967295,4294967295,4294967295]}"#,
        r#"{"Forall":[[["x",{"BitVec":[0]}]],4294967295,[[4294967295]]]}"#,
    ] {
        accepts_term(text);
    }
}

#[test]
fn malformed_term_variants_fields_nullable_containers_and_numeric_ids_refuse() {
    for text in [
        "null",
        "true",
        "0",
        "[]",
        "{}",
        r#""Var""#,
        r#"{"Unknown":0}"#,
        r#"{"0":0}"#,
        r#"{"Not":1,"Not":2}"#,
        r#"{"Not":1,"Ite":[1,2,3]}"#,
        r#"{"Const":null}"#,
        r#"{"Var":null}"#,
        r#"{"Var":["x"]}"#,
        r#"{"Var":["x",1,2]}"#,
        r#"{"Var":[null,1]}"#,
        r#"{"Var":["x",-1]}"#,
        r#"{"Var":["x",4294967296]}"#,
        r#"{"App":[{"Named":"f"},null]}"#,
        r#"{"App":[{"Named":"f"},[1,null]]}"#,
        r#"{"App":[null,[]]}"#,
        r#"{"Let":[null,0]}"#,
        r#"{"Let":[[["x"]],0]}"#,
        r#"{"Let":[[[null,1]],0]}"#,
        r#"{"Not":null}"#,
        r#"{"Not":-0}"#,
        r#"{"Not":1.0}"#,
        r#"{"Not":1e0}"#,
        r#"{"Not":"1"}"#,
        r#"{"Not":4294967296}"#,
        r#"{"Ite":[1,2]}"#,
        r#"{"Ite":[1,2,3,4]}"#,
        r#"{"Forall":[null,0,[]]}"#,
        r#"{"Forall":[[["x"]],0,[]]}"#,
        r#"{"Forall":[[["x",null]],0,[]]}"#,
        r#"{"Forall":[[],0,null]}"#,
        r#"{"Forall":[[],0,[null]]}"#,
        r#"{"Forall":[[],0,[[false]]]}"#,
        r#"{"Exists":[[],0]}"#,
        r#"{"Exists":[[],0,[],0]}"#,
        r#"{"Var":["\uD800",0]}"#,
    ] {
        assert!(serde_json::from_str::<TermData>(text).is_err(), "{text}");
        let outcome = checked(text, read);
        assert!(outcome.result.is_err(), "{text}");
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn malformed_constants_reject_unknown_duplicate_missing_and_wrong_typed_fields() {
    for text in [
        "null",
        "0",
        "{}",
        "[]",
        r#""Bool""#,
        r#"{"Unknown":0}"#,
        r#"{"Bool":null}"#,
        r#"{"Bool":0}"#,
        r#"{"Bool":true,"Bool":false}"#,
        r#"{"Int":[2,[]]}"#,
        r#"{"Int":[0,[false]]}"#,
        r#"{"Rational":[[1,[1]],[0,[9]]]}"#,
        r#"{"Rational":null}"#,
        r#"{"String":null}"#,
        r#"{"String":"\uDC00"}"#,
        r#"{"BitVec":null}"#,
        r#"{"BitVec":{"value":[1,[1]]}}"#,
        r#"{"BitVec":{"width":8}}"#,
        r#"{"BitVec":{"value":[1,[1]],"width":8,"extra":0}}"#,
        r#"{"BitVec":{"value":[1,[1]],"width":8,"width":9}}"#,
        r#"{"BitVec":{"value":[1,[1]],"val\u0075e":[1,[2]],"width":8}}"#,
        r#"{"BitVec":[[1,[1]]]}"#,
        r#"{"BitVec":[[1,[1]],8,0]}"#,
        r#"{"BitVec":[[1,[1]],-1]}"#,
        r#"{"BitVec":[[1,[1]],-0]}"#,
        r#"{"BitVec":[[1,[1]],8.0]}"#,
        r#"{"BitVec":[[1,[1]],4294967296]}"#,
    ] {
        assert!(serde_json::from_str::<Constant>(text).is_err(), "{text}");
        assert!(checked(text, constant).result.is_err(), "{text}");
        let term = format!(r#"{{"Const":{text}}}"#);
        assert!(serde_json::from_str::<TermData>(&term).is_err());
        assert!(checked(&term, read).result.is_err());
    }
}

#[test]
fn exact_short_and_zero_work_storage_limits_cover_nested_owners() {
    for text in [
        MIXED,
        r#"{"App":[{"Indexed":["extract",[7,0]]},[1,2]]}"#,
        r#"{"Const":{"Rational":[[1,[2,3]],[-1,[4,5]]]}}"#,
    ] {
        let baseline = checked(text, read);
        assert!(baseline.result.is_ok());
        let (work, bytes) = (baseline.usage.charged_work, baseline.usage.charged_bytes);
        assert!(work > 0 && bytes > 0);
        for (max_work, max_bytes, accepted) in [
            (work, bytes, true),
            (work - 1, bytes, false),
            (work, bytes - 1, false),
            (0, bytes, false),
            (work, 0, false),
        ] {
            let outcome = control::run(deadline(), &mut |_, _| true, |control| {
                control.constrain(max_work as u64, max_bytes)?;
                read(raw(text), control)
            });
            assert_eq!(outcome.result.is_ok(), accepted, "{text}");
            if !accepted {
                assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
            }
        }
    }
}

#[test]
fn two_terms_share_cumulative_work_storage_and_the_original_control() {
    let baseline = checked(MIXED, read);
    let (work, bytes) = (baseline.usage.charged_work, baseline.usage.charged_bytes);
    assert!(baseline.result.is_ok());
    for (max_work, max_bytes, accepted) in [
        (work * 2, bytes * 2, true),
        (work * 2 - 1, bytes * 2, false),
        (work * 2, bytes * 2 - 1, false),
        (work, bytes * 2, false),
    ] {
        let original_deadline = deadline();
        let outcome = control::run(original_deadline, &mut |_, _| true, |control| {
            control.constrain(max_work as u64, max_bytes)?;
            let first = read(raw(MIXED), control)?;
            let second = read(raw(MIXED), control)?;
            Ok((first, second))
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if accepted {
            assert_eq!(outcome.usage.charged_work, work * 2);
            assert_eq!(outcome.usage.charged_bytes, bytes * 2);
        } else {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
}

#[test]
fn every_small_success_and_partial_failure_callback_can_refuse_publication() {
    for text in [
        r#"{"Var":["x",1]}"#,
        r#"{"App":[{"Named":"f"},[1]]}"#,
        r#"{"Let":[[["x",1]],2]}"#,
        r#"{"Not":1}"#,
        r#"{"Ite":[1,2,3]}"#,
        r#"{"Forall":[[["x",{"Seq":"Int"}]],2,[[3]]]}"#,
        r#"{"Exists":[[],0,[[]]]}"#,
        r#"{"Const":{"Bool":true}}"#,
        r#"{"Const":{"Int":[1,[3,0]]}}"#,
        r#"{"Const":{"Rational":[[1,[2]],[-1,[4]]]}}"#,
        r#"{"Const":{"BitVec":[[1,[3]],0]}}"#,
        r#"{"Const":{"String":"\u03bb"}}"#,
        r#"{"Let":[[["x",1],["y",false]],2]}"#,
        r#"{"Const":{"Rational":[[1,[2]],[0,[4]]]}}"#,
    ] {
        let calls = Cell::new(0);
        let baseline = control::run(
            deadline(),
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            |control| read(raw(text), control),
        );
        assert_eq!(
            baseline.result.is_ok(),
            serde_json::from_str::<TermData>(text).is_ok()
        );
        let total = calls.get();
        assert!(total > 2);
        for stop in 1..=total {
            calls.set(0);
            let outcome = control::run(
                deadline(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| read(raw(text), control),
            );
            assert_eq!(
                outcome.result,
                Err(TransportError::Refused),
                "{text} at {stop}"
            );
            assert_eq!(calls.get(), stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(outcome.usage, baseline.usage);
            }
        }
    }
}

#[test]
fn expired_original_deadline_and_sticky_failures_prevent_owner_publication() {
    for text in [MIXED, r#"{"Not":null}"#] {
        let outcome = control::run(
            Instant::now() - Duration::from_secs(1),
            &mut |_, _| -> bool { panic!("expired before callback") },
            |control| read(raw(text), control),
        );
        assert_eq!(outcome.result, Err(TransportError::Deadline));
        assert_eq!(outcome.usage.charged_work, 0);
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
    let outcome = control::run(deadline(), &mut |_, _| true, |control| {
        let first = read(raw(r#"{"Let":[[["x",1],["y",null]],0]}"#), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(read(raw(MIXED), control), Err(first));
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(
        outcome.result,
        Err(TransportError::InvalidShape(_))
    ));
}
