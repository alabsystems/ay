// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests admit RawValue outside the controlled leaf call. This is not a full
//! owning wire decoder or proof-acceptance test; semantic checks remain later.

use super::{named_members, signature, step, term_entry};
use crate::bundle::retained::{
    control::{self, Control},
    owned_values::RawSlice,
    TransportError, TransportOutcome,
};
use ay_core::{time::Instant, NraSosCertificate, NraSosRational, ProofStep, TermId};
use serde::{de::DeserializeOwned, Serialize};
use serde_json::value::RawValue;
use std::{fmt::Debug, time::Duration};

type Decoder<T> = fn(RawSlice<'_>, &mut Control<'_>) -> Result<T, TransportError>;
const WORK: u64 = 2_000_000;
const STORAGE: usize = 2 * 1024 * 1024;
const THEORY: &str = r#"{"TheoryLemma":{"theory":"LIA\u0000λ","clause":[1,1,4294967295],"farkas":{"coefficients":[[2,4],[-6,-8]]},"kind":"Generic","lia":{"CuttingPlane":[[[[0,-7]]],0]}}}"#;

#[test]
fn variable_field_rows_decode_only_under_original_transport_admission() {
    let expected = ProofStep::FiniteFieldLinear {
        clause: (0..20).map(TermId).collect(),
        multipliers: vec![6; 20],
    };
    let text = serde_json::to_string(&expected).unwrap();
    assert!(serde_json::from_str::<ProofStep>(&text).is_err());
    assert_eq!(checked(&text, step).result.unwrap(), expected);
    assert!(attempt(&text, step, WORK, 16, end(), &mut |_, _| true)
        .result
        .is_err());
    assert!(attempt(&text, step, 3, STORAGE, end(), &mut |_, _| true)
        .result
        .is_err());
    assert!(
        attempt(&text, step, WORK, STORAGE, end(), &mut |_, _| false)
            .result
            .is_err()
    );
    let wrong = r#"{"FiniteFieldLinear":{"clause":[1,2],"multipliers":[1]}}"#;
    assert!(checked(wrong, step).result.is_err());
    let negative = r#"{"FiniteFieldLinear":{"clause":[1],"multipliers":[-1]}}"#;
    assert!(checked(negative, step).result.is_err());
}
const SIGNATURE: &str = r#"{"identity":"Cλ","argument_sorts":["Int",{"Seq":"Char"}],"result_sort":{"Datatype":["D",[["C",[]]]]},"nullary_term":4294967295}"#;

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
    // Numeric equality is insufficient for raw rational annotations.
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

fn sos_step() -> ProofStep {
    let rational = |numerator: i32, denominator: i32| NraSosRational {
        numerator: numerator.into(),
        denominator: denominator.into(),
    };
    ProofStep::NraSos {
        clause: vec![TermId(3)],
        certificate: NraSosCertificate {
            basis: vec![vec![]],
            gram: vec![vec![rational(0, 1)]],
            terms: vec![],
            rhs: rational(-1, 1),
        },
    }
}

#[test]
fn every_proof_step_variant_matches_existing_serde_values_and_bytes() {
    for text in [
        r#"{"Assume":4294967295}"#,
        r#"{"Resolution":{"clause":[1,2,1],"pivot":3,"clause1":0,"clause2":4294967295}}"#,
        THEORY,
        r#"{"Step":{"rule":{"Custom":"λ\u0000"},"clause":[1,1],"premises":[4294967295,0],"args":[2,2]}}"#,
        r#"{"Anchor":{"end_step":4294967295,"variables":[["x","Int"],["x",{"BitVec":[0]}]]}}"#,
    ] {
        accepts(text, step);
    }
    accepts(&serde_json::to_string(&sos_step()).unwrap(), step);
}

#[test]
fn struct_step_variants_accept_exact_sequences_reordered_and_escaped_fields() {
    for text in [
        r#"{"Resolution":[[1,2,1],3,0,4294967295]}"#,
        r#"{"Resolution":{"clause2":1,"pivot":0,"clause1":2,"clause":[]}}"#,
        r#"{"TheoryLemma":["BV",[1],null,{"BvBitBlastGate":["Add",0]},null]}"#,
        r#"{"TheoryLemma":{"kind":"Generic","theory":"T","clause":[],"lia":null,"farkas":null}}"#,
        r#"{"Step":["True",[],[],[]]}"#,
        r#"{"St\u0065p":{"ar\u0067s":[],"premises":[0],"clause":[],"rule":{"AndPos":0}}}"#,
        r#"{"Anchor":[0,[["λ",{"Seq":"Char"}]]]}"#,
    ] {
        accepts(text, step);
    }
    let value = serde_json::to_value(sos_step()).unwrap();
    let body = &value["NraSos"];
    let text = format!(
        r#"{{"NraSos":[{},{}]}}"#,
        body["clause"], body["certificate"]
    );
    accepts(&text, step);
}

#[test]
fn theory_map_option_omission_and_null_are_distinct_from_short_sequences() {
    for optional in [
        "",
        r#", "farkas":null"#,
        r#", "lia":null"#,
        r#", "farkas":null,"lia":null"#,
    ] {
        let text =
            format!(r#"{{"TheoryLemma":{{"theory":"T","clause":[],"kind":"Generic"{optional}}}}}"#);
        accepts(&text, step);
        if let ProofStep::TheoryLemma { farkas, lia, .. } = checked(&text, step).result.unwrap() {
            assert!(farkas.is_none() && lia.is_none());
        } else {
            panic!("theory variant lost");
        }
    }
    for text in [
        r#"{"TheoryLemma":["T",[],null,"Generic"]}"#,
        r#"{"TheoryLemma":["T",[]]}"#,
        r#"{"TheoryLemma":["T",[],"Generic",null]}"#,
        r#"{"TheoryLemma":{"theory":"T","clause":[]}}"#,
    ] {
        rejects(text, step);
    }
}

#[test]
fn proof_step_missing_unknown_duplicate_nullable_and_numeric_fields_refuse() {
    for text in [
        "null",
        "0",
        "[]",
        "{}",
        r#""Assume""#,
        r#"{"0":0}"#,
        r#"{"Assume":null}"#,
        r#"{"Assume":1.0}"#,
        r#"{"Assume":-0}"#,
        r#"{"Assume":4294967296}"#,
        r#"{"Assume":1,"Assume":2}"#,
        r#"{"Resolution":{"clause":[],"pivot":0,"clause1":1}}"#,
        r#"{"Resolution":[[],0,1,2,3]}"#,
        r#"{"Resolution":[[],0,-1,2]}"#,
        r#"{"Resolution":{"clause":[],"pivot":0,"clause1":1,"clause2":2,"extra":0}}"#,
        r#"{"TheoryLemma":{"theory":"T","clause":[],"kind":"Generic","farkas":null,"farkas":null}}"#,
        r#"{"TheoryLemma":{"theory":"T","clause":[],"kind":"Generic","lia":null,"l\u0069a":null}}"#,
        r#"{"TheoryLemma":{"theory":"T","clause":[],"kind":"Generic","extra":0}}"#,
        r#"{"TheoryLemma":["T",[],false,"Generic",null]}"#,
        r#"{"Step":{"rule":"True","clause":[],"premises":[]}}"#,
        r#"{"Step":["True",[],null,[]]}"#,
        r#"{"Step":["True",[],[],[null]]}"#,
        r#"{"Anchor":[0,null]}"#,
        r#"{"Anchor":[0,[["x"]]]}"#,
        r#"{"Anchor":[0,[["x",null]]]}"#,
    ] {
        rejects(text, step);
    }
}

#[test]
fn positional_term_entries_preserve_order_without_authenticating_the_store() {
    for text in [
        r#"[{"Const":{"Bool":true}},"Bool"]"#,
        r#"[{"Var":["x",4294967295]},{"BitVec":[0]}]"#,
        r#"[{"Not":4294967295},"Int"]"#,
        r#"[{"Const":{"Rational":[[1,[2]],[-1,[4]]]}},"Real"]"#,
    ] {
        accepts(text, term_entry);
    }
    for text in [
        "null",
        "[]",
        r#"[{"Not":0}]"#,
        r#"["Bool",{"Not":0}]"#,
        r#"[{"Not":0},"Bool",0]"#,
        r#"[{"Not":0},null]"#,
        r#"{"term":{"Not":0},"sort":"Bool"}"#,
    ] {
        rejects(text, term_entry);
    }
}

#[test]
fn declaration_name_and_members_are_exact_tuples_with_order_and_duplicates() {
    for text in [
        r#"["D",["C","C","A"]]"#,
        r#"["",[]]"#,
        r#"["\u0000λ",["\uD83D\uDE00","","λ"]]"#,
    ] {
        accepts(text, named_members);
    }
    let actual = checked(r#"["D",["C","C","A"]]"#, named_members)
        .result
        .unwrap();
    assert_eq!(actual.1, ["C", "C", "A"]);
    for text in [
        "null",
        "[]",
        r#"["D"]"#,
        r#"["D",[],0]"#,
        r#"[[],"D"]"#,
        r#"["D",null]"#,
        r#"["D",[null]]"#,
        r#"{"name":"D","members":[]}"#,
        r#"["\uD800",[]]"#,
    ] {
        rejects(text, named_members);
    }
}

#[test]
fn signatures_preserve_all_sorts_and_map_only_implicit_option_defaults() {
    for text in [
        SIGNATURE,
        r#"{"identity":"C","argument_sorts":[],"result_sort":"Bool"}"#,
        r#"{"identity":"C","argument_sorts":[],"result_sort":"Bool","nullary_term":null}"#,
        r#"["C",["Int","Int"],"Bool",null]"#,
        r#"["C",[],"Bool",4294967295]"#,
        r#"{"result_sort":"Bool","argument_sorts":[],"ident\u0069ty":"C","nullary_term":0}"#,
    ] {
        accepts(text, signature);
    }
    for text in [
        "null",
        "{}",
        "[]",
        r#"["C",[],"Bool"]"#,
        r#"["C",[],"Bool",null,0]"#,
        r#"{"identity":"C","argument_sorts":[]}"#,
        r#"{"identity":"C","argument_sorts":null,"result_sort":"Bool"}"#,
        r#"{"identity":"C","argument_sorts":[],"result_sort":"Bool","extra":0}"#,
        r#"{"identity":"C","argument_sorts":[],"result_sort":"Bool","nullary_term":null,"nullary_term":0}"#,
        r#"["C",[],"Bool",-0]"#,
        r#"["C",[],"Bool",4294967296]"#,
    ] {
        rejects(text, signature);
    }
}

#[test]
fn sos_wire_rejects_noncanonical_integers_and_extra_fields_but_not_theorem_shape() {
    let original = serde_json::to_value(sos_step()).unwrap();
    for invalid in [
        serde_json::json!([1, [1, 0]]),
        serde_json::json!([0, [1]]),
        serde_json::json!([1, []]),
        serde_json::json!([2, [1]]),
    ] {
        let mut value = original.clone();
        value["NraSos"]["certificate"]["rhs"]["numerator"] = invalid;
        rejects(&value.to_string(), step);
    }
    let mut value = original.clone();
    value["NraSos"]["certificate"]["invented_source"] = serde_json::json!([]);
    rejects(&value.to_string(), step);
    let mut value = original;
    value["NraSos"]["certificate"]["rhs"]["denominator"] = serde_json::json!([0, []]);
    // Canonical zero is accepted by the SOS wire grammar, but not by its
    // semantic shape validator. The typed transport must not invent authority.
    accepts(&value.to_string(), step);
    let ProofStep::NraSos { certificate, .. } = checked(&value.to_string(), step).result.unwrap()
    else {
        panic!("SOS variant lost");
    };
    assert!(certificate.validate_shape().is_err());
}

#[test]
fn sos_clause_bound_is_preserved_by_the_snapshot_step_decoder() {
    let mut value = serde_json::to_value(sos_step()).unwrap();
    value["NraSos"]["clause"] =
        serde_json::json!(vec![u32::MAX; NraSosCertificate::MAX_CLAUSE_SLOTS]);
    accepts(&value.to_string(), step);
    value["NraSos"]["clause"] =
        serde_json::json!(vec![u32::MAX; NraSosCertificate::MAX_CLAUSE_SLOTS + 1]);
    rejects(&value.to_string(), step);
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
        let outcome = attempt(text, decode, work, bytes, end(), &mut |_, _| true);
        assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn exact_and_short_limits_cover_every_snapshot_owner_family() {
    boundaries(THEORY, step);
    boundaries(&serde_json::to_string(&sos_step()).unwrap(), step);
    boundaries(r#"[{"Var":["owned",1]},{"Seq":"Int"}]"#, term_entry);
    boundaries(r#"["D",["C","C"]]"#, named_members);
    boundaries(SIGNATURE, signature);
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
        let outcome = attempt(text, decode, WORK, STORAGE, end(), &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert_eq!(
            outcome.result,
            Err(TransportError::Refused),
            "{text} at {stop}"
        );
        assert_eq!(calls, stop);
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
        if stop == total {
            assert_eq!(outcome.usage, full.usage);
        }
    }
}

#[test]
fn every_step_route_and_partial_owner_cleanup_can_refuse_at_each_callback() {
    for text in [
        r#"{"Assume":1}"#,
        r#"{"Resolution":[[],0,1,2]}"#,
        r#"{"TheoryLemma":{"theory":"T","clause":[],"kind":"Generic"}}"#,
        r#"{"Step":["True",[],[],[]]}"#,
        r#"{"Anchor":[0,[["x","Int"]]]}"#,
        r#"{"Anchor":[0,[["x","Int"],["y",null]]]}"#,
    ] {
        checkpoints(text, step);
    }
    checkpoints(&serde_json::to_string(&sos_step()).unwrap(), step);
    checkpoints(r#"[{"Var":["x",0]},"Bool"]"#, term_entry);
    checkpoints(r#"["D",["C",null]]"#, named_members);
    checkpoints(r#"["C",[],"Bool",null]"#, signature);
}

fn shared<T: Debug + PartialEq>(text: &str, decode: Decoder<T>) {
    let full = checked(text, decode);
    assert!(full.result.is_ok());
    let (work, bytes) = (full.usage.charged_work as u64, full.usage.charged_bytes);
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    for (work, bytes, accepted) in [
        (work * 2, bytes * 2, true),
        (work * 2 - 1, bytes * 2, false),
        (work * 2, bytes * 2 - 1, false),
    ] {
        let outcome = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(work, bytes)?;
            let first = decode(RawSlice::from_raw(raw), control)?;
            let second = decode(RawSlice::from_raw(raw), control)?;
            Ok((first, second))
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
}

#[test]
fn consecutive_owners_share_one_cumulative_budget_without_renewal() {
    shared(THEORY, step);
    shared(r#"[{"Var":["x",1]},"Bool"]"#, term_entry);
    shared(r#"["D",["C"]]"#, named_members);
    shared(SIGNATURE, signature);
}

fn terminal<T: Debug + PartialEq>(invalid: &str, valid: &str, decode: Decoder<T>) {
    for text in [invalid, valid] {
        let outcome = attempt(
            text,
            decode,
            WORK,
            STORAGE,
            Instant::now().checked_sub(Duration::from_secs(1)).unwrap(),
            &mut |_, _| -> bool { panic!("expired before callback") },
        );
        assert_eq!(outcome.result, Err(TransportError::Deadline));
        assert_eq!(outcome.usage.charged_work, 0);
        assert_eq!(outcome.usage.charged_bytes, 0);
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
fn original_deadline_and_caught_errors_cannot_authorize_a_later_owner() {
    terminal(r#"{"Step":["True",[],[],[null]]}"#, THEORY, step);
    terminal(r#"[{"Not":0},null]"#, r#"[{"Not":0},"Bool"]"#, term_entry);
    terminal(r#"["D",[null]]"#, r#"["D",[]]"#, named_members);
    terminal(r#"["C",[],"Bool"]"#, SIGNATURE, signature);
}
