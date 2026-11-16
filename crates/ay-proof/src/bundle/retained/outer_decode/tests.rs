// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full owning transport tests, not proof acceptance or external-query binding.

use super::*;
use crate::bundle::retained::{
    encode_bundle, RetainedStepPayload, TransportOutcome, RETAINED_SCHEMA, SNAPSHOT_SCHEMA,
};
use serde_json::{json, Value};
use std::{cell::Cell, panic::AssertUnwindSafe, time::Duration};

const EMPTY: &str = r#"{"schema":"ay.proofbundle/v5","steps":[],"term_entries":[],"true_term":null,"false_term":null,"var_counter":0,"obligation_assertions":[],"datatype_declarations":[],"constructor_selectors":[],"datatype_member_signatures":[],"declared_function_identities":[]}"#;
const MIXED: &str = r#"{
 "schema":"ay.proofbundle/v5",
 "steps":[
  {"Assume":0},
  {"Resolution":[[0,0],1,0,4294967295]},
  {"TheoryLemma":{"theory":"LIA\u0000λ","clause":[1,1],"farkas":{"coefficients":[[2,4],[-6,-8]]},"kind":"Generic","lia":{"CuttingPlane":[[[[0,-7]]],0]}}},
  {"Step":[{"Custom":"λ\u0000"},[],[0,0],[1]]},
  {"Anchor":[5,[["x",{"Array":["Int",{"Seq":"Char"}]}]]]},
  {"NraSos":{"clause":[0],"certificate":[[[]],[],[],[[1,[2]],[0,[]]]]}}
 ],
 "term_entries":[
  [{"Const":{"String":"quoted \"λ\"\n\u0000"}},"String"],
  [{"Const":{"Int":[-1,[4294967295,2,1]]}},"Int"],
  [{"Const":{"Rational":[[1,[2]],[-1,[4]]]}},"Real"],
  [{"App":[{"Indexed":["extract",[7,0,7]]},[0,0]]},{"BitVec":[8]}],
  [{"Forall":[[["q",{"Array":["Int",{"Seq":"Char"}]}]],0,[[0,1],[]]]},"Bool"],
  [{"Const":{"Bool":true}},"Bool"]
 ],
 "true_term":5,"false_term":null,"var_counter":4294967295,
 "obligation_assertions":[0,0,4294967295],
 "datatype_declarations":[["Dλ",["C","C"]]],
 "constructor_selectors":[["C",["sel\u0000","sel"]]],
 "datatype_member_signatures":[{"identity":"Cλ","argument_sorts":["Int",{"Seq":"Char"}],"result_sort":{"Datatype":["D",[["C",[]]]]},"nullary_term":4294967295}],
 "declared_function_identities":["user_mode","fp.neg"]
}"#;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn limits() -> BundleLimits {
    BundleLimits {
        max_json_bytes: 1024 * 1024,
        max_storage_bytes: 8 * 1024 * 1024,
        max_work: 10_000_000,
        deadline: end(),
    }
}

fn wire() -> WireLimits {
    WireLimits {
        max_json_bytes: 1024 * 1024,
        max_rows: 100,
        max_literals: 1000,
        max_hints: 1000,
        max_work: 1_000_000,
        max_storage_bytes: 8 * 1024 * 1024,
        deadline: end(),
    }
}

fn attempt(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> TransportOutcome<RetainedBundle> {
    let deadline = deadline.min(limits.deadline).min(wire.deadline);
    control::run(deadline, progress, |control| {
        control.constrain(limits.max_work, limits.max_storage_bytes)?;
        read(bytes, limits, wire, deadline, control)
    })
}

fn checked(bytes: &[u8]) -> TransportOutcome<RetainedBundle> {
    attempt(bytes, &limits(), &wire(), end(), &mut |_, _| true)
}

fn document(source: &str, inventory: &str) -> Vec<u8> {
    let mut value: Value = serde_json::from_str(source).unwrap();
    value["schema"] = json!(RETAINED_SCHEMA);
    value["retained"] = serde_json::from_str(inventory).unwrap();
    serde_json::to_vec(&value).unwrap()
}

fn empty() -> Vec<u8> {
    document(EMPTY, "[]")
}

#[test]
fn all_snapshot_owner_kinds_match_serde_values_and_bytes_after_input_drop() {
    let mut source: SerializableProofBundle = serde_json::from_str(MIXED).unwrap();
    let payload = br#"{ "unrecognized": 7 }"#.to_vec(); // intentionally no proof authority
    let field = RetainedField::Present(vec![RetainedStepPayload {
        step: 2,
        payload: payload.clone(),
    }]);
    let bytes = encode_bundle(&source, &field, &limits(), &wire(), end(), &mut |_, _| true)
        .result
        .unwrap();
    let result = checked(&bytes);
    assert_eq!(result.usage.returned_owned_bytes, 0); // not a false inventory-only total
    let decoded = result.result.unwrap();
    drop(bytes);
    source.schema = RETAINED_SCHEMA.to_owned();
    let (actual, inventory) = decoded.parts();
    assert_eq!(actual.steps, source.steps);
    assert_eq!(actual.term_entries, source.term_entries);
    assert_eq!(
        actual.datatype_member_signatures,
        source.datatype_member_signatures
    );
    assert_eq!(
        serde_json::to_vec(actual).unwrap(),
        serde_json::to_vec(&source).unwrap()
    );
    assert_eq!(inventory, &[RetainedStepPayload { step: 2, payload }]);
    assert_eq!(actual.schema, RETAINED_SCHEMA);
}

#[test]
fn present_empty_inventory_and_omitted_or_null_legacy_options_are_preserved() {
    for omit_true in [false, true] {
        for omit_false in [false, true] {
            let mut value: Value = serde_json::from_slice(&empty()).unwrap();
            if omit_true {
                value.as_object_mut().unwrap().remove("true_term");
            }
            if omit_false {
                value.as_object_mut().unwrap().remove("false_term");
            }
            let decoded = checked(&serde_json::to_vec(&value).unwrap())
                .result
                .unwrap();
            let (actual, inventory) = decoded.parts();
            assert_eq!(actual.true_term, None);
            assert_eq!(actual.false_term, None);
            assert_eq!(inventory, []);
            value.as_object_mut().unwrap().remove("retained");
            let expected: SerializableProofBundle = serde_json::from_value(value).unwrap();
            assert_eq!(
                serde_json::to_vec(actual).unwrap(),
                serde_json::to_vec(&expected).unwrap()
            );
        }
    }
}

#[test]
fn legacy_and_schema_presence_errors_refuse_before_typed_owners() {
    let bound = limits();
    let wire = wire();
    let deadline = end();
    let borrowed = control::run(deadline, &mut |_, _| true, |control| {
        outer_view::read(EMPTY.as_bytes(), bound.max_json_bytes, control)
    });
    assert!(borrowed.result.is_ok());
    let legacy = attempt(EMPTY.as_bytes(), &bound, &wire, deadline, &mut |_, _| true);
    assert!(matches!(
        legacy.result,
        Err(TransportError::Presence(PresenceError::UnsupportedSchema))
    ));
    assert_eq!(legacy.usage.charged_bytes, borrowed.usage.charged_bytes);
    for (schema, retained) in [
        (SNAPSHOT_SCHEMA, Some(json!([]))),
        (RETAINED_SCHEMA, None),
        (RETAINED_SCHEMA, Some(Value::Null)),
        ("ay.proofbundle/v5", Some(json!([]))),
    ] {
        let mut value: Value = serde_json::from_str(EMPTY).unwrap();
        value["schema"] = json!(schema);
        if let Some(retained) = retained {
            value["retained"] = retained;
        }
        assert!(checked(&serde_json::to_vec(&value).unwrap())
            .result
            .is_err());
    }
    for key in [
        "schema",
        "steps",
        "term_entries",
        "var_counter",
        "obligation_assertions",
        "datatype_declarations",
        "constructor_selectors",
        "datatype_member_signatures",
    ] {
        let mut value: Value = serde_json::from_slice(&empty()).unwrap();
        value.as_object_mut().unwrap().remove(key);
        assert!(
            checked(&serde_json::to_vec(&value).unwrap())
                .result
                .is_err(),
            "{key}"
        );
    }
}

#[test]
fn escaped_schema_and_keys_accept_but_duplicate_or_unknown_keys_refuse() {
    let text = String::from_utf8(empty()).unwrap();
    let escaped = text
        .replace("schema", r#"sch\u0065ma"#)
        .replace("ay.proofbundle/v6", r#"ay.proofbundle\/v6"#);
    assert_eq!(
        checked(escaped.as_bytes()).result.unwrap().parts().0.schema,
        RETAINED_SCHEMA
    );
    for prefix in [
        r#"{"unknown":0,"#,
        r#"{"retained":[],"#,
        r#"{"sch\u0065ma":"ay.proofbundle/v6","#,
    ] {
        let duplicate = text.replacen('{', prefix, 1);
        assert!(checked(duplicate.as_bytes()).result.is_err());
    }
}

#[test]
fn malformed_typed_fields_and_null_children_cannot_publish_partial_snapshot() {
    for (key, invalid) in [
        ("steps", json!([{"Assume": null}])),
        (
            "steps",
            json!([{"TheoryLemma": ["T", [], null, "Generic"]}]),
        ),
        ("term_entries", json!([[{"Not":0}, null]])),
        ("datatype_declarations", json!([["D", [null]]])),
        ("constructor_selectors", json!([["C"]])),
        ("datatype_member_signatures", json!([["C", [], "Bool"]])),
        ("obligation_assertions", json!([4294967296_u64])),
        ("true_term", json!(-1)),
        ("false_term", json!(1.0)),
        ("var_counter", Value::Null),
    ] {
        let mut value: Value = serde_json::from_slice(&document(MIXED, "[]")).unwrap();
        value[key] = invalid;
        let outcome = checked(&serde_json::to_vec(&value).unwrap());
        assert!(outcome.result.is_err(), "{key}");
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn inventory_shape_and_eight_entry_bound_do_not_authenticate_payload_or_ids() {
    let entries = json!((0..8)
        .map(|_| json!({"step":4294967295_u32,"payload":{"unknown":7}}))
        .collect::<Vec<_>>());
    let bytes = document(EMPTY, &entries.to_string());
    assert_eq!(checked(&bytes).result.unwrap().parts().1.len(), 8);
    // Duplicate IDs and unknown payload fields intentionally remain untrusted
    // transport; replay must reject them, not silently omit or normalize them.
    for inventory in [
        json!((0..9)
            .map(|_| json!({"step":0,"payload":{}}))
            .collect::<Vec<_>>()),
        json!([{"step":0}]),
        json!([{"step":0,"payload":null}]),
        json!([{"step":0,"payload":0}]),
        json!([{"step":0,"payload":{},"extra":0}]),
        json!([{"step":4294967296_u64,"payload":{}}]),
    ] {
        assert!(checked(&document(EMPTY, &inventory.to_string()))
            .result
            .is_err());
    }
}

#[test]
fn input_exact_one_short_and_whole_work_storage_ceilings_are_enforced() {
    let bytes = document(MIXED, r#"[{"step":2,"payload":{}}]"#);
    let full = checked(&bytes);
    assert!(full.result.is_ok());
    let mut bound = limits();
    bound.max_json_bytes = bytes.len();
    bound.max_work = full.usage.charged_work as u64;
    bound.max_storage_bytes = full.usage.charged_bytes;
    assert!(attempt(&bytes, &bound, &wire(), end(), &mut |_, _| true)
        .result
        .is_ok());
    for which in 0..3 {
        let mut short = limits();
        match which {
            0 => short.max_json_bytes = bytes.len() - 1,
            1 => short.max_work = full.usage.charged_work as u64 - 1,
            _ => short.max_storage_bytes = full.usage.charged_bytes - 1,
        }
        let refused = attempt(&bytes, &short, &wire(), end(), &mut |_, _| true);
        assert!(matches!(refused.result, Err(TransportError::Limit { .. })));
        assert_eq!(refused.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn wire_local_caps_and_whole_caps_both_constrain_the_same_inventory_charges() {
    let raw = br#"[{"step":0,"payload":{"unknown":7}}]"#;
    let local = control::run(end(), &mut |_, _| true, |control| {
        inventory(raw, &wire(), end(), control)
    });
    assert!(local.result.is_ok());
    let bytes = document(EMPTY, std::str::from_utf8(raw).unwrap());
    let full = checked(&bytes);
    assert!(full.result.is_ok());
    assert!(full.usage.charged_work > local.usage.charged_work);
    assert!(full.usage.charged_bytes > local.usage.charged_bytes);
    for (work, storage, accepted) in [
        (
            local.usage.charged_work as u64,
            local.usage.charged_bytes,
            true,
        ),
        (
            local.usage.charged_work as u64 - 1,
            local.usage.charged_bytes,
            false,
        ),
        (
            local.usage.charged_work as u64,
            local.usage.charged_bytes - 1,
            false,
        ),
        (0, local.usage.charged_bytes, false),
    ] {
        let mut wire = wire();
        wire.max_work = work;
        wire.max_storage_bytes = storage;
        assert_eq!(
            attempt(&bytes, &limits(), &wire, end(), &mut |_, _| true)
                .result
                .is_ok(),
            accepted
        );
    }
    let mut short = limits();
    short.max_work = full.usage.charged_work as u64 - 1;
    assert!(matches!(
        attempt(&bytes, &short, &wire(), end(), &mut |_, _| true).result,
        Err(TransportError::Limit {
            resource: "transport work",
            ..
        })
    ));
    let mut short_payload = wire();
    short_payload.max_json_bytes = br#"{"unknown":7}"#.len() - 1;
    assert!(matches!(
        attempt(&bytes, &limits(), &short_payload, end(), &mut |_, _| true).result,
        Err(TransportError::Limit {
            resource: "payload JSON bytes",
            ..
        })
    ));
}

#[test]
fn repeated_reads_share_the_original_ledger_even_after_first_owner_is_dropped() {
    let bytes = empty();
    let full = checked(&bytes);
    assert!(full.result.is_ok());
    let deadline = end();
    let outcome = control::run(deadline, &mut |_, _| true, |control| {
        control.constrain(full.usage.charged_work as u64, full.usage.charged_bytes)?;
        drop(read(&bytes, &limits(), &wire(), deadline, control)?);
        read(&bytes, &limits(), &wire(), deadline, control)
    });
    assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
    assert!(outcome.usage.charged_work >= full.usage.charged_work);
}

#[test]
fn every_success_and_inventory_failure_poll_is_terminal_including_cleanup() {
    for (bytes, accepted) in [(empty(), true), (document(EMPTY, r#"[{"step":0}]"#), false)] {
        let calls = Cell::new(0);
        let full = attempt(&bytes, &limits(), &wire(), end(), &mut |_, _| {
            calls.set(calls.get() + 1);
            true
        });
        assert_eq!(full.result.is_ok(), accepted);
        let total = calls.get();
        for stop in 1..=total {
            calls.set(0);
            let stopped = attempt(&bytes, &limits(), &wire(), end(), &mut |_, _| {
                calls.set(calls.get() + 1);
                calls.get() != stop
            });
            assert!(matches!(stopped.result, Err(TransportError::Refused)));
            assert_eq!(calls.get(), stop);
            assert_eq!(stopped.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(stopped.usage, full.usage);
            }
        }
    }
}

#[test]
fn all_original_deadlines_refuse_without_callback_or_new_inner_deadline() {
    for source in 0..3 {
        let (mut bound, mut wire, mut deadline) = (limits(), wire(), end());
        let expired = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
        match source {
            0 => deadline = expired,
            1 => bound.deadline = expired,
            _ => wire.deadline = expired,
        }
        let outcome = attempt(&empty(), &bound, &wire, deadline, &mut |_, _| -> bool {
            panic!("expired")
        });
        assert!(matches!(outcome.result, Err(TransportError::Deadline)));
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn swallowed_inner_error_and_caught_callback_panic_cannot_revive_control() {
    let bytes = document(EMPTY, r#"[{"step":0}]"#);
    let deadline = end();
    let outcome = control::run(deadline, &mut |_, _| true, |control| {
        let error = read(&bytes, &limits(), &wire(), deadline, control).unwrap_err();
        let before = control.usage;
        assert!(
            matches!(read(&empty(), &limits(), &wire(), deadline, control), Err(found) if found == error)
        );
        assert_eq!(control.usage, before);
        Ok(())
    });
    assert!(outcome.result.is_err());
    let calls = Cell::new(0);
    let outcome = control::run(
        deadline,
        &mut |_, _| {
            calls.set(calls.get() + 1);
            assert_ne!(calls.get(), 4, "callback panic");
            true
        },
        |control| {
            assert!(std::panic::catch_unwind(AssertUnwindSafe(|| read(
                &empty(),
                &limits(),
                &wire(),
                deadline,
                control
            )))
            .is_err());
            assert!(matches!(
                read(&empty(), &limits(), &wire(), deadline, control),
                Err(TransportError::Refused)
            ));
            Ok(())
        },
    );
    assert_eq!(outcome.result, Err(TransportError::Refused));
    assert_eq!(calls.get(), 4);
}
