// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn strict_schema_rejects_missing_duplicate_extra_and_query_claim_fields() {
    let token = CancellationToken::new();
    let (source, trace) = fixtures::scalar(&token);
    let wire = fixtures::wire(&source, &trace, &token);
    let bytes = transport::encode(&wire, &control(&token)).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    for field in ["schema", "source", "steps", "functions", "pinned_sha256"] {
        let mut missing = json.clone();
        missing.as_object_mut().unwrap().remove(field);
        assert!(transport::decode::<wire::Wire>(
            &serde_json::to_vec(&missing).unwrap(),
            &control(&token)
        )
        .is_none());
    }
    for (field, value) in [
        ("query_id", serde_json::json!({"source_query_ordinal": 0})),
        ("native_sat_validated", serde_json::json!(true)),
        ("replay_script", serde_json::json!("(assert true)")),
    ] {
        let mut extra = json.clone();
        extra[field] = value;
        assert!(transport::decode::<wire::Wire>(
            &serde_json::to_vec(&extra).unwrap(),
            &control(&token)
        )
        .is_none());
    }
    let text = std::str::from_utf8(&bytes).unwrap();
    let duplicate = format!("{{\"schema\":\"{}\",{}", wire::SCHEMA, &text[1..]);
    assert!(transport::decode::<wire::Wire>(duplicate.as_bytes(), &control(&token)).is_none());
    for path in ["steps", "bindings"] {
        let mut extra = json.clone();
        if path == "steps" {
            extra["steps"][0]["unused"] = serde_json::json!(0);
        } else {
            extra["steps"][0]["bindings"][0]["sort"] = serde_json::json!("Bool");
        }
        assert!(transport::decode::<wire::Wire>(
            &serde_json::to_vec(&extra).unwrap(),
            &control(&token)
        )
        .is_none());
    }
}

#[test]
fn source_topology_manifest_and_pin_mutations_refuse_without_partial_preparation() {
    let token = CancellationToken::new();
    let (source, trace) = fixtures::scalar(&token);
    for mutation in 0..12 {
        let mut wire = fixtures::wire(&source, &trace, &token);
        match mutation {
            0 => wire.source.push_str("; changed unused source\n"),
            1 => wire.schema.push_str("/foreign"),
            2 => wire.steps[0].clause_index = usize::MAX,
            3 => wire.steps[2].premises.swap(0, 1),
            4 => wire.steps[2].premises[1] = 0,
            5 => {
                wire.steps.pop();
            }
            6 => wire.steps[0].bindings.clear(),
            7 => wire.steps[0].bindings[0].name.push_str("foreign"),
            8 => wire.steps[0].bindings[0].value = "false".to_owned(),
            9 => wire.steps[0].bindings[0].value = "(_ bv4 2)".to_owned(),
            10 => wire.steps[0].bindings[0].value = "(_ bv1 2)".to_owned(),
            _ => wire.pinned_sha256 = "0".repeat(64),
        }
        // Swapping ordered edges is structurally valid, but changes full pins.
        assert!(
            rebuild::prepare(&source, &wire, &control(&token)).is_none(),
            "{mutation}"
        );
    }
    let wire = fixtures::wire(&source, &trace, &token);
    assert!(rebuild::prepare(&source, &wire, &control(&token)).is_some());
}

#[test]
fn public_entry_limits_refuse_and_do_not_revive_observed_cancellation() {
    let token = CancellationToken::new();
    let (source, trace) = fixtures::scalar(&token);
    for duration in [Duration::ZERO, Duration::MAX] {
        assert!(trace.export_artifact(&source, duration, &token).is_err());
        assert!(source
            .validate_trace_artifact(b"{}", duration, None, &token)
            .is_err());
    }
    assert!(source
        .validate_trace_artifact(b"{}", Duration::from_secs(1), Some(0), &token)
        .is_err());
    {
        let _memory = SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(trace
            .export_artifact(&source, Duration::from_secs(1), &token)
            .is_err());
    }
    let stopped = control(&token);
    token.cancel();
    assert!(stopped.poll().is_none());
    token.reset();
    assert!(transport::decode::<wire::Wire>(b"{}", &stopped).is_none());
    let exhausted = control(&token);
    exhausted.bytes(64 * 1024 * 1024).unwrap();
    assert!(rebuild::prepare(
        &source,
        &fixtures::wire(&source, &trace, &token),
        &exhausted
    )
    .is_none());
    assert!(rebuild::prepare(
        &source,
        &fixtures::wire(&source, &trace, &token),
        &control(&token)
    )
    .is_some());
}
