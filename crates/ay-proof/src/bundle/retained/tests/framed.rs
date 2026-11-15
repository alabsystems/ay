// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn framed_payload_depth_six_and_inventory_depth_eight_are_exact_boundaries() {
    // Each ordinary refutation reaches depth four at a row's literals/hints.
    // Its enclosing role object and frame array add exactly two levels.
    let raw = std::str::from_utf8(PAYLOAD).unwrap();
    let payload = format!("[{{\"outside_free_offset\":{raw}}},{{\"final_clause\":{raw}}}]");
    let field = RetainedField::Present(vec![RetainedStepPayload {
        step: 0,
        payload: payload.as_bytes().to_vec(),
    }]);
    let bytes = encoded(&field);
    assert_eq!(decoded(&bytes).result.unwrap(), field);
    let deeper = format!("[{payload}]");
    let too_deep = RetainedField::Present(vec![RetainedStepPayload {
        step: 0,
        payload: deeper.as_bytes().to_vec(),
    }]);
    assert_eq!(
        encode(RETAINED_SCHEMA, &too_deep, &limits(), end(), &mut |_, _| {
            true
        })
        .result,
        Err(TransportError::InvalidJson),
    );
    let raw_inventory = format!("[{{\"step\":0,\"payload\":{deeper}}}]");
    let outcome = decoded(raw_inventory.as_bytes());
    assert_eq!(outcome.result, Err(TransportError::InvalidJson));
    assert_eq!(outcome.usage.charged_bytes, 0);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn an_array_payload_is_only_transport_and_preserves_unknown_claims() {
    for payload in [b"[]".as_slice(), br#"[{"unrecognized":{}}]"#] {
        let field = RetainedField::Present(vec![RetainedStepPayload {
            step: u32::MAX,
            payload: payload.to_vec(),
        }]);
        assert_eq!(decoded(&encoded(&field)).result.unwrap(), field);
    }
    // Mandatory source-bound framing/replay, not this owner codec, must reject
    // these invented roles, empty frame sets and nonexistent proof-step IDs.
}
