// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn unknown_duplicate_missing_null_version_and_wrong_field_types_refuse() {
    let fixture = Fixture::new();
    let base = std::str::from_utf8(JSON).unwrap();
    let invalid = [
        base.replace("\"version\":1", "\"version\":2"),
        base.replace("\"version\":1", "\"version\":null"),
        base.replace("\"version\":1", "\"version\":[]"),
        base.replace("\"version\":1", "\"version\":\"1\""),
        base.replace("\"version\":1", "\"version\":1,\"version\":1"),
        base.replace("\"version\":1,", ""),
        base.replace("\"rows\":", "\"unknown\":"),
        base.replace("\"id\":4", "\"id\":4,\"id\":4"),
        base.replace("\"id\":4,", ""),
        base.replace("\"literals\":[2]", "\"literals\":null"),
        base.replace("\"literals\":[2]", "\"literals\":[null]"),
        base.replace("\"hints\":[1,2]", "\"hints\":{}"),
        base.replace("\"hints\":[1,2]", "\"hints\":[1,2],\"other\":0"),
        base.replace("\"empty_clause_id\":5", "\"empty_clause_id\":null"),
        format!("{base} 0"),
        "null".into(),
        "[]".into(),
        "{}".into(),
    ];
    for bytes in invalid {
        let outcome = fixture.decode(bytes.as_bytes());
        assert!(outcome.result.is_err(), "accepted {bytes}");
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn lexical_tokens_depth_invalid_utf8_and_escape_controls_refuse() {
    let fixture = Fixture::new();
    let base = std::str::from_utf8(JSON).unwrap();
    for number in [
        "-1",
        "1.0",
        "1e0",
        "01",
        "18446744073709551616",
        "999999999999999999999",
    ] {
        assert!(fixture
            .decode(
                base.replace("\"id\":4", &format!("\"id\":{number}"))
                    .as_bytes()
            )
            .result
            .is_err());
    }
    for bad in [
        br#"{"version":1,"rows":[{"id":4,"literals":[[2]],"hints":[]}],"empty_clause_id":4}"#
            .as_slice(),
        br#"{"\uZZZZ":1}"#.as_slice(),
        b"{\"\xff\":1}".as_slice(),
        br#"{"version":1,"rows":[],"empty_clause_id":0}"#.as_slice(),
        br#"{"version":1"#.as_slice(),
    ] {
        assert!(fixture.decode(bad).result.is_err());
    }
    let wide = format!("{{\"{}\":0}}", "x".repeat(lexical::MAX_KEY_BYTES + 1));
    assert_eq!(
        fixture.decode(wide.as_bytes()).result,
        Err(WireError::InvalidJson)
    );
    let out_of_u32 = base.replace("\"literals\":[2]", "\"literals\":[4294967296]");
    assert!(fixture.decode(out_of_u32.as_bytes()).result.is_err());
}

#[test]
fn row_order_hints_terminal_and_empty_payload_refuse_in_both_directions() {
    let fixture = Fixture::new();
    for case in 0..8 {
        let mut value = payload();
        match case {
            0 => value.version += 1,
            1 => value.rows.clear(),
            2 => value.rows[0].id = 0,
            3 => value.rows[1].id = 4,
            4 => value.rows[0].hints[0] = 0,
            5 => value.rows[0].hints[0] = 4,
            6 => value.empty_clause_id = 4,
            7 => value.rows[1].literals.push(0),
            _ => unreachable!(),
        }
        assert!(fixture.encode(&value).result.is_err(), "case {case}");
        let bytes = serde_json::to_vec(&value).unwrap();
        assert!(fixture.decode(&bytes).result.is_err(), "case {case}");
    }
}
