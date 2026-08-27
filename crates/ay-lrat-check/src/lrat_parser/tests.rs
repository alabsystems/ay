// Copyright 2026 Andrew Yates
// Unit tests for the LRAT proof parser.

use super::*;

#[test]
fn test_parse_text_addition() {
    let input = "4 1 -2 0 1 2 3 0\n";
    let steps = parse_text_lrat(input).unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 4,
            clause: vec![lit(1), lit(-2)],
            hints: vec![1, 2, 3],
        }
    );
}

#[test]
fn test_parse_text_deletion() {
    let input = "5 d 1 2 3 0\n";
    let steps = parse_text_lrat(input).unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0], LratStep::Delete { ids: vec![1, 2, 3] });
}

#[test]
fn test_parse_text_empty_clause() {
    let input = "3 0 1 2 0\n";
    let steps = parse_text_lrat(input).unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 3,
            clause: vec![],
            hints: vec![1, 2],
        }
    );
}

#[test]
fn test_parse_text_multiple_steps() {
    let input = "\
4 1 -2 0 1 2 0
5 d 1 0
6 0 4 3 0
";
    let steps = parse_text_lrat(input).unwrap();
    assert_eq!(steps.len(), 3);
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 4,
            clause: vec![lit(1), lit(-2)],
            hints: vec![1, 2],
        }
    );
    assert_eq!(steps[1], LratStep::Delete { ids: vec![1] });
    assert_eq!(
        steps[2],
        LratStep::Add {
            id: 6,
            clause: vec![],
            hints: vec![4, 3],
        }
    );
}

#[test]
fn test_is_binary_detection() {
    assert!(is_binary_lrat(&[b'a', 3, 2, 0, 1, 0]));
    assert!(is_binary_lrat(&[b'd', 1, 0]));
    assert!(!is_binary_lrat(b"4 1 -2 0 1 2 0\n"));
    assert!(!is_binary_lrat(b""));
}

#[test]
fn test_parse_binary_addition() {
    // Binary LRAT encodes IDs and hints as 2*value (same encoding as literals).
    // id=3 -> encoded as 6 (2*3), hint=1 -> 2 (2*1), hint=2 -> 4 (2*2)
    // lit=+1 -> encoded as 2 (2*1+0)
    let data = vec![b'a', 6, 2, 0, 2, 4, 0];
    let steps = parse_binary_lrat(&data).unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 3,
            clause: vec![lit(1)],
            hints: vec![1, 2],
        }
    );
}

#[test]
fn test_parse_binary_deletion() {
    // Deletion IDs are also doubled: id=1 -> 2 (2*1), id=2 -> 4 (2*2)
    let data = vec![b'd', 2, 4, 0];
    let steps = parse_binary_lrat(&data).unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0], LratStep::Delete { ids: vec![1, 2] });
}

#[test]
fn test_decode_binary_lit() {
    // positive var 1 -> encoded as 2 (2*1)
    assert_eq!(decode_binary_lit(2).unwrap(), lit(1));
    // negative var 1 -> encoded as 3 (2*1 + 1)
    assert_eq!(decode_binary_lit(3).unwrap(), lit(-1));
    // positive var 5 -> encoded as 10 (2*5)
    assert_eq!(decode_binary_lit(10).unwrap(), lit(5));
    // negative var 5 -> encoded as 11 (2*5 + 1)
    assert_eq!(decode_binary_lit(11).unwrap(), lit(-5));
}

#[test]
fn test_parse_binary_negative_lit() {
    // id=3 -> encoded 6, lit=-1 -> encoded 3 (2*1+1), hint=1 -> encoded 2 (2*1)
    let data = vec![b'a', 6, 3, 0, 2, 0];
    let steps = parse_binary_lrat(&data).unwrap();
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 3,
            clause: vec![lit(-1)],
            hints: vec![1],
        }
    );
}

#[test]
fn test_leb128_roundtrip() {
    // Test LEB128 decoding of multi-byte values
    // 300 = 0b100101100 -> LEB128: [0xAC, 0x02]
    let data = vec![0xAC, 0x02];
    let (val, consumed) = read_leb128(&data, 0).unwrap();
    assert_eq!(val, 300);
    assert_eq!(consumed, 2);
}

#[test]
fn test_parse_text_with_comments() {
    let input = "\
c This is a comment
4 1 0 1 2 0
c Another comment
";
    let steps = parse_text_lrat(input).unwrap();
    assert_eq!(steps.len(), 1);
}

// ─── Error path tests ───────────────────────────────────────────

#[test]
fn test_parse_text_invalid_step_id() {
    let input = "abc 1 0 1 0\n";
    let err = parse_text_lrat(input).unwrap_err();
    assert!(err.to_string().contains("invalid step ID"), "got: {err}");
}

#[test]
fn test_parse_text_rejects_zero_step_id() {
    assert!(parse_text_lrat("0 1 0 1 0\n").is_err());
    assert!(parse_text_lrat("0 d 1 0\n").is_err());
}

#[test]
fn test_parse_text_rejects_non_monotonic_step_ids() {
    assert!(parse_text_lrat("4 1 0 1 0\n3 2 0 2 0\n").is_err());
    // A second *addition* reusing the previous ID is still non-monotonic.
    assert!(parse_text_lrat("4 1 0 1 0\n4 2 0 2 0\n").is_err());
}

#[test]
fn test_parse_text_invalid_literal() {
    let input = "4 xyz 0 1 0\n";
    let err = parse_text_lrat(input).unwrap_err();
    assert!(err.to_string().contains("invalid literal"), "got: {err}");
}

#[test]
fn test_parse_text_invalid_hint_id() {
    let input = "4 1 0 abc 0\n";
    let err = parse_text_lrat(input).unwrap_err();
    assert!(err.to_string().contains("invalid hint ID"), "got: {err}");
}

#[test]
fn test_parse_text_invalid_deletion_id() {
    let input = "5 d xyz 0\n";
    let err = parse_text_lrat(input).unwrap_err();
    assert!(
        err.to_string().contains("invalid deletion ID"),
        "got: {err}"
    );
}

#[test]
fn test_parse_text_requires_both_addition_terminators() {
    assert!(parse_text_lrat("4 1 1 2 0\n").is_err());
    assert!(parse_text_lrat("4 1 0 1 2\n").is_err());
}

#[test]
fn test_parse_text_requires_deletion_terminator() {
    assert!(parse_text_lrat("5 d 1 2\n").is_err());
}

#[test]
fn test_parse_text_rejects_tokens_after_terminator() {
    assert!(parse_text_lrat("4 1 0 1 0 extra\n").is_err());
    assert!(parse_text_lrat("5 d 1 0 extra\n").is_err());
}

#[test]
fn test_binary_lrat_invalid_marker() {
    let data = vec![b'x', 6, 0, 2, 0];
    let err = parse_binary_lrat(&data).unwrap_err();
    assert!(
        err.to_string().contains("invalid binary LRAT marker byte"),
        "got: {err}"
    );
}

#[test]
fn test_binary_lrat_rejects_zero_or_signed_record_ids() {
    assert!(parse_binary_lrat(&[b'a', 0, 0, 0]).is_err());
    assert!(parse_binary_lrat(&[b'a', 3, 0, 0]).is_err());
    assert!(parse_binary_lrat(&[b'd', 1, 0]).is_err());
}

#[test]
fn test_binary_lrat_rejects_non_monotonic_addition_ids() {
    // Addition IDs 3 then 2, with empty clauses and hint lists.
    assert!(parse_binary_lrat(&[b'a', 6, 0, 0, b'a', 4, 0, 0]).is_err());
}

#[test]
fn test_binary_lrat_rejects_negative_zero_hint() {
    assert!(parse_binary_lrat(&[b'a', 4, 2, 0, 1, 0]).is_err());
}

#[test]
fn test_binary_lrat_truncated_leb128() {
    // 'a' marker then EOF — truncated LEB128 for the id
    let data = vec![b'a'];
    let err = parse_binary_lrat(&data).unwrap_err();
    assert!(err.to_string().contains("unexpected end"), "got: {err}");
}

#[test]
fn test_binary_lrat_leb128_overflow() {
    // 10 continuation bytes (each with high bit set) causes shift >= 64
    let mut data = vec![b'a'];
    data.extend(std::iter::repeat_n(0x80u8, 10));
    data.push(0x01); // final byte
    let err = parse_binary_lrat(&data).unwrap_err();
    assert!(err.to_string().contains("LEB128"), "got: {err}");
}

#[test]
fn test_is_binary_lrat_whitespace_prefix() {
    // Binary data with leading whitespace should still be detected
    assert!(is_binary_lrat(b"  \t\na\x06\x00\x02\x00"));
    // Text data with whitespace
    assert!(!is_binary_lrat(b"  4 1 0 1 0\n"));
}

#[test]
fn test_parse_binary_lrat_whitespace_prefix() {
    let steps = parse_binary_lrat(b"  \t\na\x06\x02\x00\x02\x00").unwrap();
    assert_eq!(
        steps,
        vec![LratStep::Add {
            id: 3,
            clause: vec![lit(1)],
            hints: vec![1],
        }]
    );
}

#[test]
fn test_decode_binary_id_coverage() {
    // decode_binary_id is simple (encoded >> 1) — verify directly
    assert_eq!(decode_binary_id(0), 0);
    assert_eq!(decode_binary_id(2), 1);
    assert_eq!(decode_binary_id(6), 3);
    assert_eq!(decode_binary_id(200), 100);
}

/// Text LRAT parser rejects literals exceeding i32 range.
/// Previously `lit as Lit` silently truncated i64 to i32; now the
/// MAX_LRAT_VAR cap fires first with an allocation-refusal message.
#[test]
fn test_text_lrat_rejects_large_literal() {
    let input = "4 3000000000 0 1 0\n";
    let err = parse_text_lrat(input).unwrap_err();
    assert!(
        err.to_string().contains("supported maximum variable index"),
        "got: {err}"
    );
}

/// Binary LRAT decode_binary_lit rejects encoded literals exceeding i32 range.
/// Previously `(encoded >> 1) as i32` silently truncated u64 to i32; now the
/// MAX_LRAT_VAR cap fires first with an allocation-refusal message.
#[test]
fn test_binary_lrat_rejects_large_encoded_lit() {
    let encoded: u64 = 6_000_000_000;
    let result = decode_binary_lit(encoded);
    assert!(result.is_err(), "var 3 billion should be rejected");
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("supported maximum variable index"));
}

/// A ~20-byte malicious text proof referencing a huge variable must be
/// refused at parse time instead of driving the checker into a ~100GB
/// dense-array allocation (regression for the giant-variable DoS).
#[test]
fn test_text_lrat_rejects_giant_variable_one_liner() {
    let input = "2 2147483646 0 0\n";
    let err = parse_text_lrat(input).unwrap_err();
    assert!(
        err.to_string().contains("supported maximum variable index"),
        "got: {err}"
    );
}

/// Boundary: the dense-checker cap itself is accepted and one above is
/// rejected. Parsing this step alone does not allocate checker watch tables.
#[test]
fn test_lrat_var_cap_boundary() {
    let at_cap = MAX_LRAT_VAR as i64;
    let steps = parse_text_lrat(&format!("2 {at_cap} 0 0\n")).unwrap();
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 2,
            clause: vec![lit(i32::try_from(at_cap).unwrap())],
            hints: vec![],
        }
    );
    assert!(parse_text_lrat(&format!("2 {} 0 0\n", at_cap + 1)).is_err());
    assert!(parse_text_lrat(&format!("2 -{} 0 0\n", at_cap + 1)).is_err());

    // Binary side: encoded = 2*var (+1 for negative).
    let at_cap_u64 = MAX_LRAT_VAR;
    assert!(decode_binary_lit(at_cap_u64 * 2).is_ok());
    assert!(decode_binary_lit((at_cap_u64 + 1) * 2).is_err());
    assert!(decode_binary_lit((at_cap_u64 + 1) * 2 + 1).is_err());
}

/// decode_binary_lit rejects encoded value 1 (maps to variable 0, invalid DIMACS).
/// Binary encoding: encoded=1 → var = 1>>1 = 0 → DIMACS variable 0.
/// `Literal::try_from_dimacs(0)` returns a typed error, and
/// `decode_binary_lit` must reject the invalid binary value with context.
#[test]
fn test_decode_binary_lit_rejects_var_zero() {
    let result = decode_binary_lit(1);
    assert!(result.is_err(), "encoded=1 maps to var=0, must be rejected");
    assert!(
        result.unwrap_err().to_string().contains("variable 0"),
        "error must mention variable 0"
    );
}

// ─── RAT hint parsing tests (#5243) ─────────────────────────────

/// Text LRAT parser accepts negative hint IDs for RAT witnesses.
#[test]
fn test_parse_text_negative_hints() {
    let input = "5 1 0 -2 1 -4 3 0\n";
    let steps = parse_text_lrat(input).unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 5,
            clause: vec![lit(1)],
            hints: vec![-2, 1, -4, 3],
        }
    );
}

/// Text LRAT parser: mixed positive and negative hints.
#[test]
fn test_parse_text_mixed_hints() {
    // RUP hints first (positive), then RAT witnesses (negative + positive).
    let input = "10 1 2 0 3 4 -5 6 7 0\n";
    let steps = parse_text_lrat(input).unwrap();
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 10,
            clause: vec![lit(1), lit(2)],
            hints: vec![3, 4, -5, 6, 7],
        }
    );
}

/// decode_binary_hint: positive and negative hint IDs.
#[test]
fn test_decode_binary_hint() {
    // Positive: encoded = 2*value, sign_bit=0
    assert_eq!(decode_binary_hint(2), 1); // 2*1
    assert_eq!(decode_binary_hint(6), 3); // 2*3
    assert_eq!(decode_binary_hint(200), 100); // 2*100
                                              // Negative: encoded = 2*value + 1, sign_bit=1
    assert_eq!(decode_binary_hint(3), -1); // 2*1 + 1
    assert_eq!(decode_binary_hint(7), -3); // 2*3 + 1
    assert_eq!(decode_binary_hint(201), -100); // 2*100 + 1
}

/// Binary LRAT parser handles negative hint IDs for RAT.
#[test]
fn test_parse_binary_negative_hints() {
    // id=5 -> encoded 10 (2*5)
    // clause: lit(1) -> encoded 2 (2*1+0)
    // hints: -2 -> encoded 5 (2*2+1), 1 -> encoded 2 (2*1+0),
    //        -4 -> encoded 9 (2*4+1), 3 -> encoded 6 (2*3+0)
    let data = vec![b'a', 10, 2, 0, 5, 2, 9, 6, 0];
    let steps = parse_binary_lrat(&data).unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(
        steps[0],
        LratStep::Add {
            id: 5,
            clause: vec![lit(1)],
            hints: vec![-2, 1, -4, 3],
        }
    );
}
