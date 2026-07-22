// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_text_addition() {
    let data = b"1 -2 3 0\n";
    let steps = parse_text_drat(data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Add(lits) => {
            assert_eq!(lits.len(), 3);
            assert_eq!(lits[0].to_dimacs(), 1);
            assert_eq!(lits[1].to_dimacs(), -2);
            assert_eq!(lits[2].to_dimacs(), 3);
        }
        _ => panic!("expected Add"),
    }
}

#[test]
fn test_parse_text_deletion() {
    let data = b"d 1 -2 0\n";
    let steps = parse_text_drat(data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Delete(lits) => {
            assert_eq!(lits.len(), 2);
            assert_eq!(lits[0].to_dimacs(), 1);
            assert_eq!(lits[1].to_dimacs(), -2);
        }
        _ => panic!("expected Delete"),
    }
}

#[test]
fn test_binary_detection() {
    assert!(is_binary_drat(&[0x61, 0x04, 0x00])); // 'a' + lit + 0
    assert!(!is_binary_drat(b"1 -2 0\n")); // text
    assert!(!is_binary_drat(b"d 1 0\n")); // text deletion (d + space)
                                          // Binary proof starting with 'd' (deletion) — byte after 'd' is
                                          // LEB128 data (0x03), not a space, so detected as binary.
    assert!(is_binary_drat(&[0x64, 0x03, 0x00])); // binary 'd' + LEB128 + 0
                                                  // Empty data is not binary.
    assert!(!is_binary_drat(&[]));
}

#[test]
fn test_parse_binary_single_add() {
    // Binary DRAT encoding: positive DIMACS var 1 -> 2*(0+1) = 2
    // 'a' (0x61), LEB128(2) = 0x02, terminator 0x00
    let data = [0x61, 0x02, 0x00];
    let steps = parse_binary_drat(&data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Add(lits) => {
            assert_eq!(lits.len(), 1);
            assert_eq!(lits[0].to_dimacs(), 1);
        }
        _ => panic!("expected Add"),
    }
}

#[test]
fn test_parse_binary_deletion() {
    // Binary DRAT encoding: negative DIMACS var 1 -> 2*(1+1)+1 = 3
    // 'd' (0x64), LEB128(3) = 0x03, terminator 0x00
    let data = [0x64, 0x03, 0x00];
    let steps = parse_binary_drat(&data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Delete(lits) => {
            assert_eq!(lits.len(), 1);
            assert_eq!(lits[0].to_dimacs(), -1);
        }
        _ => panic!("expected Delete"),
    }
}

#[test]
fn test_leb128_roundtrip() {
    // Encode 300 in LEB128: 300 = 0b100101100
    // byte 1: 0b0101100 | 0x80 = 0xAC
    // byte 2: 0b0000010 = 0x02
    let data = [0xAC, 0x02];
    let (val, pos) = read_leb128(&data, 0).unwrap();
    assert_eq!(val, 300);
    assert_eq!(pos, 2);
}

#[test]
fn test_empty_clause_add() {
    let data = b"0\n";
    let steps = parse_text_drat(data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Add(lits) => assert!(lits.is_empty()),
        _ => panic!("expected Add"),
    }
}

// ─── Error path tests ───────────────────────────────────────────

#[test]
fn test_parse_text_comment_lines_skipped() {
    let data = b"c this is a comment\n1 -2 0\nc another comment\n";
    let steps = parse_text_drat(data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Add(lits) => {
            assert_eq!(lits.len(), 2);
            assert_eq!(lits[0].to_dimacs(), 1);
            assert_eq!(lits[1].to_dimacs(), -2);
        }
        _ => panic!("expected Add, got Delete"),
    }
}

#[test]
fn test_parse_text_bad_literal() {
    let data = b"1 xyz 0\n";
    let err = parse_text_drat(data).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("bad literal"), "got: {msg}");
}

#[test]
fn test_parse_text_requires_clause_terminator() {
    assert!(parse_text_drat(b"1 -2\n").is_err());
    assert!(parse_text_drat(b"d 1 -2\n").is_err());
}

#[test]
fn test_parse_text_rejects_tokens_after_terminator() {
    assert!(parse_text_drat(b"1 -2 0 extra\n").is_err());
    assert!(parse_text_drat(b"d 1 -2 0 extra\n").is_err());
}

#[test]
fn test_binary_unexpected_marker() {
    let data = [0x42, 0x02, 0x00]; // 'B' is invalid marker
    let err = parse_binary_drat(&data).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("unexpected marker byte"), "got: {msg}");
}

#[test]
fn test_binary_truncated_leb128() {
    // 'a' marker then EOF — truncated LEB128
    let data = [0x61];
    let err = parse_binary_drat(&data).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("unexpected end"), "got: {msg}");
}

#[test]
fn test_binary_leb128_overflow() {
    // 5+ continuation bytes cause shift >= 32 for u32 LEB128
    let mut data = vec![0x61]; // 'a' marker
    data.extend(std::iter::repeat_n(0x80, 5)); // continuation bytes
    data.push(0x01); // final byte
    let err = parse_binary_drat(&data).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("LEB128 value too large"), "got: {msg}");
}

#[test]
fn test_binary_invalid_literal_encoding() {
    // val=1: var_plus_one = 1>>1 = 0, which triggers "invalid literal encoding"
    let data = [0x61, 0x01, 0x00]; // 'a', LEB128(1), terminator
    let err = parse_binary_drat(&data).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("invalid literal encoding"), "got: {msg}");
}

#[test]
fn test_binary_multi_literal_clause() {
    // Binary DRAT: add clause with 3 literals: +1, -2, +3
    // +1 = 2*(0+1) = 2, -2 = 2*(1+1)+1 = 5, +3 = 2*(2+1) = 6
    let data = [0x61, 0x02, 0x05, 0x06, 0x00];
    let steps = parse_binary_drat(&data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Add(lits) => {
            assert_eq!(lits.len(), 3);
            assert_eq!(lits[0].to_dimacs(), 1);
            assert_eq!(lits[1].to_dimacs(), -2);
            assert_eq!(lits[2].to_dimacs(), 3);
        }
        _ => panic!("expected Add"),
    }
}

/// Binary DRAT: the max u32 LEB128 value maps to var_idx 2147483646, which
/// exceeds MAX_DRAT_VAR — it must be rejected cleanly at parse time instead
/// of driving `DratChecker::ensure_capacity` into a ~100GB watch-array
/// allocation (regression for the giant-variable DoS).
#[test]
fn test_binary_drat_rejects_giant_variable() {
    let data = [0x61, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00]; // LEB128(u32::MAX)
    let err = parse_binary_drat(&data).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("supported maximum variable index"),
        "got: {msg}"
    );
}

/// A one-line malicious text proof referencing a huge variable must be
/// refused at parse time instead of aborting on allocation later.
#[test]
fn test_text_drat_rejects_giant_variable_one_liner() {
    let data = b"2147483647 0\n";
    let err = parse_text_drat(data).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("supported maximum variable index"),
        "got: {msg}"
    );
}

/// Boundary: the dense-checker cap itself is accepted and one above is
/// rejected, in both text and binary formats. Parsing the boundary does not
/// instantiate the checker or allocate its dense watch tables.
#[test]
fn test_drat_var_cap_boundary() {
    // Binary DRAT encodes DIMACS var v as 2*v (+1 for negative), LEB128.
    fn leb128(mut v: u32) -> Vec<u8> {
        let mut out = Vec::new();
        loop {
            let byte = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                out.push(byte);
                return out;
            }
            out.push(byte | 0x80);
        }
    }

    let at_cap = MAX_DRAT_VAR;
    let steps = parse_text_drat(format!("{at_cap} 0\n").as_bytes()).unwrap();
    match &steps[0] {
        ProofStep::Add(lits) => {
            assert_eq!(lits[0].to_dimacs(), i32::try_from(at_cap).unwrap());
        }
        _ => panic!("expected Add"),
    }
    assert!(parse_text_drat(format!("{} 0\n", at_cap + 1).as_bytes()).is_err());
    assert!(parse_text_drat(format!("-{} 0\n", at_cap + 1).as_bytes()).is_err());

    // Binary side: encode 2*(at_cap) and 2*(at_cap + 1) as LEB128.
    let mut ok = vec![0x61];
    ok.extend(leb128(at_cap * 2));
    ok.push(0x00);
    assert!(parse_binary_drat(&ok).is_ok());

    let mut over = vec![0x61];
    over.extend(leb128((at_cap + 1) * 2));
    over.push(0x00);
    assert!(parse_binary_drat(&over).is_err());
}

#[test]
fn test_parse_drat_auto_detect_text() {
    let data = b"1 -2 0\n";
    let steps = parse_drat(data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Add(lits) => {
            assert_eq!(lits.len(), 2);
            assert_eq!(lits[0].to_dimacs(), 1);
            assert_eq!(lits[1].to_dimacs(), -2);
        }
        _ => panic!("expected Add"),
    }
}

#[test]
fn test_parse_drat_auto_detect_binary() {
    let data = [0x61, 0x02, 0x00]; // binary add: var 1 positive
    let steps = parse_drat(&data).unwrap();
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ProofStep::Add(lits) => {
            assert_eq!(lits.len(), 1);
            assert_eq!(lits[0].to_dimacs(), 1);
        }
        _ => panic!("expected Add"),
    }
}

#[test]
fn test_parse_binary_drat_whitespace_prefix() {
    let steps = parse_drat(b" \t\na\x02\x00").unwrap();
    assert!(matches!(&steps[..], [ProofStep::Add(lits)] if lits == &[Literal::from_dimacs(1)]));
}

#[test]
fn test_parse_drat_text_deletion_with_tab_separator() {
    let steps = parse_drat(b"d\t1 0\n").unwrap();
    assert!(matches!(&steps[..], [ProofStep::Delete(lits)] if lits == &[Literal::from_dimacs(1)]));
}

#[test]
fn test_parse_drat_ambiguous_binary_deletion_byte() {
    // LEB128 byte 0x20 is both ASCII space and encoded literal +16.
    let steps = parse_drat(&[b'd', b' ', 0]).unwrap();
    assert!(matches!(&steps[..], [ProofStep::Delete(lits)] if lits == &[Literal::from_dimacs(16)]));
}
