// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn leading_zero_numerals_and_decimals_are_rejected() {
    for source in ["00", "0123", "00.1", "01.25"] {
        let error = parse_sexp(source).expect_err("leading zero must be rejected");
        assert!(
            error.message.contains("leading zeros"),
            "unexpected error for {source:?}: {error}"
        );
    }
}

#[test]
fn quoted_symbols_decode_z3_500_escapes_and_reject_control_characters() {
    let source = "|a\u{000b}b|";
    let error = parse_sexp(source).expect_err("forbidden quoted-symbol character");
    assert!(
        error
            .message
            .contains("quoted symbol contains forbidden character"),
        "unexpected error for {source:?}: {error}"
    );
    assert_eq!(
        parse_sexp(r"|a\|b|").expect("escaped pipe"),
        SExpr::Symbol("a|b".to_string())
    );
    assert_eq!(
        parse_sexp(r"|a\\b|").expect("escaped backslash"),
        SExpr::Symbol(r"a\b".to_string())
    );
    assert_eq!(
        parse_sexp(r"|a\b|").expect("backslash before ordinary character"),
        SExpr::Symbol(r"a\b".to_string())
    );
    for symbol in ["||", "a|b", r"a\b"] {
        let expression = SExpr::Symbol(symbol.to_string());
        let printed = expression.to_string();
        assert_eq!(
            parse_sexp(&printed).expect("escaped symbol must round-trip"),
            expression
        );
    }
    assert_eq!(
        parse_sexp("|line one\nline two é|").expect("legal quoted symbol"),
        SExpr::Symbol("line one\nline two é".to_string())
    );
}

#[test]
fn strings_reject_non_whitespace_control_characters() {
    let error = parse_sexp("\"a\u{000b}b\"").expect_err("vertical tab is not legal");
    assert!(error
        .message
        .contains("string literal contains forbidden character"));
    assert_eq!(
        parse_sexp("\"line one\nline two é\"").expect("legal string"),
        SExpr::String("line one\nline two é".to_string())
    );
}

#[test]
fn test_parse_symbol() {
    let sexp = parse_sexp("foo").unwrap();
    assert_eq!(sexp, SExpr::Symbol("foo".to_string()));
}

#[test]
fn test_parse_numeral() {
    let sexp = parse_sexp("42").unwrap();
    assert_eq!(sexp, SExpr::Numeral("42".to_string()));
}

#[test]
fn test_parse_empty_list() {
    let sexp = parse_sexp("()").unwrap();
    assert_eq!(sexp, SExpr::List(vec![]));
}

#[test]
fn test_parse_simple_list() {
    let sexp = parse_sexp("(a b c)").unwrap();
    assert_eq!(
        sexp,
        SExpr::List(vec![
            SExpr::Symbol("a".to_string()),
            SExpr::Symbol("b".to_string()),
            SExpr::Symbol("c".to_string()),
        ])
    );
}

#[test]
fn test_parse_nested_list() {
    let sexp = parse_sexp("(a (b c) d)").unwrap();
    assert_eq!(
        sexp,
        SExpr::List(vec![
            SExpr::Symbol("a".to_string()),
            SExpr::List(vec![
                SExpr::Symbol("b".to_string()),
                SExpr::Symbol("c".to_string()),
            ]),
            SExpr::Symbol("d".to_string()),
        ])
    );
}

#[test]
fn test_parse_check_sat() {
    let sexp = parse_sexp("(check-sat)").unwrap();
    assert_eq!(
        sexp,
        SExpr::List(vec![SExpr::Symbol("check-sat".to_string())])
    );
}

#[test]
fn test_parse_declare_fun() {
    let sexp = parse_sexp("(declare-fun x () Int)").unwrap();
    assert_eq!(
        sexp,
        SExpr::List(vec![
            SExpr::Symbol("declare-fun".to_string()),
            SExpr::Symbol("x".to_string()),
            SExpr::List(vec![]),
            SExpr::Symbol("Int".to_string()),
        ])
    );
}

#[test]
fn test_parse_assert() {
    let sexp = parse_sexp("(assert (> x 0))").unwrap();
    assert_eq!(
        sexp,
        SExpr::List(vec![
            SExpr::Symbol("assert".to_string()),
            SExpr::List(vec![
                SExpr::Symbol(">".to_string()),
                SExpr::Symbol("x".to_string()),
                SExpr::Numeral("0".to_string()),
            ]),
        ])
    );
}

#[test]
fn test_parse_bitvector() {
    let sexp = parse_sexp("#xDEAD").unwrap();
    assert_eq!(sexp, SExpr::Hexadecimal("#xDEAD".to_string()));

    let sexp = parse_sexp("#b1010").unwrap();
    assert_eq!(sexp, SExpr::Binary("#b1010".to_string()));
}

#[test]
fn test_parse_keyword() {
    let sexp = parse_sexp(":named").unwrap();
    assert_eq!(sexp, SExpr::Keyword(":named".to_string()));
}

#[test]
fn test_parse_multiple() {
    let sexps = parse_sexps("(set-logic QF_LIA) (check-sat)").unwrap();
    assert_eq!(sexps.len(), 2);
    assert_eq!(
        sexps[0],
        SExpr::List(vec![
            SExpr::Symbol("set-logic".to_string()),
            SExpr::Symbol("QF_LIA".to_string()),
        ])
    );
    assert_eq!(
        sexps[1],
        SExpr::List(vec![SExpr::Symbol("check-sat".to_string())])
    );
}

#[test]
fn test_parse_booleans() {
    let sexp = parse_sexp("(and true false)").unwrap();
    assert_eq!(
        sexp,
        SExpr::List(vec![
            SExpr::Symbol("and".to_string()),
            SExpr::True,
            SExpr::False,
        ])
    );
}

#[test]
fn test_parse_quoted_symbol() {
    let sexp = parse_sexp("|quoted symbol|").unwrap();
    assert_eq!(sexp, SExpr::Symbol("quoted symbol".to_string()));
}

#[test]
fn test_error_unmatched_paren() {
    let result = parse_sexp("(a b");
    assert!(result.is_err());
}

#[test]
fn test_error_unexpected_rparen() {
    let result = parse_sexp(")");
    assert!(result.is_err());
}

// ========== Line number tracking tests ==========

#[test]
fn test_error_includes_line_number_single_line() {
    let result = parse_sexp(")");
    let err = result.unwrap_err();
    assert_eq!(err.line, Some(1));
    assert!(
        err.to_string().starts_with("line 1:"),
        "Expected 'line 1:' prefix, got: {err}"
    );
}

#[test]
fn test_error_includes_line_number_multiline() {
    // Error is on line 3 (unclosed list started on line 3)
    let input = "(a b)\n(c d)\n(e f";
    let result = parse_sexps(input);
    let err = result.unwrap_err();
    assert_eq!(err.line, Some(3), "Error should be on line 3, got: {err}");
    assert!(
        err.to_string().starts_with("line 3:"),
        "Expected 'line 3:' prefix, got: {err}"
    );
}

#[test]
fn test_error_line_number_unexpected_rparen_line_2() {
    let input = "(set-logic QF_LIA)\n)";
    let result = parse_sexps(input);
    let err = result.unwrap_err();
    assert_eq!(
        err.line,
        Some(2),
        "')' on line 2 should report line 2, got: {err}"
    );
}

#[test]
fn test_error_line_number_in_display_format() {
    let err = ParseError::with_line("bad token", 42, 5);
    assert_eq!(err.to_string(), "line 5: Parse error: bad token");
}

#[test]
fn test_error_without_line_preserves_position_format() {
    let err = ParseError::with_position("bad token", 42);
    assert_eq!(err.to_string(), "Parse error at position 42: bad token");
}

#[test]
fn test_error_without_position_preserves_bare_format() {
    let err = ParseError::new("bad token");
    assert_eq!(err.to_string(), "Parse error: bad token");
}

// ========== Trailing input rejection tests (Part of #2705) ==========

#[test]
fn test_parse_single_rejects_trailing_expression() {
    let result = parse_sexp("(a) (b)");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.message.contains("trailing input"),
        "Expected trailing-input error, got: {err}"
    );
}

#[test]
fn test_parse_single_rejects_trailing_invalid_token() {
    let result = parse_sexp("foo '");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.message.contains("trailing input"),
        "Expected trailing-input error, got: {err}"
    );
    assert_eq!(err.position, Some(4));
}

// ========== Depth limit tests (Part of #2689, #4602, #6888) ==========

#[test]
fn test_depth_limit_exceeded() {
    // MAX_PARSE_DEPTH + 1 nested open parens exceeds the limit
    let deep_input = "(".repeat(MAX_PARSE_DEPTH + 1);
    let result = parse_sexp(&deep_input);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.message.contains("Maximum nesting depth"),
        "Expected depth error, got: {err}"
    );
}

#[test]
fn test_deep_nesting_2048_levels() {
    // 2048 levels exceeds the old 1024 limit; must succeed with new limit (#4602).
    // Uses stacker::maybe_grow for stack safety. Iterative Drop prevents
    // stack overflow when the deeply nested SExpr tree is freed.
    let depth = 2048;
    let mut input = String::with_capacity(depth * 2 + 1);
    for _ in 0..depth {
        input.push('(');
    }
    input.push('x');
    for _ in 0..depth {
        input.push(')');
    }
    let result = parse_sexp(&input);
    assert!(
        result.is_ok(),
        "Parsing at depth {depth} should succeed: {result:?}"
    );
}

#[test]
fn test_deep_nesting_10000_levels() {
    // 10,000 levels exercises stacker stack growth at scale.
    // This would have caused stack overflow before the stacker + iterative Drop fix.
    let depth = 10_000;
    let mut input = String::with_capacity(depth * 2 + 1);
    for _ in 0..depth {
        input.push('(');
    }
    input.push('x');
    for _ in 0..depth {
        input.push(')');
    }
    let result = parse_sexp(&input);
    assert!(
        result.is_ok(),
        "Parsing at depth {depth} should succeed: {result:?}"
    );
}

#[test]
fn test_depth_limit_returns_error_not_crash() {
    // Input exceeding MAX_PARSE_DEPTH must return an error, not crash
    let deep_input = "(".repeat(MAX_PARSE_DEPTH + 100);
    let result = parse_sexp(&deep_input);
    let err = result.expect_err("nesting beyond MAX_PARSE_DEPTH must fail");
    assert!(
        err.message.contains("Maximum nesting depth"),
        "Expected depth-limit error, got: {}",
        err.message
    );
}

#[test]
fn test_deep_nesting_1100_succeeds() {
    // 1100 levels of nesting must succeed (previously failed with 1024 limit).
    // This is the depth range seen in QF_BV sage/Sage2 benchmark families.
    let mut input = String::new();
    for _ in 0..1100 {
        input.push('(');
    }
    input.push('x');
    for _ in 0..1100 {
        input.push(')');
    }
    let result = parse_sexp(&input);
    assert!(result.is_ok(), "1100-deep nesting must succeed: {result:?}");
}

#[test]
fn test_deep_nesting_100000_succeeds() {
    // 100,000 levels of nesting must succeed — this is the depth range seen
    // in k=100 BMC benchmarks (kratos pipeline-bug, mem_slave_tlm) that
    // exceeded the old 65536 limit (#6888).
    let depth = 100_000;
    let mut input = String::with_capacity(depth * 2 + 1);
    for _ in 0..depth {
        input.push('(');
    }
    input.push('x');
    for _ in 0..depth {
        input.push(')');
    }
    let result = parse_sexp(&input);
    assert!(
        result.is_ok(),
        "Parsing at depth {depth} should succeed: {result:?}"
    );
}

include!("sexp_tests/round_trip.rs");
