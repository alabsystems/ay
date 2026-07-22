// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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

// ========== Round-trip tests (Part of #1250) ==========

#[test]
fn test_round_trip_quoted_symbol() {
    // Parse a quoted symbol
    let sexp = parse_sexp("|x y|").unwrap();
    // Internal representation has unquoted name
    assert_eq!(sexp, SExpr::Symbol("x y".to_string()));
    // Display re-quotes it
    let output = sexp.to_string();
    assert_eq!(output, "|x y|");
    // Parsing the output gives the same result
    let sexp2 = parse_sexp(&output).unwrap();
    assert_eq!(sexp2, sexp);
}

#[test]
fn test_round_trip_symbol_with_colons() {
    // Rust-style names (common in model-checker-consumer)
    let sexp = parse_sexp("|foo::bar|").unwrap();
    assert_eq!(sexp, SExpr::Symbol("foo::bar".to_string()));
    let output = sexp.to_string();
    assert_eq!(output, "|foo::bar|");
    let sexp2 = parse_sexp(&output).unwrap();
    assert_eq!(sexp2, sexp);
}

#[test]
fn test_round_trip_simple_symbol() {
    // Simple symbols should NOT be quoted
    let sexp = parse_sexp("myVar").unwrap();
    assert_eq!(sexp, SExpr::Symbol("myVar".to_string()));
    let output = sexp.to_string();
    assert_eq!(output, "myVar");
}

#[test]
fn test_round_trip_string() {
    // Parse a string literal
    let sexp = parse_sexp(r#""hello""#).unwrap();
    // Internal representation is contents only
    assert_eq!(sexp, SExpr::String("hello".to_string()));
    // Display re-quotes it
    let output = sexp.to_string();
    assert_eq!(output, r#""hello""#);
    // Parsing the output gives the same result
    let sexp2 = parse_sexp(&output).unwrap();
    assert_eq!(sexp2, sexp);
}

#[test]
fn test_round_trip_string_with_escapes() {
    // SMT-LIB 2.6: a backslash is a LITERAL character (only `\u…` are escapes).
    // Legacy input `\"` is therefore parsed as backslash+quote, NOT as an
    // escaped quote — decoding it away was a wrong-verdict soundness bug on
    // str.len/membership (see ay-core::unescape_string_contents, commit
    // 204a245f which updated the parallel smtlib_tests assertions).
    let sexp = parse_sexp(r#""say \"hi\"""#).unwrap();
    // Internal representation keeps the backslashes literal.
    assert_eq!(sexp, SExpr::String(r#"say \"hi\""#.to_string()));

    // The canonical SMT-LIB 2.6 way to embed a quote is `""`. A string that
    // mixes a literal backslash (not adjacent to a quote) with an embedded quote
    // round-trips: the printer emits the backslash as-is and doubles the quote,
    // and re-parsing recovers the same value.
    let mixed = SExpr::String(r#"a\b"c"#.to_string());
    let output = mixed.to_string();
    assert_eq!(output, r#""a\b""c""#);
    let reparsed = parse_sexp(&output).unwrap();
    assert_eq!(reparsed, mixed);
}

#[test]
fn test_round_trip_string_with_smtlib_escapes() {
    // SMT-LIB 2.6 standard: "" for literal quote
    let sexp = parse_sexp(r#""say ""hi""""#).unwrap();
    assert_eq!(sexp, SExpr::String(r#"say "hi""#.to_string()));
    let output = sexp.to_string();
    assert_eq!(output, r#""say ""hi""""#);
    let sexp2 = parse_sexp(&output).unwrap();
    assert_eq!(sexp2, sexp);
}

#[test]
fn test_round_trip_string_with_backslash() {
    // SMT-LIB 2.6: a backslash is a LITERAL character (no C-style escapes), so
    // `\\` is TWO backslashes — matching z3. Decoding `\\` to a single `\` was a
    // wrong-verdict soundness bug on str.len/membership (see ay-core, commit
    // 204a245f which updated the parallel smtlib_tests assertions).
    let sexp = parse_sexp(r#""path\\to\\file""#).unwrap();
    // Internal representation keeps both backslashes of each `\\`.
    assert_eq!(sexp, SExpr::String(r"path\\to\\file".to_string()));
    // Display: backslashes are literal in SMT-LIB 2.6 (printed as-is).
    let output = sexp.to_string();
    assert_eq!(output, r#""path\\to\\file""#);
    // Parsing the output gives the same result.
    let sexp2 = parse_sexp(&output).unwrap();
    assert_eq!(sexp2, sexp);
}

#[test]
fn test_round_trip_reserved_symbol() {
    // Reserved words must be quoted
    // Note: parse_sexp("true") returns SExpr::True, not a symbol
    // So we test via Display on a symbol named "true"
    let sexp = SExpr::Symbol("true".to_string());
    let output = sexp.to_string();
    assert_eq!(output, "|true|");
    let sexp2 = parse_sexp(&output).unwrap();
    assert_eq!(sexp2, sexp);
}

/// Verify sanitized symbols from quote_symbol can be parsed (#1841)
#[test]
fn test_sanitized_symbol_parseable() {
    use ay_core::quote_symbol;

    // quote_symbol sanitizes | and \ to _ before quoting
    let quoted = quote_symbol("a|b");
    assert_eq!(quoted, "|a_b|");

    // Parser should accept the sanitized output
    let sexp = parse_sexp(&quoted).unwrap();
    assert_eq!(sexp, SExpr::Symbol("a_b".to_string()));

    // The symbol name changed from "a|b" to "a_b" - this is expected
    // (sanitization is a lossy one-way operation per #1841)

    // Test backslash sanitization
    let quoted2 = quote_symbol(r"x\y");
    assert_eq!(quoted2, "|x_y|");
    let sexp2 = parse_sexp(&quoted2).unwrap();
    assert_eq!(sexp2, SExpr::Symbol("x_y".to_string()));

    // Multiple invalid chars
    let quoted3 = quote_symbol(r"a|b\c|d");
    assert_eq!(quoted3, "|a_b_c_d|");
    let sexp3 = parse_sexp(&quoted3).unwrap();
    assert_eq!(sexp3, SExpr::Symbol("a_b_c_d".to_string()));
}

#[test]
fn test_parse_annotation_sexp() {
    // SMT-LIB term annotation: (! term :keyword value)
    let sexp = parse_sexp("(! p :named a1)").unwrap();
    assert_eq!(
        sexp,
        SExpr::List(vec![
            SExpr::Symbol("!".to_string()),
            SExpr::Symbol("p".to_string()),
            SExpr::Keyword(":named".to_string()),
            SExpr::Symbol("a1".to_string()),
        ])
    );
}
