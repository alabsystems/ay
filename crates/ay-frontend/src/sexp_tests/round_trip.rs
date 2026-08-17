// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `sexp::tests` to preserve test FQNs.

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
    // It follows that a literal ENDS at the first unpaired `"` even when a
    // backslash immediately precedes it — `\"` does not escape the quote.
    //
    // This assertion previously expected `"say \"hi\""` to parse as ONE string,
    // which contradicted the very rule stated above. That was only reachable
    // because the LEXER still carried a `\\.` alternative and swallowed the
    // terminating quote; the decoder had already been corrected. z3 5.0.0
    // adjudicates: `(str.len "say \")` is 5, and the longer form errors with
    // "unknown constant hi" — i.e. the literal really does stop at that quote.
    let sexp = parse_sexp(r#""say \""#).unwrap();
    assert_eq!(sexp, SExpr::String(r"say \".to_string()));

    // And the legacy form is now rejected rather than silently re-interpreted,
    // matching z3, which also errors on it.
    assert!(
        parse_sexp(r#""say \"hi\"""#).is_err(),
        "backslash must not escape the terminating quote"
    );

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

/// Verify Z3 5.0.0 quoted-symbol escapes preserve symbol identity.
#[test]
fn test_escaped_symbol_round_trip() {
    use ay_core::quote_symbol;

    for (symbol, quoted) in [
        ("a|b", r"|a\|b|"),
        (r"x\y", r"|x\\y|"),
        (r"a|b\c|d", r"|a\|b\\c\|d|"),
    ] {
        let output = quote_symbol(symbol);
        assert_eq!(output, quoted);
        assert_eq!(
            parse_sexp(&output).unwrap(),
            SExpr::Symbol(symbol.to_string())
        );
    }
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
