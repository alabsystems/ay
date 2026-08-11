// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_basic_tokens() {
    let input = "(check-sat)";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::LParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("check-sat"))));
    assert_eq!(lexer.next(), Some(Ok(Token::RParen)));
    assert_eq!(lexer.next(), None);
}

#[test]
fn test_numerals() {
    let input = "42 0 12345";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::Numeral("42"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Numeral("0"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Numeral("12345"))));
}

#[test]
fn test_leading_zero_runs_are_one_invalid_token() {
    for source in ["00", "0123", "00.1", "01.25"] {
        let mut lexer = Token::lexer(source);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token::InvalidLeadingZeroNumeral)),
            "{source} must not split into legal adjacent numerals"
        );
        assert_eq!(lexer.next(), None);
    }

    let mut lexer = Token::lexer("0 12 0.0 12.003");
    assert_eq!(lexer.next(), Some(Ok(Token::Numeral("0"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Numeral("12"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Decimal("0.0"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Decimal("12.003"))));
}

#[test]
fn test_bitvectors() {
    let input = "#xDEADBEEF #b10101010";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::Hexadecimal("#xDEADBEEF"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Binary("#b10101010"))));
}

#[test]
fn test_strings() {
    let input = r#""hello" "world""#;
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::String("\"hello\""))));
    assert_eq!(lexer.next(), Some(Ok(Token::String("\"world\""))));
}

#[test]
fn test_keywords() {
    let input = ":named :status";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::Keyword(":named"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Keyword(":status"))));
}

#[test]
fn test_keyword_cannot_start_with_a_digit() {
    let mut lexer = Token::lexer(":1bad");
    assert_eq!(lexer.next(), Some(Err(())));
}

#[test]
fn test_booleans() {
    let input = "true false";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::True)));
    assert_eq!(lexer.next(), Some(Ok(Token::False)));
}

#[test]
fn test_comments() {
    let input = "(check-sat) ; this is a comment\n(exit)";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::LParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("check-sat"))));
    assert_eq!(lexer.next(), Some(Ok(Token::RParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::LParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("exit"))));
    assert_eq!(lexer.next(), Some(Ok(Token::RParen)));
}

#[test]
fn test_comment_ends_at_carriage_return() {
    let mut lexer = Token::lexer("; comment\r(check-sat)");
    assert_eq!(lexer.next(), Some(Ok(Token::LParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("check-sat"))));
    assert_eq!(lexer.next(), Some(Ok(Token::RParen)));
    assert_eq!(lexer.next(), None);
}

#[test]
fn test_quoted_symbol() {
    let input = "|quoted symbol with spaces|";
    let mut lexer = Token::lexer(input);

    assert_eq!(
        lexer.next(),
        Some(Ok(Token::QuotedSymbol("|quoted symbol with spaces|")))
    );
}

#[test]
fn test_z3_500_escaped_quoted_symbol() {
    let input = r"|\|\||";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::QuotedSymbol(input))));
    assert_eq!(lexer.next(), None);
}

#[test]
fn test_declare_fun() {
    let input = "(declare-fun x () Int)";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::LParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("declare-fun"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("x"))));
    assert_eq!(lexer.next(), Some(Ok(Token::LParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::RParen)));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("Int"))));
    assert_eq!(lexer.next(), Some(Ok(Token::RParen)));
}

#[test]
fn test_bang_annotation_tokens() {
    let input = "(! p :named a1)";
    let mut lexer = Token::lexer(input);

    assert_eq!(lexer.next(), Some(Ok(Token::LParen)));
    // `!` is a valid SMT-LIB symbol character
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("!"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("p"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Keyword(":named"))));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("a1"))));
    assert_eq!(lexer.next(), Some(Ok(Token::RParen)));
}

#[test]
fn test_string_backslash_does_not_escape_terminating_quote() {
    // SMT-LIB 2.6: `""` is the ONLY in-literal escape. A backslash is an
    // ordinary character, so a literal ends at the first unpaired `"` even when
    // a backslash immediately precedes it.
    //
    // The token pattern used to carry a `\\.` alternative, which made the lexer
    // treat `\"` as an escaped quote and scan straight past the literal's real
    // end into the rest of the file — so well-formed input that z3 accepts was
    // rejected with "Invalid token in list". z3 5.0.0 adjudicates:
    // `(str.len "a\")` is 2, and `(str.len "say \")` is 5.
    let mut lexer = Token::lexer(r#""a\" rest"#);
    assert_eq!(lexer.next(), Some(Ok(Token::String(r#""a\""#))));

    // The quote that follows the backslash TERMINATES the literal; what comes
    // after it is separate input, not string content.
    let mut lexer = Token::lexer(r#""say \"hi"#);
    assert_eq!(lexer.next(), Some(Ok(Token::String(r#""say \""#))));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("hi"))));

    // A lone backslash is ordinary content.
    let mut lexer = Token::lexer(r#""\""#);
    assert_eq!(lexer.next(), Some(Ok(Token::String(r#""\""#))));
}

#[test]
fn test_string_doubled_quote_still_escapes() {
    // The one real escape must keep working: `""` denotes a literal quote and
    // does NOT terminate the literal.
    let mut lexer = Token::lexer(r#""say ""hi""" tail"#);
    assert_eq!(lexer.next(), Some(Ok(Token::String(r#""say ""hi""""#))));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("tail"))));

    // Empty string, then a string that is exactly one escaped quote.
    //
    // Note the trailing token: with the literal at bare EOF the final `"` is
    // genuinely ambiguous (close, or open a `""` escape that never completes),
    // and logos resolves that without backtracking. That ambiguity lives in the
    // `""` alternative, which is byte-identical in the old and new patterns, so
    // it is pre-existing and untouched by the backslash fix. Real SMT-LIB always
    // has a following token, which resolves it — verified end-to-end against
    // z3 5.0.0: `(str.len "")` = 0, `(str.len """")` = 1, `(str.len """""")` = 2.
    let mut lexer = Token::lexer(r#""" """" tail"#);
    assert_eq!(lexer.next(), Some(Ok(Token::String(r#""""#))));
    assert_eq!(lexer.next(), Some(Ok(Token::String(r#""""""#))));
    assert_eq!(lexer.next(), Some(Ok(Token::Symbol("tail"))));

    // A backslash adjacent to a doubled quote: the `""` still escapes.
    let mut lexer = Token::lexer(r#""a\""b""#);
    assert_eq!(lexer.next(), Some(Ok(Token::String(r#""a\""b""#))));
}
