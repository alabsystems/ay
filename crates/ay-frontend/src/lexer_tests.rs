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
fn test_quoted_symbol() {
    let input = "|quoted symbol with spaces|";
    let mut lexer = Token::lexer(input);

    assert_eq!(
        lexer.next(),
        Some(Ok(Token::QuotedSymbol("|quoted symbol with spaces|")))
    );
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
