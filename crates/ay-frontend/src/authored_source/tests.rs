// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lexer::Token;
use ay_core::original_query::StopReason;
use logos::Logos;
use std::ops::ControlFlow;

fn capture(input: &str) -> AuthoredSource<'_> {
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000_000, &mut checkpoint);
    AuthoredSource::capture(input, &mut work).expect("lexical fixture")
}

fn native_tokens(input: &str) -> Option<Vec<SourceToken<'_>>> {
    Token::lexer(input)
        .spanned()
        .map(|(token, span)| {
            let kind = match token.ok()? {
                Token::LParen => SourceTokenKind::LeftParen,
                Token::RParen => SourceTokenKind::RightParen,
                Token::Keyword(_) => SourceTokenKind::Keyword,
                Token::Numeral(_) => SourceTokenKind::Literal(LiteralKind::Numeral),
                Token::Decimal(_) => SourceTokenKind::Literal(LiteralKind::Decimal),
                Token::Hexadecimal(_) => SourceTokenKind::Literal(LiteralKind::Hexadecimal),
                Token::Binary(_) => SourceTokenKind::Literal(LiteralKind::Binary),
                Token::String(_) => SourceTokenKind::Literal(LiteralKind::String),
                Token::True | Token::False => SourceTokenKind::Literal(LiteralKind::Boolean),
                Token::Symbol(_) => SourceTokenKind::Symbol(SymbolKind::Simple),
                Token::QuotedSymbol(_) => SourceTokenKind::Symbol(SymbolKind::Quoted),
                Token::InvalidLeadingZeroNumeral => return None,
            };
            Some(SourceToken {
                kind,
                raw: &input[span.clone()],
                span,
            })
        })
        .collect()
}

#[test]
fn quoted_reserved_spelling_never_becomes_a_builtin_or_boolean_token() {
    let source = capture("true |true| forall |forall| _ |_| 8 |8|");
    let expected = [
        SourceTokenKind::Literal(LiteralKind::Boolean),
        SourceTokenKind::Symbol(SymbolKind::Quoted),
        SourceTokenKind::Symbol(SymbolKind::Simple),
        SourceTokenKind::Symbol(SymbolKind::Quoted),
        SourceTokenKind::Symbol(SymbolKind::Simple),
        SourceTokenKind::Symbol(SymbolKind::Quoted),
        SourceTokenKind::Literal(LiteralKind::Numeral),
        SourceTokenKind::Symbol(SymbolKind::Quoted),
    ];
    assert_eq!(
        source.tokens().map(|token| token.kind).collect::<Vec<_>>(),
        expected
    );
    assert_eq!(source.tokens().nth(1).expect("quoted token").raw, "|true|");
}

#[test]
fn complete_original_bytes_and_duplicate_assertions_are_preserved() {
    let input = "; header\n(assert false)\r\n; unchanged\n(assert false)\n";
    let source = capture(input);
    assert_eq!(source.original(), input);
    assert_eq!(
        source
            .tokens()
            .filter(|token| token.raw == "assert")
            .count(),
        2
    );
    for token in source.tokens() {
        assert_eq!(&input[token.span.clone()], token.raw);
    }
}

#[test]
fn every_literal_kind_and_index_spelling_agrees_with_native_lexer() {
    let input = "(_ extract 7 0) ((_ pble 0.5 |8| #x0A #b001) true) 12 0.00 false";
    assert_eq!(
        capture(input).tokens().cloned().collect::<Vec<_>>(),
        native_tokens(input).expect("native fixture")
    );
}

#[test]
fn raw_unicode_quoted_symbols_strings_and_escapes_are_not_decoded() {
    let input = r#"(|λ\|x| "a""b\" "🙂" |\\| ||)"#;
    let source = capture(input);
    assert_eq!(
        source.tokens().cloned().collect::<Vec<_>>(),
        native_tokens(input).expect("native quoted fixture")
    );
    assert_eq!(source.tokens().nth(1).expect("quoted token").raw, r"|λ\|x|");
}

#[test]
fn native_lexical_boundary_matrix_retains_exact_kinds_and_spans() {
    let atoms = [
        "true", "false", "x", "|true|", "0", "12", "1.25", "#xF", "#b10", ":k", "\"\"", "|a b|",
        "(", ")",
    ];
    let separators = [" ", "\t", "\r\n", "; comment\n"];
    for left in atoms {
        for right in atoms {
            for separator in separators {
                let input = format!("{left}{separator}{right}");
                assert_eq!(
                    capture(&input).tokens().cloned().collect::<Vec<_>>(),
                    native_tokens(&input).expect("native matrix"),
                    "{input:?}"
                );
            }
        }
    }
}

fn assert_native_parity(input: &str) {
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000_000, &mut checkpoint);
    let captured = AuthoredSource::capture(input, &mut work)
        .ok()
        .map(|source| source.tokens().cloned().collect::<Vec<_>>());
    assert_eq!(captured, native_tokens(input), "{input:?}");
}

#[test]
fn adjacent_token_and_quote_eof_matrix_matches_native_maximal_munch() {
    let atoms = [
        "true", "false", "x", "|true|", "0", "12", "1.25", "#xF", "#b10", ":k", "\"\"", "|a b|",
        "(", ")",
    ];
    for left in atoms {
        for right in atoms {
            assert_native_parity(&format!("{left}{right}"));
        }
    }
    for input in [
        "\"\"",
        "\"\"\"\"",
        "\"\"\"\"\"\"",
        "\"\"true",
        "\"\"\"\"true",
        "\"\"\"\"\"\"true",
        "0.",
        "1.",
        "12.3x",
        "0.1.2",
        "#b012",
        "#xFaG",
        "truefalse",
        "true0",
        "|\\🙂|",
        "|x\0|",
        "|x\\\0|",
    ] {
        assert_native_parity(input);
    }
}

#[test]
fn malformed_lexical_inputs_fail_without_normalizing_them() {
    for input in [
        "00",
        "01.2",
        "#x",
        "#b",
        ":",
        "|unterminated",
        "\"unterminated",
        "λ",
        "|x\\\0|",
    ] {
        let mut checkpoint = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(10_000, &mut checkpoint);
        assert!(
            matches!(
                AuthoredSource::capture(input, &mut work),
                Err(AuthoredSourceError::Lexical { .. })
            ),
            "{input:?}"
        );
        assert!(
            native_tokens(input).is_none(),
            "native lexer must also reject {input:?}"
        );
    }
}

#[test]
fn lexical_capture_alone_does_not_claim_balanced_or_valid_commands() {
    let source = capture("(assert (get-model");
    assert_eq!(source.token_count(), 4);
    assert_eq!(source.original(), "(assert (get-model");
}

fn interrupted_inside(input: &str, reason: StopReason) {
    let mut calls = 0;
    let mut checkpoint = || {
        calls += 1;
        if calls == 2048 {
            ControlFlow::Break(reason)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(1_000_000, &mut checkpoint);
    assert_eq!(
        AuthoredSource::capture(input, &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Interrupted(reason))
    );
    // A later permissive callback cannot reopen the same owner ledger.
    assert_eq!(
        AuthoredSource::capture("true", &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Interrupted(reason))
    );
    assert_eq!(calls, 2048);
}

#[test]
fn cancellation_is_polled_inside_one_long_string() {
    interrupted_inside(
        &format!("\"{}\"", "x".repeat(16_384)),
        StopReason::Cancelled,
    );
}

#[test]
fn deadline_is_polled_inside_one_long_quoted_identifier() {
    interrupted_inside(&format!("|{}|", "x".repeat(16_384)), StopReason::Deadline);
}

#[test]
fn cancellation_is_polled_inside_a_long_comment() {
    interrupted_inside(
        &format!(";{}\ntrue", "x".repeat(16_384)),
        StopReason::Cancelled,
    );
}

#[test]
fn cancellation_is_polled_inside_a_long_simple_symbol() {
    interrupted_inside(&"x".repeat(16_384), StopReason::Cancelled);
}

#[test]
fn deadline_is_polled_inside_a_long_numeral() {
    interrupted_inside(&"1".repeat(16_384), StopReason::Deadline);
}

#[test]
fn storage_insertion_requires_credit_after_scanning_the_token() {
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(4, &mut checkpoint);
    assert_eq!(
        AuthoredSource::capture("true", &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Exhausted)
    );
    assert_eq!(work.remaining(), 0);
    assert_eq!(
        AuthoredSource::capture("", &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Exhausted)
    );
}

#[test]
fn cancellation_at_storage_admission_cannot_publish_a_complete_capture() {
    let mut calls = 0;
    let mut checkpoint = || {
        calls += 1;
        if calls == 6 {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(1_000, &mut checkpoint);
    assert_eq!(
        AuthoredSource::capture("true", &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(
        AuthoredSource::capture("true", &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(calls, 6);
}

#[test]
fn exhausted_credit_cannot_be_renewed_by_a_second_capture() {
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(2, &mut checkpoint);
    assert_eq!(
        AuthoredSource::capture("true", &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Exhausted)
    );
    assert_eq!(
        AuthoredSource::capture("", &mut work).unwrap_err(),
        AuthoredSourceError::Control(QueryError::Exhausted)
    );
}

#[test]
fn deeply_nested_tokens_use_flat_storage_and_drop() {
    let input = format!("{}true{}", "(".repeat(16_384), ")".repeat(16_384));
    let source = capture(&input);
    assert_eq!(source.token_count(), 32_769);
    assert_eq!(source.original(), input);
    drop(source);
}
