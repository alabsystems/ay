// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;
use ay_frontend::sexp::{parse_sexps, SExpr};

fn rejected(input: &str, reason: &str) {
    let Err(ChcError::Parse(message)) = check(input) else {
        panic!("expected lexical refusal")
    };
    assert!(message.contains(reason), "{message}");
}

#[test]
fn empty_and_comment_only_input_add_no_forms_or_tokens() {
    for input in [
        "",
        " \t\r\n",
        "; ( | \" \\ ignored to EOF",
        "; ignored\r; also ignored\n",
    ] {
        check(input).unwrap();
        assert!(parse_sexps(input).unwrap().is_empty());
    }
    let input = "(rule true); (not another form)\n(check-sat) ; trailing";
    check(input).unwrap();
    assert_eq!(parse_sexps(input).unwrap().len(), 2);
}

#[test]
fn quoted_spaces_parentheses_and_semicolons_are_one_symbol() {
    let input = "(|array (name); with spaces| |line\nname| |double\"quote|)";
    check(input).unwrap();
    let forms = parse_sexps(input).unwrap();
    let SExpr::List(items) = &forms[0] else {
        panic!("one list")
    };
    assert_eq!(items.len(), 3);
    assert_eq!(items[0].as_symbol(), Some("array (name); with spaces"));
    assert_eq!(items[1].as_symbol(), Some("line\nname"));
    assert_eq!(items[2].as_symbol(), Some("double\"quote"));
}

#[test]
fn quoted_syntax_and_literal_lookalikes_cannot_lose_their_identity() {
    for name in [
        "forall",
        "exists",
        "let",
        "_",
        "!",
        "as",
        "true",
        "false",
        "and",
        "xor",
        "select",
        "store",
        "bvadd",
        "extract",
        "rotate_left",
        "int2bv",
        "Bool",
        "Array",
        "BitVec",
        "HORN",
        "rule",
        "query",
        "assert",
        "declare-rel",
        "set-logic",
        "check-sat",
        "push",
        "pop",
        "reset",
        "123",
        "#b1",
        ":named",
        "bv123",
    ] {
        rejected(&format!("|{name}|"), "quoted syntax");
        // The frontend really does erase this distinction; this preflight must
        // run before its Symbol can be mistaken for a syntax/operator spelling.
        assert_eq!(
            parse_sexps(&format!("|{name}|")).unwrap()[0].as_symbol(),
            Some(name)
        );
    }
    for input in [
        "|forall user|",
        "|BV123|",
        "|ordinary|",
        "|rule-ish|",
        "|bv_name|",
    ] {
        check(input).unwrap();
    }
}

#[test]
fn strings_escapes_non_ascii_and_control_bytes_are_refused() {
    for input in ["\"text\"", "(rule \"text\")", "a\\b", "|a\\b|", "|a\\|b|"] {
        assert!(check(input).is_err());
    }
    for input in ["é", "|é|", "; é", "\0", "\u{7f}", "\u{b}", "|a\u{1f}b|"] {
        rejected(input, "ASCII");
    }
    check("; comments may contain \" and \\\n(rule true)").unwrap();
}

#[test]
fn byte_limit_is_checked_even_for_lexically_inert_input() {
    let input = " ".repeat(MAX_INPUT_BYTES);
    check(&input).unwrap();
    rejected(&(input + " "), "input byte limit");
}

#[test]
fn depth_limit_ignores_quoted_and_commented_parentheses() {
    let input = format!("{}x{}", "(".repeat(MAX_DEPTH), ")".repeat(MAX_DEPTH));
    check(&input).unwrap();
    rejected(&format!("({input})"), "nesting depth");
    check(&format!("|{}| ; {}\n", "(".repeat(100), ")".repeat(100))).unwrap();
    for input in ["(", ")", "() )", "(x", "|unterminated", "(|unterminated)"] {
        assert!(check(input).is_err());
    }
}

#[test]
fn raw_token_limits_include_quoted_delimiters() {
    check(&"x".repeat(MAX_TOKEN_BYTES)).unwrap();
    rejected(
        &"x".repeat(MAX_TOKEN_BYTES + 1),
        "ordinary token byte limit",
    );
    check(&format!("|{}|", "x".repeat(MAX_TOKEN_BYTES - 2))).unwrap();
    rejected(
        &format!("|{}|", "x".repeat(MAX_TOKEN_BYTES - 1)),
        "quoted token byte limit",
    );
    // Comments are charged only against total bytes, not a fictitious token.
    check(&format!(";{}", "x".repeat(MAX_TOKEN_BYTES + 1))).unwrap();
}

#[test]
fn token_limit_counts_delimiters_and_scans_all_top_level_forms() {
    let input = "() ".repeat(MAX_TOKENS / 2);
    check(&input).unwrap();
    rejected(&(input + "x"), "token limit");
    let input = "x ".repeat(MAX_TOKENS);
    check(&input).unwrap();
    rejected(&(input + "(check-sat)"), "token limit");
}

#[test]
fn adjacent_frontend_tokens_never_hide_behind_one_ordinary_run() {
    // Each of these whitespace-delimited chunks is multiple frontend tokens.
    for chunk in ["1abc", "a:b", "#x1z"] {
        assert_eq!(parse_sexps(chunk).unwrap().len(), 2);
        let input = format!("{chunk} ").repeat(MAX_TOKENS / 2 + 1);
        rejected(&input, "token limit");
    }
    // Admission does not claim to replace the frontend's actual lexer.
    check("00").unwrap();
    assert!(parse_sexps("00").is_err());
}
