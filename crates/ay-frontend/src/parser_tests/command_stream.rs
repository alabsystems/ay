// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `parser::tests` to preserve test FQNs.

#[test]
fn command_stream_matches_parse_for_valid_input() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (check-sat)
        (exit)
    "#;
    let stream: Vec<_> = drain_stream(input);
    let direct = parse(input).unwrap();
    assert_eq!(stream.len(), direct.len());
    for (item, expected) in stream.iter().zip(direct.iter()) {
        match item {
            CommandStreamItem::Command(cmd) => assert_eq!(cmd.as_ref(), expected),
            CommandStreamItem::Error(e) => panic!("unexpected error for valid input: {e}"),
        }
    }
}

#[test]
fn command_stream_recovers_from_unknown_command() {
    // (bogus-command) parses as an S-expression but is not a known command:
    // the stream reports the error and continues with the next command.
    let input = "(declare-const x Int)(assert (> x 0))(check-sat)(bogus-command)(assert (< x 5))(check-sat)";
    let items = drain_stream(input);
    let mut errors = 0;
    let mut check_sats = 0;
    for item in &items {
        match item {
            CommandStreamItem::Command(command)
                if matches!(command.as_ref(), Command::CheckSat) =>
            {
                check_sats += 1;
            }
            CommandStreamItem::Command(_) => {}
            CommandStreamItem::Error(_) => errors += 1,
        }
    }
    assert_eq!(errors, 1, "exactly one bad command: {items:?}");
    assert_eq!(check_sats, 2, "both check-sats must survive: {items:?}");
    // The command after the error must still parse.
    assert!(
        items.last().is_some_and(stream_item_is_check_sat),
        "stream must continue past the bad command"
    );
}

#[test]
fn command_stream_recovers_from_stray_close_paren() {
    // A malformed top-level form (stray ')') must not abort following commands.
    let input = "(declare-const x Int)(check-sat))(declare-const y Int)(check-sat)";
    let items = drain_stream(input);
    let check_sats = items
        .iter()
        .filter(|item| stream_item_is_check_sat(item))
        .count();
    let errors = items
        .iter()
        .filter(|i| matches!(i, CommandStreamItem::Error(_)))
        .count();
    assert_eq!(check_sats, 2, "both check-sats must survive: {items:?}");
    assert!(errors >= 1, "stray paren must produce an error: {items:?}");
    assert!(
        items.iter().any(|item| matches!(
            item,
            CommandStreamItem::Command(command)
                if matches!(command.as_ref(), Command::DeclareConst(name, _) if name == "y")
        )),
        "the command immediately after the stray token must not be discarded: {items:?}"
    );
}

#[test]
fn command_stream_preserves_command_after_invalid_top_level_token() {
    let items = drain_stream("#q(check-sat)");
    assert_eq!(
        items.len(),
        2,
        "one error and one command expected: {items:?}"
    );
    assert!(matches!(items[0], CommandStreamItem::Error(_)));
    assert!(stream_item_is_check_sat(&items[1]));
}

#[test]
fn command_stream_resync_honors_escaped_bar_in_quoted_symbol() {
    // The invalid token makes S-expression parsing stop before the quoted
    // symbol. Recovery still has to skip the entire malformed command. The
    // escaped bar is not the symbol terminator, and the `)` / `(` inside the
    // symbol are not structural parentheses.
    let input = r"(assert #q |name\|) with ( parens|)(check-sat)";
    let items = drain_stream(input);
    assert_eq!(
        items.len(),
        2,
        "one error and one command expected: {items:?}"
    );
    assert!(matches!(items[0], CommandStreamItem::Error(_)));
    assert!(stream_item_is_check_sat(&items[1]));
}

#[test]
fn command_stream_error_does_not_consume_following_command() {
    // After an unknown command, the very next command is parsed intact.
    let input = "(bogus)(check-sat)";
    let items = drain_stream(input);
    assert!(matches!(items[0], CommandStreamItem::Error(_)));
    assert!(stream_item_is_check_sat(&items[1]));
    assert_eq!(items.len(), 2);
}

#[test]
fn command_stream_coalesces_stray_atom_run_into_one_positioned_error() {
    // Regression: each stray top-level token used to produce its own identical
    // unpositioned "Command must be a list" error (one per token). A run of
    // stray atoms must now yield ONE error that names the first token and its
    // line/column, and the following command must still parse.
    let input = "garbage line one\ngarbage two\n(check-sat)\n";
    let items = drain_stream(input);
    assert_eq!(items.len(), 2, "one coalesced error + check-sat: {items:?}");
    match &items[0] {
        CommandStreamItem::Error(e) => {
            assert_eq!(e.line, Some(1), "error must point at the stray token");
            assert_eq!(e.position, Some(0));
            assert!(
                e.message.contains("'garbage'")
                    && e.message.contains("line 1 column 1")
                    && e.message.contains("skipped 5"),
                "message must name token, position, and coalesced count: {}",
                e.message
            );
        }
        other => panic!("expected coalesced stray-token error, got: {other:?}"),
    }
    assert!(stream_item_is_check_sat(&items[1]));
}

#[test]
fn command_stream_rebases_parse_error_positions_to_whole_input() {
    // A syntax error inside the third command must be reported with an
    // absolute line number, not one relative to the command's own slice.
    let input = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0)))\n(check-sat)\n";
    let items = drain_stream(input);
    let err = items
        .iter()
        .find_map(|i| match i {
            CommandStreamItem::Error(e) => Some(e),
            CommandStreamItem::Command(_) => None,
        })
        .expect("stray ')' must produce an error");
    assert_eq!(
        err.line,
        Some(3),
        "position must be absolute in the input: {err:?}"
    );
}

#[test]
fn command_stream_handles_only_whitespace_and_comments() {
    let input = "  ; a comment\n   \n; another\n";
    let items = drain_stream(input);
    assert!(items.is_empty(), "no commands expected: {items:?}");
}

#[test]
fn command_stream_resync_skips_comments_and_strings() {
    // A string/comment containing parens must not confuse boundary detection.
    let input = "(set-info :note \"a ) paren in a string\")(check-sat)";
    let items = drain_stream(input);
    let check_sats = items
        .iter()
        .filter(|item| stream_item_is_check_sat(item))
        .count();
    assert_eq!(
        check_sats, 1,
        "check-sat after string must parse: {items:?}"
    );
}
