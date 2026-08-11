// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::command::{Constant, Sort, Term};

#[test]
fn test_parse_simple_problem() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (< y 10))
        (check-sat)
        (exit)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 7);
    assert!(matches!(commands[0], Command::SetLogic(_)));
    assert!(matches!(commands[1], Command::DeclareConst(_, _)));
    assert!(matches!(commands[2], Command::DeclareConst(_, _)));
    assert!(matches!(commands[3], Command::Assert(_)));
    assert!(matches!(commands[4], Command::Assert(_)));
    assert!(matches!(commands[5], Command::CheckSat));
    assert!(matches!(commands[6], Command::Exit));
}

#[test]
fn test_parse_qf_eia_integer_power() {
    let commands = parse("(set-logic QF_EIA) (assert (= (** 2 10) 1024))").unwrap();
    assert!(matches!(
        &commands[0],
        Command::SetLogic(logic) if logic == "QF_EIA"
    ));
    let Command::Assert(Term::App(eq, equality_args)) = &commands[1] else {
        panic!("expected equality assertion");
    };
    assert_eq!(eq, "=");
    let Term::App(power, power_args) = &equality_args[0] else {
        panic!("expected integer-power application");
    };
    assert_eq!(power, "**");
    assert_eq!(power_args.len(), 2);
}

#[test]
fn test_parse_bitvector_problem() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvadd x y) #x00000001))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 5);

    // Check bitvector sort
    if let Command::DeclareConst(name, Sort::Indexed(sort, indices)) = &commands[1] {
        assert_eq!(name, "x");
        assert_eq!(sort, "BitVec");
        assert_eq!(
            indices,
            &vec![crate::command::Index::Numeral("32".to_string())]
        );
    } else {
        panic!("Expected DeclareConst with indexed sort");
    }
}

#[test]
fn test_parse_array_problem() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const arr (Array Int Int))
        (declare-const i Int)
        (assert (= (select arr i) 42))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 5);

    // Check array sort
    if let Command::DeclareConst(name, Sort::Parameterized(sort, params)) = &commands[1] {
        assert_eq!(name, "arr");
        assert_eq!(sort, "Array");
        assert_eq!(params.len(), 2);
    } else {
        panic!("Expected DeclareConst with parameterized sort");
    }
}

#[test]
fn test_parse_with_let() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (let ((y (+ x 1))) (> y 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 4);

    if let Command::Assert(Term::Let(bindings, body)) = &commands[2] {
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].0, "y");
        assert!(matches!(**body, Term::App(_, _)));
    } else {
        panic!("Expected Assert with Let term");
    }
}

#[test]
fn test_parse_with_quantifier() {
    let input = r#"
        (set-logic AUFLIA)
        (assert (forall ((x Int) (y Int)) (=> (> x y) (> (+ x 1) y))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 3);

    if let Command::Assert(Term::Forall(bindings, _body)) = &commands[1] {
        assert_eq!(bindings.len(), 2);
        assert_eq!(bindings[0].0, "x");
        assert_eq!(bindings[1].0, "y");
    } else {
        panic!("Expected Assert with Forall term");
    }
}

#[test]
fn test_parse_define_fun() {
    let input = r#"
        (set-logic QF_LIA)
        (define-fun abs ((x Int)) Int (ite (< x 0) (- x) x))
        (declare-const a Int)
        (assert (= (abs a) 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 5);

    if let Command::DefineFun(name, params, ret_sort, body) = &commands[1] {
        assert_eq!(name, "abs");
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].0, "x");
        assert!(matches!(ret_sort, Sort::Simple(s) if s == "Int"));
        assert!(matches!(body, Term::App(f, _) if f == "ite"));
    } else {
        panic!("Expected DefineFun command");
    }
}

#[test]
fn test_parse_sygus_general_track_scaffold() {
    let input = r#"
        (set-logic LIA)
        (declare-var x Int)
        (synth-fun abs ((x Int)) Int
          ((Start Int (x 0 1 (- Start) (+ Start Start)))))
        (constraint (= (abs x) (ite (>= x 0) x (- x))))
        (check-synth)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 5);
    assert!(matches!(commands[0], Command::SetLogic(_)));
    assert!(matches!(commands[1], Command::DeclareVar(_, _)));
    assert!(matches!(commands[2], Command::SynthFun(_, _, _, Some(_))));
    assert!(matches!(commands[3], Command::SygusConstraint(_)));
    assert!(matches!(commands[4], Command::CheckSynth));
}

#[test]
fn test_parse_sygus_inv_track_scaffold() {
    let input = r#"
        (set-logic LIA)
        (synth-inv inv ((x Int))
          ((Start Bool ((>= x 0) (<= x 10) (and Start Start)))))
        (declare-fun pre (Int) Bool)
        (declare-fun trans (Int Int) Bool)
        (declare-fun post (Int) Bool)
        (inv-constraint inv pre trans post)
        (check-synth)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 7);
    assert!(matches!(commands[1], Command::SynthInv(_, _, Some(_))));
    assert!(matches!(commands[5], Command::InvConstraint(_, _, _, _)));
    assert!(matches!(commands[6], Command::CheckSynth));
}

#[test]
fn test_parse_push_pop() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (> x 0))
        (check-sat)
        (pop 1)
        (assert (< x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 8);
    assert!(matches!(commands[2], Command::Push(1)));
    assert!(matches!(commands[5], Command::Pop(1)));
}

#[test]
fn test_parse_constants() {
    let input = r#"
        (assert (and true false))
        (assert (= 42 42))
        (assert (= 3.14 3.14))
        (assert (= #xDEAD #xDEAD))
        (assert (= #b1010 #b1010))
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 5);

    // Check boolean constants
    if let Command::Assert(Term::App(_, args)) = &commands[0] {
        assert!(matches!(&args[0], Term::Const(Constant::True)));
        assert!(matches!(&args[1], Term::Const(Constant::False)));
    }
}

#[test]
fn test_parse_comments() {
    let input = r#"
        ; This is a comment
        (set-logic QF_LIA) ; inline comment
        ; Another comment
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    assert_eq!(commands.len(), 2);
}

#[test]
fn test_parse_empty_input() {
    let commands = parse("").unwrap();
    assert!(commands.is_empty());
}

#[test]
fn test_parse_whitespace_only() {
    let commands = parse("   \n\t\n   ").unwrap();
    assert!(commands.is_empty());
}

#[test]
fn test_parse_error_missing_paren() {
    let result = parse("(set-logic QF_LIA");
    assert!(result.is_err());
}

#[test]
fn test_parse_error_unknown_command() {
    let result = parse("(unknown-command foo)");
    assert!(result.is_err());
}

/// Regression test for #2689: parser must reject pathological nesting depth
/// with an error (never stack overflow).
/// The S-expression parser uses iterative (heap-stack) parsing, so this
/// tests the MAX_PARSE_DEPTH guard (1,000,000), not stack overflow.
#[test]
fn test_parse_depth_limit_exceeded_issue_2689() {
    // 1,000,001 nesting levels exceeds MAX_PARSE_DEPTH (1,000,000).
    // The parser hits the limit early and returns an error without
    // building the full tree, so this runs in milliseconds.
    let depth = 1_000_001;
    let mut input = String::from("(set-logic QF_LIA)\n(assert ");
    for _ in 0..depth {
        input.push_str("(not ");
    }
    input.push_str("true");
    for _ in 0..depth {
        input.push(')');
    }
    input.push_str(")\n(check-sat)\n");

    let result = parse(&input);
    assert!(
        result.is_err(),
        "{depth}-deep nesting should be rejected by MAX_PARSE_DEPTH guard"
    );
}

/// Regression test for #6888: 66,000-deep nesting must succeed after
/// the limit was raised from 65,536 to 1,000,000 for BMC benchmarks.
#[test]
fn test_parse_depth_66000_succeeds_after_limit_raise() {
    let mut input = String::from("(set-logic QF_LIA)\n(assert ");
    for _ in 0..66_000 {
        input.push_str("(not ");
    }
    input.push_str("true");
    for _ in 0..66_000 {
        input.push(')');
    }
    input.push_str(")\n(check-sat)\n");

    let result = parse(&input);
    assert!(
        result.is_ok(),
        "66,000-deep nesting must succeed with 1M limit (#6888): {result:?}"
    );
}

/// Regression test for #5453: parser must handle term annotations.
#[test]
fn test_parse_annotation_issue_5453() {
    let input = r#"
        (set-logic QF_UF)
        (declare-fun p () Bool)
        (assert (! p :named a1))
        (check-sat)
    "#;

    let result = parse(input);
    assert!(result.is_ok(), "Annotation parsing failed: {result:?}");
    let commands = result.expect("already checked");
    assert_eq!(commands.len(), 4);
    assert!(matches!(commands[2], Command::Assert(_)));
}

/// Parser must handle moderate nesting that real QF_BV benchmarks require
/// (sage/Sage2 families). Previously failed with MAX_PARSE_DEPTH=1024.
/// Test uses 200 levels (safe for debug-mode thread stack where each
/// `Term::from_sexp` + `parse_application` frame can be ~3KB). In release
/// mode, the full pipeline handles 1000+ levels. The sexp parser itself
/// is iterative and handles up to 65,536 levels.
#[test]
fn test_parse_moderate_nesting_succeeds_issue_4602() {
    let mut input = String::from("(set-logic QF_LIA)\n(assert ");
    for _ in 0..200 {
        input.push_str("(not ");
    }
    input.push_str("true");
    for _ in 0..200 {
        input.push(')');
    }
    input.push_str(")\n(check-sat)\n");

    let result = parse(&input);
    assert!(result.is_ok(), "200-deep nesting must succeed: {result:?}");
}

/// Helper: drain a `CommandStream` into a vector of (ok?, debug) outcomes.
fn drain_stream(input: &str) -> Vec<CommandStreamItem> {
    CommandStream::new(input).collect()
}

fn stream_item_is_check_sat(item: &CommandStreamItem) -> bool {
    matches!(
        item,
        CommandStreamItem::Command(command) if matches!(command.as_ref(), Command::CheckSat)
    )
}

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
