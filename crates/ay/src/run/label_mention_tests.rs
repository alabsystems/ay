// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Outside `--z3-mode`, a later command that mentions a label z3 binds and
//! this session does not withholds verdicts (`z3_session_start.rs`). These
//! pin the two scans that decide it: the names a command labels, and whether
//! a command's source mentions one.

use super::*;
use std::collections::HashSet;

fn names(list: &[&str]) -> HashSet<String> {
    list.iter().map(ToString::to_string).collect()
}

/// A mention counts wherever it stands, including against a `;` comment and
/// after a `|` in a string or comment, which the earlier token scan read as
/// part of the symbol or as the start of a quoted one.
#[test]
fn a_mention_is_found_wherever_it_stands() {
    let label = names(&["a"]);
    for text in [
        "(assert a)",
        "(assert (= a 7))",
        "(declare-const a Int)",
        "(declare-const a;\n Int)",
        "(assert (= a;\n 7))",
        "(assert |a|)",
        "(assert (! p :named a))",
        "(echo \"|\")(assert a)",
        "; a | in a comment\n(assert a)",
        "(assert (= \"x\" \"a\"))",
    ] {
        assert!(source_mentions_any_symbol(text, &label), "{text}");
    }
}

/// A name inside a longer symbol is not a mention of it.
#[test]
fn a_longer_symbol_is_not_a_mention() {
    let label = names(&["a"]);
    for text in [
        "(check-sat)",
        "(assert ab)",
        "(assert (= ba 1))",
        "(assert a.b)",
        "(assert |ab|)",
    ] {
        assert!(!source_mentions_any_symbol(text, &label), "{text}");
    }
}

/// A quoted name is found in its quoted spelling. A name holding `|` or `\`,
/// which a quoted symbol spells with escapes, counts as mentioned by every
/// command, and so does the empty name.
#[test]
fn quoted_names_are_found_or_assumed_mentioned() {
    assert!(source_mentions_any_symbol(
        "(assert (not |a b|))",
        &names(&["a b"])
    ));
    assert!(!source_mentions_any_symbol(
        "(assert |xa b|)",
        &names(&["a b"])
    ));
    for name in ["a|b", "c\\d", ""] {
        assert!(
            source_mentions_any_symbol("(check-sat)", &names(&[name])),
            "{name:?}"
        );
    }
}

/// Every `:named` label written in a command's terms, at any depth.
#[test]
fn every_label_a_command_writes_is_named() {
    let commands = parse(
        "(define-fun f () Bool (and (! p :named a) \
         (let ((x (! q :named b))) (forall ((y Int)) (! (> y 0) :named c)))))\
         (check-sat-assuming ((! p :named d)))",
    )
    .expect("valid script");
    let mut labels: Vec<String> = commands.iter().flat_map(command_label_names).collect();
    labels.sort();
    assert_eq!(labels, ["a", "b", "c", "d"]);
}
