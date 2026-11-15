// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Carcara parses the WHOLE authored file: a command it skips, a command AY
//! dropped, and every command after the query that decides a verdict. Each
//! Carcara outcome was measured with `carcara parse` (carcara 1.1.0, git
//! 9a352ee) on the problem alone.

use ay_frontend::{CommandStream, CommandStreamItem};

use super::AuthoredProblemSurface;

/// Read `problem` the way the CLI's file mode does: each command's text, then
/// its parsed command (a dropped command's text only). With `stop_at_query`,
/// reading stops at the first `check-sat`, after reading the rest ahead, as
/// when that query decides the verdict before the later commands run.
fn read(problem: &str, stop_at_query: bool) -> Option<String> {
    let mut surface = AuthoredProblemSurface::default();
    let mut stream = CommandStream::new(problem);
    loop {
        let start = stream.position();
        let Some(item) = stream.next_command() else {
            break;
        };
        let text = &problem[start..stream.position()];
        match item {
            CommandStreamItem::Command(command) => {
                if stop_at_query && matches!(*command, ay_frontend::Command::CheckSat) {
                    surface.look_ahead(&problem[start..]);
                    break;
                }
                surface.observe_source_text(text);
                surface.observe(&command);
            }
            CommandStreamItem::Error(_) => surface.observe_dropped_text(text),
        }
    }
    surface.gap().map(str::to_string)
}

const PRELUDE: &str = "(set-logic ALL)(declare-datatype E ((A) (B)))(declare-const e E)\
    (declare-const x Int)(assert (> x 0))(assert (< x 0))";

/// Carcara skips `define-const` whole: `identifier 'c' is not defined` where
/// the problem uses `c`, and the problem parses where it does not (review
/// probe b03: `valid`, which AY used to disclose `unsupported`).
#[test]
fn define_const_is_refused_exactly_where_its_symbol_is_used() {
    for used in ["(assert (= c 1))", "(define-fun g () Int c)"] {
        let problem = format!("{PRELUDE}(define-const c Int 1){used}(check-sat)");
        let gap = read(&problem, false).unwrap_or_else(|| panic!("{used}: supported"));
        assert!(
            gap.contains("`define-const`") && gap.contains("`c`"),
            "{used}: {gap}"
        );
    }
    let unused = format!("{PRELUDE}(define-const c Int 1)(check-sat)");
    assert_eq!(read(&unused, false), None);
    // The flag covers the one parsed command after the text, no later one.
    let later = format!("{PRELUDE}(define-const c Int 1)(define-fun d () Int 2)(assert (= d 2))");
    assert_eq!(read(&later, false), None);
    // A flag left by text whose `define-fun` never arrived hides no other
    // command: the next one is still read.
    let mut surface = AuthoredProblemSurface::default();
    surface.observe_source_text("(define-const c Int 1)");
    let commands = ay_frontend::parse(&format!("{PRELUDE}(assert (= e (as A E)))")).unwrap();
    for command in &commands {
        surface.observe(command);
    }
    assert!(surface.gap().is_some_and(|gap| gap.contains("(as A E)")));
}

/// Review probes b01/b02: `--rigor strict` published `unsat` with
/// `carcara_surface=supported` at the `check-sat`, and Carcara stops at the
/// command after it. b09 (a clean tail) parses.
#[test]
fn a_construct_after_the_deciding_query_is_read_ahead() {
    let refused = [
        ("(declare-const f (_ FloatingPoint 8 24))", "FloatingPoint"),
        ("(assert (= e (as A E)))", "(as A E)"),
        ("(define-const c Int 1)(assert (= c 1))", "`define-const`"),
        ("(set-info :source |C:\\ay|)", "lexer"),
        // Dropped by AY (a leading-zero numeral), still lexed by Carcara.
        ("(set-option :random-seed 007)", "leading zero"),
    ];
    for (tail, fragment) in refused {
        let problem = format!("{PRELUDE}(check-sat){tail}(exit)");
        let gap = read(&problem, true).unwrap_or_else(|| panic!("{tail}: supported"));
        assert!(gap.contains(fragment), "{tail}: {gap}");
    }
    let clean = format!("{PRELUDE}(check-sat)(get-value (x))(push 1)(assert (= e A))(pop 1)(exit)");
    assert_eq!(read(&clean, true), None);
}

/// One read ahead per file, whatever the number of queries: the second call
/// is a no-op, so a caller may pass every query's remainder.
#[test]
fn the_read_ahead_runs_once() {
    let mut surface = AuthoredProblemSurface::default();
    surface.look_ahead("(check-sat)(assert true)");
    surface.look_ahead("(check-sat)(declare-const f (_ FloatingPoint 8 24))");
    assert_eq!(surface.gap(), None);
}

/// A dropped command is only lexed: Carcara skips an unknown command, and
/// stops at a `\` in a quoted symbol wherever it is.
#[test]
fn a_dropped_command_is_judged_by_the_lexer_alone() {
    let mut surface = AuthoredProblemSurface::default();
    surface.observe_dropped_text("(frobnicate 1 (x y))");
    assert_eq!(surface.gap(), None);
    surface.observe_dropped_text("(frobnicate |a\\b|)");
    assert!(surface.gap().is_some_and(|gap| gap.contains("lexer")));
}
