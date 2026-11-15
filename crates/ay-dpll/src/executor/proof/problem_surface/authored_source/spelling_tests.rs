// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Spellings only the command's source text, or the problem's logic, shows:
//! AY's command parser normalizes them, and pinned Carcara (1.1.0, git
//! 9a352ee) refuses them, measured with `carcara parse` on each problem.

use super::tests::gap_of;
use super::AuthoredProblemSurface;

/// Spellings AY's command parser normalizes, so only the source text shows
/// them. Carcara: `expected non-empty sequence` (legacy datatypes),
/// `unexpected token: 'A'` (bare constructors); `assert-not` is skipped, so its
/// premise is missing. `define-const`: `whole_file_tests`.
#[test]
fn command_spellings_only_the_source_text_shows_are_unsupported() {
    let refused = [
        ("  ; lead\n(assert-not false)", "`assert-not`"),
        ("(declare-var x Int)", "`declare-var`"),
        ("(declare-datatypes () ((E A B)))", "legacy"),
        ("(declare-datatype E (A B))", "bare symbol"),
        ("(declare-datatypes ((E 0)) ((A B)))", "bare symbol"),
        (
            "(declare-datatype L (par (T) (nil (cons (hd T) (tl (L T))))))",
            "bare symbol",
        ),
    ];
    for (source, fragment) in refused {
        let mut surface = AuthoredProblemSurface::default();
        surface.observe_source_text(source);
        assert!(
            surface.gap().is_some_and(|gap| gap.contains(fragment)),
            "{source}: {:?}",
            surface.gap()
        );
    }
    let accepted = [
        "(declare-datatypes ((E 0)) (((A) (B))))\n; trailing comment\n",
        "(declare-datatype E ((A) (B (b Int))))",
        "(declare-datatype L (par (T) ((nil) (cons (hd T) (tl (L T))))))",
        "(set-info :status unsat)",
        "(assert (! p :named |a b|))",
        "(get-value (x))",
        "(check-sat)\n",
    ];
    for source in accepted {
        let mut surface = AuthoredProblemSurface::default();
        surface.observe_source_text(source);
        assert_eq!(surface.gap(), None, "{source}");
    }
}

/// Parsed-command shapes that depend on the logic or the command's arity,
/// each measured with `carcara parse` at 9a352ee and each published `unsat`
/// under `--rigor strict` before this check (adversarial review probes a01,
/// a03, a04, a12/a13).
#[test]
fn empty_assumptions_and_real_only_numerals_are_unsupported() {
    let refused = [
        // `expected non-empty sequence`
        (
            "(set-logic ALL)(declare-const p Bool)(assert p)(check-sat-assuming ())",
            "check-sat-assuming",
        ),
        // panicked at carcara/src/parser/mod.rs:1452 (Real arity unwrapped)
        (
            "(set-logic QF_UFLRA)(declare-datatypes ((E 0)) (((A) (B))))(check-sat)",
            "real",
        ),
        // `expected integer constant, got '4.0'`
        (
            "(set-logic QF_BVFPLRA)(declare-const b (_ BitVec 4))(check-sat)",
            "real",
        ),
        (
            "(set-logic QF_LRA)(assert (= (_ bv1 4) (_ bv1 4)))(check-sat)",
            "real",
        ),
    ];
    for (problem, fragment) in refused {
        let gap = gap_of(problem).unwrap_or_else(|| panic!("{problem}: disclosed supported"));
        assert!(gap.contains(fragment), "{problem}: {gap}");
    }
    // Controls Carcara parses: the singular datatype form reads no arity
    // numeral, and a non-empty assumption list.
    for problem in [
        "(set-logic QF_LRA)(declare-datatype E ((A) (B)))(declare-const e E)(check-sat)",
        "(set-logic ALL)(declare-const p Bool)(check-sat-assuming (p))",
        "(set-logic QF_LIA)(declare-datatypes ((E 0)) (((A) (B))))(check-sat)",
    ] {
        assert_eq!(gap_of(problem), None, "{problem}");
    }
}

/// Only the source text shows these; Carcara's lexer tokenizes skipped
/// commands and skipped attributes too (review probes a02, a06-a09, a15,
/// b04, b06, b07, d04, d05).
#[test]
fn spellings_carcaras_lexer_rejects_are_unsupported() {
    let refused = [
        ("(declare-sort S)", "arity"),
        ("(set-info :source |C:\\path|)", "lexer"),
        ("(set-info :source |a \\| b|)", "lexer"),
        ("(set-info :notes \"\\u{d800}\")", "lexer"),
        ("(echo \"\\ud800\")", "lexer"),
        ("(declare-const -1x Int)", "lexer"),
        (
            "(assert (forall ((s String)) (! (p s) :pattern ((f \"\\u{dfff}\")))))",
            "lexer",
        ),
        ("(set-option :random-seed 007)", "lexer"),
        ("(assert (= b #o17))", "lexer"),
    ];
    for (source, fragment) in refused {
        let mut surface = AuthoredProblemSurface::default();
        surface.observe_source_text(source);
        assert!(
            surface.gap().is_some_and(|gap| gap.contains(fragment)),
            "{source}: {:?}",
            surface.gap()
        );
    }
    let accepted = [
        "(declare-sort S 0)",
        "(set-info :source |plain; text (with parens)|)",
        "(assert (= s \"\\u{41}\\u0042\\x41 \\\\ \"\"q\"\"\"))",
        "(assert (= s \"\\u{30000}\"))",
        "(assert (= x (- 5)))",
        "(assert (= x -5))",
        "(assert (= r -1.5))",
        "(assert (= b #x0F))",
        "(assert (! p :named |a b|)) ; trailing |comment\\",
    ];
    for source in accepted {
        let mut surface = AuthoredProblemSurface::default();
        surface.observe_source_text(source);
        assert_eq!(surface.gap(), None, "{source}");
    }
}
