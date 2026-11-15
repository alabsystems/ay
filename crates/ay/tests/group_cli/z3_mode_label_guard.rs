// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repros from the label-conformance review of the z3-reach walk that the
//! label guard and z3 mode's acceptance missed, each with a twin that
//! answers sat: a mention the guard did not see (class B), a label name it
//! did not record, a command ay cannot parse that binds a label, and
//! constructs z3 4.12.5 rejects with no label. The expected answers are z3
//! 4.12.5's or `unknown` in `--z3-mode`; plain mode gives z3's answer,
//! `unknown`, or its documented own reading. Plain mode does not trust a
//! label in a subterm elaboration passes over, so a twin with one answers
//! `unknown` there.

use ntest::timeout;

use super::label_answer_lanes::{assert_pairs, Case};

const A_LABEL_MENTION_AFTER_A_BAR_IN_A_STRING_OR_COMMENT: &[(Case, Case)] = &[
    (
        (
            "mention_scan_string_bar",
            r#"(declare-const p Bool)
(declare-const q Bool)
(declare-const s String)
(assert (or (forall ((z Int)) 5) (ite true true (! q :named a))))
(assert (and (= s "|") (not a) (= s "|")))
(assert q)
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "mention_scan_string_bar_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(declare-const s String)
(assert (or (forall ((z Int)) true) (ite true true (! q :named a))))
(assert (and (= s "|") (not a) (= s "|")))
(assert p)
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "mention_scan_comment_bar",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or (forall ((z Int)) 5) (ite true true (! q :named a))))
(assert (and true ; |
  (not a) ; |
  true))
(assert q)
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "mention_scan_comment_bar_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or (forall ((z Int)) true) (ite true true (! q :named a))))
(assert (and true ; |
  (not a) ; |
  true))
(assert p)
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "mention_scan_z3_unvouched",
            r#"(declare-const q Bool)
(declare-const s String)
(assert (or (= (str.len s) 1) (! q :named a)))
(assert (and (= s "|") (not a) (= s "|")))
(check-sat)
"#,
            "unknown",
            "sat",
        ),
        (
            "mention_scan_z3_unvouched_twin",
            r#"(declare-const q Bool)
(declare-const s String)
(assert (or (= (str.len s) 1) (! q :named a)))
(assert (and (= s "|") (not q) (= s "|")))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "c2_empty_binders_comment_bar",
            r#"(declare-const p Bool)
(assert (or true (ite true true (and (exists () p) (! false :named a)))))
(assert (and true ; |
 a))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "c2_empty_binders_comment_bar_twin",
            r#"(declare-const p Bool)
(assert (or true (ite true true (and (exists ((z Int)) p) (! false :named a)))))
(assert (and true ; |
 p))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "c2_empty_binders_string_bar",
            r#"(declare-const p Bool)
(declare-const s String)
(assert (or true (and (exists () p) (! false :named a))))
(assert (and (= s "|") a (= s "|")))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "c2_empty_binders_string_bar_twin",
            r#"(declare-const p Bool)
(declare-const s String)
(assert (or true (and (exists ((z Int)) p) (! false :named a))))
(assert (and (= s "|") p (= s "|")))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "plain_unbound_mention_comment_bar",
            r#"(declare-const p Bool)
(assert (let ((y p)) (! y :named a)))
(declare-const ; |
 a Bool)
(assert (and true ; |
 (= a (not p))))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "plain_unbound_mention_comment_bar_twin",
            r#"(declare-const p Bool)
(assert (let ((y p)) (! y :named a)))
(declare-const ; |
 b Bool)
(assert (and true ; |
 (= b (not p))))
(check-sat)
"#,
            "unknown",
            "sat",
        ),
    ),
];

/// The mention guard read every `|` as opening a quoted symbol, even in a
/// string or a comment, and skipped to the next `|`, so a label mentioned
/// after `"|"` or `; |` was not seen (the review's class B): wrong unsat and
/// wrong sat. The scan now splits at every character that cannot be in a
/// plain symbol and also reads every stretch between two bars. Each twin
/// mentions no guarded label and answers sat in the lanes where the label
/// is guarded only by mention.
#[test]
#[timeout(180_000)]
fn a_label_mention_after_a_bar_in_a_string_or_comment() {
    assert_pairs(A_LABEL_MENTION_AFTER_A_BAR_IN_A_STRING_OR_COMMENT);
}

const A_LABEL_NAMED_TRUE_IS_GUARDED: &[(Case, Case)] = &[(
    (
        "label_named_true",
        r#"(declare-const p Bool)
(assert (or (! p :named true) (not p)))
(assert (not true))
(check-sat)
"#,
        "unknown",
        "unknown",
    ),
    (
        "label_named_true_twin",
        r#"(declare-const p Bool)
(assert (or (! p :named true) (not p)))
(assert (not p))
(check-sat)
"#,
        "unknown",
        "sat",
    ),
)];

/// A label named `true` is bound by z3 4.12.5 and left unbound here; the
/// guard recorded only symbol names, so `(assert (not true))` was not seen
/// as a mention (unsat where z3 4.12.5 answers sat). The twin mentions `p`
/// and answers sat in plain mode; z3 mode withholds every answer after a
/// label it leaves unbound.
#[test]
#[timeout(180_000)]
fn a_label_named_true_is_guarded() {
    assert_pairs(A_LABEL_NAMED_TRUE_IS_GUARDED);
}

const A_COMMAND_THAT_FAILS_TO_PARSE_WITH_A_LABEL: &[(Case, Case)] = &[(
    (
        "preexisting_csa_extra_arg_label",
        r#"(declare-const p Bool)
(declare-const q Bool)
(check-sat-assuming ((! p :named a)) extra)
(assert (! q :named a))
(assert (not q))
(check-sat)
"#,
        "unknown",
        "unknown",
    ),
    (
        "preexisting_csa_extra_arg_label_twin",
        r#"(declare-const p Bool)
(declare-const q Bool)
(echo "p" extra)
(assert (! q :named a))
(assert (not p))
(check-sat)
"#,
        "sat",
        "sat",
    ),
)];

/// z3 answers `(check-sat-assuming ((! p :named a)) extra)` and binds `a`;
/// ay cannot parse it, so it never saw the label and accepted a later
/// `(! q :named a)` that z3 rejects (unsat where z3 answers sat). Unparsed
/// text holding `:named` now withholds the later answers. The twin's
/// unparsed command has no label. It is not a query either: a dropped query
/// withholds the later answers too, since z3 may have answered it.
#[test]
#[timeout(180_000)]
fn a_command_that_fails_to_parse_with_a_label() {
    assert_pairs(A_COMMAND_THAT_FAILS_TO_PARSE_WITH_A_LABEL);
}

const Z3_MODE_REJECTS_WHAT_Z3_4_12_5_REJECTS: &[(Case, Case)] = &[
    (
        (
            "divisible_late_option",
            r#"(declare-const x Int)
(set-option :smtlib2_compliant true)
(assert (and ((_ divisible 2) x) (= x 1)))
(check-sat)
"#,
            "unknown",
            "unsat",
        ),
        (
            "divisible_late_option_twin",
            r#"(set-option :smtlib2_compliant true)
(declare-const x Int)
(assert (and ((_ divisible 2) x) (= x 2)))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "min_builtin",
            r#"(declare-const x Int)
(assert (= (min x 3) 5))
(check-sat)
"#,
            "unknown",
            "unsat",
        ),
        (
            "min_builtin_twin",
            r#"(declare-fun min (Int Int) Int)
(declare-const x Int)
(assert (= (min x 3) 5))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "string_arith",
            r#"(declare-const x Int)
(declare-const s String)
(assert (and (< x s) (= x 1)))
(assert (= x 0))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "string_arith_twin",
            r#"(declare-const x Int)
(declare-const s String)
(assert (and (< x (str.len s)) (= x 1)))
(assert (= (str.len s) 2))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "seq_mixed",
            r#"(declare-const q (Seq Int))
(declare-const s String)
(assert (= (seq.len (seq.++ q s)) 5))
(assert (= q (as seq.empty (Seq Int))))
(assert (= s ""))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "seq_mixed_twin",
            r#"(declare-const q (Seq Int))
(declare-const s (Seq Int))
(assert (= (seq.len (seq.++ q s)) 5))
(assert (= q (as seq.empty (Seq Int))))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "map_sort",
            r#"(declare-const m (Map Int Int))
(assert (distinct m m))
(check-sat)
"#,
            "unknown",
            "unsat",
        ),
        (
            "map_sort_twin",
            r#"(declare-const m (Array Int Int))
(assert (= m m))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
];

/// Constructs z3 4.12.5 rejects and z3 mode accepted, with no label: a
/// late `:smtlib2_compliant` (z3 reads it as its session starts), an
/// operator it does not know, a String operand of arithmetic, a String
/// beside a `(Seq Int)` and a sort it does not know. z3 drops the assertion
/// and answers sat; a rejected assertion withholds a later sat. Plain mode
/// keeps its own reading of the late option, `min` and `Map` (unsat on an
/// unsat formula) and rejects the String operand and the mixed sequence, as
/// every mode does. The twins are well-sorted for z3 4.12.5, and the `min`
/// twin declares `min` itself.
#[test]
#[timeout(180_000)]
fn z3_mode_rejects_what_z3_4_12_5_rejects() {
    assert_pairs(Z3_MODE_REJECTS_WHAT_Z3_4_12_5_REJECTS);
}
