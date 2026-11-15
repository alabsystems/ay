// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repros from the fifth label-conformance review for commands ay rejects
//! and z3 runs, or answers differently:
//!
//! - a command named by a quoted symbol, `(|pop| 1 extra)`, was dropped with
//!   no taint, because its keyword was compared as written; z3 runs it as a
//!   pop before it reports the extra argument;
//! - a `check-sat-assuming` z3 rejects printed the error and `unknown`,
//!   where z3 prints only the error, so every later answer was read against
//!   the query before it;
//! - a query dropped for a parse error gave no answer, where z3 may answer
//!   it, which moves every later answer the other way;
//! - plain mode takes a `:global-declarations` change at any point, where
//!   z3 refuses it once its session has started.
//!
//! Each repro has a twin that differs in one line. The expected answers are
//! z3 4.12.5's or `unknown`, on stdin and on a file, in z3 mode, plain mode
//! and the default posture.

use ntest::timeout;

use super::label_answer_lanes::{assert_script_pairs_on_every_input, Script};

const A_QUOTED_COMMAND_KEYWORD: &[(Script, Script)] = &[
    (
        (
            "quoted_pop_with_an_extra_argument",
            "(declare-const p Bool)\n(push 1)\n(assert false)\n(|pop| 1 extra)\n(check-sat)\n",
            &["unknown"],
            &["unknown"],
        ),
        (
            "quoted_pop_with_an_extra_argument_twin",
            "(declare-const p Bool)\n(push 1)\n(assert false)\n(|pop| 1)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "quoted_assert_with_an_extra_argument",
            "(declare-const p Bool)\n(|assert| false extra)\n(check-sat)\n",
            &["unknown"],
            &["unknown"],
        ),
        (
            "quoted_assert_with_an_extra_argument_twin",
            "(declare-const p Bool)\n(|assert| false)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "quoted_set_option_with_an_extra_value",
            "(|set-option| :global-declarations true false)\n(push 1)\n(define-fun d () Int 5)\n(pop 1)\n(define-fun d () Int 6)\n(assert (= d 5))\n(check-sat)\n",
            &["unknown"],
            &["unknown"],
        ),
        (
            "quoted_set_option_with_an_extra_value_twin",
            "(|set-option| :global-declarations false)\n(push 1)\n(define-fun d () Int 5)\n(pop 1)\n(define-fun d () Int 6)\n(assert (= d 5))\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
];

/// A dropped command named by a quoted symbol taints the session like the
/// same command written plainly: z3 pops before it reports `extra` (sat),
/// asserts `false` (unsat) and keeps `d` through the pop (sat).
#[test]
#[timeout(300_000)]
fn a_dropped_command_with_a_quoted_keyword_withholds_the_answer() {
    assert_script_pairs_on_every_input(A_QUOTED_COMMAND_KEYWORD);
}

const A_CHECK_SAT_ASSUMING_Z3_REJECTS: &[(Script, Script)] = &[
    (
        (
            "check_sat_assuming_an_undefined_name",
            "(declare-const p Bool)\n(check-sat-assuming (q))\n(assert (not p))\n(check-sat)\n",
            &["unknown"],
            &["unknown", "unknown"],
        ),
        (
            "check_sat_assuming_an_undefined_name_twin",
            "(declare-const p Bool)\n(check-sat-assuming (p))\n(assert (not p))\n(check-sat)\n",
            &["sat", "sat"],
            &["sat", "sat"],
        ),
    ),
    (
        (
            "check_sat_assuming_a_non_boolean",
            "(declare-const x Int)\n(check-sat-assuming (x))\n(assert false)\n(check-sat)\n",
            &["unsat"],
            &["unknown", "unknown"],
        ),
        (
            "check_sat_assuming_a_non_boolean_twin",
            "(declare-const x Int)\n(check-sat-assuming ((> x 0)))\n(assert false)\n(check-sat)\n",
            &["sat", "unsat"],
            &["sat", "unsat"],
        ),
    ),
];

/// Under `--z3-mode` a `check-sat-assuming` that z3 rejects gets the error
/// and no answer, as in z3, which answers the second query alone (sat,
/// unsat). After an undefined name the later answers are withheld, in case
/// z3 knows the name and answered the query. Plain mode answers every
/// query, so it withholds the answers after one z3 may leave unanswered.
#[test]
#[timeout(300_000)]
fn a_check_sat_assuming_z3_rejects_gets_no_answer_in_z3_mode() {
    assert_script_pairs_on_every_input(A_CHECK_SAT_ASSUMING_Z3_REJECTS);
}

const A_DROPPED_QUERY: &[(Script, Script)] = &[
    (
        (
            "check_sat_assuming_with_an_extra_argument",
            "(declare-const p Bool)\n(check-sat-assuming (p) extra)\n(assert (not p))\n(check-sat)\n(assert p)\n(check-sat)\n",
            &["unknown", "unknown"],
            &["unknown", "unknown"],
        ),
        (
            "check_sat_assuming_with_an_extra_argument_twin",
            "(declare-const p Bool)\n(check-sat-assuming (p))\n(assert (not p))\n(check-sat)\n(assert p)\n(check-sat)\n",
            &["sat", "sat", "unsat"],
            &["sat", "sat", "unsat"],
        ),
    ),
    (
        (
            "check_sat_assuming_without_a_list",
            "(declare-const p Bool)\n(check-sat-assuming p)\n(assert (not p))\n(check-sat)\n(assert p)\n(check-sat)\n",
            &["unknown", "unknown"],
            &["unknown", "unknown"],
        ),
        (
            "check_sat_assuming_without_a_list_twin",
            "(declare-const p Bool)\n(check-sat-assuming (p))\n(assert (not p))\n(check-sat)\n(assert p)\n(check-sat)\n",
            &["sat", "sat", "unsat"],
            &["sat", "sat", "unsat"],
        ),
    ),
];

const OUT_OF_STEP_ACROSS_RESET: &[(Script, Script)] = &[
    (
        (
            "undefined_assumption_before_a_reset",
            "(declare-const p Bool)\n(check-sat-assuming (q))\n(reset)\n(declare-const p Bool)\n(assert (not p))\n(check-sat)\n",
            &["unknown"],
            &["unknown", "unknown"],
        ),
        (
            "undefined_assumption_before_a_reset_twin",
            "(declare-const p Bool)\n(check-sat-assuming (p))\n(reset)\n(declare-const p Bool)\n(assert (not p))\n(check-sat)\n",
            &["sat", "sat"],
            &["sat", "sat"],
        ),
    ),
    (
        (
            "dropped_query_before_a_reset",
            "(declare-const p Bool)\n(check-sat-assuming (p) extra)\n(reset)\n(declare-const p Bool)\n(assert (not p))\n(check-sat)\n",
            &["unknown"],
            &["unknown"],
        ),
        (
            "dropped_query_before_a_reset_twin",
            "(declare-const p Bool)\n(check-sat-assuming (p))\n(reset)\n(declare-const p Bool)\n(assert (not p))\n(check-sat)\n",
            &["sat", "sat"],
            &["sat", "sat"],
        ),
    ),
];

/// A `(reset)` clears the problem but not the offset between ay's answers
/// and z3's, so the answers after a query z3 may have answered differently
/// stay withheld after it. z3 answers the dropped query (sat, sat) and not
/// the undefined assumption (sat).
#[test]
#[timeout(300_000)]
fn answers_out_of_step_stay_withheld_after_a_reset() {
    assert_script_pairs_on_every_input(OUT_OF_STEP_ACROSS_RESET);
}

/// A query dropped for a parse error withholds the later answers. z3
/// answers `(check-sat-assuming (p) extra)` before it reports `extra`
/// (sat, sat, unsat) and gives no answer for `(check-sat-assuming p)` (sat,
/// unsat). Dropped without an answer, the first one moved every later
/// answer onto the query before it: ay's unsat was read as the answer to
/// z3's sat.
#[test]
#[timeout(300_000)]
fn a_dropped_query_withholds_later_answers() {
    assert_script_pairs_on_every_input(A_DROPPED_QUERY);
}

const A_LATE_GLOBAL_DECLARATIONS: &[(Script, Script)] = &[
    (
        (
            "global_declarations_after_a_declaration",
            "(declare-const p Bool)\n(set-option :global-declarations true)\n(push)\n(define-fun d () Int 5)\n(pop)\n(define-fun d () Int 6)\n(assert (= d 5))\n(check-sat)\n",
            &["unsat"],
            &["unknown"],
        ),
        (
            "global_declarations_after_a_declaration_twin",
            "(set-option :global-declarations true)\n(declare-const p Bool)\n(push)\n(define-fun d () Int 5)\n(pop)\n(define-fun d () Int 6)\n(assert (= d 5))\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "global_declarations_after_a_failed_simplify",
            "(simplify (true)) (set-option :global-declarations true)\n(declare-const p Bool)\n(push)\n(define-fun d () Int 5)\n(pop)\n(define-fun d () Int 6)\n(assert (= d 5))\n(check-sat)\n",
            &["unsat"],
            &["unknown"],
        ),
        (
            "global_declarations_after_a_failed_simplify_twin",
            "(set-option :global-declarations true)\n(declare-const p Bool)\n(push)\n(define-fun d () Int 5)\n(pop)\n(define-fun d () Int 6)\n(assert (= d 5))\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
    ),
];

/// z3 refuses `:global-declarations` once its session has started, even by
/// a command it then rejects, so `d` is popped and z3 answers unsat. Plain
/// mode takes the option and withholds its answers instead of answering sat.
#[test]
#[timeout(300_000)]
fn a_late_global_declarations_change_withholds_plain_answers() {
    assert_script_pairs_on_every_input(A_LATE_GLOBAL_DECLARATIONS);
}
