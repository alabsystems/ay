// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repros from the fourth label-conformance review. On stdin, a line that
//! failed to parse was dropped whole, with every command on it, and the
//! session was tainted only when one of them asserted or declared. A
//! malformed query beside a `define-const`, a `set-option` or a `check-sat`
//! dropped that command silently: ay answered unsat where z3 answers sat, or
//! left a query unanswered. Stdin now reads such a line one command at a
//! time, as file mode reads a file, and a dropped `define-const` or
//! `set-option`, or dropped text that holds more than one command, taints
//! the session. Each repro has a twin that differs in one line. The expected
//! answers are z3 4.12.5's or `unknown`, on stdin and on a file, in z3 mode,
//! plain mode and the default posture.

use ntest::timeout;

use super::label_answer_lanes::{assert_script_pairs_on_every_input, Script};

const A_COMMAND_BESIDE_A_MALFORMED_QUERY: &[(Script, Script)] = &[
    (
        (
            "nullary_parens_get_value_beside_define_const",
            r#"(declare-const p Bool)
(get-value ((p))) (define-const c Int 5)
(define-fun c () Int 6)
(assert (= c 5))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
        (
            "nullary_parens_get_value_beside_define_const_twin",
            r#"(declare-const p Bool)
(get-value ((p))) (define-const c Int 5)
(define-fun c () Int 6)
(assert (= c 6))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "nullary_parens_get_value_beside_global_decls",
            r#"(set-option :global-declarations true) (get-value ((x)))
(declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 5))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
        (
            "nullary_parens_get_value_beside_global_decls_twin",
            r#"(set-option :global-declarations true) (get-value ((x)))
(declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 6))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "nullary_parens_simplify_beside_global_decls",
            r#"(set-option :global-declarations true) (simplify (x))
(declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 5))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
        (
            "nullary_parens_simplify_beside_global_decls_twin",
            r#"(set-option :global-declarations true) (simplify (x))
(declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 6))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "parse_error_beside_define_const",
            r#"(declare-const p Bool)
(get-value ((1 2))) (define-const c Int 5)
(define-fun c () Int 6)
(assert (= c 5))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
        (
            "parse_error_beside_define_const_twin",
            r#"(declare-const p Bool)
(get-value ((1 2))) (define-const c Int 5)
(define-fun c () Int 6)
(assert (= c 6))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "parse_error_beside_global_decls",
            r#"(set-option :global-declarations true) (simplify (true))
(declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 5))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
        (
            "parse_error_beside_global_decls_twin",
            r#"(set-option :global-declarations true) (simplify (true))
(declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 6))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "assert_beside_parse_error",
            r#"(declare-const p Bool)
(assert (not p)) (get-value ((1 2)))
(assert p)
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
        (
            "assert_beside_parse_error_twin",
            r#"(declare-const p Bool)
(assert (not p)) (get-value ((1 2)))
(assert (not p))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
];

/// Every well-formed command on a line with a malformed query runs, as z3
/// runs it: the `define-const` keeps `c` at 5 and the option keeps `d`
/// through the `pop`, so the later definitions fail. Dropping the line read
/// `c` and `d` as 6.
#[test]
#[timeout(300_000)]
fn a_command_beside_a_malformed_query_runs() {
    assert_script_pairs_on_every_input(A_COMMAND_BESIDE_A_MALFORMED_QUERY);
}

const A_CHECK_SAT_BESIDE_A_FAILED_COMMAND: &[(Script, Script)] = &[
    (
        (
            "nullary_parens_get_value_beside_check_sat",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert q)
(get-value ((p))) (check-sat)
(assert (not q))
(check-sat)
"#,
            &["sat", "unsat"],
            &["sat", "unsat"],
        ),
        (
            "nullary_parens_get_value_beside_check_sat_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert q)
(get-value ((p))) (check-sat)
(assert (not p))
(check-sat)
"#,
            &["sat", "sat"],
            &["sat", "sat"],
        ),
    ),
    (
        (
            "unknown_command_beside_check_sat",
            r#"(declare-const p Bool)
(assert p)
(frobnicate) (check-sat)
(assert (not p))
(check-sat)
"#,
            &["sat", "unsat"],
            &["sat", "unsat"],
        ),
        (
            "unknown_command_beside_check_sat_twin",
            r#"(declare-const p Bool)
(assert p)
(frobnicate) (check-sat)
(assert p)
(check-sat)
"#,
            &["sat", "sat"],
            &["sat", "sat"],
        ),
    ),
];

/// A `check-sat` on a line with a failed command is answered, so a reader
/// that pairs answers with queries in order reads each one right. The
/// dropped line left the first query unanswered, and the second query's
/// unsat was read as the first one's.
#[test]
#[timeout(300_000)]
fn a_check_sat_beside_a_failed_command_is_answered() {
    assert_script_pairs_on_every_input(A_CHECK_SAT_BESIDE_A_FAILED_COMMAND);
}

const A_DROPPED_DEFINITION_OR_OPTION: &[(Script, Script)] = &[
    (
        (
            "malformed_define_const_beside_a_declaration",
            r#"(declare-const p Bool)
(define-const c Int (p)) (declare-const y Int)
(define-fun c () Int 6)
(assert (= c 6))
(assert (= y 1))
(check-sat)
"#,
            &["unknown"],
            &["unknown"],
        ),
        (
            "malformed_define_const_beside_a_declaration_twin",
            r#"(declare-const p Bool)
(define-const c Int 5) (declare-const y Int)
(define-fun c () Int 6)
(assert (= c 5))
(assert (= y 1))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "set_option_with_an_extra_value",
            r#"(set-option :global-declarations true false) (declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 6))
(check-sat)
"#,
            &["unknown"],
            &["unknown"],
        ),
        (
            "set_option_with_an_extra_value_twin",
            r#"(set-option :global-declarations false) (declare-const p Bool)
(push)
(define-fun d () Int 5)
(pop)
(define-fun d () Int 6)
(assert (= d 6))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
];

/// A dropped `define-const` or `set-option` taints the session, in file
/// mode too. z3 4.12.5 sets `:global-declarations` before it rejects the
/// extra value, so `d` stays 5 and z3 answers unsat; ay dropped the option
/// and answered sat on a file.
#[test]
#[timeout(300_000)]
fn a_dropped_definition_or_option_withholds_the_answer() {
    assert_script_pairs_on_every_input(A_DROPPED_DEFINITION_OR_OPTION);
}

const HORN_LINES_WITH_A_FAILED_COMMAND: &[(Script, Script)] = &[
    (
        (
            "horn_rule_beside_a_malformed_query",
            r#"(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) false))) (get-value ((1 2)))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
        (
            "horn_rule_beside_a_malformed_query_twin",
            r#"(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (>= x 0)))) (get-value ((1 2)))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "horn_malformed_rule_beside_a_declaration",
            r#"(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (p)))) (declare-fun Q (Int) Bool)
(check-sat)
"#,
            &["unknown"],
            &["unknown"],
        ),
        (
            "horn_malformed_rule_beside_a_declaration_twin",
            r#"(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (>= x 0)))) (declare-fun Q (Int) Bool)
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
];

/// A streamed HORN session keeps a rule written beside a malformed query,
/// and answers unknown after it drops a rule, as the executor does.
#[test]
#[timeout(300_000)]
fn horn_lines_with_a_failed_command() {
    assert_script_pairs_on_every_input(HORN_LINES_WITH_A_FAILED_COMMAND);
}

const A_STRAY_TOKEN_BEFORE_A_LABEL: &[(Script, Script)] = &[
    (
        (
            "stray_parens_on_their_own_lines",
            r#"(declare-const p Bool)
)
(declare-const q Bool)
)
(assert (let ((v p)) (! v :named L)))
(define-fun L () Bool false)
(assert L)
(check-sat)
(declare-const r Bool)
(declare-const s Bool)
"#,
            &["unknown"],
            &["unknown"],
        ),
        (
            "stray_parens_on_their_own_lines_twin",
            r#"(declare-const p Bool)
)
(declare-const q Bool)
)
(assert (let ((v p)) v))
(define-fun L () Bool false)
(assert L)
(check-sat)
(declare-const r Bool)
(declare-const s Bool)
"#,
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "stray_parens_on_one_line",
            r#"(declare-const p Bool)
) (declare-const q Bool) ) (assert (let ((v p)) (! v :named L))) (define-fun L () Bool false) (assert L) (check-sat) (declare-const r Bool) (declare-const s Bool)
"#,
            &["unknown"],
            &["unknown"],
        ),
        (
            "stray_parens_on_one_line_twin",
            r#"(declare-const p Bool)
) (declare-const q Bool) ) (assert (let ((v p)) v)) (define-fun L () Bool false) (assert L) (check-sat) (declare-const r Bool) (declare-const s Bool)
"#,
            &["unsat"],
            &["unsat"],
        ),
    ),
];

/// z3 binds `L` to `p` and rejects the later `define-fun L`, so it answers
/// sat. A label over a `let` name is left unbound here, and a later command
/// that mentions it withholds the answers. Each command's text was the
/// balanced chunk at its index, which a stray `)` shifts: the `define-fun`
/// and the `assert` were checked against later commands' text, so plain
/// mode on a file answered unsat. Each command now carries the text it was
/// read from.
#[test]
#[timeout(300_000)]
fn a_stray_token_does_not_shift_a_command_text() {
    assert_script_pairs_on_every_input(A_STRAY_TOKEN_BEFORE_A_LABEL);
}
