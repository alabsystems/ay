// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! False-UNSAT regression: `str.in_re` of a `str.replace` term against a
//! finite-length regex, and the three cvc5 benchmarks that
//! `differential_qf_s_qf_slia_cvc5_vs_z3` used to exempt as "known false-UNSAT".
//!
//! Every formula here is SATISFIABLE — each carries a hand-checkable witness,
//! and z3 answers `sat` (4.16.0 and cvc5 1.3.4 for the upstream cases, 4.8.12
//! for the reduction family and the N_UNIFY cases). AY may answer `sat` or a
//! fail-closed `unknown`/timeout; `unsat` is a soundness bug.
//!
//! Root cause of the `unsat`: the regex length-set disjointness conflict
//! (ay-strings `check_regex_length_disjoint`) explained `len(x) = n` with the
//! single asserted equality `(= (str.len x) t)` whenever `t` RESOLVED to `n`
//! through its equivalence class, dropping the literals that put the constant
//! there. With `x = str.replace(b, "z", "")` the equality it picked was the
//! axiom `len(replace(..)) = len(sk_rep_res)`, so the learned clause refuted the
//! membership outright.
//!
//! The cvc5 files are gitignored under `reference/cvc5` (reference/SOURCES.md),
//! so the corpus-driven differential test never ran; they are inlined here from
//! cvc5 commit d7d5b948c11d2d83be0212d4a954ef49740ecdab (BSD-3-Clause), with
//! the `; COMMAND-LINE`/`; REQUIRES` driver comments dropped and whitespace
//! compacted.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

/// Per-formula budget. A timeout is `Timeout`, never `Unsat`, so the one-sided
/// assertion below does not depend on the host's load.
const BUDGET_SECS: u64 = 10;

fn assert_not_unsat(name: &str, witness: &str, smt: &str) {
    let outcome = run_executor_smt_with_timeout(smt, BUDGET_SECS)
        .unwrap_or_else(|e| panic!("{name}: executor error: {e}"));
    assert_ne!(
        outcome,
        SolverOutcome::Unsat,
        "{name} is SATISFIABLE ({witness}); the reference solvers named in \
         the module doc answer sat. AY's unsat is a false refutation."
    );
}

/// Minimal shape: membership of a replace term in a one-word union.
#[test]
#[timeout(60_000)]
fn replace_term_in_finite_union_is_not_unsat() {
    assert_not_unsat(
        "replace-in-union",
        "b = \"u\"",
        r#"(set-logic QF_SLIA)
(declare-fun b () String)
(assert (str.in_re (str.replace b "z" "") (re.union (str.to_re "u") re.none)))
(check-sat)"#,
    );
}

/// Both replace branches, each pinned by the guard: no occurrence of the
/// needle (result is `b`) and an occurrence (result drops it).
#[test]
#[timeout(60_000)]
fn replace_term_in_range_under_either_branch_is_not_unsat() {
    for (name, guard, witness) in [
        (
            "no-match branch",
            r#"(not (str.contains b "z"))"#,
            "b = \"u\"",
        ),
        ("match branch", r#"(str.contains b "z")"#, "b = \"zu\""),
    ] {
        let smt = format!(
            r#"(set-logic QF_SLIA)
(declare-fun b () String)
(assert (str.in_re (str.replace b "z" "") (re.range "u" "v")))
(assert {guard})
(check-sat)"#
        );
        assert_not_unsat(name, witness, &smt);
    }
}

/// The integrator's reduction family of issue8481: a replace term in a union
/// of a length-1 and a length-2 word (or the same set spelled with `re.opt` /
/// an empty alternative), under a symbolic or constant needle and a symbolic,
/// constant or empty replacement. `b = "u"` satisfies each one whatever the
/// other variables are (`a = c = "q"`): the needle does not occur.
#[test]
#[timeout(120_000)]
fn replace_term_in_two_length_union_family_is_not_unsat() {
    let u_or_ub = r#"(re.union (str.to_re "u") (str.to_re "ub"))"#;
    for (name, subject, regex) in [
        ("replace b a \"\"", r#"(str.replace b a "")"#, u_or_ub),
        ("replace b \"z\" \"\"", r#"(str.replace b "z" "")"#, u_or_ub),
        ("replace b a c", "(str.replace b a c)", u_or_ub),
        ("replace b a \"x\"", r#"(str.replace b a "x")"#, u_or_ub),
        (
            "re.opt spelling",
            r#"(str.replace b a "")"#,
            r#"(re.++ (str.to_re "u") (re.opt (str.to_re "b")))"#,
        ),
        (
            "empty-alternative spelling",
            r#"(str.replace b a "")"#,
            r#"(re.++ (str.to_re "u") (re.union (str.to_re "b") (str.to_re "")))"#,
        ),
    ] {
        let smt = format!(
            r#"(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert (str.in_re {subject} {regex}))
(check-sat)"#
        );
        assert_not_unsat(name, "b = \"u\", a = c = \"q\"", &smt);
    }
}

/// Same false-UNSAT class, reached through the word-equation core instead of
/// the regex length check: on the `len(x) = 1` branch the NF pass unified
/// `x = "a"` (N_UNIFY) with the input equation as its only reason, dropping
/// the length literals, and the membership conflict on `x = "a"` then refuted
/// the input. The length reaches the core as a decided literal, or through
/// arithmetic and Nelson-Oppen (`len(x) < 2` and `len(x) > 0`); the side
/// constraint that refutes `x = "a"` is a suffix class or a union exclusion.
/// Every formula answered `unsat` at 0071296d4 under the default rigor and
/// `--rigor fast`; z3 4.8.12 answers `sat`.
#[test]
#[timeout(120_000)]
fn length_decided_unify_is_not_unsat() {
    let ends_in_digit = r#"(assert (str.in_re x (re.++ re.all (re.range "0" "9"))))"#;
    let len_1_or_4 = "(assert (or (= (str.len x) 1) (= (str.len x) 4)))";
    for (name, witness, equation, constraints) in [
        (
            "x ++ \"c\" ++ y = \"a\" ++ z ++ \"q\"",
            "x = \"aAB8\", y = \"q\", z = \"AB8c\"",
            r#"(= (str.++ x "c" y) (str.++ "a" z "q"))"#,
            [len_1_or_4, ends_in_digit, ""],
        ),
        (
            "x ++ \"b\" ++ y = \"a\" ++ z ++ \"c\", y non-empty",
            "x = \"aAB8\", y = \"c\", z = \"AB8b\"",
            r#"(= (str.++ x "b" y) (str.++ "a" z "c"))"#,
            [len_1_or_4, ends_in_digit, r#"(assert (not (= y "")))"#],
        ),
        (
            "length through arithmetic: len(x) < 2 or len(x) = 4, len(x) > 0",
            "x = \"aAB8\", y = \"q\", z = \"AB8c\"",
            r#"(= (str.++ x "c" y) (str.++ "a" z "q"))"#,
            [
                "(assert (or (< (str.len x) 2) (= (str.len x) 4)))",
                "(assert (> (str.len x) 0))",
                ends_in_digit,
            ],
        ),
        (
            "x ++ \"ab\" ++ y = \"a\" ++ z ++ \"bc\", x not in a|aq",
            "x = \"aaba\", y = \"c\", z = \"abaa\"",
            r#"(= (str.++ x "ab" y) (str.++ "a" z "bc"))"#,
            [
                len_1_or_4,
                r#"(assert (not (str.in_re x (re.union (str.to_re "a") (str.to_re "aq")))))"#,
                "",
            ],
        ),
    ] {
        let [c1, c2, c3] = constraints;
        let smt = format!(
            r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert {equation})
{c1}
{c2}
{c3}
(check-sat)"#
        );
        assert_not_unsat(name, witness, &smt);
    }
}

/// cvc5 `regress0/strings/issue8481.smt2`.
#[test]
#[timeout(60_000)]
fn cvc5_issue8481_is_not_unsat() {
    assert_not_unsat(
        "issue8481.smt2",
        "a = \"0\", b = \"u\"",
        r#"(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(assert (str.in_re (str.replace b a "") (re.++ (str.to_re "u") (re.union (str.to_re "b") (str.to_re "")))))
(assert (= (str.to_int (str.++ a a)) 0))
(check-sat)"#,
    );
}

/// cvc5 `regress0/strings/issue3497.smt2`.
#[test]
#[timeout(60_000)]
fn cvc5_issue3497_is_not_unsat() {
    assert_not_unsat(
        "issue3497.smt2",
        "x = \"A\", y = \"\"",
        r#"(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.indexof x y 1) (str.len x)))
(assert (str.contains x y))
(check-sat)"#,
    );
}

/// cvc5 `regress1/strings/issue2429-code.smt2`.
#[test]
#[timeout(60_000)]
fn cvc5_issue2429_code_is_not_unsat() {
    assert_not_unsat(
        "issue2429-code.smt2",
        "size1..3 = off1..4 = \"\\u{0}\", size4 = \"\\u{a}\", p1 = \"ANEAA\", \
         p2 = \"BAGIK\": p2_size = 10, p2_off = 0, p3_off = 10",
        r#"(set-logic QF_SLIA)
(set-option :produce-models true)
(set-info :status sat)
(define-fun byte_2_int ((s String)) Int (ite (= (str.len s) 1) (str.to_code s) 256))
(define-fun read_buffer16 ((s1 String) (s2 String)) Int
  (+ (* 256 (byte_2_int s1)) (byte_2_int s2)))
(define-fun read_buffer32 ((s1 String) (s2 String) (s3 String) (s4 String)) Int
  (+ (+ (+ (* 16777216 (byte_2_int s1))
           (*    65536 (byte_2_int s2)))
           (*      256 (byte_2_int s3)))
           (byte_2_int s4)))
(declare-const magic String)
(declare-const p1 String)
(declare-const p2 String)
(declare-const p3 String)
(declare-const size1 String)
(declare-const size2 String)
(declare-const size3 String)
(declare-const size4 String)
(declare-const off1 String)
(declare-const off2 String)
(declare-const off3 String)
(declare-const off4 String)
(assert (= magic "ABCD"))
(assert (= 1 (str.len size1)))
(assert (= 1 (str.len size2)))
(assert (= 1 (str.len size3)))
(assert (= 1 (str.len size4)))
(assert (= 1 (str.len off1)))
(assert (= 1 (str.len off2)))
(assert (= 1 (str.len off3)))
(assert (= 1 (str.len off4)))
(declare-const p3_off Int)
(declare-const before_p3 String)
(assert (= before_p3 (str.++ p1 p2)))
(assert (not (str.contains before_p3 magic)))
(assert (= p3_off (str.len before_p3)))
(declare-const p2_size Int)
(declare-const p2_off Int)
(declare-const p2_min_size Int)
(assert (= p2_size (read_buffer32 size1 size2 size3 size4)))
(assert (= p2_off (read_buffer32 off1 off2 off3 off4)))
(assert (<= (+ p2_size p2_off) p3_off))
(assert (>= p2_size p2_min_size))
(assert (= p2_min_size 10))
(check-sat)"#,
    );
}
