// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Commands the CHC parser does not model fail closed.
//!
//! They used to be skipped as "unknown commands", which changed the problem
//! (found by the 2026-09-29 CHC differential generator, z3 5.1 cross-checked):
//! - `(define-fun c () Int 5)`: every later `c` fell through to the
//!   unknown-symbol fallback and became a fresh, universally quantified Int
//!   variable, so `x < c` guarded nothing and a safe system answered `unsat`;
//! - `(push 1) (assert R) (pop 1)` and `(reset-assertions)`: the retracted
//!   clauses stayed in the problem and a safe system answered `unsat`;
//! - an `assert` after `check-sat`: the one verdict answered the union of both
//!   scripts, not the first `check-sat`.

use super::*;

fn rejected(input: &str, needle: &str) {
    match ChcParser::parse(input) {
        Err(error) => assert!(
            error.to_string().contains(needle),
            "expected a parse error naming `{needle}`, got: {error}"
        ),
        Ok(problem) => panic!(
            "`{needle}` must be rejected, but the input parsed to {} clauses",
            problem.clauses().len()
        ),
    }
}

const HEAD: &str = "(set-logic HORN)\n(declare-fun P (Int) Bool)\n(assert (P 0))\n";
const QUERY: &str = "(assert (forall ((x Int)) (=> (and (P x) (> x 0)) false)))\n";
const STEP: &str = "(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))\n";

#[test]
fn a_define_fun_constant_is_rejected_not_read_as_a_free_variable() {
    rejected(
        "(set-logic HORN)
         (define-fun c () Int 5)
         (declare-fun P (Int) Bool)
         (assert (P 0))
         (assert (forall ((x Int)) (=> (and (P x) (< x c)) (P (+ x 1)))))
         (assert (forall ((x Int)) (=> (and (P x) (> x c)) false)))
         (check-sat)",
        "define-fun",
    );
    for command in ["define-fun-rec", "define-funs-rec", "define-const"] {
        rejected(
            &format!("(set-logic HORN)\n({command} f () Int 1)\n(check-sat)"),
            command,
        );
    }
}

#[test]
fn assertion_stack_commands_are_rejected() {
    rejected(
        &format!("{HEAD}(push 1)\n{STEP}(pop 1)\n{QUERY}(check-sat)\n"),
        "push",
    );
    rejected(
        &format!("{HEAD}{STEP}(reset-assertions)\n{QUERY}(check-sat)\n"),
        "reset-assertions",
    );
    rejected(&format!("{HEAD}{QUERY}(reset)\n(check-sat)\n"), "reset");
    rejected(
        &format!("{HEAD}{QUERY}(check-sat-assuming ())\n"),
        "check-sat-assuming",
    );
}

#[test]
fn an_assert_after_check_sat_is_rejected() {
    rejected(
        &format!("{HEAD}{QUERY}(check-sat)\n{STEP}(check-sat)\n"),
        "after `check-sat`",
    );
}

#[test]
fn the_usual_trailing_commands_still_parse() {
    let problem = ChcParser::parse(&format!(
        "(set-info :status sat)\n{HEAD}{STEP}{QUERY}(check-sat)\n(get-model)\n(check-sat)\n(exit)\n"
    ))
    .expect("check-sat / get-model / exit after the clauses parse");
    assert_eq!(problem.clauses().len(), 3);
}
