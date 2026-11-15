// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Syntactic constructs this frontend read with a meaning and z3 rejects or
//! reads otherwise: a nullary symbol in parentheses, a bound variable applied
//! to arguments, and `match` cases whose bodies differ in sort. Each kept an
//! assertion z3 drops, which gave wrong `unsat` answers in every mode, and,
//! beside a label in an untaken `ite` branch, bound that label as if z3 had
//! kept the assertion. Every mode now rejects them; a label in a subterm
//! elaboration passes over is trusted only under `--z3-mode` when the whole
//! assertion is in the vouched fragment. The CLI tests pin the answers.

use super::*;

const PRELUDE: &str = "(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))\
     (declare-fun g (Int) Int)(define-fun dc () Int 3)(declare-const d D)\
     (declare-const p Bool)(declare-const q Bool)(declare-const x Int)\
     (declare-const r Real)(declare-const s String)(declare-const a (Array Int Int))";

/// Whether the last command of `PRELUDE` + `input` is accepted, under
/// `--z3-mode` (`z3`) or not.
fn accepted(z3: bool, input: &str) -> bool {
    let mut ctx = Context::new();
    ctx.set_z3_mode(z3);
    let commands = parse(&format!("{PRELUDE}{input}")).unwrap();
    let (last, rest) = commands.split_last().unwrap();
    for cmd in rest {
        ctx.process_command(cmd).unwrap();
    }
    ctx.process_command(last).is_ok()
}

/// The last command's result and label outcome, under `--z3-mode` (`z3`) or
/// not.
fn last_outcome(z3: bool, input: &str) -> (bool, Option<LabelFailure>) {
    let mut ctx = Context::new();
    ctx.set_z3_mode(z3);
    let commands = parse(&format!("{PRELUDE}{input}")).unwrap();
    let mut outcome = (true, None);
    for cmd in &commands {
        let ok = ctx.process_command(cmd).is_ok();
        outcome = (ok, ctx.take_label_failure());
    }
    outcome
}

/// `(x)` applies `x` to no arguments: z3 rejects it ("invalid function
/// application, arguments missing"), whatever `x` is, and so does the parser.
#[test]
fn a_nullary_symbol_in_parentheses_does_not_parse() {
    for term in [
        "(= (x) 1)",
        "(= (nil) d)",
        "(= (dc) 3)",
        "(str.in_re s (re.allchar))",
        "(str.in_re s (re.none))",
        "(ite false (! p :named l) (= (x) 1))",
        "(match d (((mk z) (= (fst (mk z)) 1)) (nil (p))))",
    ] {
        let script = format!("{PRELUDE}(assert {term})");
        let error = parse(&script).expect_err(term);
        assert!(
            error
                .to_string()
                .contains("invalid function application, arguments missing"),
            "{term}: {error}"
        );
    }
    assert!(parse(&format!("{PRELUDE}(assert (= x 1))")).is_ok());
    assert!(parse(&format!("{PRELUDE}(assert (= (as nil D) d))")).is_ok());
}

/// A `let`, quantifier, `match` or parameter variable shadows every function
/// of its name: z3 reads `(g 1)` as `select` on the variable, an error unless
/// it is an array, and `(as x Int)` as the variable. Resolving the global
/// gave the term another meaning.
#[test]
fn a_bound_variable_applied_to_arguments_is_rejected() {
    for command in [
        "(assert (let ((g 0)) (= (g 1) 1)))",
        "(assert (let ((g a)) (= (g 1) 5)))",
        "(assert (forall ((g Int)) (= (g 1) 1)))",
        "(assert (exists ((g (Array Int Int))) (= (g 1) 1)))",
        "(assert (let ((+ 1)) (= (+ 1 1) 2)))",
        "(assert (match d (((mk g) (= (g 1) 1)) (nil true))))",
        "(assert (match d ((g (= (g 1) 1)))))",
        "(assert (ite false (let ((g 0)) (= (g 1) 1)) true))",
        "(assert (let ((g 0)) (ite true true (= (g 1) 1))))",
        "(define-fun h ((g Int)) Int (g 1))",
        // Under a sort ascription z3 reads the variable too.
        "(assert (let ((g a)) (= ((as g Int) 1) 5)))",
        "(assert (let ((p 0)) ((as p Bool) 1)))",
        "(assert (let ((x 5)) (= (as x Int) 5)))",
        "(assert (forall ((x Int)) (= (as x Int) x)))",
    ] {
        assert!(!accepted(true, command), "{command}");
        assert!(!accepted(false, command), "{command}");
    }
    for command in [
        "(assert (= (g 1) 1))",
        "(assert (let ((v 0)) (= (g v) 1)))",
        "(assert (let ((g a)) (= (select g 1) 5)))",
        "(assert (forall ((v Int)) (= (g v) (g v))))",
        "(assert (= ((as g Int) 1) 1))",
        "(assert (let ((v 5)) (= (as x Int) v)))",
    ] {
        assert!(accepted(true, command), "{command}");
        assert!(accepted(false, command), "{command}");
    }
}

/// Every case body of a `match` has one sort. z3 4.12.5 rejects a Bool body
/// beside an Int one; z3 joins an Int and a Real, which is not modeled.
#[test]
fn match_cases_with_bodies_of_different_sorts_are_rejected() {
    for term in [
        "(match d (((mk z) true) (nil x)))",
        "(match d (((mk z) x) (nil p)))",
        "(= 1.0 (match d (((mk z) z) (nil r))))",
        "(ite false (match d (((mk z) true) (nil x))) true)",
        "(match (mk 1) (((mk z) true) (nil x)))",
    ] {
        let command = format!("(assert {term})");
        assert!(!accepted(true, &command), "{term}");
        assert!(!accepted(false, &command), "{term}");
    }
    for term in [
        "(match d (((mk z) true) (nil p)))",
        "(= x (match d (((mk z) z) (nil 0))))",
    ] {
        let command = format!("(assert {term})");
        assert!(accepted(true, &command), "{term}");
        assert!(accepted(false, &command), "{term}");
    }
}

/// A label in an untaken `ite` branch or an unused `let` value is read in a
/// scratch copy. Its binding is trusted only under `--z3-mode`, and only when
/// the vouched walk reads the whole assertion: z3 may otherwise reject the
/// assertion at a construct this frontend accepts and keep the label alone.
#[test]
fn a_skipped_label_is_trusted_only_in_a_vouched_assertion() {
    let vouched = "(assert (ite false (! p :named l) (= x 1)))";
    assert_eq!(last_outcome(true, vouched), (true, None));
    assert_eq!(
        last_outcome(false, vouched),
        (true, Some(LabelFailure::Diverged))
    );
    for command in [
        // A string operator is outside the vouched fragment.
        "(assert (ite false (! p :named l) (= (str.len s) 1)))",
        "(assert (ite true (= (str.len s) 1) (! p :named l)))",
        "(assert (and (= (str.len s) 1) (ite false (! p :named l) true)))",
        "(assert (let ((v (! p :named l))) (= (str.len s) 1)))",
        // A match is outside it too.
        "(assert (ite false (! p :named l) (match d (((mk z) true) (nil p)))))",
    ] {
        for z3 in [true, false] {
            assert_eq!(
                last_outcome(z3, command),
                (true, Some(LabelFailure::Diverged)),
                "z3 mode {z3}: {command}"
            );
        }
    }
    // A label taken by elaboration keeps the reach walk's outcome.
    let taken = "(assert (and (! p :named l) (= (str.len s) 1)))";
    assert_eq!(last_outcome(true, taken), (true, None));
}

/// A rejected assertion with a label from a skipped subterm keeps z3's exact
/// outcome under `--z3-mode`, where the walk vouches for every subterm before
/// the rejecting label. Plain mode's dialect leaves it unknown.
#[test]
fn a_skipped_label_rejection_is_exact_only_in_z3_mode() {
    let command = "(assert (ite false (! p :named l) (! q :named l)))";
    assert_eq!(
        last_outcome(true, command),
        (false, Some(LabelFailure::Exact))
    );
    assert_eq!(
        last_outcome(false, command),
        (false, Some(LabelFailure::Diverged))
    );
}

/// A `:pattern` or `:no-pattern` term is read in the scope of the term it
/// annotates, so a `let` name used only there means the `let` value, as in
/// z3. The liveness scan skipped attribute values, left such a binding
/// unbound, and the pattern read the global of the same name: an applied
/// `let` name kept an assertion z3 rejects.
#[test]
fn a_let_name_used_only_in_a_pattern_is_the_let_value() {
    for command in [
        "(assert (let ((g 0)) (forall ((v Int)) (! (> v 0) :pattern ((g v))))))",
        "(assert (let ((g 0)) (forall ((v Int)) (! (> v 0) :pattern ((+ (g v) 1))))))",
        "(assert (let ((g 0)) (forall ((v Int)) (! (> v 0) :no-pattern (g v)))))",
        "(assert (let ((g 0)) (let ((k 1)) (forall ((v Int)) (! (> v k) :pattern ((g v)))))))",
    ] {
        assert!(!accepted(true, command), "{command}");
        assert!(!accepted(false, command), "{command}");
    }
    for command in [
        "(assert (let ((k a)) (forall ((v Int)) (! (> v 0) :pattern ((select k v))))))",
        "(assert (let ((k 0)) (forall ((v Int)) (! (> v 0) :pattern ((g (+ v k)))))))",
        "(assert (let ((v 0)) (forall ((v Int)) (! (> v 0) :pattern ((g v))))))",
    ] {
        assert!(accepted(true, command), "{command}");
        assert!(accepted(false, command), "{command}");
    }
}
