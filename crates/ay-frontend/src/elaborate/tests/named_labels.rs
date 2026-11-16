// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `:named` labels in assertions are nullary definitions, as in SMT-LIB and
//! z3: they collide with other names, can be used as terms, and follow the
//! scoping of definitions.

use super::*;

type LabelStep = (Result<()>, Option<LabelFailure>);

/// Process every command, returning each result and the label outcome read
/// after it.
fn run(input: &str) -> (Context, Vec<LabelStep>) {
    let mut ctx = Context::new();
    let results = parse(input)
        .unwrap()
        .iter()
        .map(|cmd| {
            let result = ctx.process_command(cmd).map(|_| ());
            (result, ctx.take_label_failure())
        })
        .collect();
    (ctx, results)
}

fn error_text(result: &Result<()>) -> String {
    result
        .as_ref()
        .err()
        .map(ToString::to_string)
        .unwrap_or_default()
}

#[test]
fn a_label_is_a_definition_usable_as_a_term() {
    let (ctx, results) =
        run("(declare-const x Int)(assert (and (! (> x 0) :named a) a))(assert (not a))");
    assert!(results
        .iter()
        .all(|(result, failure)| result.is_ok() && failure.is_none()));
    assert!(ctx.fun_defs.contains_key("a"));
    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn a_label_collides_as_z3_says() {
    let (_, results) = run("(declare-const x Int)(assert (! (> x 0) :named a))\
         (assert (! (< x 0) :named a))(declare-const a Bool)(define-fun a () Bool true)");
    assert_eq!(
        error_text(&results[2].0),
        "named expression already defined"
    );
    assert_eq!(results[2].1, Some(LabelFailure::Exact));
    assert_eq!(
        error_text(&results[3].0),
        "invalid declaration, named expression already defined with this name a"
    );
    assert_eq!(
        error_text(&results[4].0),
        "named expression already defined"
    );

    let (_, results) =
        run("(declare-const a Bool)(declare-const x Int)(assert (! (> x 0) :named a))");
    assert_eq!(
        error_text(&results[2].0),
        "invalid named expression, declaration already defined with this name a"
    );
    assert_eq!(results[2].1, Some(LabelFailure::Exact));
}

#[test]
fn a_rejected_assertion_keeps_the_labels_before_the_rejection() {
    let (ctx, results) =
        run("(declare-const x Int)(assert (and (! (> x 0) :named a) (! (< x 0) :named a)))");
    assert_eq!(results[1].1, Some(LabelFailure::Exact));
    assert!(ctx.fun_defs.contains_key("a"));
    assert_eq!(ctx.assertions.len(), 0);
}

#[test]
fn a_label_is_scoped_like_a_definition() {
    let (ctx, results) = run(
        "(declare-const x Int)(push)(assert (! (> x 0) :named a))(pop)\
         (assert (! (< x 0) :named a))",
    );
    assert!(results.iter().all(|(result, _)| result.is_ok()));
    assert!(ctx.fun_defs.contains_key("a"));

    let (_, results) = run(
        "(set-option :global-declarations true)(declare-const x Int)(push)\
         (assert (! (> x 0) :named a))(pop)(assert (! (< x 0) :named a))",
    );
    assert_eq!(
        error_text(&results[5].0),
        "named expression already defined"
    );
}

#[test]
fn labels_z3_rejects_or_ay_cannot_bind() {
    let (_, results) = run("(declare-const x Int)(assert (forall ((y Int)) (! (> y 0) :named a)))");
    assert_eq!(
        error_text(&results[1].0),
        "invalid named expression, expression contains free variables"
    );
    assert_eq!(results[1].1, Some(LabelFailure::Exact));

    // z3 binds these; here the assertion is kept with its meaning, the label
    // stays unbound, and the outcome names it.
    for (input, label) in [
        (
            "(declare-const a Int)(declare-const x Int)(assert (! (> x 0) :named a))",
            "a",
        ),
        (
            "(declare-const x Int)(assert (let ((z x)) (! (> z 0) :named a)))",
            "a",
        ),
        (
            "(declare-const x Int)(assert (! (> x 0) :named and))",
            "and",
        ),
        (
            "(declare-const m (Array Int Int))(assert (= (! m :named n) m))",
            "n",
        ),
    ] {
        let (ctx, results) = run(input);
        let (result, failure) = results.last().unwrap();
        assert!(result.is_ok(), "{input}: {}", error_text(result));
        assert_eq!(*failure, Some(LabelFailure::Unbound), "{input}");
        assert_eq!(ctx.unbound_label_names(), [label.to_string()], "{input}");
        assert_eq!(ctx.assertions.len(), 1, "{input}");
        assert!(!ctx.fun_defs.contains_key(label), "{input}");
    }

    // z3 checks the name of a label over a `let`-bound name as it checks any
    // other, and rejects this one.
    let (_, results) = run("(declare-const b Int)(declare-const x Int)\
         (assert (let ((z x)) (= (! z :named b) 0)))");
    let (result, failure) = results.last().unwrap();
    assert_eq!(
        error_text(result),
        "invalid named expression, declaration already defined with this name b"
    );
    assert_eq!(*failure, Some(LabelFailure::Exact));

    // A label left unbound before a rejection: z3 would have bound it, so the
    // context no longer matches z3's and nothing is committed.
    let (ctx, results) = run("(declare-const a Int)(declare-const x Int)\
         (assert (and (! (> x 0) :named a) (! (> x 1) :named b) (! (> x 2) :named b)))");
    let (result, failure) = results.last().unwrap();
    assert!(result.is_err());
    assert_eq!(*failure, Some(LabelFailure::Diverged));
    assert!(!ctx.fun_defs.contains_key("b"));
}

/// z3 binds a label this frontend leaves unbound, so a second label of the
/// same name in the same assertion is z3's "named expression already
/// defined", and z3 drops the assertion. Accepting it here kept an assertion
/// z3 rejects (the review's plain_collision repros, wrong unsat in plain
/// mode). The outcome diverges: the session lacks the first label.
#[test]
fn a_label_left_unbound_collides_with_a_later_one() {
    for input in [
        "(declare-const arr (Array Int Int))\
         (assert (and (= (! arr :named a) arr) (! false :named a)))",
        "(declare-const p Bool)(assert (and (! p :named and) (! false :named and)))",
        "(declare-const p Bool)(declare-const a Int)(assert (and (! p :named a) (! false :named a)))",
        "(declare-const p Bool)(declare-const q Bool)\
         (assert (and (let ((y p)) (! y :named a)) (! q :named a) p))",
        "(declare-const p Bool)(declare-const q Bool)\
         (assert (and (ite true true (let ((y p)) (! y :named a))) (! false :named a)))",
    ] {
        let (ctx, results) = run(input);
        let (result, failure) = results.last().unwrap();
        assert_eq!(error_text(result), "named expression already defined", "{input}");
        assert_eq!(*failure, Some(LabelFailure::Diverged), "{input}");
        assert!(ctx.assertions.is_empty(), "{input}");
    }
}

#[test]
fn a_datatype_member_cannot_take_a_label_name() {
    let (_, results) = run(
        "(declare-const x Int)(assert (! (> x 0) :named a))(declare-datatypes ((D 0)) (((a) (b))))",
    );
    assert_eq!(
        error_text(&results[2].0),
        "invalid declaration, named expression already defined with this name a"
    );
}

#[test]
fn a_quoted_boolean_option_value_is_the_boolean() {
    let (ctx, _) = run("(set-option :global-declarations |true|)");
    assert!(ctx.global_declarations_enabled());
    let (ctx, _) =
        run("(set-option :global-declarations true)(set-option :global-declarations foo)");
    assert!(ctx.global_declarations_enabled());
}
