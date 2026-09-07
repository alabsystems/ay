// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `define-fun` macro expansion is memoized (`elaborate/macro_memo.rs`). These
//! tests pin BOTH halves of that: the scaling the memo exists for, and the
//! behaviour it must leave exactly as it was.

use super::*;

fn elaborate_all(input: &str) -> (Context, Vec<Result<()>>) {
    let commands = parse(input).expect("parse");
    let mut ctx = Context::new();
    let mut outcomes = Vec::new();
    for cmd in &commands {
        outcomes.push(ctx.process_command(cmd).map(|_| ()));
    }
    (ctx, outcomes)
}

/// A Fibonacci-shaped chain of unary `define-fun`s: no datatypes, no
/// arithmetic. The elaborated result is three nodes wide, but re-elaborating
/// the callee's parse tree at every call site costs `Fib(n)` — the defect this
/// memo fixes. `n = 64` is `Fib(64) ≈ 1.1e13` expansions un-memoized and a few
/// hundred memoized, so the bound below separates the two by many orders of
/// magnitude rather than by a machine-speed factor.
fn fibonacci_define_fun_chain(n: usize) -> String {
    let mut script = String::from(
        "(set-logic QF_UF)\n\
         (declare-fun p (Bool) Bool)\n\
         (declare-const b Bool)\n\
         (define-fun f0 ((x Bool)) Bool (p x))\n\
         (define-fun f1 ((x Bool)) Bool (p (p x)))\n",
    );
    for k in 2..=n {
        script.push_str(&format!(
            "(define-fun f{k} ((x Bool)) Bool (and (f{} x) (f{} x)))\n",
            k - 1,
            k - 2
        ));
    }
    script.push_str(&format!("(assert (f{n} b))\n"));
    script
}

#[test]
fn define_fun_chain_expansion_is_not_exponential() {
    let script = fibonacci_define_fun_chain(64);
    let (sender, receiver) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let (ctx, outcomes) = elaborate_all(&script);
            let ok = outcomes.iter().all(std::result::Result::is_ok);
            // Report the elaborated shape, not the context: it must not cross
            // the channel while the receiver may already have given up.
            let shape = ctx.assertions.first().map(|&root| {
                let mut names = Vec::new();
                collect_var_names(&ctx.terms, root, &mut names);
                (ctx.assertions.len(), names)
            });
            let _ = sender.send((ok, shape));
        })
        .expect("spawn");

    let (ok, shape) = receiver
        .recv_timeout(std::time::Duration::from_secs(60))
        .expect("a 64-link define-fun chain must elaborate; un-memoized it is Fib(64) expansions");
    assert!(ok, "every command must elaborate");
    let (count, names) = shape.expect("one assertion");
    assert_eq!(count, 1);
    // (and (p b) (p (p b))): `and` folds the repeated conjuncts, so the whole
    // chain collapses onto the single declared constant, reached once through
    // each conjunct.
    assert_eq!(names, vec!["b".to_string(), "b".to_string()]);
}

/// The memo is keyed on argument TERMS, never on the use-site environment, so a
/// caller's binder can still not capture a global the body names (the #6812
/// capture-avoidance contract). The second `(f)` here is the one that would be
/// served from the memo.
#[test]
fn memoized_expansion_stays_capture_avoiding() {
    let (ctx, outcomes) = elaborate_all(
        "(declare-const x Int)
         (define-fun f () Int x)
         (assert (= f 11))
         (assert (forall ((x Int)) (= f 11)))",
    );
    for outcome in &outcomes {
        outcome.as_ref().expect("elaborates");
    }
    assert_eq!(ctx.assertions.len(), 2);
    let mut outer = Vec::new();
    collect_var_names(&ctx.terms, ctx.assertions[0], &mut outer);
    let mut under_binder = Vec::new();
    collect_var_names(&ctx.terms, ctx.assertions[1], &mut under_binder);
    // Both occurrences of `f` denote the GLOBAL x — the quantifier's own `x` is
    // a freshly minted variable with a different name.
    assert_eq!(outer, vec!["x".to_string()]);
    assert_eq!(under_binder, vec!["x".to_string()]);
}

/// Two call sites at different argument terms are different keys.
#[test]
fn different_arguments_are_not_shared() {
    let (ctx, outcomes) = elaborate_all(
        "(declare-const a Int)
         (declare-const c Int)
         (define-fun double ((v Int)) Int (+ v v))
         (assert (= (double a) 0))
         (assert (= (double c) 0))
         (assert (= (double a) 0))",
    );
    for outcome in &outcomes {
        outcome.as_ref().expect("elaborates");
    }
    assert_eq!(ctx.assertions.len(), 3);
    assert_ne!(
        ctx.assertions[0], ctx.assertions[1],
        "different arguments must elaborate to different terms"
    );
    assert_eq!(
        ctx.assertions[0], ctx.assertions[2],
        "the same argument must intern to the same term"
    );
}

/// A body whose expansion mints a fresh variable per occurrence — here a
/// quantifier binder — must NOT be shared: the memo records only expansions
/// that left the variable counter untouched.
#[test]
fn bodies_that_mint_fresh_variables_are_not_shared() {
    let (ctx, outcomes) = elaborate_all(
        "(declare-const a Int)
         (define-fun some_larger ((v Int)) Bool (exists ((w Int)) (> w v)))
         (assert (some_larger a))
         (assert (some_larger a))",
    );
    for outcome in &outcomes {
        outcome.as_ref().expect("elaborates");
    }
    assert_eq!(ctx.assertions.len(), 2);
    assert_ne!(
        ctx.assertions[0], ctx.assertions[1],
        "each occurrence must keep its own freshly minted binder"
    );
}

/// A binder INSIDE the body that shadows a caller-visible name still binds the
/// body's own occurrence, at the memoized call site as at the first one.
#[test]
fn body_binder_shadowing_a_caller_name_is_unchanged() {
    let (ctx, outcomes) = elaborate_all(
        "(declare-const w Int)
         (define-fun shadowing ((v Int)) Int (let ((w 7)) (+ w v)))
         (assert (= (shadowing w) 0))
         (assert (= (shadowing w) 0))",
    );
    for outcome in &outcomes {
        outcome.as_ref().expect("elaborates");
    }
    assert_eq!(ctx.assertions.len(), 2);
    assert_eq!(ctx.assertions[0], ctx.assertions[1]);
    let mut names = Vec::new();
    collect_var_names(&ctx.terms, ctx.assertions[0], &mut names);
    // Exactly one occurrence of the global `w` — the argument. The body's `w`
    // is the let-bound 7, not the global.
    assert_eq!(names, vec!["w".to_string()]);
}

/// Only SUCCESSFUL expansions are recorded, so an ill-formed application keeps
/// reporting at every call site instead of being answered from a cache.
#[test]
fn ill_formed_applications_report_every_time() {
    let (_ctx, outcomes) = elaborate_all(
        "(declare-const a Int)
         (define-fun unary ((v Int)) Int (+ v 1))
         (assert (= (unary a a) 0))
         (assert (= (unary a) 0))
         (assert (= (unary a a) 0))",
    );
    assert!(outcomes[0].is_ok(), "declare-const");
    assert!(outcomes[1].is_ok(), "define-fun");
    assert!(outcomes[2].is_err(), "first arity error");
    assert!(outcomes[3].is_ok(), "well-formed call in between");
    assert!(outcomes[4].is_err(), "arity error reported again");
}

/// `pop` removes a definition, and the memo must not answer for the
/// replacement. Both scripts below use the SAME call syntax at the same
/// argument term; only the definition in scope differs.
#[test]
fn a_popped_definition_is_not_served_from_the_memo() {
    let (ctx, outcomes) = elaborate_all(
        "(declare-const a Int)
         (push 1)
         (define-fun f ((v Int)) Int (+ v 1))
         (assert (= (f a) 0))
         (pop 1)
         (define-fun f ((v Int)) Int (+ v 2))
         (assert (= (f a) 0))
         (assert (= (+ a 2) 0))
         (assert (= (+ a 1) 0))",
    );
    for outcome in &outcomes {
        outcome.as_ref().expect("elaborates");
    }
    // The pushed assertion is gone; the surviving call must have expanded
    // through the REPLACEMENT body. Hash-consing makes the two controls exact.
    assert_eq!(ctx.assertions.len(), 3);
    assert_eq!(
        ctx.assertions[0], ctx.assertions[1],
        "the post-pop definition must expand to `(+ a 2)`"
    );
    assert_ne!(
        ctx.assertions[0], ctx.assertions[2],
        "and must not be answered with the popped `(+ a 1)` body"
    );
}

/// The memo survives a `define-fun` that binds a fresh name — that is what
/// keeps a chain of definitions linear — EXCEPT when the new name is a spelling
/// an earlier expansion resolved as a builtin. `const` is exactly that case:
/// `(as const S)` is the builtin constant-array only while `const` is
/// undeclared, so introducing it must re-derive the earlier body and reproduce
/// the ill-sortedness the un-memoized elaboration reports.
#[test]
fn a_definition_shadowing_a_builtin_spelling_invalidates_the_memo() {
    let (_ctx, outcomes) = elaborate_all(
        "(set-logic QF_ALIA)
         (declare-const i Int)
         (define-fun m () (Array Int Int) ((as const (Array Int Int)) 0))
         (assert (= (select m i) 0))
         (define-fun const ((a Int) (b Int)) Int a)
         (assert (= (select m i) 0))",
    );
    assert!(
        outcomes[3].is_ok(),
        "the builtin const-array reading is fine"
    );
    assert!(outcomes[4].is_ok(), "`const` is user-definable");
    assert!(
        matches!(outcomes[5], Err(ElaborateError::SortMismatch { .. })),
        "`m` must be re-derived against the macro, not served from the memo: {:?}",
        outcomes[5]
    );
}

/// `define-fun-rec` is expanded by the same site and bounded by the same depth
/// guard. A terminating recursion still unrolls; a non-terminating one still
/// hits `RecursionDepthExceeded`, at every call site.
#[test]
fn recursive_definitions_keep_their_depth_guard() {
    let (ctx, outcomes) = elaborate_all(
        "(define-fun-rec fact ((n Int)) Int (ite (= n 0) 1 (* n (fact (- n 1)))))
         (assert (= (fact 3) 6))
         (assert (= (fact 3) 6))",
    );
    for outcome in &outcomes {
        outcome.as_ref().expect("a terminating recursion unrolls");
    }
    assert_eq!(ctx.assertions.len(), 2);
    assert_eq!(ctx.assertions[0], ctx.assertions[1]);

    let (_diverging_ctx, diverging) = elaborate_all(
        "(declare-const a Int)
         (define-fun-rec loop ((n Int)) Int (+ 1 (loop n)))
         (assert (= (loop a) 0))
         (assert (= (loop a) 0))",
    );
    assert!(
        matches!(diverging[2], Err(ElaborateError::RecursionDepthExceeded(_))),
        "first divergent call must be refused: {:?}",
        diverging[2]
    );
    assert!(
        matches!(diverging[3], Err(ElaborateError::RecursionDepthExceeded(_))),
        "and so must the second: {:?}",
        diverging[3]
    );
}

/// The memo skips nested expansions, and each entry records how deep below
/// itself it reached so it is never served where one of those would have hit
/// [`MAX_FUN_EXPANSION_DEPTH`]. The boundary must therefore sit at exactly the
/// same chain length as an un-memoized walk. Measured identical on both sides:
/// `(assert (f999 b))` over `f0 .. f999` elaborates, and one link further the
/// assertion — and only the assertion — is refused.
#[test]
fn the_expansion_depth_boundary_is_unmoved() {
    fn linear_define_fun_chain(n: usize) -> String {
        let mut script = String::from(
            "(set-logic QF_UF)\n\
             (declare-fun p (Bool) Bool)\n\
             (declare-const b Bool)\n\
             (define-fun f0 ((x Bool)) Bool (p x))\n",
        );
        for k in 1..=n {
            script.push_str(&format!(
                "(define-fun f{k} ((x Bool)) Bool (p (f{} x)))\n",
                k - 1
            ));
        }
        script.push_str(&format!("(assert (f{n} b))\n"));
        script
    }

    let (deepest_ok, ok_outcomes) = elaborate_all(&linear_define_fun_chain(999));
    for outcome in &ok_outcomes {
        outcome
            .as_ref()
            .expect("999 links stays inside the expansion limit");
    }
    assert_eq!(deepest_ok.assertions.len(), 1);

    let (_over, over_outcomes) = elaborate_all(&linear_define_fun_chain(1000));
    let refusals: Vec<_> = over_outcomes
        .iter()
        .filter(|outcome| matches!(outcome, Err(ElaborateError::RecursionDepthExceeded(_))))
        .collect();
    assert_eq!(
        refusals.len(),
        1,
        "exactly the definition one link past the limit is refused"
    );
}
