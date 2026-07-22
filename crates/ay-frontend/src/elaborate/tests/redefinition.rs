// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! z3 4.15.4 parity for redefinition/redeclaration collisions
//! ([`Context::redefinition_error`], #P0.3). These pin the exact accept/reject
//! matrix across `declare-const`/`declare-fun` (Declare), `define-fun` (Macro),
//! and `define-fun-rec`/`define-funs-rec` (Recursive) — every reject message is
//! byte-identical to z3's, and every z3-accepted overload returns `None`.
//!
//! The follow-up-commit motivation: the first P0.3 landing guarded only
//! `declare-const`/`declare-fun`, so a `define-fun` that redefined an existing
//! name silently shadowed it (a live wrong verdict — z3 rejects and keeps the
//! original binding, AY answered on the shadow). These tests lock the closed
//! matrix so that regression cannot recur.

use super::*;
use crate::command::{Command, Sort};

/// Build a context by processing every command except the last, then return the
/// `redefinition_error` verdict for the last command (the redefinition under
/// test), using the same `IntroKind` mapping the CLI applies.
fn redef_verdict(input: &str) -> Option<String> {
    let commands = parse(input).unwrap();
    let (last, prefix) = commands.split_last().expect("at least one command");
    let mut ctx = Context::new();
    for cmd in prefix {
        // A prefix command may itself be a (legal) definition; process it.
        let _ = ctx.process_command(cmd);
    }
    let arg_sorts = |params: &[(String, Sort)]| -> Vec<Sort> {
        params.iter().map(|(_, s)| s.clone()).collect()
    };
    match last {
        Command::DeclareConst(name, sort) => {
            ctx.redefinition_error(IntroKind::Declare, name, &[], sort)
        }
        Command::DeclareFun(name, args, ret) => {
            ctx.redefinition_error(IntroKind::Declare, name, args, ret)
        }
        Command::DefineFun(name, params, ret, _) => {
            ctx.redefinition_error(IntroKind::Macro, name, &arg_sorts(params), ret)
        }
        Command::DefineFunRec(name, params, ret, _) => {
            ctx.redefinition_error(IntroKind::Recursive, name, &arg_sorts(params), ret)
        }
        Command::DefineFunsRec(decls, _) => decls.iter().find_map(|(name, params, ret)| {
            ctx.redefinition_error(IntroKind::Recursive, name, &arg_sorts(params), ret)
        }),
        other => panic!("last command is not a (re)definition: {other:?}"),
    }
}

fn assert_reject(input: &str, expected_msg: &str) {
    assert_eq!(
        redef_verdict(input).as_deref(),
        Some(expected_msg),
        "expected z3-parity rejection for:\n{input}"
    );
}

fn assert_accept(input: &str) {
    assert_eq!(
        redef_verdict(input),
        None,
        "z3 accepts this overload; AY must not reject:\n{input}"
    );
}

// --- Macro (define-fun) on the incoming side: the class the first landing missed ---

#[test]
fn macro_after_macro_same_domain_rejects() {
    // W1: `named expression already defined` (result sort ignored for macros).
    assert_reject(
        "(define-fun g () Int 1)(define-fun g () Int 2)",
        "named expression already defined",
    );
}

#[test]
fn macro_after_macro_nary_rejects() {
    // W3.
    assert_reject(
        "(define-fun h ((x Int)) Int x)(define-fun h ((x Int)) Int (+ x 1))",
        "named expression already defined",
    );
}

#[test]
fn macro_after_macro_differing_result_sort_still_rejects() {
    // Macros are keyed by name+domain only; a differing result sort collides.
    assert_reject(
        "(define-fun g () Int 1)(define-fun g () Bool true)",
        "named expression already defined",
    );
}

#[test]
fn macro_after_declare_const_rejects() {
    // W2.
    assert_reject(
        "(declare-const g Int)(define-fun g () Int 2)",
        "invalid named expression, declaration already defined with this name g",
    );
}

#[test]
fn macro_after_declare_fun_rejects() {
    assert_reject(
        "(declare-fun f (Int) Int)(define-fun f ((y Int)) Int 99)",
        "invalid named expression, declaration already defined with this name f",
    );
}

#[test]
fn macro_after_declare_const_differing_result_sort_accepts() {
    // A declare overloads on the full signature; a macro with a different
    // result sort does not collide with it.
    assert_accept("(declare-const g Int)(define-fun g () Bool true)");
}

#[test]
fn macro_after_recfun_same_signature_rejects() {
    assert_reject(
        "(define-fun-rec g () Int 1)(define-fun g () Int 2)",
        "invalid named expression, declaration already defined with this name g",
    );
}

#[test]
fn macro_overload_by_arity_accepts() {
    assert_accept("(define-fun g () Int 1)(define-fun g ((x Int)) Int 2)");
}

// --- Recursive (define-fun-rec / define-funs-rec) on the incoming side ---

#[test]
fn recfun_after_recfun_same_signature_rejects() {
    assert_reject(
        "(define-fun-rec g () Int 1)(define-fun-rec g () Int 2)",
        "invalid declaration, constant 'g' (with the given signature) already declared",
    );
}

#[test]
fn funs_rec_after_funs_rec_rejects() {
    assert_reject(
        "(define-funs-rec ((g () Int)) (1))(define-funs-rec ((g () Int)) (2))",
        "invalid declaration, constant 'g' (with the given signature) already declared",
    );
}

#[test]
fn recfun_after_recfun_differing_result_sort_accepts() {
    // Recfuns overload on the full signature (unlike plain macros).
    assert_accept("(define-fun-rec g () Int 1)(define-fun-rec g () Bool true)");
}

#[test]
fn recfun_after_macro_rejects() {
    assert_reject(
        "(define-fun g () Int 1)(define-fun-rec g () Int 2)",
        "invalid declaration, named expression already defined with this name g",
    );
}

#[test]
fn recfun_after_declare_accepts() {
    // z3 accepts: the recfun plugin lives in a distinct namespace from decls.
    assert_accept("(declare-const g Int)(define-fun-rec g () Int 2)");
}

// --- Declare (declare-const / declare-fun) on the incoming side ---

#[test]
fn declare_const_after_declare_const_same_signature_rejects() {
    assert_reject(
        "(declare-const g Int)(declare-const g Int)",
        "invalid declaration, constant 'g' (with the given signature) already declared",
    );
}

#[test]
fn declare_fun_after_declare_fun_same_signature_rejects() {
    assert_reject(
        "(declare-fun f (Int) Int)(declare-fun f (Int) Int)",
        "invalid declaration, function 'f' (with the given signature) already declared",
    );
}

#[test]
fn declare_const_after_declare_const_differing_result_sort_accepts() {
    assert_accept("(declare-const g Int)(declare-const g Bool)");
}

#[test]
fn declare_after_macro_rejects() {
    assert_reject(
        "(define-fun g () Int 1)(declare-const g Int)",
        "invalid declaration, named expression already defined with this name g",
    );
}

#[test]
fn declare_after_macro_differing_result_sort_still_rejects() {
    // The existing binding is a macro (name+domain keyed), so the result sort
    // is ignored on the existing side.
    assert_reject(
        "(define-fun g () Int 1)(declare-const g Bool)",
        "invalid declaration, named expression already defined with this name g",
    );
}

#[test]
fn declare_after_recfun_is_not_a_redefinition_error() {
    // z3 accepts it (overload); the CLI fail-closes the pending check-sat to
    // `unknown` separately (AY cannot represent the overload) — but the
    // redefinition gate itself must return `None`, not a spurious error.
    assert_accept("(define-fun-rec g () Int 1)(declare-const g Int)");
}

#[test]
fn declare_fun_overload_by_domain_accepts() {
    assert_accept("(declare-fun f (Int) Int)(declare-fun f (Bool) Int)");
}

// --- A fresh name never collides (fast path). ---

#[test]
fn fresh_name_never_collides() {
    assert_accept("(declare-const a Int)(define-fun b () Int 1)");
    assert_accept("(define-fun g () Int 1)(define-fun h () Int 2)");
}

// --- Scoping: a redefinition after the original is popped is legal again. ---

#[test]
fn macro_redefinition_after_pop_is_legal() {
    assert_accept("(push 1)(define-fun g () Int 1)(pop 1)(define-fun g () Int 2)");
}
