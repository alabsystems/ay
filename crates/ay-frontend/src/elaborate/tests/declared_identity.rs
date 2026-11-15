// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A user declaration under a private core identity (`__ay_overload_N`) is
//! registered with the term store as a declared function: a consumer that
//! reads `__ay*` spellings as interpreted (the CDCL(T) kernel) learns from
//! the store that this one is uninterpreted.

use super::*;

/// The head symbol of every declared application below `root`.
fn heads(ctx: &Context, root: TermId) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(term) {
            if !args.is_empty() && ctx.dt_surface_name(name).is_some() {
                out.push(name.to_string());
            }
        }
        stack.extend(ctx.terms.children(term));
    }
    out
}

fn context(input: &str) -> Context {
    let mut ctx = Context::new();
    for command in &parse(input).expect("script parses") {
        ctx.process_command(command).expect("command elaborates");
    }
    ctx
}

#[test]
fn a_redeclaration_after_pop_is_a_registered_declared_function() {
    let ctx = context(
        "(declare-sort U 0) (declare-fun a () U) (declare-fun b () U) \
         (push 1) (declare-fun f (U) U) (assert (= (f a) b)) (pop 1) \
         (declare-fun f (U U) Bool) (assert (f a b))",
    );
    let last = *ctx.assertions.last().expect("an assertion");
    let heads = heads(&ctx, last);
    assert_eq!(heads.len(), 1, "{heads:?}");
    assert!(heads[0].starts_with(INTERNAL_SYMBOL_PREFIX), "{heads:?}");
    assert!(ctx.terms.is_declared_function(&heads[0]));
    assert!(
        !ctx.terms.is_declared_function("f"),
        "a surface name needs no entry"
    );
}

#[test]
fn a_function_named_like_a_builtin_is_a_registered_declared_function() {
    let ctx = context(
        "(declare-fun abs (Real) Real) (declare-fun x () Real) \
         (assert (> (abs x) 1.0))",
    );
    let heads = heads(&ctx, ctx.assertions[0]);
    assert_eq!(heads.len(), 1, "{heads:?}");
    assert!(heads[0].starts_with(INTERNAL_SYMBOL_PREFIX), "{heads:?}");
    assert!(ctx.terms.is_declared_function(&heads[0]));
}
