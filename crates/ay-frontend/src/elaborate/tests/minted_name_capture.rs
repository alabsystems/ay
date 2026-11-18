// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A variable the elaborator mints and a declared symbol never share a core
//! spelling, and alpha sharing does not identify two free variables that are
//! different terms.

use super::*;

fn context(input: &str) -> Context {
    let mut ctx = Context::new();
    for command in &parse(input).expect("script parses") {
        ctx.process_command(command).expect("command elaborates");
    }
    ctx
}

fn bound_term(ctx: &Context, name: &str) -> TermId {
    ctx.symbols
        .get(name)
        .and_then(|info| info.term)
        .unwrap_or_else(|| panic!("'{name}' has no bound term"))
}

fn var_name(ctx: &Context, term: TermId) -> String {
    match ctx.terms.get(term) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("expected a variable, got {other:?}"),
    }
}

fn free_var_terms(ctx: &Context, root: TermId) -> Vec<TermId> {
    fn walk(terms: &TermStore, term: TermId, bound: &mut Vec<String>, out: &mut Vec<TermId>) {
        match terms.get(term) {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if !bound.contains(name) && !out.contains(&term) {
                    out.push(term);
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    walk(terms, arg, bound, out);
                }
            }
            TermData::Not(inner) => walk(terms, *inner, bound, out),
            TermData::Ite(c, t, e) => {
                for branch in [*c, *t, *e] {
                    walk(terms, branch, bound, out);
                }
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                let mark = bound.len();
                bound.extend(vars.iter().map(|(name, _)| name.clone()));
                walk(terms, *body, bound, out);
                bound.truncate(mark);
            }
            other => panic!("unexpected term {other:?}"),
        }
    }
    let mut out = Vec::new();
    walk(&ctx.terms, root, &mut Vec::new(), &mut out);
    out
}

/// The script of hunt probe `binder-n/qs8`: the first assertion's inner
/// quantifier has the outer binder `x_0` free.
const BINDER_THEN_CONSTANT: &str = "(set-logic LIA)\n\
    (assert (forall ((x Int)) (or (< x 1) (> x 1) (forall ((y Int)) (=> (> y x) (> y 0))))))\n\
    (declare-const x_0 Int)\n\
    (assert (forall ((w Int)) (=> (> w x_0) (> w 0))))\n\
    (assert (= x_0 (- 1)))";

#[test]
fn a_constant_declared_after_a_binder_of_its_spelling_takes_a_private_identity() {
    let ctx = context(BINDER_THEN_CONSTANT);
    let user = bound_term(&ctx, "x_0");
    let identity = var_name(&ctx, user);
    assert_ne!(identity, "x_0");
    assert!(identity.starts_with(INTERNAL_SYMBOL_PREFIX), "{identity}");
    assert!(!ctx.is_internal_symbol(&identity), "{identity}");
    assert_eq!(ctx.dt_surface_name(&identity), Some("x_0"));
    let binder = ctx
        .terms
        .find_fresh_var_spelled("x_0")
        .expect("the outer binder is spelled x_0");
    assert_ne!(binder, user);
}

#[test]
fn a_quantifier_over_the_users_constant_is_not_shared_with_one_over_a_binder() {
    let ctx = context(BINDER_THEN_CONSTANT);
    let user = bound_term(&ctx, "x_0");
    assert_eq!(free_var_terms(&ctx, ctx.assertions[1]), vec![user]);
    assert_eq!(
        free_var_terms(&ctx, ctx.assertions[0]),
        Vec::<TermId>::new()
    );
}

#[test]
fn a_quantifier_over_a_constant_is_not_shared_with_one_over_a_formal_of_its_name() {
    let ctx = context(
        "(define-fun h ((x Int)) Bool (forall ((z Int)) (>= (+ z x) z)))\n\
         (declare-const x Int)\n\
         (assert (forall ((w Int)) (>= (+ w x) w)))",
    );
    let user = bound_term(&ctx, "x");
    assert_eq!(free_var_terms(&ctx, ctx.assertions[0]), vec![user]);
}

#[test]
fn alpha_equivalent_quantifiers_over_one_constant_are_still_shared() {
    let ctx = context(
        "(declare-const c Int)\n\
         (assert (forall ((y Int)) (=> (> y c) (> y 0))))\n\
         (assert (forall ((w Int)) (=> (> w c) (> w 0))))",
    );
    assert_eq!(ctx.assertions[0], ctx.assertions[1]);
}

#[test]
fn a_binder_is_not_spelled_like_a_function_declared_before_it() {
    let ctx = context(
        "(declare-fun y_0 (Int) Int)\n\
         (declare-fun f (Int) Int)\n\
         (assert (forall ((y Int)) (= (f y) (+ (y_0 y) 1))))",
    );
    let binders = match ctx.terms.get(ctx.assertions[0]) {
        TermData::Forall(vars, _, _) => vars.clone(),
        other => panic!("expected a forall, got {other:?}"),
    };
    assert_eq!(binders.len(), 1);
    assert_ne!(binders[0].0, "y_0");
    assert!(ctx.symbols.contains_key("y_0"));
}

#[test]
fn a_function_declared_after_a_binder_of_its_spelling_takes_a_private_identity() {
    let ctx = context(
        "(assert (forall ((y Int)) (> y (- y 1))))\n\
         (declare-fun y_0 (Int) Int)\n\
         (assert (= (y_0 0) 1))",
    );
    let application = match ctx.terms.get(ctx.assertions[1]) {
        TermData::App(_, args) => args.clone(),
        other => panic!("expected an equality, got {other:?}"),
    };
    let head = application
        .iter()
        .find_map(|&side| match ctx.terms.get(side) {
            TermData::App(symbol, args) if args.len() == 1 => Some(symbol.name().to_string()),
            _ => None,
        })
        .expect("one side applies the declared function");
    assert_ne!(head, "y_0");
    assert_eq!(ctx.dt_surface_name(&head), Some("y_0"));
}

#[test]
fn every_occurrence_of_a_negative_power_shares_one_reserved_witness() {
    let ctx = context(
        "(declare-const x Real)\n\
         (assert (= (^ x (- 1)) 0.0))\n\
         (assert (= (^ x (- 1)) 0.0))\n\
         (assert (= (^ x (- 2)) 0.0))",
    );
    assert_eq!(ctx.assertions[0], ctx.assertions[1]);
    assert_ne!(ctx.assertions[0], ctx.assertions[2]);
    let user = bound_term(&ctx, "x");
    let mut witnesses = Vec::new();
    for &assertion in &ctx.assertions {
        for var in free_var_terms(&ctx, assertion) {
            if var != user && !witnesses.contains(&var) {
                witnesses.push(var);
            }
        }
    }
    let names: Vec<String> = witnesses.iter().map(|&w| var_name(&ctx, w)).collect();
    assert_eq!(
        names,
        [
            "!ay.zero-power-of-negative.Real.1",
            "!ay.zero-power-of-negative.Real.2"
        ]
    );
    for name in &names {
        assert!(is_source_reserved_symbol(name), "{name}");
    }
}

#[test]
fn the_old_negative_power_spelling_is_an_ordinary_user_constant() {
    let ctx = context(
        "(declare-const x Real)\n\
         (assert (= (^ x (- 1)) 0.0))\n\
         (declare-const pow_neg_at_zero_2 Real)\n\
         (assert (= pow_neg_at_zero_2 5.0))",
    );
    let user = bound_term(&ctx, "pow_neg_at_zero_2");
    assert_eq!(var_name(&ctx, user), "pow_neg_at_zero_2");
    assert!(!free_var_terms(&ctx, ctx.assertions[0]).contains(&user));
}
