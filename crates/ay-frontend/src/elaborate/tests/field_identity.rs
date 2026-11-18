// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The field constants eager single-constructor elimination mints for a
//! declared constant take private core identities, so a user symbol spelled
//! like `<root>!<selector>` keeps its own binding in either declaration order.

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

/// The constructor arguments `name` is bound to.
fn fields(ctx: &Context, name: &str) -> Vec<TermId> {
    match ctx.terms.get(bound_term(ctx, name)) {
        TermData::App(_, args) => args.clone(),
        other => panic!("'{name}' is not bound to a constructor: {other:?}"),
    }
}

fn var_name(ctx: &Context, term: TermId) -> String {
    match ctx.terms.get(term) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("expected a variable, got {other:?}"),
    }
}

/// The two sides of the equality asserted at `index`.
fn equality_sides(ctx: &Context, index: usize) -> (TermId, TermId) {
    match ctx.terms.get(ctx.assertions[index]) {
        TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
            (args[0], args[1])
        }
        other => panic!("assertion {index} is not an equality: {other:?}"),
    }
}

/// `user` is a user constant distinct from `field`, and `field` carries a
/// recorded private field identity that is suppressed from models.
fn assert_distinct_user_and_field(ctx: &Context, user: &str, field: TermId) {
    let user_term = bound_term(ctx, user);
    assert_ne!(user_term, field, "'{user}' is bound to the field constant");
    assert_eq!(var_name(ctx, user_term), user);
    let identity = var_name(ctx, field);
    assert!(identity.starts_with(INTERNAL_SYMBOL_PREFIX), "{identity}");
    assert!(ctx.is_dt_field_identity(&identity), "{identity}");
    assert!(!ctx.is_dt_field_identity(user));
    assert!(ctx.is_internal_symbol(&identity));
    assert!(!ctx.is_internal_symbol(user));
}

#[test]
fn a_user_constant_declared_before_the_root_keeps_its_binding() {
    let ctx = context(
        "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
         (declare-const p!x Int)\n\
         (declare-const p P)\n\
         (assert (= p!x 1))\n\
         (assert (= (x p) 2))",
    );
    let field = fields(&ctx, "p")[0];
    assert_distinct_user_and_field(&ctx, "p!x", field);
    assert_eq!(equality_sides(&ctx, 0).0, bound_term(&ctx, "p!x"));
    assert_eq!(equality_sides(&ctx, 1).0, field);
}

#[test]
fn a_user_constant_declared_after_the_root_is_accepted_and_kept_apart() {
    let ctx = context(
        "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
         (declare-const p P)\n\
         (declare-const p!x Int)\n\
         (assert (= p!x 1))\n\
         (assert (= (x p) 2))",
    );
    let field = fields(&ctx, "p")[0];
    assert_distinct_user_and_field(&ctx, "p!x", field);
    assert_eq!(equality_sides(&ctx, 0).0, bound_term(&ctx, "p!x"));
    assert_eq!(equality_sides(&ctx, 1).0, field);
}

#[test]
fn an_empty_selector_name_does_not_capture_the_root_spelled_with_a_bang() {
    let ctx = context(
        "(declare-datatypes ((P 0)) (((mk (|| Int)))))\n\
         (declare-const p! Int)\n\
         (declare-const p P)\n\
         (assert (= p! 1))\n\
         (assert (= (|| p) 2))",
    );
    let field = fields(&ctx, "p")[0];
    assert_distinct_user_and_field(&ctx, "p!", field);
    assert_eq!(equality_sides(&ctx, 1).0, field);
}

#[test]
fn nested_fields_do_not_capture_user_constants_spelled_like_their_path() {
    let ctx = context(
        "(declare-datatypes ((I 0)) (((mkI (top Int)))))\n\
         (declare-datatypes ((O 0)) (((mkO (right I) (lft Int)))))\n\
         (declare-const s!right!top Int)\n\
         (declare-const s!lft Int)\n\
         (declare-const s O)",
    );
    let outer = fields(&ctx, "s");
    let inner = match ctx.terms.get(outer[0]) {
        TermData::App(_, args) => args.clone(),
        other => panic!("the `right` field is not a constructor: {other:?}"),
    };
    assert_distinct_user_and_field(&ctx, "s!right!top", inner[0]);
    assert_distinct_user_and_field(&ctx, "s!lft", outer[1]);
    assert_ne!(var_name(&ctx, inner[0]), var_name(&ctx, outer[1]));
}

#[test]
fn a_field_identity_cannot_be_declared_by_the_user() {
    let ctx = context(
        "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
         (declare-const p P)",
    );
    let identity = var_name(&ctx, fields(&ctx, "p")[0]);
    let mut ctx = ctx;
    let script = format!("(declare-const |{identity}| Int)");
    let command = &parse(&script).expect("script parses")[0];
    assert!(
        matches!(
            ctx.process_command(command),
            Err(ElaborateError::ReservedSymbol(_))
        ),
        "{identity}"
    );
}
