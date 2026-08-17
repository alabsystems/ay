// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn multi_binder_definitional_forall_is_not_adopted_or_tautologized() {
    let commands = parse(
        "(declare-fun f (Int Int) Int) \
         (assert (forall ((x Int) (y Int)) (= (f x y) (+ x y))))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context
            .process_command(command)
            .expect("elaboration succeeds");
    }

    assert!(context.adopted_macro_interp("f").is_none());
    assert_eq!(context.assertions.len(), 1);
    let TermData::Forall(vars, body, _) = context.terms.get(context.assertions[0]) else {
        panic!("the source definition must remain quantified");
    };
    assert_eq!(vars.len(), 2);
    assert_ne!(
        *body,
        context.terms.true_term(),
        "refused adoption must retain the source constraint"
    );
}
