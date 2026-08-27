// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Definitional-`forall` macro adoption at binder arities above one.
//!
//! 92e37dcf3 bounded adoption to a single binder and pinned that bound with a
//! test asserting the refusal. The bound was not a soundness property — arity
//! appears nowhere in the definitional-extension argument, and every other
//! guard in `try_adopt_definitional_forall` is written over k binders — while
//! the cost was real: a refused multi-binder definition stays quantified and
//! the AUFLIA lazy split loop does not converge on that family, turning a 2s
//! `sat` into a divergence.
//!
//! So the arity assertion is gone and what replaces it is the property the old
//! test was actually protecting: an assertion may be discharged to the
//! reflexive tautology ONLY in exchange for a registered macro that carries its
//! meaning. Adoption and retention are the two halves of that trade, and both
//! are pinned below.

use super::*;

fn elaborate(script: &str) -> Context {
    let commands = parse(script).expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context
            .process_command(command)
            .expect("elaboration succeeds");
    }
    context
}

/// A two-binder definitional extension is adopted, and the macro it registers
/// carries BOTH binders — the meaning the discharged assertion gave up.
#[test]
fn multi_binder_definitional_forall_is_adopted_with_all_its_binders() {
    let context = elaborate(
        "(declare-fun f (Int Int) Int) \
         (assert (forall ((x Int) (y Int)) (= (f x y) (+ x y))))",
    );

    let (binders, _) = context
        .adopted_macro_interp("f")
        .expect("a two-binder definitional extension must be adopted");
    assert_eq!(
        binders.len(),
        2,
        "the registered macro must carry every binder of the definition it replaces"
    );
}

/// The discharge is only sound in exchange for the macro, so it is pinned
/// against that exchange rather than on its own: the source constraint becomes
/// the reflexive tautology BECAUSE `f` now expands to its definition.
#[test]
fn adopted_multi_binder_definition_is_discharged_by_its_macro() {
    let context = elaborate(
        "(declare-fun f (Int Int) Int) \
         (assert (forall ((x Int) (y Int)) (= (f x y) (+ x y))))",
    );

    assert!(
        context.adopted_macro_interp("f").is_some(),
        "discharge without a registered macro would drop the constraint"
    );
    assert_eq!(context.assertions.len(), 1);
    let TermData::Forall(_, body, _) = context.terms.get(context.assertions[0]) else {
        // Elaboration may fold the whole tautology away; either form is the
        // same discharged constraint.
        assert_eq!(context.assertions[0], context.terms.true_term());
        return;
    };
    assert_eq!(
        *body,
        context.terms.true_term(),
        "an adopted definition expands to `t = t` and discharges"
    );
}

/// THE SOUNDNESS HALF, and the reason the old test earned its place: when a
/// guard refuses adoption, the source constraint must SURVIVE. Here `f` is
/// already mentioned by an earlier assertion, so adopting would leave that raw
/// occurrence constraining a disconnected symbol while later ones expand.
/// Refusal is required — and refusal must not also discard the definition.
#[test]
fn refused_multi_binder_adoption_retains_the_source_constraint() {
    let context = elaborate(
        "(declare-fun f (Int Int) Int) \
         (assert (> (f 1 2) 0)) \
         (assert (forall ((x Int) (y Int)) (= (f x y) (+ x y))))",
    );

    assert!(
        context.adopted_macro_interp("f").is_none(),
        "a pre-adoption raw occurrence of `f` must refuse adoption"
    );
    assert_eq!(context.assertions.len(), 2);
    let TermData::Forall(vars, body, _) = context.terms.get(context.assertions[1]) else {
        panic!("the refused definition must remain quantified");
    };
    assert_eq!(vars.len(), 2);
    assert_ne!(
        *body,
        context.terms.true_term(),
        "refused adoption must retain the source constraint"
    );
}
