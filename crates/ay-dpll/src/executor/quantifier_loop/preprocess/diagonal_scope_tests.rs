// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;

/// A boxed sort `U`, binders `x`, `y` of it, and the terms of the binary
/// definition `(f x y) = (g x)` with pattern `(f x y)`.
struct Definition {
    terms: TermStore,
    vars: Vec<(String, Sort)>,
    x: TermId,
    y: TermId,
    f_xy: TermId,
    body: TermId,
}

fn sort_u() -> Sort {
    Sort::Uninterpreted("U".to_owned())
}

fn definition(sort: Sort) -> Definition {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let f_xy = terms.mk_app(Symbol::named("f"), vec![x, y], sort.clone());
    let g_x = terms.mk_app(Symbol::named("g"), vec![x], sort.clone());
    let body = terms.mk_app(Symbol::named("="), vec![f_xy, g_x], Sort::Bool);
    Definition {
        terms,
        vars: vec![("x".to_owned(), sort.clone()), ("y".to_owned(), sort)],
        x,
        y,
        f_xy,
        body,
    }
}

#[test]
fn a_triggers_only_input_keeps_a_patterned_definition_out_of_the_pass() {
    let d = definition(sort_u());
    let triggers = vec![vec![d.f_xy]];
    assert!(!takes_diagonal_instances(
        &d.terms,
        &d.vars,
        d.body,
        &triggers,
        Instantiation::TriggersOnly,
        Standing::Asserted
    ));
    // The twin: the same definition without its pattern.
    assert!(takes_diagonal_instances(
        &d.terms,
        &d.vars,
        d.body,
        &[],
        Instantiation::TriggersOnly,
        Standing::Asserted
    ));
}

/// The same patterned definition as a hypothesis inside a larger assertion:
/// the pass keeps it, and its twin, asserted by itself, stays out.
#[test]
fn a_triggers_only_input_keeps_a_patterned_hypothesis_in_the_pass() {
    let d = definition(sort_u());
    let triggers = vec![vec![d.f_xy]];
    assert!(takes_diagonal_instances(
        &d.terms,
        &d.vars,
        d.body,
        &triggers,
        Instantiation::TriggersOnly,
        Standing::PartOfAnAssertion
    ));
    assert!(!takes_diagonal_instances(
        &d.terms,
        &d.vars,
        d.body,
        &triggers,
        Instantiation::TriggersOnly,
        Standing::Asserted
    ));
}

/// Where a universal stands matters to a triggers-only input alone, and
/// never lets an interpreted-sort definition in.
#[test]
fn standing_changes_nothing_else() {
    let triggers_of = |d: &Definition| vec![vec![d.f_xy]];
    let d = definition(sort_u());
    for standing in [Standing::Asserted, Standing::PartOfAnAssertion] {
        assert!(takes_diagonal_instances(
            &d.terms,
            &d.vars,
            d.body,
            &triggers_of(&d),
            Instantiation::Unrestricted,
            standing
        ));
    }
    let d = definition(Sort::Int);
    for instantiation in [Instantiation::Unrestricted, Instantiation::TriggersOnly] {
        assert!(!takes_diagonal_instances(
            &d.terms,
            &d.vars,
            d.body,
            &triggers_of(&d),
            instantiation,
            Standing::PartOfAnAssertion
        ));
    }
}

#[test]
fn an_unrestricted_input_has_the_patterned_definition_taken() {
    let d = definition(sort_u());
    let triggers = vec![vec![d.f_xy]];
    // The same definition and pattern as the skipped case above; the input
    // did not switch model-based instantiation off.
    assert!(takes_diagonal_instances(
        &d.terms,
        &d.vars,
        d.body,
        &triggers,
        Instantiation::Unrestricted,
        Standing::Asserted
    ));
}

#[test]
fn a_universal_without_a_pattern_is_taken_whatever_the_input_asked() {
    let d = definition(sort_u());
    for instantiation in [Instantiation::Unrestricted, Instantiation::TriggersOnly] {
        assert!(takes_diagonal_instances(
            &d.terms,
            &d.vars,
            d.body,
            &[],
            instantiation,
            Standing::Asserted
        ));
    }
}

#[test]
fn a_function_free_body_is_taken_whatever_its_pattern_and_the_input() {
    for sort in [sort_u(), Sort::Int] {
        let mut d = definition(sort);
        // (= (=> (p x) (s x y)) (p y)): predicates over the binders only.
        let p_x = d.terms.mk_app(Symbol::named("p"), vec![d.x], Sort::Bool);
        let p_y = d.terms.mk_app(Symbol::named("p"), vec![d.y], Sort::Bool);
        let s_xy = d
            .terms
            .mk_app(Symbol::named("s"), vec![d.x, d.y], Sort::Bool);
        let not_p_x = d.terms.mk_not_raw(p_x);
        let imp = d
            .terms
            .mk_app(Symbol::named("or"), vec![not_p_x, s_xy], Sort::Bool);
        let body = d
            .terms
            .mk_app(Symbol::named("="), vec![imp, p_y], Sort::Bool);
        let triggers = vec![vec![s_xy]];
        for instantiation in [Instantiation::Unrestricted, Instantiation::TriggersOnly] {
            assert!(takes_diagonal_instances(
                &d.terms,
                &d.vars,
                body,
                &triggers,
                instantiation,
                Standing::Asserted
            ));
        }
    }
}

#[test]
fn an_interpreted_sort_definition_is_skipped_whatever_the_input_asked() {
    let d = definition(Sort::Int);
    let triggers = vec![vec![d.f_xy]];
    for instantiation in [Instantiation::Unrestricted, Instantiation::TriggersOnly] {
        assert!(!takes_diagonal_instances(
            &d.terms,
            &d.vars,
            d.body,
            &triggers,
            instantiation,
            Standing::Asserted
        ));
        // Not even without its pattern: the body applies `g` to an `Int`.
        assert!(!takes_diagonal_instances(
            &d.terms,
            &d.vars,
            d.body,
            &[],
            instantiation,
            Standing::Asserted
        ));
    }
}
