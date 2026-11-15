// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::constraint::Constraint;
use crate::expr::ExprValue;
use crate::sort::Sort;

mod names;
mod oracle;

fn boolean(name: &str) -> Expr {
    Expr::var(name, Sort::bool())
}

fn large(mut value: Expr) -> Expr {
    // Forty real native builder nodes, no constant folding; even parity keeps
    // its Boolean meaning while exceeding the ordinary sharing threshold.
    for _ in 0..40 {
        value = value.not();
    }
    value
}

fn bind(name: &str) -> Vec<(String, Sort)> {
    vec![(name.to_owned(), Sort::bool())]
}

fn check(expr: &Expr, values: &[(&str, bool)], expected: bool) {
    let original = oracle::assertion(&format!("{expr}"));
    let shared = oracle::assertion(&expr.to_smtlib_shared());
    assert_eq!(oracle::evaluate(&original, values), Some(expected));
    assert_eq!(oracle::evaluate(&shared, values), Some(expected));
}

#[test]
fn universal_and_existential_shared_bodies_stay_below_their_binders() {
    let term = large(boolean("x"));
    let body = term.clone().or(term);
    check(&Expr::forall(bind("x"), body.clone()), &[], false);
    check(&Expr::exists(bind("x"), body), &[], true);
}

#[test]
fn one_arc_used_free_and_bound_keeps_two_lexical_meanings() {
    let term = large(boolean("x"));
    let quantified = Expr::forall(bind("x"), term.clone().or(term.clone()));
    let source = term.and(quantified);
    for x in [false, true] {
        // The universal is false regardless of the identically named free x.
        check(&source, &[("x", x)], false);
    }
}

#[test]
fn sibling_quantifiers_do_not_share_their_bound_values() {
    let term = large(boolean("x"));
    let repeated = term.clone().and(term);
    let source = Expr::forall(bind("x"), repeated.clone()).or(Expr::exists(bind("x"), repeated));
    check(&source, &[], true);
    for x in [false, true] {
        check(&source, &[("x", x)], true);
    }
}

#[test]
fn nested_quantifiers_retain_outer_and_inner_dependencies() {
    let term = large(boolean("x").xor(boolean("y")));
    let body = term.clone().or(term);
    let source = Expr::forall(bind("x"), Expr::exists(bind("y"), body));
    check(&source, &[], true);
    let shadowed = large(boolean("x"));
    let inner = Expr::exists(bind("x"), shadowed.clone().and(shadowed));
    check(
        &Expr::forall(bind("x"), inner.and(boolean("x"))),
        &[],
        false,
    );
}

#[test]
fn generated_name_avoidance_scans_free_names_below_quantifier_barriers() {
    for free_symbol in [
        boolean("ay_let_share_0"),
        Expr::func_app("ay_let_share_0", vec![]),
    ] {
        let term = large(boolean("b"));
        let body = free_symbol.and(boolean("x"));
        let source = term.clone().eq(term).and(Expr::exists(bind("x"), body));
        for b in [false, true] {
            for free in [false, true] {
                check(&source, &[("b", b), ("ay_let_share_0", free)], free);
            }
        }
    }
}

#[test]
fn repeated_whole_quantifier_is_shareable_without_lifting_its_body() {
    let term = large(boolean("x"));
    let quantifier = Expr::forall(bind("x"), term.clone().eq(term));
    let source = quantifier.clone().and(quantifier);
    let text = source.to_smtlib_shared();
    assert!(text.contains("(let "));
    assert_eq!(text.matches("(forall ").count(), 1);
    check(&source, &[], true);
}

#[test]
fn small_quantified_regions_do_not_regrow_an_exponential_tree() {
    let mut source = boolean("p");
    for i in 0..12 {
        source = Expr::forall(bind(&format!("unused{i}")), source.clone().and(source));
    }
    // Each local region has only a few nodes. Repeated whole quantifiers must
    // remain shareable even when treated as opaque by an enclosing plan.
    for text in [source.to_smtlib_shared(), format!("{source}")] {
        assert!(
            text.len() < 10_000,
            "quantified DAG expanded: {}",
            text.len()
        );
        assert_eq!(text.matches("(forall ").count(), 12);
        let parsed = oracle::assertion(&text);
        for p in [false, true] {
            assert_eq!(oracle::evaluate(&parsed, &[("p", p)]), Some(p));
        }
    }
}

#[test]
fn trigger_terms_keep_the_original_binder_and_direct_annotation() {
    let term = large(boolean("x"));
    let trigger = Expr::func_app("f", vec![boolean("x")]);
    let source = Expr::forall_with_triggers(
        bind("x"),
        term.clone().eq(term),
        vec![vec![trigger.clone()]],
    );
    let text = source.to_smtlib_shared();
    assert!(text.contains(":pattern ((f x))"));
    let parsed = oracle::assertion(&text);
    let ay_frontend::Term::Forall(_, body) = &parsed else {
        panic!("original quantifier must remain")
    };
    assert!(matches!(body.as_ref(), ay_frontend::Term::Annotated(_, _)));
    assert_eq!(oracle::evaluate(&parsed, &[]), Some(true));
    let ExprValue::Forall { triggers, .. } = source.value.as_ref() else {
        panic!("native forall retained")
    };
    assert!(Arc::ptr_eq(&triggers[0][0].value, &trigger.value));
}

#[test]
fn native_rule_display_preserves_quantified_body_scope() {
    let term = large(boolean("x"));
    let rule = Constraint::Rule {
        head: Some(boolean("P")),
        body: Expr::forall(bind("x"), term.clone().or(term)),
    };
    let text = format!("{rule}");
    let commands = ay_frontend::parse(&text).unwrap();
    let [ay_frontend::Command::Rule(body)] = commands.as_slice() else {
        panic!("one original Rule command")
    };
    for predicate in [false, true] {
        assert_eq!(oracle::evaluate(body, &[("P", predicate)]), Some(true));
    }
}
