// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#defn-fold-binder-capture) The aggregate-definition fold never moves a
//! variable spelled like a binder under that binder. Every case has a twin
//! that differs only in the spelling of the foreign variable, and the twin
//! still folds, so the fold's payoff (#defn-fold-under-forall) is kept.

use ay_core::Sort;
use num_bigint::BigInt;

use super::*;
use crate::executor::Executor;

const HEAD: &str = "(set-logic ALL) \
     (declare-const lens (Array Int Int)) \
     (declare-const w (Array Int Int)) \
     (assert (forall ((i Int)) \
       (=> (and (<= 0 i) (< i (select lens 0))) (= i (select w 0)))))";

const TAIL: &str = "(assert (= lens (store ((as const (Array Int Int)) 0) 0 2))) \
     (assert (= w (store ((as const (Array Int Int)) 0) 0 @B@)))";

/// Elaborate [`HEAD`], then declare an Int constant and elaborate `tail` with
/// `@B@` naming it. With `collide` the constant is spelled like the binder the
/// frontend minted for the universal (a declaration made AFTER the universal
/// is the only way to get that spelling); otherwise it is spelled `x`.
/// Returns the executor, the authored universal and the constant.
fn load(tail: &str, collide: bool) -> (Executor, TermId, TermId) {
    let mut exec = Executor::new();
    let head = ay_frontend::parse(HEAD).expect("head parses");
    exec.execute_all(&head).expect("head elaborates");
    let universal = exec.ctx.assertions[0];
    let TermData::Forall(vars, _, _) = exec.ctx.terms.get(universal).clone() else {
        panic!("the head's first assertion is the universal");
    };
    let name = if collide {
        vars[0].0.clone()
    } else {
        "x".to_string()
    };
    let later = ay_frontend::parse(&format!(
        "(declare-const {name} Int) {}",
        tail.replace("@B@", &name)
    ))
    .expect("tail parses");
    exec.execute_all(&later).expect("tail elaborates");
    let constant = exec
        .ctx
        .terms
        .term_ids()
        .filter(|&t| matches!(exec.ctx.terms.get(t), TermData::Var(n, _) if *n == name))
        .max()
        .expect("the tail declares the constant");
    let spelled_alike = exec
        .ctx
        .terms
        .term_ids()
        .filter(|&t| matches!(exec.ctx.terms.get(t), TermData::Var(n, _) if *n == name))
        .count();
    assert_eq!(
        spelled_alike,
        if collide { 2 } else { 1 },
        "the fixture must hold two identities spelled `{name}` exactly when it collides"
    );
    (exec, universal, constant)
}

fn var_named(exec: &mut Executor, name: &str) -> TermId {
    exec.ctx
        .terms
        .mk_var(name, Sort::array(Sort::Int, Sort::Int))
}

fn singleton(term: TermId) -> HashSet<TermId> {
    [term].into_iter().collect()
}

/// The definitions the producer itself collects, which must be `lens` and
/// `w` for every fixture here.
fn definitions(exec: &mut Executor) -> HashMap<TermId, TermId> {
    let definitions = exec.collect_ground_aggregate_definitions();
    let lens = var_named(exec, "lens");
    let w = var_named(exec, "w");
    assert!(definitions.len() == 2 && definitions.contains_key(&lens));
    assert!(definitions.contains_key(&w));
    definitions
}

#[test]
fn a_definition_spelling_the_binder_is_refused_and_its_twin_admitted() {
    for collide in [true, false] {
        let (mut exec, universal, _) = load(TAIL, collide);
        let definitions = definitions(&mut exec);
        let w = var_named(&mut exec, "w");
        let admitted = capture_free_definitions(&exec.ctx.terms, universal, &definitions);
        assert_eq!(
            admitted.contains_key(&w),
            !collide,
            "`w := (store K 0 c)` folds exactly when `c` is not spelled like the binder"
        );
        assert_eq!(
            admitted.len(),
            if collide { 1 } else { 2 },
            "`lens` always folds"
        );

        let defined: HashSet<TermId> = definitions.keys().copied().collect();
        let admitted = admitted_definitions(&exec.ctx.terms, universal, &definitions, &defined)
            .expect("the bound of the binder still reads `lens`");
        assert_eq!(admitted.contains_key(&w), !collide);
    }
}

/// Refusing the only definition a bound reads leaves the universal authored,
/// as if that definition had never been asserted: folding the remaining body
/// read would only cost the universal its E-matching provenance.
#[test]
fn refusing_every_bound_definition_leaves_the_universal_authored() {
    let tail = "(assert (= lens (store ((as const (Array Int Int)) 0) @B@ 2))) \
         (assert (= w (store ((as const (Array Int Int)) 0) 0 5)))";
    for collide in [true, false] {
        let (mut exec, universal, _) = load(tail, collide);
        let definitions = definitions(&mut exec);
        let lens = var_named(&mut exec, "lens");
        let defined: HashSet<TermId> = definitions.keys().copied().collect();
        let folded = fold(&mut exec.ctx.terms, universal, &definitions, &defined);
        if collide {
            assert_eq!(folded, universal, "no admitted definition exposes a bound");
        } else {
            assert_ne!(folded, universal);
            assert!(!term_mentions_any_var(
                &exec.ctx.terms,
                folded,
                &singleton(lens)
            ));
        }
    }
}

/// A binder of a NESTED quantifier and a `let` name are spellings too: the
/// expander substitutes every binder it reaches by name, and a `let` is
/// expanded by name.
#[test]
fn nested_binders_and_let_names_are_binder_spellings() {
    let mut terms = TermStore::new();
    let j = terms.mk_var("j", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let j_ge_one = terms.mk_ge(j, one);
    let let_body = terms.mk_let(vec![("k".to_string(), one)], j_ge_one);
    let inner = terms.mk_exists(vec![("j".to_string(), Sort::Int)], let_body);
    let outer = terms.mk_forall(vec![("i".to_string(), Sort::Int)], inner);
    let names = bound_names(&terms, outer);
    for name in ["i", "j", "k"] {
        assert!(names.contains(name), "`{name}` is bound in the fixture");
    }
    let foreign_k = terms.mk_fresh_named_var("k", Sort::Int);
    let unrelated = terms.mk_fresh_named_var("m", Sort::Int);
    assert!(mentions_a_name(&terms, foreign_k, &names));
    assert!(!mentions_a_name(&terms, unrelated, &names));
}

/// Through the producer fold itself. With the collision `lens` still folds
/// (the bound becomes the literal `2`) but `w` stays a variable in the
/// universal, so the declared constant never reaches it; the twin folds both.
#[test]
fn the_producer_fold_keeps_a_binder_spelling_out_of_the_universal() {
    for collide in [true, false] {
        let (mut exec, universal, constant) = load(TAIL, collide);
        let lens = var_named(&mut exec, "lens");
        let w = var_named(&mut exec, "w");

        exec.fold_ground_definitions_into_universals();

        let folded = exec.ctx.assertions[0];
        let terms = &exec.ctx.terms;
        assert_ne!(
            folded, universal,
            "`lens` folds either way (collide={collide})"
        );
        assert!(!term_mentions_any_var(terms, folded, &singleton(lens)));
        assert_eq!(
            term_mentions_any_var(terms, folded, &singleton(w)),
            collide,
            "`w` stays in the universal exactly when its value spells the binder"
        );
        assert_eq!(
            term_mentions_any_var(terms, folded, &singleton(constant)),
            !collide,
            "the declared constant reaches the universal only in the twin"
        );
    }
}
