// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#defn-fold-under-forall) The aggregate-definition fold rewrites a
//! universal only where a binder BOUND reads the definition.
//!
//! 5d900fd2f folded every asserted Array/Datatype definition into every
//! quantified assertion, so a nested-Vec replay obligation's bound
//! `(bvult i (fld_len v))` collapses to a literal the finite-domain expander
//! reads. A universal that reads the definition only in its BODY gains
//! nothing from that, and loses its authored identity: no E-matching instance
//! of the rewritten term has proof provenance, consequence replay finds "no
//! derivable recorded instance (0 records)", and a correct `unsat` is
//! withheld as `unknown`. The `cegqi_ce_strip_identity` wrong-fact controls
//! (`b := (store a 3 9)`) are the free-base cases; these are the twins over a
//! CONSTANT base, the very value shape the replay obligations fold, so no
//! test of the definition's VALUE can be what keeps a universal authored.
//! z3 and the pre-fold build answer every one as asserted here.

use ntest::timeout;

fn solve_with_const_base_store(forall_body: &str, fact: &str) -> Vec<String> {
    crate::common::solve_vec(&format!(
        "(set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store ((as const (Array Int Int)) 0) 3 9)))
        (assert (forall ((i Int)) {forall_body}))
        {fact}
        (check-sat)"
    ))
}

/// `v10` over a constant base: the wrong fact `b[4] != a[4]` contradicts the
/// universal at `i = 4`.
#[test]
#[timeout(10000)]
fn const_base_wrong_fact_stays_unsat() {
    let results = solve_with_const_base_store(
        "(=> (distinct i 3) (= (select b i) (select a i)))",
        "(assert (distinct (select b 4) (select a 4)))",
    );
    assert_eq!(results, vec!["unsat"], "b[4] = a[4] is entailed");
}

/// `adv2` over a constant base: `b[3] = 8` contradicts the store's `9`.
#[test]
#[timeout(10000)]
fn const_base_eq_guard_wrong_fact_stays_unsat() {
    let results = solve_with_const_base_store("(=> (= i 3) (= (select b i) 8))", "");
    assert_eq!(results, vec!["unsat"], "b[3] = 9 is asserted");
}

/// An ORDER atom in the body is still a body read, not a bound: a gate that
/// folds whenever any comparison under the binder mentions `b` leaves this
/// one `unknown`.
#[test]
#[timeout(10000)]
fn order_atom_body_read_stays_unsat() {
    let results = solve_with_const_base_store(
        "(=> (distinct i 3) (<= (select b i) (select a i)))",
        "(assert (> (select b 4) (select a 4)))",
    );
    assert_eq!(results, vec!["unsat"], "b[4] <= a[4] is entailed");
}

/// The fold's payoff, which the gate must keep: the upper bound `(select b 3)`
/// only becomes the literal `9` once `b` is folded, and only then does the
/// expander ground the universal. Without the fold this answers `unknown`.
#[test]
#[timeout(10000)]
fn a_bound_read_through_the_definition_is_still_folded() {
    let results = solve_with_const_base_store(
        "(=> (and (<= 0 i) (< i (select b 3))) (= (select a i) 0))",
        "(assert (= (select a 12) 1))",
    );
    assert_eq!(results, vec!["sat"], "a[12] lies outside the bound [0, 9)");
}
