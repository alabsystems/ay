// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{
    try_export_alethe_with_problem_scope_and_overrides, with_refused_surface_steps_declined_to_hole,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, TheoryLemmaKind};

#[test]
fn a_reordered_chain_of_distinct_constant_writes_is_the_same_array() {
    for (surface, certified) in [
        (
            "(store (store F 7 true) 5 true)",
            "(store (store F 5 true) 7 true)",
        ),
        (
            "(store (store (store a 9 u) (- 2) v) 4 w)",
            "(store (store (store a (- 2) v) 4 w) 9 u)",
        ),
        // One index, three legal bit-vector spellings.
        (
            "(store (store m #x07 #xFF) #b00000101 #x01)",
            "(store (store m (_ bv5 8) #x01) #x07 (_ bv255 8))",
        ),
    ] {
        assert!(
            same_array_by_distinct_constant_writes(surface, certified),
            "{surface} / {certified}"
        );
    }
}

/// NEGATIVE TWINS: every chain pair that need not denote one array, or that
/// this reader cannot decode, is refused.
#[test]
fn a_chain_with_another_value_index_root_or_a_symbolic_index_is_not_the_same_array() {
    for (surface, certified, why) in [
        (
            "(store (store F 7 true) 5 false)",
            "(store (store F 5 true) 7 true)",
            "a different value at 5",
        ),
        (
            "(store (store F 7 true) 6 true)",
            "(store (store F 5 true) 7 true)",
            "a different index",
        ),
        (
            "(store (store G 7 true) 5 true)",
            "(store (store F 5 true) 7 true)",
            "a different root",
        ),
        (
            "(store (store F y true) 5 true)",
            "(store (store F 5 true) y true)",
            "a symbolic index may equal 5",
        ),
        (
            "(store (store F 5 true) 5 false)",
            "(store (store F 5 false) 5 true)",
            "an overwritten index: the outer write wins",
        ),
        (
            "(store F 5 true)",
            "(store (store F 5 true) 7 true)",
            "a missing write",
        ),
        (
            "(store (store m #x07 #xFF) #x05 #x01)",
            "(store (store m #x0005 #x01) #x0007 #xFF)",
            "another index width",
        ),
        ("F", "F", "no write at all"),
    ] {
        assert!(
            !same_array_by_distinct_constant_writes(surface, certified),
            "{why}: {surface} / {certified}"
        );
    }
}

/// `c = (store (store ((as const (Array Int Bool)) false) 7 true) 5 true)`,
/// interned by `mk_store` as `store(store(F, 5, true), 7, true)`, beside its
/// authored spelling; `x` is the read index.
struct ReorderedChain {
    terms: TermStore,
    fill: String,
    outer: TermId,
    inner: TermId,
    seven: TermId,
    x: TermId,
}

fn reordered_chain() -> ReorderedChain {
    let mut terms = TermStore::new();
    let fill_value = terms.mk_bool(false);
    let fill = terms.mk_const_array(Sort::Int, fill_value);
    let yes = terms.mk_bool(true);
    let five = terms.mk_int(5.into());
    let seven = terms.mk_int(7.into());
    let authored_inner = terms.mk_store(fill, seven, yes);
    let outer = terms.mk_store(authored_inner, five, yes);
    let TermData::App(_, arguments) = terms.get(outer).clone() else {
        panic!("a two-write chain is a store");
    };
    let &[inner, outer_index, _] = arguments.as_slice() else {
        panic!("store arity");
    };
    assert_eq!(outer_index, seven, "mk_store sorts the distinct writes");
    let x = terms.mk_var("x", Sort::Int);
    let fill = AlethePrinter::new(&terms).format_term(fill);
    ReorderedChain {
        terms,
        fill,
        outer,
        inner,
        seven,
        x,
    }
}

fn export(
    chain: &ReorderedChain,
    clause: Vec<TermId>,
    index_eq: bool,
    authored: &str,
) -> Result<String, AlethePrintError> {
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        clause.clone(),
        TheoryLemmaKind::ArraySelectStore { index_eq },
    );
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(chain.outer, authored.to_string());
    try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &chain.terms,
        &clause,
        Some(&overrides),
    )
}

/// The guarded ROW2 `(or (= 7 x) (= (select c x) (select (store F 5 true) x)))`.
fn row2_clause(chain: &mut ReorderedChain) -> Vec<TermId> {
    let terms = &mut chain.terms;
    let stored = terms.mk_app(Symbol::named("select"), [chain.outer, chain.x], Sort::Bool);
    let based = terms.mk_app(Symbol::named("select"), [chain.inner, chain.x], Sort::Bool);
    let row = terms.mk_app(Symbol::named("="), [stored, based], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("="), [chain.seven, chain.x], Sort::Bool);
    vec![guard, row]
}

/// The unit ROW1 `(= (select c 7) true)`.
fn row1_clause(chain: &mut ReorderedChain) -> Vec<TermId> {
    let terms = &mut chain.terms;
    let read = terms.mk_app(
        Symbol::named("select"),
        [chain.outer, chain.seven],
        Sort::Bool,
    );
    let yes = terms.mk_bool(true);
    vec![terms.mk_app(Symbol::named("="), [read, yes], Sort::Bool)]
}

#[test]
fn a_row2_over_the_authored_write_order_is_a_surface_refusal_and_the_honest_hole() {
    let mut chain = reordered_chain();
    let clause = row2_clause(&mut chain);
    let fill = chain.fill.clone();
    let authored = format!("(store (store {fill} 7 true) 5 true)");

    let error = export(&chain, clause.clone(), false, &authored)
        .expect_err("no pinned rule spells the reordered chain");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("write order")),
        "{error}"
    );
    let output =
        with_refused_surface_steps_declined_to_hole(|| export(&chain, clause, false, &authored))
            .expect("the surface refusal declines to the hole");
    assert!(
        output.contains(&format!(
            "(step t0 (cl (= 7 x) (= (select {authored} x) (select (store {fill} 5 true) x))) \
             :rule hole)"
        )),
        "{output}"
    );
    assert!(!output.contains("arrays_row"), "{output}");
}

#[test]
fn a_unit_row1_over_the_authored_write_order_is_the_honest_hole() {
    let mut chain = reordered_chain();
    let clause = row1_clause(&mut chain);
    let fill = chain.fill.clone();
    let authored = format!("(store (store {fill} 7 true) 5 true)");

    let error = export(&chain, clause.clone(), true, &authored)
        .expect_err("no pinned rule spells the reordered chain");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error}"
    );
    let output =
        with_refused_surface_steps_declined_to_hole(|| export(&chain, clause, true, &authored))
            .expect("the surface refusal declines to the hole");
    assert!(
        output.contains(&format!(
            "(step t0 (cl (= (select {authored} 7) true)) :rule hole)"
        )),
        "{output}"
    );
}

/// NEGATIVE TWINS: an authored chain that writes another value, at another
/// index, or at a symbolic index is not the certified array, so the ROW
/// printers keep their `InvalidArrayStep` refusal, which the `--proof FILE`
/// scope does NOT decline to a hole.
#[test]
fn an_authored_chain_off_the_certified_array_stays_refused_inside_the_hole_scope() {
    let mut chain = reordered_chain();
    let row2 = row2_clause(&mut chain);
    let row1 = row1_clause(&mut chain);
    let fill = chain.fill.clone();
    for authored in [
        format!("(store (store {fill} 7 true) 5 false)"),
        format!("(store (store {fill} 7 true) 6 true)"),
        format!("(store (store {fill} 7 true) y true)"),
        format!("(store (store {fill} 7 false) 5 true)"),
    ] {
        for (clause, index_eq) in [(row2.clone(), false), (row1.clone(), true)] {
            let error = with_refused_surface_steps_declined_to_hole(|| {
                export(&chain, clause, index_eq, &authored)
            })
            .expect_err("a different array must stay refused");
            assert!(
                matches!(error, AlethePrintError::InvalidArrayStep { .. }),
                "{authored}: {error}"
            );
        }
    }
}
