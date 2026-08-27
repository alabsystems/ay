// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The empty-clause closer's DERIVED-LEAF head is not a theorem, and this file
//! is the independent refutation of it.
//!
//! the development design notes §5 reported that on
//! `benchmarks/smt/QF_AX/write_write_overwrite.smt2` the trust closer emitted
//!
//! ```text
//! (cl (not (= (select (store a i v2) j) (select a j)))
//!     (not (= (select a j) (select (store a i v1) j))))
//! ```
//!
//! as a `TheoryLemma`. It is FALSE at `i = j`, `v1 = v2 = e`, `a[j] = e`: both
//! equalities hold, so both negations fail and the clause has no true literal.
//! The producer side of that finding is fixed in `ay-dpll`
//! (`empty_clause::derive_empty_via_trust_lemma`, #closer-derived-leaf-head);
//! this file pins the SEMANTIC fact the fix rests on, in the crate that owns
//! the array validators, so the fix cannot be undone by someone who believes
//! the clause is a lemma.
//!
//! The evaluator is [`crate::array_row_axiom::model`] — the campaign's bounded
//! McCarthy model, which shares no code with any producer or validator.
//! `congruence_derivation_sweep_tests::falsifies` cannot serve here: it treats
//! `select`/`store` as UNINTERPRETED, under which nothing about arrays is
//! decidable at all.

use super::model::{
    array, decidable, element, eq, falsify, holds, index, select, small, store, Value,
};
use ay_core::{TermId, TermStore};

/// The exact five symbols and two literals of the emitted head.
struct ClosedHead {
    terms: TermStore,
    head: Vec<TermId>,
    a: TermId,
    i: TermId,
    j: TermId,
    v1: TermId,
    v2: TermId,
    /// The two DERIVED unit lemmas the closer negated to build the head.
    leaves: Vec<TermId>,
}

/// Rebuild the head exactly as the closer built it: the negation of the two
/// unit ROW2 `TheoryLemma` conclusions the array fixpoint recorded.
fn closed_head() -> ClosedHead {
    let mut terms = TermStore::new();
    let a = array(&mut terms, "a");
    let i = index(&mut terms, "i");
    let j = index(&mut terms, "j");
    let v1 = element(&mut terms, "v1");
    let v2 = element(&mut terms, "v2");

    let store_v2 = store(&mut terms, a, i, v2);
    let store_v1 = store(&mut terms, a, i, v1);
    let read_store_v2 = select(&mut terms, store_v2, j);
    let read_store_v1 = select(&mut terms, store_v1, j);
    let read_base = select(&mut terms, a, j);

    // The leaves: `row2_unit_distinct_indices`, recorded WITHOUT the `i != j`
    // premise that makes each of them valid.
    let leaf_one = eq(&mut terms, read_store_v2, read_base);
    let leaf_two = eq(&mut terms, read_base, read_store_v1);

    let head = vec![terms.mk_not_raw(leaf_one), terms.mk_not_raw(leaf_two)];
    ClosedHead {
        terms,
        head,
        a,
        i,
        j,
        v1,
        v2,
        leaves: vec![leaf_one, leaf_two],
    }
}

/// THE NAMED COUNTERMODEL, checked literal by literal.
///
/// `i = j = idx0`, `v1 = v2 = elt0`, `a = [elt0, elt1]` so `a[j] = elt0`. Both
/// equalities then hold, so BOTH head literals are false and the clause is
/// refuted — a complete refutation, not a sampled one.
///
/// The base array is deliberately NON-CONSTANT, so the witness is a real
/// two-value model rather than the degenerate one-element carrier. The
/// load-bearing part of the assignment is `v1 = v2 = a[j]`, and that is what
/// the sensitivity control below pins: move either stored value off `a[j]` and
/// the head acquires a true literal.
#[test]
fn the_closer_head_is_false_at_i_equals_j_with_v1_equals_v2_equals_a_at_j() {
    let fixture = closed_head();
    let binding = vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Index(0)),
        (fixture.j, Value::Index(0)),
        (fixture.v1, Value::Element(0)),
        (fixture.v2, Value::Element(0)),
    ];

    assert!(
        decidable(&fixture.terms, &fixture.head, &small()),
        "the array model must DECIDE this clause, or its silence would not be evidence"
    );
    for (position, &literal) in fixture.head.iter().enumerate() {
        assert_eq!(
            holds(&fixture.terms, literal, &binding, &small()),
            Some(false),
            "head literal {position} must be FALSE at i = j, v1 = v2 = a[j]: {}",
            crate::format_term_alethe(&fixture.terms, literal)
        );
    }
}

/// SENSITIVITY CONTROL for the assignment above: move ONE stored value off
/// `a[j]` and the head acquires a true literal. Without this, an assignment
/// that refuted the head for an unrelated reason would read identically.
#[test]
fn moving_one_stored_value_off_a_at_j_restores_a_true_head_literal() {
    let fixture = closed_head();
    let binding = vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Index(0)),
        (fixture.j, Value::Index(0)),
        (fixture.v1, Value::Element(0)),
        // v2 != a[j] now, so `(not (= (select (store a i v2) j) (select a j)))` holds.
        (fixture.v2, Value::Element(1)),
    ];
    assert!(
        fixture
            .head
            .iter()
            .any(|&literal| holds(&fixture.terms, literal, &binding, &small()) == Some(true)),
        "the head must acquire a TRUE literal once v2 leaves a[j] — otherwise the \
         countermodel above proves nothing about i = j"
    );
}

/// The designated evaluator's own exhaustive sweep also refutes the head, and a
/// countermodel exists in the INTERESTING region `i = j`, where the two leaves
/// stop being theorems. (`i != j` refutes the head too, for the uninteresting
/// reason that ROW2 then holds, which is why no shape is asserted of the
/// sweep's own witness.)
#[test]
fn the_closer_head_is_refuted_by_the_exhaustive_bounded_sweep() {
    let fixture = closed_head();
    assert!(
        falsify(&fixture.terms, &fixture.head, &small()).is_some(),
        "the independent array model must falsify the closer's head"
    );

    let mut aliased_countermodels = 0usize;
    for cell0 in 0..2 {
        for cell1 in 0..2 {
            for at in 0..2 {
                for first in 0..2 {
                    for second in 0..2 {
                        let binding = vec![
                            (fixture.a, Value::Array(vec![cell0, cell1])),
                            (fixture.i, Value::Index(at)),
                            (fixture.j, Value::Index(at)),
                            (fixture.v1, Value::Element(first)),
                            (fixture.v2, Value::Element(second)),
                        ];
                        if fixture.head.iter().all(|&literal| {
                            holds(&fixture.terms, literal, &binding, &small()) == Some(false)
                        }) {
                            aliased_countermodels += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(
        aliased_countermodels > 0,
        "the head must be refutable with the store and read index ALIASED"
    );
}

/// The LEAVES are not theorems either — which is why negating them is not the
/// solver's UNSAT verdict restated. Each is a ROW2 instance recorded without
/// the `i != j` premise that licenses it.
#[test]
fn each_derived_leaf_is_itself_falsifiable_without_its_index_disequality() {
    let fixture = closed_head();
    for (position, &leaf) in fixture.leaves.iter().enumerate() {
        assert!(
            decidable(&fixture.terms, &[leaf], &small()),
            "the array model must decide leaf {position}"
        );
        assert!(
            falsify(&fixture.terms, &[leaf], &small()).is_some(),
            "leaf {position} is a ROW2 instance and must be falsifiable at i = j: {}",
            crate::format_term_alethe(&fixture.terms, leaf)
        );
    }
}

/// POSITIVE CONTROL. A zero from a broken evaluator is worthless, so pin that
/// this same evaluator refuses to falsify a GENUINE array validity (ROW1 at a
/// syntactically identical index) and decides it.
#[test]
fn the_evaluator_does_not_falsify_a_genuine_row1_validity() {
    let mut terms = TermStore::new();
    let a = array(&mut terms, "a");
    let i = index(&mut terms, "i");
    let v = element(&mut terms, "v");
    let stored = store(&mut terms, a, i, v);
    let read = select(&mut terms, stored, i);
    let row1 = eq(&mut terms, read, v);

    assert!(
        decidable(&terms, &[row1], &small()),
        "the control clause must be decidable or the control proves nothing"
    );
    assert!(
        falsify(&terms, &[row1], &small()).is_none(),
        "the independent array model falsified the ROW1 validity — the evaluator is broken"
    );
}

/// PRINTER PIN. The exact wire text of the refuted head, so a rename or a
/// term-builder change cannot quietly move this test off its subject.
#[test]
fn the_refuted_head_prints_exactly_as_the_finding_recorded_it() {
    let fixture = closed_head();
    let rendered: Vec<String> = fixture
        .head
        .iter()
        .map(|&literal| crate::format_term_alethe(&fixture.terms, literal))
        .collect();
    assert_eq!(
        format!("(cl {})", rendered.join(" ")),
        "(cl (not (= (select (store a i v2) j) (select a j))) \
         (not (= (select a j) (select (store a i v1) j))))"
    );
}
