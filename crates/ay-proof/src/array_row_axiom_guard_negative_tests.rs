// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The UNGUARDED ROW2 unit is not a lemma, and this file is the independent
//! refutation of it.
//!
//! `theories::euf::array_row`'s `row2_unit_distinct_indices` arm used to push
//!
//! ```text
//! (= (select (store a i v) j) (select a j))
//! ```
//!
//! as a BARE unit — with no premise citing the `i != j` that licenses it —
//! whenever `are_terms_provably_distinct_from_assertions` could read that
//! disequality off the top-level assertions, and
//! `euf::record_array_axiom_proof` recorded it as a premiseless `Generic`
//! theory lemma. A theory lemma asserts a clause valid in EVERY model of the
//! theory; this one is FALSE at `i = j` whenever `v` differs from `a[j]`, and
//! the disequality that rescues it is a PROBLEM fact, not a theory fact.
//!
//! Measured on `benchmarks/**/*.smt2` (639 files, `--no-proof -T:10`, 10-way,
//! two independent census arms of the same binary): the arm fired **152 times
//! in 25 files**, and every one of them was licensed by an ASSERTED
//! disequality — the `are_terms_distinct_constants` sub-case (where the unit
//! really is a theory validity) fired **0 times**.
//!
//! The producer now always carries the guard, i.e. emits the ordinary
//! two-literal ROW2 clause `(or (= i j) row2)`. This file pins BOTH halves of
//! why that is the right shape, in the crate that owns the array validators:
//! the bare unit is refutable, the guarded clause is not, and the checker's own
//! recognizer accepts exactly the second.
//!
//! The evaluator is [`crate::array_row_axiom::model`] — the campaign's bounded
//! McCarthy model, which shares no code with any producer or validator.

use super::model::{
    array, decidable, element, eq, falsify, holds, index, select, small, store, Value,
};
use crate::quality::check_proof_strict;
use ay_core::{
    AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};

/// The exact terms of one `row2_unit_distinct_indices` instance.
struct Row2Instance {
    terms: TermStore,
    a: TermId,
    i: TermId,
    j: TermId,
    v: TermId,
    /// `(= (select (store a i v) j) (select a j))` — the clause the arm pushed.
    unit: TermId,
    /// `(= i j)` — the guard the arm dropped.
    index_eq: TermId,
}

fn row2_instance() -> Row2Instance {
    let mut terms = TermStore::new();
    let a = array(&mut terms, "a");
    let i = index(&mut terms, "i");
    let j = index(&mut terms, "j");
    let v = element(&mut terms, "v");

    let stored = store(&mut terms, a, i, v);
    let read_store = select(&mut terms, stored, j);
    let read_base = select(&mut terms, a, j);
    let unit = eq(&mut terms, read_store, read_base);
    let index_eq = eq(&mut terms, i, j);
    Row2Instance {
        terms,
        a,
        i,
        j,
        v,
        unit,
        index_eq,
    }
}

/// `i = j = idx0`, `a = [elt0, elt1]`, `v = elt1`.
///
/// `select(store(a, i, v), j) = elt1` and `select(a, j) = elt0`, so the single
/// literal of the emitted clause is FALSE and the clause has no true literal:
/// a COMPLETE refutation, not a sampled one.
fn falsifying_binding(fixture: &Row2Instance) -> Vec<(TermId, Value)> {
    vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Index(0)),
        (fixture.j, Value::Index(0)),
        (fixture.v, Value::Element(1)),
    ]
}

/// THE NAMED COUNTERMODEL, checked literal by literal.
#[test]
fn the_unguarded_row2_unit_is_false_at_i_equals_j_with_v_off_a_at_j() {
    let fixture = row2_instance();
    let binding = falsifying_binding(&fixture);
    assert!(
        decidable(&fixture.terms, &[fixture.unit], &small()),
        "the array model must DECIDE this clause, or its silence would not be evidence"
    );
    assert_eq!(
        holds(&fixture.terms, fixture.unit, &binding, &small()),
        Some(false),
        "the emitted unit must be FALSE at i = j = 0, a = [e0, e1], v = e1: {}",
        crate::format_term_alethe(&fixture.terms, fixture.unit)
    );
}

/// SENSITIVITY CONTROL 1: move `v` ONTO `a[j]` and the unit holds again, so the
/// countermodel above is about the stored value and not a degenerate carrier.
#[test]
fn moving_v_onto_a_at_j_restores_the_unguarded_unit() {
    let fixture = row2_instance();
    let binding = vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Index(0)),
        (fixture.j, Value::Index(0)),
        (fixture.v, Value::Element(0)),
    ];
    assert_eq!(
        holds(&fixture.terms, fixture.unit, &binding, &small()),
        Some(true),
        "with v = a[j] the ROW2 unit holds — otherwise the countermodel proves nothing"
    );
}

/// SENSITIVITY CONTROL 2: separate the indices and the unit holds for EVERY
/// stored value. This is the whole content of the missing guard.
#[test]
fn separating_the_indices_restores_the_unguarded_unit_for_every_stored_value() {
    let fixture = row2_instance();
    for cell0 in 0..2 {
        for cell1 in 0..2 {
            for stored in 0..2 {
                let binding = vec![
                    (fixture.a, Value::Array(vec![cell0, cell1])),
                    (fixture.i, Value::Index(1)),
                    (fixture.j, Value::Index(0)),
                    (fixture.v, Value::Element(stored)),
                ];
                assert_eq!(
                    holds(&fixture.terms, fixture.unit, &binding, &small()),
                    Some(true),
                    "at i != j the ROW2 unit must hold (a = [{cell0}, {cell1}], v = {stored})"
                );
            }
        }
    }
}

/// The bare unit is refuted by the evaluator's own EXHAUSTIVE sweep as well,
/// and the witness it returns aliases the indices.
#[test]
fn the_unguarded_row2_unit_is_refuted_by_the_exhaustive_bounded_sweep() {
    let fixture = row2_instance();
    let witness = falsify(&fixture.terms, &[fixture.unit], &small())
        .expect("the independent array model must falsify the unguarded ROW2 unit");
    let at = |term: TermId| {
        witness
            .iter()
            .find(|(id, _)| *id == term)
            .map(|(_, value)| value.clone())
    };
    assert_eq!(
        at(fixture.i),
        at(fixture.j),
        "every countermodel of ROW2 must ALIAS the store and read indices"
    );
}

/// THE FIX'S OWN CLAIM, checked by the same evaluator: the GUARDED clause the
/// producer now emits has NO countermodel in the sweep box, so it is a lemma
/// where the unit was not.
#[test]
fn the_guarded_row2_clause_survives_the_exhaustive_sweep() {
    let fixture = row2_instance();
    let clause = [fixture.index_eq, fixture.unit];
    assert!(
        decidable(&fixture.terms, &clause, &small()),
        "the model must decide the guarded clause or its silence is not evidence"
    );
    assert!(
        falsify(&fixture.terms, &clause, &small()).is_none(),
        "the independent array model falsified the GUARDED ROW2 clause — the fix is wrong"
    );
    // And specifically at the assignment that refutes the bare unit, the guard
    // literal is the one carrying the clause.
    let binding = falsifying_binding(&fixture);
    assert_eq!(
        holds(&fixture.terms, fixture.index_eq, &binding, &small()),
        Some(true),
        "at i = j the guard literal must be the true one"
    );
}

/// THE CHECKER'S OWN ANSWER. `recognize_array_select_store` is the validator
/// entry point the strict checker uses; it accepts the guarded clause as the
/// ROW2 schema and refuses the bare unit. Nothing here relaxes it — this test
/// exists so a later pass cannot "fix" the census by teaching a validator the
/// unconditional form.
#[test]
fn the_checker_accepts_the_guarded_clause_and_refuses_the_bare_unit() {
    let fixture = row2_instance();
    assert_eq!(
        crate::recognize_array_select_store(&fixture.terms, &[fixture.index_eq, fixture.unit]),
        Some(false),
        "the guarded ROW2 clause must be the index-UNEQUAL schema"
    );
    assert_eq!(
        crate::recognize_array_select_store(&fixture.terms, &[fixture.unit]),
        None,
        "no ROW schema may accept the unconditional ROW2 unit"
    );
    assert_eq!(
        crate::recognize_array_theory_lemma(&fixture.terms, &[fixture.unit]),
        None,
        "no array schema at all may accept the unconditional ROW2 unit"
    );
}

/// Both clauses closed into a self-contained refutation and handed to the
/// UNTOUCHED strict checker: the guarded one passes, the bare unit tagged with
/// the SAME kind is rejected.
#[test]
fn strict_checking_accepts_the_guarded_clause_and_rejects_the_bare_unit() {
    let mut fixture = row2_instance();

    let mut guarded = Proof::new();
    guarded.steps.push(ProofStep::TheoryLemma {
        theory: "ArrayEUF".to_string(),
        clause: vec![fixture.index_eq, fixture.unit],
        farkas: None,
        kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
        lia: None,
    });
    let not_index_eq = fixture.terms.mk_not(fixture.index_eq);
    let not_unit = fixture.terms.mk_not(fixture.unit);
    guarded.steps.push(ProofStep::Assume(not_index_eq));
    guarded.steps.push(ProofStep::Assume(not_unit));
    guarded.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1), ProofId(2)],
        args: Vec::new(),
    });
    assert!(
        check_proof_strict(&guarded, &fixture.terms).is_ok(),
        "the strict checker must accept the guarded ROW2 clause"
    );

    let mut bare = Proof::new();
    bare.steps.push(ProofStep::TheoryLemma {
        theory: "ArrayEUF".to_string(),
        clause: vec![fixture.unit],
        farkas: None,
        kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
        lia: None,
    });
    bare.steps.push(ProofStep::Assume(not_unit));
    bare.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    assert!(
        check_proof_strict(&bare, &fixture.terms).is_err(),
        "the strict checker must REJECT the unconditional ROW2 unit under a ROW kind"
    );
}

/// POSITIVE CONTROL for the evaluator: it must NOT falsify a genuine array
/// validity, or every `false` verdict above would be worthless.
#[test]
fn the_evaluator_does_not_falsify_a_genuine_row1_validity() {
    let mut terms = TermStore::new();
    let a = array(&mut terms, "a");
    let i = index(&mut terms, "i");
    let v = element(&mut terms, "v");
    let stored = store(&mut terms, a, i, v);
    let read = select(&mut terms, stored, i);
    let row1 = eq(&mut terms, read, v);
    assert!(decidable(&terms, &[row1], &small()));
    assert!(
        falsify(&terms, &[row1], &small()).is_none(),
        "the independent array model falsified a ROW1 validity — the evaluator is broken"
    );
}

/// PRINTER PIN. The exact wire text of the refuted unit and of the guarded
/// clause that replaced it, so a rename or a term-builder change cannot quietly
/// move this file off its subject.
#[test]
fn the_refuted_unit_and_its_guarded_replacement_print_exactly() {
    let fixture = row2_instance();
    assert_eq!(
        format!(
            "(cl {})",
            crate::format_term_alethe(&fixture.terms, fixture.unit)
        ),
        "(cl (= (select (store a i v) j) (select a j)))"
    );
    let rendered: Vec<String> = [fixture.index_eq, fixture.unit]
        .iter()
        .map(|&literal| crate::format_term_alethe(&fixture.terms, literal))
        .collect();
    assert_eq!(
        format!("(cl {})", rendered.join(" ")),
        "(cl (= i j) (= (select (store a i v) j) (select a j)))"
    );
}

/// The fixture's own well-formedness, so a builder change that silently folds
/// one of these terms cannot make the whole file vacuous.
#[test]
fn the_fixture_terms_are_the_primitive_row2_shapes() {
    let fixture = row2_instance();
    assert!(
        matches!(
            fixture.terms.get(fixture.unit),
            ay_core::TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2
        ),
        "the ROW2 unit must stay a primitive equality"
    );
    assert!(
        matches!(fixture.terms.sort(fixture.index_eq), Sort::Bool),
        "the guard must be a Bool literal"
    );
    assert_ne!(
        fixture.i, fixture.j,
        "the two indices must be distinct terms"
    );
}
