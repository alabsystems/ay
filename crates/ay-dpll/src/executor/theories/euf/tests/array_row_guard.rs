// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #row2-unit-guard, PRODUCER side.
//!
//! `add_array_row_clauses_with_cap` and `add_array_row_deep_peel_clauses` used
//! to drop the ROW2 guard whenever `are_terms_provably_distinct_from_assertions`
//! could read `i != j` off the top-level assertions, pushing the BARE unit
//! `(= (select (store a i v) j) (select a j))` and recording it as a
//! premiseless `Generic` theory lemma.
//!
//! The disequality that licenses that unit is a PROBLEM assertion, not a theory
//! fact, and it was cited nowhere — so the emitted step was FALSE in some
//! models. The refutation lives in `ay-proof`
//! (`array_row_axiom_guard_negative_tests`, which uses that crate's independent
//! McCarthy evaluator); it is re-checked HERE against the producer's own terms
//! so the two halves cannot drift apart, and then the producer's output is
//! pinned exactly.
//!
//! Corpus measurement behind these tests (`benchmarks/**/*.smt2`, 639 files,
//! `--no-proof -T:10`, 10-way, 30 s wall): the arm fired **152 times in 25
//! files** in three independent BEFORE arms and **0 times** in two AFTER arms,
//! with **0 verdict differences** across all five.

use super::super::*;
use ay_core::{ArraySort, ProofStep, Symbol};

fn int_array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
}

/// One `select(store(a, i, v), j)` pattern plus the AUTHORED `i != j` that used
/// to license the unguarded unit.
struct RowFixture {
    exec: Executor,
    i: TermId,
    j: TermId,
    v: TermId,
    a: TermId,
    /// `(= (select (store a i v) j) (select a j))` — the bare unit.
    row2_eq: TermId,
    /// `(or (= i j) row2_eq)` — the guarded clause.
    row2_clause: TermId,
    /// `(or (not (= i j)) (= (select (store a i v) j) v))` — the ROW1 clause,
    /// which this arm deliberately WITHHOLDS.
    row1_clause: TermId,
}

fn row_fixture() -> RowFixture {
    let mut exec = Executor::new();
    exec.proof_tracker.enable();
    let a = exec.ctx.terms.mk_var("a", int_array_sort());
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let w = exec.ctx.terms.mk_var("w", Sort::Int);

    let stored = exec.ctx.terms.mk_store(a, i, v);
    let select_store = exec.ctx.terms.mk_select(stored, j);
    let select_base = exec.ctx.terms.mk_select(a, j);
    let idx_eq = exec.ctx.terms.mk_eq(i, j);
    let not_idx_eq = exec.ctx.terms.mk_not(idx_eq);
    let row2_eq = exec.ctx.terms.mk_eq(select_store, select_base);
    let row2_clause = exec.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
    let row1_eq = exec.ctx.terms.mk_eq(select_store, v);
    let row1_clause = exec.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);

    // THE AUTHORED PROBLEM: the disequality the old arm mined, plus one use of
    // the read so the pattern is in scope. `w` keeps the second assertion off
    // every axiom shape this test inspects.
    let goal = exec.ctx.terms.mk_eq(select_store, w);
    exec.ctx.assertions.push(not_idx_eq);
    exec.ctx.assertions.push(goal);

    RowFixture {
        exec,
        i,
        j,
        v,
        a,
        row2_eq,
        row2_clause,
        row1_clause,
    }
}

fn recorded_lemmas(exec: &mut Executor) -> Vec<(TheoryLemmaKind, Vec<TermId>)> {
    exec.proof_tracker
        .take_proof()
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, clause, .. } => Some((*kind, clause.clone())),
            _ => None,
        })
        .collect()
}

// ===== the INDEPENDENT bounded McCarthy evaluator (producer-side copy) =====
//
// Two indices and two elements; `Int`-sorted atoms range over `{0, 1}` and an
// array value is any 2-vector over `{0, 1}`. `select`/`store` are re-derived
// from the term structure — this shares no code with the producer, with
// `ay-proof`'s validators, or with `ay-proof`'s own evaluator.

#[derive(Clone, PartialEq, Eq, Debug)]
enum Value {
    Scalar(usize),
    Array(Vec<usize>),
}

fn evaluate(terms: &TermStore, term: TermId, binding: &[(TermId, Value)]) -> Option<Value> {
    if let Some((_, value)) = binding.iter().find(|(id, _)| *id == term) {
        return Some(value.clone());
    }
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };
    match (sym.name(), args.len()) {
        ("select", 2) => {
            let Value::Array(cells) = evaluate(terms, args[0], binding)? else {
                return None;
            };
            let Value::Scalar(at) = evaluate(terms, args[1], binding)? else {
                return None;
            };
            cells.get(at).copied().map(Value::Scalar)
        }
        ("store", 3) => {
            let Value::Array(mut cells) = evaluate(terms, args[0], binding)? else {
                return None;
            };
            let Value::Scalar(at) = evaluate(terms, args[1], binding)? else {
                return None;
            };
            let Value::Scalar(value) = evaluate(terms, args[2], binding)? else {
                return None;
            };
            *cells.get_mut(at)? = value;
            Some(Value::Array(cells))
        }
        _ => None,
    }
}

/// Whether `literal` holds; `None` when the model cannot decide it, which is a
/// FAILURE to refute and never evidence of validity.
fn holds(terms: &TermStore, literal: TermId, binding: &[(TermId, Value)]) -> Option<bool> {
    match terms.get(literal) {
        TermData::Not(inner) => holds(terms, *inner, binding).map(|value| !value),
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            Some(evaluate(terms, args[0], binding)? == evaluate(terms, args[1], binding)?)
        }
        TermData::App(sym, args) if sym.name() == "or" => {
            let mut any = false;
            for &arg in args {
                any |= holds(terms, arg, binding)?;
            }
            Some(any)
        }
        _ => None,
    }
}

/// THE NAMED COUNTERMODEL of the step the producer no longer emits, checked
/// here against the PRODUCER's own terms: `i = j = 0`, `a = [0, 1]`, `v = 1`.
/// `select(store(a, i, v), j) = 1` and `select(a, j) = 0`, so the unit's only
/// literal is false and the clause has no true literal.
#[test]
fn the_bare_row2_unit_the_producer_dropped_is_false_at_i_equals_j() {
    let fixture = row_fixture();
    let binding = vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Scalar(0)),
        (fixture.j, Value::Scalar(0)),
        (fixture.v, Value::Scalar(1)),
    ];
    assert_eq!(
        holds(&fixture.exec.ctx.terms, fixture.row2_eq, &binding),
        Some(false),
        "the bare ROW2 unit must be FALSE at i = j = 0, a = [0, 1], v = 1"
    );
    // And the GUARDED clause the producer emits instead is true there.
    assert_eq!(
        holds(&fixture.exec.ctx.terms, fixture.row2_clause, &binding),
        Some(true),
        "the guarded ROW2 clause must hold at the very assignment that refutes the unit"
    );
}

/// SENSITIVITY CONTROL: move `v` onto `a[j]` and the bare unit holds again, so
/// the countermodel above is about the stored value, not a broken evaluator.
#[test]
fn the_bare_row2_unit_holds_once_v_lands_on_a_at_j() {
    let fixture = row_fixture();
    let binding = vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Scalar(0)),
        (fixture.j, Value::Scalar(0)),
        (fixture.v, Value::Scalar(0)),
    ];
    assert_eq!(
        holds(&fixture.exec.ctx.terms, fixture.row2_eq, &binding),
        Some(true),
        "with v = a[j] the ROW2 unit holds — otherwise the countermodel proves nothing"
    );
}

/// EXHAUSTIVE: the guarded clause has NO countermodel over the whole 2x2 box,
/// and the bare unit has one. A complete refutation on one side, a complete
/// verification on the other.
#[test]
fn the_guarded_clause_is_valid_and_the_bare_unit_is_not_over_the_whole_box() {
    let fixture = row_fixture();
    let terms = &fixture.exec.ctx.terms;
    let mut unit_countermodels = 0usize;
    for cell0 in 0..2 {
        for cell1 in 0..2 {
            for at_i in 0..2 {
                for at_j in 0..2 {
                    for stored in 0..2 {
                        let binding = vec![
                            (fixture.a, Value::Array(vec![cell0, cell1])),
                            (fixture.i, Value::Scalar(at_i)),
                            (fixture.j, Value::Scalar(at_j)),
                            (fixture.v, Value::Scalar(stored)),
                        ];
                        assert_eq!(
                            holds(terms, fixture.row2_clause, &binding),
                            Some(true),
                            "the guarded ROW2 clause must hold everywhere in the box"
                        );
                        if holds(terms, fixture.row2_eq, &binding) == Some(false) {
                            unit_countermodels += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(
        unit_countermodels > 0,
        "the bare ROW2 unit must be refutable somewhere in the box"
    );
}

/// THE PRODUCER, EAGER PATH. With `i != j` asserted it must emit the GUARDED
/// clause and never the bare unit, and the recorded lemma must carry the
/// checker's own ROW2 kind rather than `Generic`.
#[test]
fn the_eager_row_pass_emits_the_guarded_clause_and_never_the_bare_unit() {
    let mut fixture = row_fixture();
    fixture.exec.add_array_row_clauses();

    assert!(
        fixture.exec.ctx.assertions.contains(&fixture.row2_clause),
        "the guarded ROW2 clause must be asserted"
    );
    assert!(
        !fixture.exec.ctx.assertions.contains(&fixture.row2_eq),
        "the UNGUARDED ROW2 unit must never be asserted again"
    );

    let lemmas = recorded_lemmas(&mut fixture.exec);
    assert!(
        lemmas.contains(&(
            TheoryLemmaKind::ArraySelectStore { index_eq: false },
            vec![fixture.row2_clause]
        )),
        "the guarded clause must be recorded under the checker's own ROW2 kind, got {lemmas:?}"
    );
    assert!(
        !lemmas
            .iter()
            .any(|(_, clause)| clause.as_slice() == [fixture.row2_eq]),
        "no proof step may conclude the unguarded ROW2 unit, got {lemmas:?}"
    );
    assert!(
        !lemmas
            .iter()
            .any(|(kind, _)| *kind == TheoryLemmaKind::Generic),
        "this pass must record no trust-kind array lemma at all, got {lemmas:?}"
    );
}

/// THE RETAINED OPTIMISATION. Carrying the ROW2 guard does not re-open the ROW1
/// case split: withholding a VALID clause costs completeness only, and this arm
/// still withholds it. Without this pin, "delete the whole distinctness arm"
/// would pass the test above while doubling the clause count on 25 corpus files.
#[test]
fn the_eager_row_pass_still_withholds_row1_when_the_indices_are_provably_distinct() {
    let mut fixture = row_fixture();
    fixture.exec.add_array_row_clauses();
    assert!(
        !fixture.exec.ctx.assertions.contains(&fixture.row1_clause),
        "ROW1 must stay withheld when the indices are provably distinct"
    );
}

/// CONTROL on the arm boundary: with NO asserted disequality the ordinary path
/// runs and emits BOTH clauses — so the test above is about the distinctness
/// arm and not about ROW1 being unreachable in this fixture.
#[test]
fn without_the_asserted_disequality_the_ordinary_path_emits_both_clauses() {
    let mut fixture = row_fixture();
    let _ = fixture.exec.ctx.assertions.remove(0);
    fixture.exec.add_array_row_clauses();
    assert!(
        fixture.exec.ctx.assertions.contains(&fixture.row2_clause),
        "the ordinary path must emit the guarded ROW2 clause"
    );
    assert!(
        fixture.exec.ctx.assertions.contains(&fixture.row1_clause),
        "the ordinary path must emit the ROW1 clause"
    );
}

/// THE PRODUCER, DEEP-PEEL PATH — the same defect had a second site.
#[test]
fn the_deep_peel_pass_emits_the_guarded_clause_and_never_the_bare_unit() {
    let mut fixture = row_fixture();
    let emitted = fixture.exec.add_array_row_deep_peel_clauses(usize::MAX);
    assert!(
        emitted > 0,
        "the peel pass must emit something for this shape"
    );

    assert!(
        fixture.exec.ctx.assertions.contains(&fixture.row2_clause),
        "the peel pass must assert the guarded ROW2 clause"
    );
    assert!(
        !fixture.exec.ctx.assertions.contains(&fixture.row2_eq),
        "the peel pass must never assert the unguarded ROW2 unit"
    );

    let lemmas = recorded_lemmas(&mut fixture.exec);
    assert!(
        lemmas.contains(&(
            TheoryLemmaKind::ArraySelectStore { index_eq: false },
            vec![fixture.row2_clause]
        )),
        "the peel pass must record the checker's own ROW2 kind, got {lemmas:?}"
    );
    assert!(
        !lemmas
            .iter()
            .any(|(kind, _)| *kind == TheoryLemmaKind::Generic),
        "the peel pass must record no trust-kind array lemma, got {lemmas:?}"
    );
}

/// PRINTER PIN on the producer's exact wire text: the clause the eager pass
/// asserts, rendered by the proof printer.
#[test]
fn the_emitted_guarded_clause_prints_exactly() {
    let mut fixture = row_fixture();
    fixture.exec.add_array_row_clauses();
    let lemmas = recorded_lemmas(&mut fixture.exec);
    let rendered: Vec<String> = lemmas
        .iter()
        .filter(|(kind, _)| *kind == TheoryLemmaKind::ArraySelectStore { index_eq: false })
        .map(|(_, clause)| {
            let literals: Vec<String> = clause
                .iter()
                .map(|&t| ay_proof::format_term_alethe(&fixture.exec.ctx.terms, t))
                .collect();
            format!("(cl {})", literals.join(" "))
        })
        .collect();
    assert_eq!(
        rendered,
        vec!["(cl (or (= i j) (= (select (store a i v) j) (select a j))))".to_string()],
        "the producer's ROW2 wire text changed"
    );
}

/// FIXTURE WELL-FORMEDNESS: the builders must not have folded the very terms
/// this file is about, or every assertion here would be vacuous.
#[test]
fn the_fixture_terms_are_the_primitive_row2_shapes() {
    let fixture = row_fixture();
    let terms = &fixture.exec.ctx.terms;
    assert_ne!(fixture.row2_eq, fixture.row2_clause);
    assert_ne!(fixture.row2_eq, terms.true_term());
    assert_ne!(fixture.row2_clause, terms.true_term());
    assert!(matches!(
        terms.get(fixture.row2_clause),
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2
    ));
}
