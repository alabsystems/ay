// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NEGATIVE: a surface override that is not the compositional rendering of a
//! certified role makes the printed text disagree with the term-DAG roles the
//! extractor found. Every such disagreement declines (the honest `hole`)
//! instead of emitting an `arrays_idx` or `trans` step that pinned Carcara
//! rejects (`invalid`, strictly worse than `holey`). These pin the read-back
//! store-index identity and both conclusion-read (`same_pair`) identities,
//! which `non_compositional_store_surface_declines` (untouched cell, store
//! index) does not reach.

use super::*;

struct Clauses {
    terms: TermStore,
    store: TermId,
    /// `(select U k)`, read by both clauses.
    read: TermId,
    /// `(cl (not (= U (store V i x))) (not (= k i)) (= (select U k) x))`.
    read_back: [TermId; 3],
    /// `(cl (not (= U (store V i x))) (= i k) (= (select V k) (select U k)))`.
    untouched: [TermId; 3],
}

fn clauses() -> Clauses {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::Int, Sort::Int);
    let v = terms.mk_var("V", array.clone());
    let u = terms.mk_var("U", array.clone());
    let [i, k, x] = ["i", "k", "x"].map(|name| terms.mk_var(name, Sort::Int));
    let store = terms.mk_app(Symbol::named("store"), [v, i, x], array);
    let guard_atom = terms.mk_app(Symbol::named("="), [u, store], Sort::Bool);
    let guard = terms.mk_not_raw(guard_atom);
    let read = terms.mk_app(Symbol::named("select"), [u, k], Sort::Int);
    let mirrored = terms.mk_app(Symbol::named("="), [k, i], Sort::Bool);
    let apart = terms.mk_not_raw(mirrored);
    let value_read = terms.mk_app(Symbol::named("="), [read, x], Sort::Bool);
    let index = terms.mk_app(Symbol::named("="), [i, k], Sort::Bool);
    let base_read = terms.mk_app(Symbol::named("select"), [v, k], Sort::Int);
    let cell = terms.mk_app(Symbol::named("="), [base_read, read], Sort::Bool);
    Clauses {
        terms,
        store,
        read,
        read_back: [guard, apart, value_read],
        untouched: [guard, index, cell],
    }
}

fn lowered(
    terms: &TermStore,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
) -> Option<String> {
    AlethePrinter::new_with_overrides_and_budget(terms, overrides, None)
        .format_array_guarded_row_expansion(ProofId(9), clause)
}

/// The read-back store re-spelled `(store V (+ i 0) x)`: `arrays_idx` reads
/// `x` back only at `(+ i 0)`, while the index literal names `i`.
#[test]
fn non_compositional_read_back_store_declines() {
    let f = clauses();
    assert!(crate::recognize_array_guarded_row_expansion(
        &f.terms,
        &f.read_back
    ));
    assert!(lowered(&f.terms, &f.read_back, None).is_some());
    let mut overrides = HashMap::default();
    overrides.insert(f.store, "(store V (+ i 0) x)".to_string());
    assert!(lowered(&f.terms, &f.read_back, Some(&overrides)).is_none());
    let mut allowance = SCREEN_WORK_BUDGET;
    assert!(!checked_guarded_row_expansion_lowering_supported(
        &f.terms,
        &f.read_back,
        Some(&overrides),
        &mut allowance
    ));
}

/// The conclusion's read re-spelled `(select U (+ k 0))` is not the read the
/// `trans` chain reaches, in either lowered case.
#[test]
fn non_compositional_conclusion_read_declines() {
    let f = clauses();
    let mut overrides = HashMap::default();
    overrides.insert(f.read, "(select U (+ k 0))".to_string());
    for (case, clause) in [("read_back", f.read_back), ("untouched", f.untouched)] {
        assert!(
            crate::recognize_array_guarded_row_expansion(&f.terms, &clause),
            "{case}"
        );
        assert!(lowered(&f.terms, &clause, None).is_some(), "{case}");
        assert!(
            lowered(&f.terms, &clause, Some(&overrides)).is_none(),
            "{case}"
        );
    }
}
