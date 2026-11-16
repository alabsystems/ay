// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Component callback coverage; actual SAT installation and replay ownership
/// are checked separately at the DPLL integration boundary.
#[test]
fn current_read_acknowledgments_survive_applied_memo_eviction() {
    const READS: usize = 8_193;
    const EXISTING_MEMO_CAP: usize = 8_192;
    let mut terms = TermStore::new();
    let array_sort = make_array_sort();
    let base = terms.mk_var("base", array_sort.clone());
    let alias = terms.mk_var("alias", array_sort);
    let index = terms.mk_var("store_index", Sort::Int);
    let value = terms.mk_var("value", Sort::Int);
    let stored = terms.mk_store(base, index, value);
    let _ = terms.mk_eq(alias, stored);
    for n in 0..READS {
        let read_index = terms.mk_var(format!("read_index_{n}"), Sort::Int);
        let read = terms.mk_select(alias, read_index);
        let base_read = terms.mk_select(base, read_index);
        let _ = terms.mk_eq(index, read_index);
        let _ = terms.mk_eq(read, base_read);
    }

    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();
    let Some(TheoryResult::NeedLemmas(clauses)) = solver.check_row2() else {
        panic!("every unassigned alias read must have a guarded ROW2 obligation");
    };
    assert_eq!(clauses.len(), READS);
    let unique: HashSet<_> = clauses.iter().map(|lemma| lemma.clause.clone()).collect();
    assert_eq!(unique.len(), READS);

    // Exercise the production callback for the clauses just observed, without
    // assigning their literals or writing private acknowledgment/cache state.
    // This models an installing caller's sparse theory delivery; it is not a
    // claim that this component test itself has installed anything in SAT.
    for lemma in &clauses {
        solver.note_applied_theory_lemma(&lemma.clause);
    }
    assert!(solver.applied_theory_lemmas.len() <= EXISTING_MEMO_CAP);

    for _ in 0..3 {
        solver.generate_all_lazy_row2_axioms();
        assert!(
            solver.check_row2().is_none(),
            "evicting the bounded memo must not lose current exact-clause acknowledgments"
        );
        assert!(solver.applied_theory_lemmas.len() <= EXISTING_MEMO_CAP);
    }
}
