use super::*;

struct Fixture {
    terms: TermStore,
    stored: TermId,
    read_array: TermId,
    read: TermId,
    base_read: TermId,
    alias_eq: Option<TermId>,
    index_eq: TermId,
    read_eq: TermId,
}

fn fixture(alias: bool) -> Fixture {
    let mut terms = TermStore::new();
    let array_sort = make_array_sort();
    let a = terms.mk_var("base", array_sort.clone());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let value = terms.mk_var("value", Sort::Int);
    let stored = terms.mk_store(a, i, value);
    let read_array = if alias {
        terms.mk_var("alias", array_sort)
    } else {
        stored
    };
    let read = terms.mk_select(read_array, j);
    let base_read = terms.mk_select(a, j);
    let alias_eq = alias.then(|| terms.mk_eq(read_array, stored));
    let index_eq = terms.mk_eq(i, j);
    let read_eq = terms.mk_eq(read, base_read);
    Fixture {
        terms,
        stored,
        read_array,
        read,
        base_read,
        alias_eq,
        index_eq,
        read_eq,
    }
}

fn expected(f: &Fixture) -> Vec<TheoryLit> {
    let mut clause = vec![
        TheoryLit::new(f.index_eq, true),
        TheoryLit::new(f.read_eq, true),
    ];
    if let Some(alias) = f.alias_eq {
        clause.push(TheoryLit::new(alias, false));
    }
    clause.sort_by_key(|lit| (lit.term.0, lit.value));
    clause
}

fn emitted(result: Option<TheoryResult>) -> Vec<TheoryLemma> {
    match result {
        Some(TheoryResult::NeedLemmas(lemmas)) => lemmas,
        other => panic!("expected productive ROW2 lemmas, got {other:?}"),
    }
}

#[test]
fn direct_read_true_then_pop_false_keeps_unapplied_work() {
    let f = fixture(false);
    let mut solver = ArraySolver::new(&f.terms);
    solver.populate_caches();
    solver.push();
    solver.assert_literal(f.read_eq, true);
    solver.generate_all_lazy_row2_axioms();
    assert!(solver.check_row2().is_none());
    assert!(solver.applied_theory_lemmas.is_empty());
    solver.pop();
    solver.push();
    solver.assert_literal(f.read_eq, false);
    solver.assert_literal(f.index_eq, false);
    solver.generate_all_lazy_row2_axioms();
    let lemmas = emitted(solver.check_row2());
    assert!(lemmas.iter().any(|l| l.clause == expected(&f)));
    solver.pop();
}

#[test]
fn exact_applied_clauses_suppress_repeated_emission_until_real_reset() {
    for alias in [false, true] {
        let f = fixture(alias);
        let mut solver = ArraySolver::new(&f.terms);
        solver.populate_caches();
        solver.generate_all_lazy_row2_axioms();
        let lemmas = emitted(solver.check_row2());
        assert!(lemmas.iter().any(|l| l.clause == expected(&f)));
        for lemma in &lemmas {
            solver.note_applied_theory_lemma(&lemma.clause);
        }
        for _ in 0..3 {
            solver.generate_all_lazy_row2_axioms();
            assert!(
                solver.check_row2().is_none(),
                "an actually applied clause must not cause a no-op lemma loop"
            );
        }
        solver.reset();
        solver.populate_caches();
        solver.generate_all_lazy_row2_axioms();
        let reset = emitted(solver.check_row2());
        assert!(reset.iter().any(|l| l.clause == expected(&f)));
    }
}

#[test]
fn a_new_alias_explanation_is_not_completed_by_an_old_applied_guard() {
    let mut f = fixture(true);
    let mid = f.terms.mk_var("mid", make_array_sort());
    let first_edge = f.terms.mk_eq(f.read_array, mid);
    let second_edge = f.terms.mk_eq(mid, f.stored);
    let mut solver = ArraySolver::new(&f.terms);
    solver.populate_caches();
    solver.push();
    solver.assert_literal(f.alias_eq.unwrap(), true);
    solver.generate_all_lazy_row2_axioms();
    let old = emitted(solver.check_row2());
    assert!(old.iter().any(|l| l.clause == expected(&f)));
    for lemma in &old {
        solver.note_applied_theory_lemma(&lemma.clause);
    }
    solver.pop();
    // This is the actual DPLL callback protocol for clauses which remain in SAT.
    for lemma in &old {
        solver.note_applied_theory_lemma(&lemma.clause);
    }
    solver.push();
    solver.assert_literal(first_edge, true);
    solver.assert_literal(second_edge, true);
    solver.generate_all_lazy_row2_axioms();
    let current = emitted(solver.check_row2());
    let mut next = vec![
        TheoryLit::new(first_edge, false),
        TheoryLit::new(second_edge, false),
        TheoryLit::new(f.index_eq, true),
        TheoryLit::new(f.read_eq, true),
    ];
    next.sort_by_key(|lit| (lit.term.0, lit.value));
    assert!(current.iter().any(|l| l.clause == next));
    solver.pop();
}

#[test]
fn registered_scope_rebuild_retires_dead_read_work_and_gc_indexes() {
    let mut f = fixture(true);
    let dead_array = f.terms.mk_var("unregistered_alias", make_array_sort());
    let j = match f.terms.get(f.read) {
        TermData::App(_, args) => args[1],
        _ => unreachable!(),
    };
    let dead_read = f.terms.mk_select(dead_array, j);
    let dead_alias_eq = f.terms.mk_eq(dead_array, f.stored);
    let dead_read_eq = f.terms.mk_eq(dead_read, f.base_read);
    let mut solver = ArraySolver::new(&f.terms);
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();
    let initial = emitted(solver.check_row2());
    assert_eq!(initial.len(), 2);
    solver.enable_registered_atom_scope(true);
    for root in [f.alias_eq.unwrap(), f.index_eq, f.read_eq] {
        solver.register_atom(root);
    }
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();
    let current = emitted(solver.check_row2());
    assert_eq!(current.len(), 1);
    assert_eq!(current[0].clause, expected(&f));
    assert!(current.iter().all(|l| l
        .clause
        .iter()
        .all(|lit| lit.term != dead_alias_eq && lit.term != dead_read_eq)));
    assert!(!solver.row2_down_work.contains(&(f.stored, dead_read)));
    assert!(solver.row2_down_work.contains(&(f.stored, f.read)));
}

#[test]
fn lazy64_advances_past_applied_alias_work_without_a_noop_loop() {
    let mut f = fixture(true);
    let j = match f.terms.get(f.read) {
        TermData::App(_, args) => args[1],
        _ => unreachable!(),
    };
    for n in 0..128 {
        let array = f.terms.mk_var(format!("alias_{n}"), make_array_sort());
        let read = f.terms.mk_select(array, j);
        f.terms.mk_eq(array, f.stored);
        f.terms.mk_eq(read, f.base_read);
    }
    let mut solver = ArraySolver::new(&f.terms);
    solver.populate_caches();
    let mut seen = HashSet::default();
    for expected_count in [64, 64, 1] {
        solver.generate_lazy_row2_axioms();
        let batch = emitted(solver.check_row2());
        assert_eq!(batch.len(), expected_count);
        for lemma in batch {
            assert!(
                seen.insert(lemma.clause.clone()),
                "no already applied clause may spend a refinement round"
            );
            solver.note_applied_theory_lemma(&lemma.clause);
        }
    }
    assert_eq!(seen.len(), 129);
    solver.generate_lazy_row2_axioms();
    assert!(solver.check_row2().is_none());
}

#[test]
fn held_original_interrupt_prevents_candidate_queue_materialization() {
    let f = fixture(true);
    let mut solver = ArraySolver::new(&f.terms);
    solver.populate_caches();
    solver.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    solver.generate_lazy_row2_axioms();
    solver.generate_all_lazy_row2_axioms();
    assert!(solver.pending_axioms.is_empty());
    assert!(solver.row2_down_work.is_empty());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

#[test]
fn equal_index_prefix_does_not_spend_the_lazy64_discovery_budget_again() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("base", make_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let stored = terms.mk_store(a, i, v);
    let alias = terms.mk_var("alias", make_array_sort());
    let alias_eq = terms.mk_eq(alias, stored);
    let mut points = Vec::new();
    for n in 0..65 {
        let j = terms.mk_var(format!("j_{n}"), Sort::Int);
        let read = terms.mk_select(alias, j);
        let base_read = terms.mk_select(a, j);
        let index_eq = terms.mk_eq(i, j);
        let read_eq = terms.mk_eq(read, base_read);
        points.push((read, index_eq, read_eq));
    }
    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    // Pick the actual cached order, so this adversarial prefix requires no
    // assumption about variable names or deterministic-hasher iteration order.
    let order: Vec<_> = solver
        .select_cache
        .iter()
        .filter_map(|(&read, &(array, _))| (array == alias).then_some(read))
        .collect();
    assert_eq!(order.len(), 65);
    for &read in &order[..64] {
        let &(_, eq, _) = points.iter().find(|p| p.0 == read).unwrap();
        solver.assert_literal(eq, true);
    }
    let &(_, distinct_index, distinct_read) = points.iter().find(|p| p.0 == order[64]).unwrap();
    solver.assert_literal(distinct_index, false);
    solver.generate_lazy_row2_axioms();
    let lemmas = emitted(solver.check_row2());
    let mut expected = vec![
        TheoryLit::new(alias_eq, false),
        TheoryLit::new(distinct_index, true),
        TheoryLit::new(distinct_read, true),
    ];
    expected.sort_by_key(|lit| (lit.term.0, lit.value));
    assert!(
        lemmas.iter().any(|l| l.clause == expected),
        "a current ROW1 prefix must not starve the later ROW2 obligation"
    );
}

/// Emission is a proposal, not acknowledgment of a SAT installation.
#[test]
fn emitted_without_any_callback_stays_requestable_on_the_same_live_work() {
    let f = fixture(true);
    let mut solver = ArraySolver::new(&f.terms);
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();
    let first = emitted(solver.check_row2());
    assert!(first.iter().any(|lemma| lemma.clause == expected(&f)));
    for _ in 0..3 {
        let again = emitted(solver.check_row2());
        assert!(again.iter().any(|lemma| lemma.clause == expected(&f)));
        assert!(solver.applied_theory_lemmas.is_empty());
    }
}

fn requested_pairs(result: Option<TheoryResult>) -> HashSet<(TermId, TermId)> {
    let requests = match result {
        Some(TheoryResult::NeedModelEquality(request)) => vec![request],
        Some(TheoryResult::NeedModelEqualities(requests)) => requests,
        other => panic!("expected productive missing ROW2 atom requests, got {other:?}"),
    };
    requests
        .into_iter()
        .map(|request| ArraySolver::ordered_pair(request.lhs, request.rhs))
        .collect()
}

#[test]
fn false_alias_with_missing_atoms_parks_and_reactivates_exact_work() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", make_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let value = terms.mk_var("value", Sort::Int);
    let stored = terms.mk_store(base, i, value);
    let alias = terms.mk_var("alias", make_array_sort());
    let read = terms.mk_select(alias, j);
    let base_read = terms.mk_select(base, j);
    let alias_eq = terms.mk_eq(alias, stored);
    let expected: HashSet<_> = [
        ArraySolver::ordered_pair(i, j),
        ArraySolver::ordered_pair(read, base_read),
    ]
    .into_iter()
    .collect();
    {
        let mut solver = ArraySolver::new(&terms);
        solver.populate_caches();
        assert!(solver.get_eq_term(i, j).is_none());
        assert!(solver.get_eq_term(read, base_read).is_none());
        solver.generate_all_lazy_row2_axioms();
        let queued = solver.row2_down_work.clone();
        assert!(queued.contains(&(stored, read)));
        solver.push();
        solver.assert_literal(alias_eq, false);
        assert!(
            solver.check_row2().is_none(),
            "a false alias guard must not request either absent ROW2 atom"
        );
        assert_eq!(solver.row2_down_work, queued);
        assert!(solver.requested_model_eqs.is_empty());
        assert!(solver.applied_theory_lemmas.is_empty());
        solver.pop();
        solver.push();
        solver.assert_literal(alias_eq, true);
        solver.generate_all_lazy_row2_axioms();
        assert_eq!(requested_pairs(solver.check_row2()), expected);
        assert!(solver.row2_down_work.contains(&(stored, read)));
        solver.pop();
    }
    // An unassigned guard still requires the real atom-creation protocol.
    {
        let mut undecided = ArraySolver::new(&terms);
        undecided.populate_caches();
        undecided.generate_all_lazy_row2_axioms();
        assert_eq!(requested_pairs(undecided.check_row2()), expected);
    }
    // Parking one inactive alias must not suppress independent genuine work.
    let other_base = terms.mk_var("other_base", make_array_sort());
    let other_i = terms.mk_var("other_i", Sort::Int);
    let other_j = terms.mk_var("other_j", Sort::Int);
    let other_store = terms.mk_store(other_base, other_i, value);
    let other_read = terms.mk_select(other_store, other_j);
    let other_base_read = terms.mk_select(other_base, other_j);
    let mut mixed = ArraySolver::new(&terms);
    mixed.populate_caches();
    mixed.generate_all_lazy_row2_axioms();
    mixed.assert_literal(alias_eq, false);
    let independent: HashSet<_> = [
        ArraySolver::ordered_pair(other_i, other_j),
        ArraySolver::ordered_pair(other_read, other_base_read),
    ]
    .into_iter()
    .collect();
    assert_eq!(requested_pairs(mixed.check_row2()), independent);
    assert!(mixed.row2_down_work.contains(&(stored, read)));
}

#[test]
fn true_read_disjunct_with_missing_index_atom_reactivates_after_pop() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", make_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let value = terms.mk_var("value", Sort::Int);
    let stored = terms.mk_store(base, i, value);
    let read = terms.mk_select(stored, j);
    let base_read = terms.mk_select(base, j);
    let read_eq = terms.mk_eq(read, base_read);
    let expected: HashSet<_> = [ArraySolver::ordered_pair(i, j)].into_iter().collect();
    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    assert!(solver.get_eq_term(i, j).is_none());
    assert_eq!(solver.get_eq_term(read, base_read), Some(read_eq));
    solver.generate_all_lazy_row2_axioms();
    let queued = solver.row2_down_work.clone();
    assert!(queued.contains(&(stored, read)));
    solver.push();
    solver.assert_literal(read_eq, true);
    assert!(
        solver.check_row2().is_none(),
        "a true read disjunct must not request the absent index atom"
    );
    assert_eq!(solver.row2_down_work, queued);
    assert!(solver.requested_model_eqs.is_empty());
    assert!(solver.applied_theory_lemmas.is_empty());
    solver.pop();
    solver.push();
    solver.assert_literal(read_eq, false);
    solver.generate_all_lazy_row2_axioms();
    assert_eq!(requested_pairs(solver.check_row2()), expected);
    assert!(solver.row2_down_work.contains(&(stored, read)));
    solver.pop();
    let mut undecided = ArraySolver::new(&terms);
    undecided.populate_caches();
    undecided.generate_all_lazy_row2_axioms();
    assert_eq!(requested_pairs(undecided.check_row2()), expected);
}

struct MemoFixture {
    terms: TermStore,
    i: TermId,
    j: TermId,
    first_edge: TermId,
    second_edge: TermId,
    read_eq: TermId,
}

fn memo_fixture() -> MemoFixture {
    let mut terms = TermStore::new();
    let base = terms.mk_var("memo_base", make_array_sort());
    let i = terms.mk_var("memo_i", Sort::Int);
    let j = terms.mk_var("memo_j", Sort::Int);
    let middle = terms.mk_var("memo_middle", Sort::Int);
    let value = terms.mk_var("memo_value", Sort::Int);
    let stored = terms.mk_store(base, i, value);
    let read = terms.mk_select(stored, j);
    let base_read = terms.mk_select(base, j);
    let read_eq = terms.mk_eq(read, base_read);
    let first_edge = terms.mk_eq(i, middle);
    let second_edge = terms.mk_eq(middle, j);
    MemoFixture {
        terms,
        i,
        j,
        first_edge,
        second_edge,
        read_eq,
    }
}

fn memo_branch(solver: &mut ArraySolver<'_>, f: &MemoFixture, indices_equal: bool) {
    solver.push();
    solver.assert_literal(f.first_edge, true);
    solver.assert_literal(f.second_edge, indices_equal);
    solver.assert_literal(f.read_eq, false);
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();
    assert!(solver.get_eq_term(f.i, f.j).is_none());
    // The transitive path is genuine proof work, not the early direct ROW1
    // shortcut that would hide a stale provability memo.
    assert!(!solver.known_equal(f.i, f.j));
}

#[test]
fn row2_memo_isolates_another_solver_and_restores_its_warm_window() {
    let f = memo_fixture();
    let mut outer = ArraySolver::new(&f.terms);
    let mut inner = ArraySolver::new(&f.terms);
    memo_branch(&mut outer, &f, false);
    memo_branch(&mut inner, &f, true);
    {
        let _outer_window = eq_paths_cache::activate();
        let outer_proof = outer.explain_distinct_if_provable(f.i, f.j).unwrap();
        assert!(outer_proof.contains(&TheoryLit::new(f.first_edge, true)));
        assert!(outer_proof.contains(&TheoryLit::new(f.second_edge, false)));
        assert_eq!(
            requested_pairs(inner.check_row2()),
            [ArraySolver::ordered_pair(f.i, f.j)]
                .into_iter()
                .collect::<HashSet<_>>(),
            "ROW2 must not consume another solver's opposite index proof"
        );
        assert_eq!(
            eq_paths_cache::get_distinct(f.i, f.j),
            Some(Some(outer_proof.clone())),
            "the exact outer proof window must survive the inner ROW2 pass"
        );
        assert_eq!(
            outer.explain_distinct_if_provable(f.i, f.j),
            Some(outer_proof)
        );
    }
    assert!(eq_paths_cache::get_distinct(f.i, f.j).is_none());
}

#[test]
fn row2_memo_drops_before_pop_and_a_fresh_solver() {
    let f = memo_fixture();
    let mut solver = ArraySolver::new(&f.terms);
    memo_branch(&mut solver, &f, false);
    let first = emitted(solver.check_row2());
    assert!(first
        .iter()
        .any(|lemma| lemma.clause.contains(&TheoryLit::new(f.read_eq, true))));
    assert!(eq_paths_cache::get_distinct(f.i, f.j).is_none());
    solver.pop();
    memo_branch(&mut solver, &f, true);
    assert_eq!(
        requested_pairs(solver.check_row2()),
        [ArraySolver::ordered_pair(f.i, f.j)]
            .into_iter()
            .collect::<HashSet<_>>()
    );
    assert!(eq_paths_cache::get_distinct(f.i, f.j).is_none());
    let mut fresh = ArraySolver::new(&f.terms);
    memo_branch(&mut fresh, &f, true);
    assert_eq!(
        requested_pairs(fresh.check_row2()),
        [ArraySolver::ordered_pair(f.i, f.j)]
            .into_iter()
            .collect::<HashSet<_>>()
    );
    assert!(eq_paths_cache::get_distinct(f.i, f.j).is_none());
}

#[test]
fn row2_memo_preserves_distinct_requests_while_metadata_grows() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("memo_requests_base", make_array_sort());
    let i = terms.mk_var("memo_requests_i", Sort::Int);
    let j = terms.mk_var("memo_requests_j", Sort::Int);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let first = terms.mk_store(base, i, one);
    let second = terms.mk_store(base, i, two);
    let first_read = terms.mk_select(first, j);
    let second_read = terms.mk_select(second, j);
    let base_read = terms.mk_select(base, j);
    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();
    assert_eq!(
        requested_pairs(solver.check_row2()),
        [
            ArraySolver::ordered_pair(i, j),
            ArraySolver::ordered_pair(first_read, base_read),
            ArraySolver::ordered_pair(second_read, base_read),
        ]
        .into_iter()
        .collect::<HashSet<_>>()
    );
    assert_eq!(solver.requested_model_eqs.len(), 3);
    assert_eq!(solver.exact_select_model_eq_obligations.len(), 3);
    assert!(eq_paths_cache::get_distinct(i, j).is_none());
}
