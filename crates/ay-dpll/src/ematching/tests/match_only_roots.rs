// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `ematching::tests`.

/// (#guarded-instance-match-terms) One round of E-matching over `assertions`,
/// with `match_only_roots` offered to the matcher and nothing else.
fn match_round(
    terms: &mut TermStore,
    assertions: &[TermId],
    match_only_roots: &[TermId],
) -> EMatchingResult {
    let mut state = PersistentMatchState::new();
    perform_ematching_with_generations(
        terms,
        assertions,
        match_only_roots,
        &[],
        &EMatchingConfig::default(),
        GenerationTracker::new(),
        None,
        &|| false,
        &mut state,
        None,
    )
}

/// A match-only root supplies ground terms a trigger can bind to: the entailed
/// `forall x. g(x) = x + 1` has no ground `g`-term among the assertions, and
/// gets its instance at `1` from the term `g(1)` inside the root.
#[test]
fn match_only_roots_supply_ground_terms_to_triggers() {
    let mut terms = TermStore::new();
    let g = Symbol::named("mor_g");
    let x = terms.mk_var("x", Sort::Int);
    let g_x = terms.mk_app(g.clone(), vec![x], Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let x_plus_1 = terms.mk_add(vec![x, one]);
    let body = terms.mk_eq(g_x, x_plus_1);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let f = Symbol::named("mor_f");
    let f_1 = terms.mk_app(f, vec![one], Sort::Int);
    let g_1 = terms.mk_app(g, vec![one], Sort::Int);
    let guarded_body = terms.mk_eq(f_1, g_1);

    let without = match_round(&mut terms, &[forall], &[]);
    assert!(
        without.instantiations.is_empty(),
        "no ground g-term exists without the root; got {:?}",
        without.instantiations
    );
    let with = match_round(&mut terms, &[forall], &[guarded_body]);
    assert_eq!(
        with.instantiations.len(),
        1,
        "the root's `g(1)` must bind the trigger `g(x)`"
    );
}

/// A match-only root is NOT a fact. `(and p (q 1))` offered as a root must not
/// make `p` a unit, so `(=> p (forall x. q x))` stays unentailed and its
/// instance is never conjoined. The same term offered as an ASSERTION does
/// entail the universal — the control that shows the check can fail.
#[test]
fn match_only_roots_are_never_read_as_facts() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("mor_p", Sort::Bool);
    let q = Symbol::named("mor_q");
    let x = terms.mk_var("x", Sort::Int);
    let q_x = terms.mk_app(q.clone(), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], q_x);
    let guarded = terms.mk_implies(p, forall);
    let one = terms.mk_int(BigInt::from(1));
    let q_1 = terms.mk_app(q, vec![one], Sort::Bool);
    let root = terms.mk_and(vec![p, q_1]);

    let as_root = match_round(&mut terms, &[guarded], &[root]);
    assert!(
        as_root.instantiations.is_empty() && !as_root.entailed_foralls.contains(&forall),
        "a match-only root must not entail the guarded universal; instances {:?}",
        as_root.instantiations
    );

    let as_assertion = match_round(&mut terms, &[guarded, root], &[]);
    assert!(
        as_assertion.entailed_foralls.contains(&forall),
        "control: the same conjunction asserted DOES entail the universal"
    );
}
