// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// A POSITIVE equality is never a hypothesis. `(cl (= a b) (= (f a) (f b)))`
/// has two positive equalities and is NOT valid.
#[test]
fn a_positive_equality_is_never_a_hypothesis() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let eq_ab = mk_eq(&mut terms, a, b);
    let conclusion = mk_eq(&mut terms, fa, fb);
    let clause = vec![eq_ab, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying assignment: a := 0, b := 1, f(0) := 2, f(1) := 3. Both
    // literals are false, so the clause is FALSE.
    let countermodel = falsifying_quotient(&terms, &clause)
        .expect("two positive equalities must have a concrete countermodel");
    let block = |t: TermId| countermodel.iter().find(|(x, _)| *x == t).unwrap().1;
    assert_ne!(block(a), block(b));
    assert_ne!(block(fa), block(fb));
}

/// NEGATION PARITY: `(not (not (= a b)))` is a POSITIVE literal, so the clause
/// again has two positive equalities and the same countermodel.
#[test]
fn a_double_negated_equality_is_positive_not_a_hypothesis() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let eq_ab = mk_eq(&mut terms, a, b);
    let once = terms.mk_not_raw(eq_ab);
    let twice = terms.mk_not_raw(once);
    let conclusion = mk_eq(&mut terms, fa, fb);
    let clause = vec![twice, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying assignment: a := 0, b := 1, f(0) := 2, f(1) := 3.
    let countermodel = falsifying_quotient(&terms, &clause)
        .expect("a double negation is positive and must have a countermodel");
    let block = |t: TermId| countermodel.iter().find(|(x, _)| *x == t).unwrap().1;
    assert_ne!(block(a), block(b));
    assert_ne!(block(fa), block(fb));
}

/// NEGATION PARITY, the other side: `(not (not (not (= a b))))` is NEGATIVE,
/// so it IS a hypothesis and the clause is a valid congruence explanation.
/// Reading the polarity off the OUTERMOST `not` alone accepts the same clause
/// for the wrong reason on an even count — see
/// `a_double_negated_equality_is_positive_not_a_hypothesis` — and declines
/// this one; only the parity is right in both directions.
#[test]
fn a_triple_negated_equality_is_a_hypothesis() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let eq_ab = mk_eq(&mut terms, a, b);
    let once = terms.mk_not_raw(eq_ab);
    let twice = terms.mk_not_raw(once);
    let thrice = terms.mk_not_raw(twice);
    let conclusion = mk_eq(&mut terms, fa, fb);
    let clause = vec![thrice, conclusion];
    assert!(accepts(&terms, &clause));
    assert!(
        is_valid(&terms, &clause),
        "the independent evaluator must agree the accepted clause is valid"
    );
}

/// A symbol OVERLOADED AT TWO SORTS names two different functions, and the
/// congruence head carries the result sort so they are never merged.
///
/// `TermStore::mk_app` deliberately keeps `(symbol, args)` entries apart when
/// the sorts differ (the sort-polymorphic nullary-constructor case), so both
/// nodes really do coexist — pinned below before the clause is built.
#[test]
fn a_symbol_overloaded_at_two_sorts_is_not_merged() {
    let mut terms = TermStore::new();
    let int_array = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let bool_array = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Bool)));
    let empty_int = mk_fun(&mut terms, "empty", vec![], int_array);
    let empty_bool = mk_fun(&mut terms, "empty", vec![], bool_array);
    assert_ne!(
        empty_int, empty_bool,
        "the store must keep the two sorts apart for this test to mean anything"
    );
    let f_int = mk_fun(&mut terms, "f", vec![empty_int], Sort::Int);
    let f_bool = mk_fun(&mut terms, "f", vec![empty_bool], Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let hypothesis = neq(&mut terms, x, f_int);
    let conclusion = mk_eq(&mut terms, x, f_bool);
    let clause = vec![hypothesis, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying structure, spelled out (the enumerator reads a symbol
    // UNSORTED and so cannot express it): `empty` denotes the all-zero array
    // at `(Array Int Int)` and the all-false array at `(Array Int Bool)`;
    // `f : (Array Int Int) -> Int` returns 0 and the DIFFERENT function
    // `f : (Array Int Bool) -> Int` returns 1; `x := 0`. The hypothesis
    // `x = f empty_int` holds, so its negation is false, and the conclusion
    // `x = f empty_bool` is `0 = 1`, false. The clause is FALSE.
    let f_on_int_array = 0i32;
    let f_on_bool_array = 1i32;
    let x_value = 0i32;
    assert_eq!(x_value, f_on_int_array, "the hypothesis holds");
    assert_ne!(x_value, f_on_bool_array, "the conclusion is false");
}

/// CONGRUENCE DOES NOT REACH UNDER A BINDER. `x = c` does NOT make
/// `(forall x. p x)` equal to `(forall x. p c)`.
#[test]
fn congruence_does_not_reach_under_a_binder() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let p_x = mk_fun(&mut terms, "p", vec![x], Sort::Bool);
    let p_c = mk_fun(&mut terms, "p", vec![c], Sort::Bool);
    let all_x = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_x);
    let all_c = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_c);
    let hypothesis = neq(&mut terms, x, c);
    let conclusion = mk_eq(&mut terms, all_x, all_c);
    let clause = vec![hypothesis, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying structure, spelled out: domain {0, 1}; the free `x` and `c`
    // both denote 0; `p` is true at 0 and false at 1. Then the hypothesis
    // `x = c` holds (so `(not (= x c))` is false); `(forall x. p x)` is FALSE
    // because p(1) is false, while `(forall x. p c)` is p(0) = TRUE (the body
    // does not mention the bound variable). So the conclusion equality is
    // false and the clause is FALSE.
    let p = [true, false];
    let (x_value, c_value) = (0usize, 0usize);
    assert_eq!(x_value, c_value, "the hypothesis x = c holds");
    let forall_p_x = p[0] && p[1];
    let forall_p_c = p[c_value] && p[c_value];
    assert!(!forall_p_x);
    assert!(forall_p_c);
    assert_ne!(forall_p_x, forall_p_c, "the conclusion equality is false");
}

/// The `not` former and a unary APPLICATION must not share a congruence head.
/// If they did, `(not p)` and `(f q)` would merge whenever `p` and `q` do.
#[test]
fn the_not_former_does_not_share_a_head_with_a_unary_application() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let f_q = mk_fun(&mut terms, "f", vec![q], Sort::Bool);
    let hypothesis = neq(&mut terms, p, q);
    let conclusion = mk_eq(&mut terms, not_p, f_q);
    let clause = vec![hypothesis, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying structure: p := q := true, f(true) := true. The hypothesis
    // `p = q` holds; `(not p)` is false while `(f q)` is true, so the
    // conclusion is false and the clause is FALSE.
    let (p_value, q_value) = (true, true);
    assert_eq!(p_value, q_value, "the hypothesis p = q holds");
    let f = |b: bool| b;
    assert_ne!(!p_value, f(q_value), "the conclusion equality is false");
}

/// A clause whose sub-term DAG exceeds `MAX_NODES` is REJECTED, not accepted
/// unchecked. Built as a `store` chain deeper than the bound.
#[test]
fn an_oversize_subterm_graph_is_rejected_rather_than_accepted() {
    let mut terms = TermStore::new();
    let array = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    // A FIXED depth, chosen so the fixture is oversize for the shipped bound
    // (each `store` contributes three nodes) without depending on it for its
    // size — deleting the bound must not turn this test into a memory bomb.
    const CHAIN: usize = 4200;
    assert!(
        CHAIN * 3 > MAX_NODES,
        "the fixture must exceed MAX_NODES to exercise the bound"
    );
    let mut chain = terms.mk_var("base", array.clone());
    for step in 0..CHAIN {
        let index = terms.mk_var(&format!("i{step}"), Sort::Int);
        let value = terms.mk_var(&format!("v{step}"), Sort::Int);
        chain = mk_fun(
            &mut terms,
            "store",
            vec![chain, index, value],
            array.clone(),
        );
    }
    let other = terms.mk_var("other", array);
    let hypothesis = neq(&mut terms, chain, other);
    let conclusion = mk_eq(&mut terms, chain, other);
    // `(cl (not (= C O)) (= C O))` is a TAUTOLOGY, so a validator that
    // ignored the bound would accept it; the bound makes it a REJECT.
    let clause = vec![hypothesis, conclusion];
    let error = strict(&terms, clause.clone()).expect_err("the size bound must reject");
    assert!(
        format!("{error:?}").contains("exceeds the validation bound"),
        "unexpected rejection reason: {error:?}"
    );
    assert!(!accepts(&terms, &clause));
}

/// The validator DEBITS the strict checker's meter and fails closed with the
/// typed `ResourceLimit` when the caller's envelope runs out — it does not
/// silently finish the closure on someone else's budget.
#[test]
fn the_validator_fails_closed_when_the_progress_meter_runs_out() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let hypothesis = neq(&mut terms, a, b);
    let conclusion = mk_eq(&mut terms, fa, fb);
    let clause = [hypothesis, conclusion];
    // With an unlimited meter the clause is ACCEPTED, so the refusal below is
    // attributable to the meter and to nothing about the clause.
    let mut budget = usize::MAX;
    validate_euf_congruence_explanation(&terms, ProofId(0), &clause, &mut |work, _| {
        budget = budget.saturating_sub(work);
        budget > 0
    })
    .expect("an unlimited meter must accept the clause");
    // Now allow exactly one debit.
    let mut calls = 0usize;
    let error = validate_euf_congruence_explanation(&terms, ProofId(0), &clause, &mut |_, _| {
        calls += 1;
        calls <= 1
    })
    .expect_err("an exhausted meter must refuse");
    assert!(
        matches!(error, ProofCheckError::ResourceLimit),
        "expected the typed ResourceLimit refusal, got {error:?}"
    );
}

/// SCOPE, not soundness: a one-literal clause is `eq_reflexive`'s job. Pinned
/// because two guards (`len < 2` and `hypotheses.is_empty()`) jointly enforce
/// it and neither is individually observable — see `GUARD_MUTATION_LEDGER`.
#[test]
fn a_bare_reflexive_unit_is_out_of_scope() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let refl = mk_eq(&mut terms, a, a);
    assert!(!accepts(&terms, &[refl]));
    // And the same clause packed as a single-disjunct `or`, which
    // `flatten_or_clause` deliberately does NOT flatten.
    let packed = terms.mk_app(ay_core::Symbol::named("or"), vec![refl], Sort::Bool);
    assert!(!accepts(&terms, &[packed]));
}

/// A clause with NO positive equality at all cannot be a congruence
/// explanation, whatever its hypotheses entail.
#[test]
fn a_clause_with_no_positive_equality_is_rejected() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let h1 = neq(&mut terms, a, b);
    let h2 = neq(&mut terms, b, a);
    assert!(!accepts(&terms, &[h1, h2]));
}

/// SCOPE: a SECOND positive equality puts the clause out of this rule's
/// schema even when the clause is valid. Dropping the guard would silently
/// pick one of them as "the" conclusion.
#[test]
fn a_second_positive_equality_is_out_of_scope() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let hypothesis = neq(&mut terms, a, b);
    let extra = mk_eq(&mut terms, a, c);
    let conclusion = mk_eq(&mut terms, fa, fb);
    // Valid (the last disjunct alone follows from the hypothesis), and still
    // REJECTED: two positive equalities are outside the schema.
    let clause = vec![hypothesis, extra, conclusion];
    assert!(is_valid(&terms, &clause));
    assert!(!accepts(&terms, &clause));
}

/// SCOPE: a NON-EQUALITY literal puts the clause out of the schema, again even
/// when the clause is valid. Silently skipping it would widen the rule to
/// clauses whose recorded shape this validator has not audited.
#[test]
fn a_non_equality_literal_puts_the_clause_out_of_scope() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let predicate = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let hypothesis = neq(&mut terms, a, b);
    let conclusion = mk_eq(&mut terms, fa, fb);
    let clause = vec![predicate, hypothesis, conclusion];
    assert!(!accepts(&terms, &clause));
    // Without the predicate the same clause IS in scope and accepted, so the
    // rejection is attributable to that literal and nothing else.
    assert!(accepts(&terms, &[hypothesis, conclusion]));
}

// ===== exhaustive sweeps =====

/// Build the alphabet `{a, b, c, f a, f b, f c}` and every unordered pair of
/// distinct terms from it.
fn unary_alphabet() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let fc = mk_fun(&mut terms, "f", vec![c], Sort::Int);
    (terms, vec![a, b, c, fa, fb, fc])
}

/// Build the alphabet `{a, b, g a a, g a b, g b a, g b b}`.
fn binary_alphabet() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let gaa = mk_fun(&mut terms, "g", vec![a, a], Sort::Int);
    let gab = mk_fun(&mut terms, "g", vec![a, b], Sort::Int);
    let gba = mk_fun(&mut terms, "g", vec![b, a], Sort::Int);
    let gbb = mk_fun(&mut terms, "g", vec![b, b], Sort::Int);
    (terms, vec![a, b, gaa, gab, gba, gbb])
}

struct SweepTally {
    clauses: usize,
    accepts: usize,
    rejects: usize,
}

/// Sweep every clause with one positive equality and `1..=max_hypotheses`
/// negated equalities over the alphabet, and check the recognizer against the
/// independent evaluator in BOTH directions:
///
/// * every ACCEPT is valid — the soundness claim;
/// * every REJECT is invalid — a completeness claim that holds because
///   congruence closure DECIDES ground EUF entailment, so a schema-shaped
///   clause is accepted exactly when it is valid. Asserting it two-sided means
///   a future tightening that starts declining valid clauses is also caught.
fn sweep(alphabet: (TermStore, Vec<TermId>), max_hypotheses: usize) -> SweepTally {
    let (mut terms, universe) = alphabet;
    let mut atoms = Vec::new();
    for i in 0..universe.len() {
        for j in (i + 1)..universe.len() {
            atoms.push((universe[i], universe[j]));
        }
    }
    let positives: Vec<TermId> = atoms
        .iter()
        .map(|&(l, r)| mk_eq(&mut terms, l, r))
        .collect();
    let negatives: Vec<TermId> = atoms.iter().map(|&(l, r)| neq(&mut terms, l, r)).collect();

    let mut tally = SweepTally {
        clauses: 0,
        accepts: 0,
        rejects: 0,
    };
    let mut combination = Vec::new();
    fn choose(
        start: usize,
        remaining: usize,
        pool: &[TermId],
        combination: &mut Vec<TermId>,
        emit: &mut impl FnMut(&[TermId]),
    ) {
        if remaining == 0 {
            emit(combination);
            return;
        }
        for index in start..pool.len() {
            combination.push(pool[index]);
            choose(index + 1, remaining - 1, pool, combination, emit);
            combination.pop();
        }
    }
    for &conclusion in &positives {
        for size in 1..=max_hypotheses {
            let mut clauses: Vec<Vec<TermId>> = Vec::new();
            choose(0, size, &negatives, &mut combination, &mut |chosen| {
                let mut clause = vec![conclusion];
                clause.extend_from_slice(chosen);
                clauses.push(clause);
            });
            for clause in clauses {
                tally.clauses += 1;
                let accepted = recognize_euf_congruence_explanation(&terms, &clause);
                let valid = is_valid(&terms, &clause);
                assert_eq!(
                    accepted, valid,
                    "recognizer and independent evaluator disagree on {clause:?}"
                );
                if accepted {
                    tally.accepts += 1;
                } else {
                    tally.rejects += 1;
                }
                // The packed `(cl (or ..))` form must get the SAME verdict.
                let packed = mk_or(&mut terms, clause.clone());
                assert_eq!(
                    recognize_euf_congruence_explanation(&terms, &[packed]),
                    accepted,
                    "packed and flat forms disagree"
                );
            }
        }
    }
    tally
}

#[test]
fn sweep_unary_alphabet_agrees_with_the_independent_evaluator() {
    let tally = sweep(unary_alphabet(), 3);
    // 15 conclusions x (15 + 105 + 455) hypothesis sets.
    assert_eq!(tally.clauses, 15 * (15 + 105 + 455));
    // Pinned: 3984 of the 8625 clauses in the box are valid, and the
    // recognizer accepts exactly those. A change to either side moves this.
    assert_eq!((tally.accepts, tally.rejects), (3984, 4641));
    assert!(tally.accepts > 0 && tally.rejects > 0, "sweep is two-sided");
    assert_eq!(tally.accepts + tally.rejects, tally.clauses);
}

#[test]
fn sweep_binary_alphabet_agrees_with_the_independent_evaluator() {
    let tally = sweep(binary_alphabet(), 2);
    assert_eq!(tally.clauses, 15 * (15 + 105));
    // Pinned, as in the unary sweep: 465 of 1800 are valid.
    assert_eq!((tally.accepts, tally.rejects), (465, 1335));
    assert!(tally.accepts > 0 && tally.rejects > 0, "sweep is two-sided");
    assert_eq!(tally.accepts + tally.rejects, tally.clauses);
}

// ===== the wire =====

/// The kind has NO Alethe counterpart, so the emitted document must carry the
/// honest `hole` — never a false rule name (which makes the whole document
/// `invalid` rather than merely holey) and never `eq_transitive`.
#[test]
fn the_kind_lowers_to_the_honest_hole_wire() {
    assert_eq!(
        TheoryLemmaKind::EufCongruenceExplanation.alethe_rule(),
        "euf_congruence_explanation"
    );
    assert_eq!(
        TheoryLemmaKind::EufCongruenceExplanation.alethe_wire_rule(),
        ay_core::UNPROVED_STEP_RULE
    );
    assert!(!ay_core::is_checkable_alethe_rule(
        TheoryLemmaKind::EufCongruenceExplanation.alethe_rule()
    ));
    assert!(!TheoryLemmaKind::EufCongruenceExplanation.is_trust());
}

// ===== guard-mutation ledger =====

/// Delete or invert the guard, run this module, observe the NAMED test FAIL,
/// restore. Every row below was RUN, not reasoned about.
///
/// | # | mutation | first named test observed red |
/// |---|---|---|
/// | M1 | a POSITIVE equality also becomes a hypothesis | `rejects_a_chain_with_a_broken_link` (+7 more) |
/// | M2 | polarity taken from the OUTERMOST `not` instead of the parity | `a_double_negated_equality_is_positive_not_a_hypothesis` |
/// | M3 | "exactly one positive": keep the LAST, ignore the rest | `a_second_positive_equality_is_out_of_scope` |
/// | M4 | "every literal an equality": skip the ones that are not | `a_non_equality_literal_puts_the_clause_out_of_scope` |
/// | M5 | let congruence descend into a quantifier body | `congruence_does_not_reach_under_a_binder` |
/// | M6 | `HEAD_APP_BASE = 0`, so an application head collides with `not` | `the_not_former_does_not_share_a_head_with_a_unary_application` |
/// | M7 | drop the result SORT from the congruence head | `a_symbol_overloaded_at_two_sorts_is_not_merged` |
/// | M8 | remove the `MAX_NODES` sub-term graph bound | `an_oversize_subterm_graph_is_rejected_rather_than_accepted` |
/// | M9 | canonicalise with raw child ids instead of `find(child)` | `accepts_the_measured_congruence_explanation_shape` (+5 more) |
/// | M10 | never merge the stated hypotheses | `accepts_the_measured_congruence_explanation_shape` (+5 more) |
/// | M13 | `MAX_ROUNDS = 1` | `accepts_the_measured_congruence_explanation_shape` (+5 more) |
///
/// NEGATIVE RESULTS, recorded rather than hidden. Deleting EITHER of these two
/// alone fails NO test, because the other catches the same clause: a
/// one-literal clause has no negated literal, and a clause with no negated
/// literal and one positive literal has one literal. They are SCOPE — a bare
/// `(cl (= a a))` is `eq_reflexive`'s job, not this rule's — and the property
/// they jointly enforce is pinned directly by
/// `a_bare_reflexive_unit_is_out_of_scope`:
///
/// * M11 `literals.len() < 2`
/// * M12 `hypotheses.is_empty()`
const GUARD_MUTATION_LEDGER: &str = "see the doc comment above";

#[test]
fn guard_mutation_ledger_is_present() {
    assert!(!GUARD_MUTATION_LEDGER.is_empty());
}
