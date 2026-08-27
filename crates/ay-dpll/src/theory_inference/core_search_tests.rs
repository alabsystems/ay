// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bounded core search's feasibility gate is DECIDED against the
//! pre-existing exhaustive search, not asserted: every case below runs both
//! [`SubsetSearch`] modes over the same conflict and requires the same answer.

use super::*;
use ay_core::{Sort, TermStore, TheoryLit};
use num_bigint::BigInt;

fn negations_for(terms: &mut TermStore, conflict: &[TheoryLit]) -> HashMap<TermId, TermId> {
    let mut negations = HashMap::default();
    for literal in conflict {
        let negated = terms.mk_not(literal.term);
        negations.entry(literal.term).or_insert(negated);
    }
    negations
}

fn both_modes_agree(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>)> {
    let gated = classifiable_core_decomposition_with(
        terms,
        negations,
        conflict,
        clause,
        SubsetSearch::Gated,
    );
    let exhaustive = classifiable_core_decomposition_with(
        terms,
        negations,
        conflict,
        clause,
        SubsetSearch::Exhaustive,
    );
    assert_eq!(
        gated, exhaustive,
        "the feasibility gate changed the search's answer"
    );
    gated
}

fn int_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn int_const(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

/// The gate must not prune the shape the pass exists for: an arithmetic core
/// hidden under foreign Boolean literals.
#[test]
fn a_foreign_literal_core_is_still_found_under_the_gate() {
    let mut terms = TermStore::new();
    let foreign_a = terms.mk_var("foreign_a", Sort::Bool);
    let foreign_b = terms.mk_var("foreign_b", Sort::Bool);
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let le_zero = terms.mk_le(x, zero);
    let ge_one = terms.mk_ge(x, one);
    let conflict = vec![
        TheoryLit::new(foreign_a, true),
        TheoryLit::new(foreign_b, true),
        TheoryLit::new(le_zero, true),
        TheoryLit::new(ge_one, true),
    ];
    let negations = negations_for(&mut terms, &conflict);
    let clause = super::super::build_blocking_clause_terms(&negations, &conflict)
        .expect("every conflict literal has a negation");

    let (kind, core, weakened) = both_modes_agree(&terms, &negations, &conflict, &clause)
        .expect("dropping both foreign literals exposes the arithmetic core");
    assert_eq!(kind, TheoryLemmaKind::LraFarkas);
    assert_eq!(core.len(), 2);
    assert_eq!(weakened.len(), clause.len());
}

/// The case the model gate MUST NOT prune: a purely arithmetic conflict whose
/// only obstacle is one uncancelled row. `x <= 0`, `x >= 1` is the core;
/// `y <= 0` carries a variable no other row mentions.
///
/// Dropping `y <= 0` leaves an UNSATISFIABLE pool, so the single-deletion model
/// probe declines and the chain runs exactly as before.
#[test]
fn a_pure_arithmetic_core_under_one_uncancelled_row_is_still_found() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let x_le_zero = terms.mk_le(x, zero);
    let x_ge_one = terms.mk_ge(x, one);
    let y_le_zero = terms.mk_le(y, zero);
    let conflict = vec![
        TheoryLit::new(y_le_zero, true),
        TheoryLit::new(x_le_zero, true),
        TheoryLit::new(x_ge_one, true),
    ];
    let negations = negations_for(&mut terms, &conflict);
    let clause = super::super::build_blocking_clause_terms(&negations, &conflict)
        .expect("every conflict literal has a negation");

    let (kind, core, _) = both_modes_agree(&terms, &negations, &conflict, &clause)
        .expect("dropping the uncancelled row exposes the arithmetic core");
    assert_eq!(kind, TheoryLemmaKind::LraFarkas);
    assert_eq!(core.len(), 2);
}

/// The gate's own prune must fire and must not change the answer: a conflict
/// with SIX literals no arithmetic route can consume cannot expose an
/// arithmetic core by dropping at most three, and its non-equality count can
/// never reach 0 or 2, so no arm survives.
#[test]
fn an_unreachable_core_is_pruned_without_changing_the_answer() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);
    let foreign: Vec<TermId> = (0..6)
        .map(|i| terms.mk_var(format!("foreign{i}"), Sort::Bool))
        .collect();
    let mut rows = vec![terms.mk_le(x, zero), terms.mk_ge(x, one)];
    rows.extend(foreign.iter().copied());
    let conflict: Vec<TheoryLit> = rows.iter().map(|&r| TheoryLit::new(r, true)).collect();
    let negations = negations_for(&mut terms, &conflict);
    let clause = super::super::build_blocking_clause_terms(&negations, &conflict)
        .expect("every conflict literal has a negation");

    assert!(both_modes_agree(&terms, &negations, &conflict, &clause).is_none());

    // …and the prune really fired, so the agreement above is not vacuous.
    let present = SortedTheoryPresence::over(&terms, &clause);
    let feasibility = AttemptFeasibility {
        admissibility: LiteralAdmissibility::over(&terms, &conflict),
        present: &present,
    };
    assert!(!feasibility.attempt_may_classify(&clause, &[0]));
    assert!(!feasibility.attempt_may_classify(&clause, &[2, 3]));
    assert!(!feasibility.attempt_may_classify(&clause, &[2, 3, 4]));
}

/// The ambiguity guard the pre-existing search carries must survive the gate.
#[test]
fn ambiguous_duplicate_core_still_does_not_abort_later_candidates() {
    let mut terms = TermStore::new();
    let foreign = terms.mk_var("foreign", Sort::Bool);
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let le_zero = terms.mk_le(x, zero);
    let ge_one = terms.mk_ge(x, one);
    let conflict = vec![
        TheoryLit::new(foreign, true),
        TheoryLit::new(le_zero, true),
        TheoryLit::new(ge_one, true),
        TheoryLit::new(le_zero, true),
    ];
    let negations = negations_for(&mut terms, &conflict);
    let clause = super::super::build_blocking_clause_terms(&negations, &conflict)
        .expect("every conflict literal has a negation");

    let (kind, core, _) = both_modes_agree(&terms, &negations, &conflict, &clause)
        .expect("a later unambiguous arithmetic core remains available");
    assert_eq!(kind, TheoryLemmaKind::LraFarkas);
    assert_eq!(core.len(), 2);
}

/// EUF cores live at `kept_non_equalities == 0`; the gate must let them through.
#[test]
fn an_euf_transitivity_core_survives_the_gate() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort.clone());
    let c = terms.mk_var("c", sort);
    let extra = terms.mk_var("extra", Sort::Bool);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let conflict = vec![
        TheoryLit::new(extra, true),
        TheoryLit::new(eq_ab, true),
        TheoryLit::new(eq_bc, true),
        TheoryLit::new(eq_ac, false),
    ];
    let negations = negations_for(&mut terms, &conflict);
    let clause = super::super::build_blocking_clause_terms(&negations, &conflict)
        .expect("every conflict literal has a negation");

    let (kind, _, weakened) = both_modes_agree(&terms, &negations, &conflict, &clause)
        .expect("dropping the foreign Boolean exposes the transitivity core");
    assert_eq!(kind, TheoryLemmaKind::EufTransitive);
    assert_eq!(weakened.len(), clause.len());
}

/// A sweep: every conflict drawn from a mixed alphabet must give the same
/// answer in both modes, and the sweep must exercise BOTH outcomes so it cannot
/// pass vacuously.
#[test]
fn gated_and_exhaustive_searches_agree_over_a_mixed_alphabet() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);
    let two = int_const(&mut terms, 2);
    let sort = Sort::Uninterpreted("U".to_string());
    let p = terms.mk_var("p", sort.clone());
    let q = terms.mk_var("q", sort);

    let alphabet: Vec<TermId> = vec![
        terms.mk_le(x, zero),
        terms.mk_ge(x, one),
        terms.mk_le(y, zero),
        terms.mk_ge(y, two),
        terms.mk_ge(x, y),
        terms.mk_eq(p, q),
        terms.mk_var("boolean_a", Sort::Bool),
        terms.mk_var("boolean_b", Sort::Bool),
    ];

    let mut accepts = 0usize;
    let mut rejects = 0usize;
    let n = alphabet.len();
    for i in 0..n {
        for j in (i + 1)..n {
            for k in (j + 1)..n {
                for polarity in 0..8u8 {
                    let conflict = vec![
                        TheoryLit::new(alphabet[i], polarity & 1 == 0),
                        TheoryLit::new(alphabet[j], polarity & 2 == 0),
                        TheoryLit::new(alphabet[k], polarity & 4 == 0),
                    ];
                    let negations = negations_for(&mut terms, &conflict);
                    let Some(clause) =
                        super::super::build_blocking_clause_terms(&negations, &conflict)
                    else {
                        continue;
                    };
                    if both_modes_agree(&terms, &negations, &conflict, &clause).is_some() {
                        accepts += 1;
                    } else {
                        rejects += 1;
                    }
                }
            }
        }
    }
    assert!(accepts > 0, "sweep found no accepting conflict");
    assert!(rejects > 0, "sweep found no rejecting conflict");
}

/// The array presence gate is a NECESSARY condition for
/// `recognize_array_theory_lemma`: no schema it accepts can be stated without
/// an Array-sorted term reachable from the clause. Sweep the recognizer over
/// array-free clauses built from every non-array shape the classifier chain
/// otherwise sees, and require it to decline every one.
#[test]
fn array_recognizers_all_decline_without_an_array_sorted_term() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = int_const(&mut terms, 0);
    let sort = Sort::Uninterpreted("U".to_string());
    let p = terms.mk_var("p", sort.clone());
    let q = terms.mk_var("q", sort.clone());
    let f_p = terms.mk_app(ay_core::Symbol::named("f"), vec![p], sort.clone());
    let f_q = terms.mk_app(ay_core::Symbol::named("f"), vec![q], sort.clone());
    let truth = terms.true_term();

    let atoms: Vec<TermId> = vec![
        terms.mk_le(x, zero),
        terms.mk_ge(x, y),
        terms.mk_eq(x, y),
        terms.mk_eq(p, q),
        terms.mk_eq(f_p, f_q),
        terms.mk_var("boolean", Sort::Bool),
        truth,
    ];
    let mut clauses: Vec<Vec<TermId>> = Vec::new();
    for &a in &atoms {
        let not_a = terms.mk_not(a);
        clauses.push(vec![a]);
        clauses.push(vec![not_a]);
        for &b in &atoms {
            let not_b = terms.mk_not(b);
            clauses.push(vec![a, b]);
            clauses.push(vec![not_a, b]);
            clauses.push(vec![not_a, not_b]);
        }
    }
    // Include the `or`-wrapped unit shape `flatten_clause_literals` unpacks.
    let wrapped: Vec<TermId> = clauses
        .iter()
        .filter(|c| c.len() == 2)
        .map(|c| terms.mk_app(ay_core::Symbol::named("or"), c.clone(), Sort::Bool))
        .collect();
    for lit in wrapped {
        clauses.push(vec![lit]);
    }

    for clause in &clauses {
        let presence = SortedTheoryPresence::over(&terms, clause);
        assert!(
            !presence.array(),
            "the sweep is supposed to be array-free: {clause:?}"
        );
        assert!(
            ay_proof::recognize_array_theory_lemma(&terms, clause).is_none(),
            "an array schema accepted an array-free clause: {clause:?}"
        );
    }
    assert!(clauses.len() > 100, "sweep is too small to be meaningful");
}

/// The regex gate is a NECESSARY condition for
/// `recognize_regex_intersect_empty`: every membership it decodes needs a
/// `Sort::String` subject.
#[test]
fn regex_recognizer_declines_without_a_string_sorted_term() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let zero = int_const(&mut terms, 0);
    let le = terms.mk_le(x, zero);
    let not_le = terms.mk_not(le);
    let boolean = terms.mk_var("boolean", Sort::Bool);
    for clause in [vec![le], vec![not_le, boolean], vec![boolean]] {
        let presence = SortedTheoryPresence::over(&terms, &clause);
        assert!(!presence.string_or_regex());
        assert!(!ay_proof::recognize_regex_intersect_empty(&terms, &clause));
    }
}
