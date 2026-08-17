// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Placement tests for the original-clause proof-authority ledgers.
//!
//! Each guard here was a production `assert!` before this module existed, so
//! every case below is a scenario that used to abort the whole `check-sat`.

use ay_core::{AletheRule, TermId, TheoryLemmaKind, TheoryLemmaProof};
use ay_sat::{Literal, Solver, Variable};

use super::*;

/// A solver holding `count` original clauses, so IDs `1..=count` are issued.
fn solver_with_originals(count: usize) -> Solver {
    let mut solver = Solver::new(count + 1);
    for i in 0..count {
        let lit = Literal::positive(Variable::new(u32::try_from(i).expect("small index")));
        let other = Literal::negative(Variable::new(u32::try_from(count).expect("small index")));
        assert!(solver.add_clause(vec![lit, other]));
    }
    solver
}

fn clausification(source: u32) -> ClausificationProof {
    ClausificationProof {
        rule: AletheRule::AndPos(0),
        source_term: TermId::new(source),
    }
}

fn theory_lemma(term: u32) -> TheoryLemmaProof {
    TheoryLemmaProof {
        clause: vec![TermId::new(term)],
        kind: TheoryLemmaKind::EufReflexive,
        farkas: None,
        lia: None,
    }
}

fn ledgers() -> (
    Vec<Option<ClausificationProof>>,
    Vec<Option<TheoryLemmaProof>>,
) {
    (Vec::new(), Vec::new())
}

#[test]
fn first_placement_takes_the_slot() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();

    let outcome = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    assert_eq!(outcome, AuthorityPlacement::Placed);
    assert!(same_clausification(
        cl[0].as_ref().expect("slot filled"),
        &clausification(7)
    ));
}

/// The legitimate re-placement: the split loop revisits a clause across
/// rounds and re-derives the SAME rule for the SAME source term. This used
/// to abort the whole solve.
#[test]
fn identical_replacement_is_reaffirmed_not_a_panic() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();
    let _ = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    let outcome = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    assert_eq!(outcome, AuthorityPlacement::Reaffirmed);
    assert!(cl[0].is_some(), "the resident authority must survive");
}

#[test]
fn identical_theory_replacement_is_reaffirmed() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();
    let _ = place_original_clause_authority_at_id(
        &solver,
        2,
        None,
        Some(theory_lemma(3)),
        &mut cl,
        &mut th,
    );

    let outcome = place_original_clause_authority_at_id(
        &solver,
        2,
        None,
        Some(theory_lemma(3)),
        &mut cl,
        &mut th,
    );

    assert_eq!(outcome, AuthorityPlacement::Reaffirmed);
    assert!(th[1].is_some());
}

/// The illegitimate re-placement: a different rule for the same clause ID.
/// Fail closed by RETRACTING both slots — the winner is nobody.
#[test]
fn conflicting_replacement_retracts_both_slots() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();
    let _ = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    let outcome = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(9)),
        None,
        &mut cl,
        &mut th,
    );

    assert_eq!(
        outcome,
        AuthorityPlacement::Refused(AuthorityRefusal::ConflictingReplacement)
    );
    assert!(cl[0].is_none(), "the contested clausification is retracted");
    assert!(th[0].is_none(), "the contested theory slot is retracted");
}

/// Cross-kind re-placement is a conflict too: one clause has one indexed
/// authority, so a theory lemma may not displace a clausification rule.
#[test]
fn cross_kind_replacement_retracts_both_slots() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();
    let _ = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    let outcome = place_original_clause_authority_at_id(
        &solver,
        1,
        None,
        Some(theory_lemma(7)),
        &mut cl,
        &mut th,
    );

    assert_eq!(
        outcome,
        AuthorityPlacement::Refused(AuthorityRefusal::ConflictingReplacement)
    );
    assert!(cl[0].is_none());
    assert!(th[0].is_none());
}

#[test]
fn two_independent_authorities_are_refused_without_placing() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();

    let outcome = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(7)),
        Some(theory_lemma(7)),
        &mut cl,
        &mut th,
    );

    assert_eq!(
        outcome,
        AuthorityPlacement::Refused(AuthorityRefusal::TwoIndependentAuthorities)
    );
    assert!(cl[0].is_none());
    assert!(th[0].is_none());
}

#[test]
fn unissued_id_is_refused_without_placing() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();

    let outcome = place_original_clause_authority_at_id(
        &solver,
        99,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    assert_eq!(
        outcome,
        AuthorityPlacement::Refused(AuthorityRefusal::IdNotIssuedAsOriginal)
    );
    assert!(cl.iter().all(Option::is_none));
}

#[test]
fn zero_id_is_refused_without_placing() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();

    let outcome = place_original_clause_authority_at_id(
        &solver,
        0,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    assert_eq!(
        outcome,
        AuthorityPlacement::Refused(AuthorityRefusal::IdIsZero)
    );
    assert!(cl.iter().all(Option::is_none));
}

#[test]
fn vacuous_placement_leaves_a_resident_authority_alone() {
    let solver = solver_with_originals(2);
    let (mut cl, mut th) = ledgers();
    let _ = place_original_clause_authority_at_id(
        &solver,
        1,
        Some(clausification(7)),
        None,
        &mut cl,
        &mut th,
    );

    let outcome = place_original_clause_authority_at_id(&solver, 1, None, None, &mut cl, &mut th);

    assert_eq!(outcome, AuthorityPlacement::Vacuous);
    assert!(cl[0].is_some());
}

#[test]
fn single_authority_helper_reports_the_issued_id() {
    let mut solver = Solver::new(4);
    let before = solver.issued_original_clause_id_max();
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]));
    let (mut cl, mut th) = ledgers();

    let id = place_single_original_clause_authority(
        &solver,
        before,
        Some(clausification(5)),
        None,
        &mut cl,
        &mut th,
    );

    let id = id.expect("exactly one original ID was issued");
    assert!(solver.is_issued_original_clause_id(id));
    let index = usize::try_from(id - 1).expect("addressable");
    assert!(cl[index].is_some());
}

#[test]
fn single_authority_helper_refuses_two_independent_authorities() {
    let mut solver = Solver::new(4);
    let before = solver.issued_original_clause_id_max();
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]));
    let (mut cl, mut th) = ledgers();

    let id = place_single_original_clause_authority(
        &solver,
        before,
        Some(clausification(5)),
        Some(theory_lemma(5)),
        &mut cl,
        &mut th,
    );

    assert_eq!(id, None);
    assert!(cl.iter().all(Option::is_none));
    assert!(th.iter().all(Option::is_none));
}
