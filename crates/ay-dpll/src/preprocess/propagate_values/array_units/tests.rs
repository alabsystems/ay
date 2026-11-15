// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Symbol};

fn projected() -> (TermStore, Vec<TermId>, Arc<Proof>, ProofId, TermId) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let source = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let mut proof = Proof::new();
    let source_id = proof.add_assume(source, None);
    let not_source = terms.mk_not_raw(source);
    let projection = proof.add_rule_step(
        AletheRule::AndPos(0),
        vec![not_source, p],
        Vec::new(),
        vec![source],
    );
    let conclusion = proof.add_resolution(vec![p], source, projection, source_id);
    (terms, vec![source], Arc::new(proof), conclusion, p)
}

#[test]
fn exact_unit_is_source_authenticated_and_clones_share_the_proof() {
    let (mut terms, roots, proof, conclusion, term) = projected();
    let unit = ArrayUnitDerivation::checked(
        &terms,
        &roots,
        Arc::clone(&proof),
        conclusion,
        term,
        &mut |_, _| true,
    )
    .expect("exact source projection");
    assert_eq!(unit.term(), term);
    let copy = unit.clone();
    assert!(Arc::ptr_eq(&unit.proof, &copy.proof));
    assert!(Arc::ptr_eq(&unit.proof, &proof));
    // Append-only scratch growth is harmless; the consumer nevertheless
    // rechecks the source-bound proof instead of trusting the old result.
    terms.mk_var("scratch", Sort::bitvec(129));
    assert!(copy
        .reauthenticate(&terms, &roots, &mut |_, _| true)
        .is_some());
    assert!(copy.reauthenticate(&terms, &[], &mut |_, _| true).is_none());
    assert!(copy
        .reauthenticate(&terms, &[term], &mut |_, _| true)
        .is_none());
}

#[test]
fn claimed_unit_and_proof_conclusion_must_match_exactly() {
    let (terms, roots, proof, conclusion, term) = projected();
    for (claimed_term, claimed_conclusion) in [
        (terms.false_term(), conclusion),
        (term, ProofId(0)),
        (term, ProofId(u32::MAX)),
        (TermId(u32::MAX), conclusion),
    ] {
        assert!(ArrayUnitDerivation::checked(
            &terms,
            &roots,
            Arc::clone(&proof),
            claimed_conclusion,
            claimed_term,
            &mut |_, _| true,
        )
        .is_none());
    }
    assert!(
        ArrayUnitDerivation::checked(&terms, &[], proof, conclusion, term, &mut |_, _| true,)
            .is_none()
    );
}

#[test]
fn cancellation_at_admission_and_replay_never_reuses_an_earlier_success() {
    let (terms, roots, proof, conclusion, term) = projected();
    assert!(ArrayUnitDerivation::checked(
        &terms,
        &roots,
        Arc::clone(&proof),
        conclusion,
        term,
        &mut |_, _| false,
    )
    .is_none());
    let unit =
        ArrayUnitDerivation::checked(&terms, &roots, proof, conclusion, term, &mut |_, _| true)
            .unwrap();
    let mut calls = 0;
    assert!(unit
        .reauthenticate(&terms, &roots, &mut |_, _| {
            calls += 1;
            calls < 3
        })
        .is_none());
    assert_eq!(calls, 3);
    assert!(unit
        .reauthenticate(&terms, &roots, &mut |_, _| true)
        .is_some());
}
