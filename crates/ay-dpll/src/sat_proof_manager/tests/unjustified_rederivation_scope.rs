// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope of the certified re-derivation in `process_trace`
//! (DR-AY-EUF-BRIDGE-20261103): it targets an original whose step would be
//! unjustified, a `Generic` annotation or an already seeded premiseless
//! `trust`/`Generic` leaf. An unannotated original keeps the step the proof
//! answers it with (its authority when authored, outside the DR's scope
//! otherwise), and a clause the proof already carries with a justified step
//! is answered by that step whatever its annotation says; neither is traded
//! for a replay over the processed versions. The acceptance path is
//! `test_process_trace_rederives_generic_annotated_original`.

use ay_core::{TheoryLemmaKind, TheoryLemmaProof};

use super::*;

/// Every step the derivation of `root` rests on.
fn premise_closure(proof: &Proof, root: ProofId) -> Vec<ProofId> {
    let mut seen: HashSet<ProofId> = HashSet::default();
    let mut stack = vec![root];
    let mut closure = Vec::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        closure.push(id);
        match proof.get_step(id) {
            Some(ProofStep::Resolution {
                clause1, clause2, ..
            }) => stack.extend([*clause1, *clause2]),
            Some(ProofStep::Step { premises, .. }) => stack.extend(premises.iter().copied()),
            _ => {}
        }
    }
    closure
}

fn generic(clause: Vec<TermId>) -> TheoryLemmaProof {
    TheoryLemmaProof {
        clause,
        kind: TheoryLemmaKind::Generic,
        farkas: None,
        lia: None,
    }
}

/// How the proof under assembly already carries the unit `p`.
enum SeededP {
    /// An authored assumption.
    Assumed,
    /// A certified (non-`Generic`) theory lemma.
    CertifiedLemma,
}

/// `q` carries only a `Generic` annotation and nothing derives it, so it stays
/// a `Generic` leaf. `¬q`, `p` and `¬p` are input clauses, `p` and `¬p`
/// already carried by the proof (`p` as `seeded`), and the trace refutes
/// `p ∧ ¬p`. By the time `p` is processed, `{q, ¬q}` already refutes by
/// propagation, so a replay of `p` "derives" the empty clause, a strict
/// subclause, through the `Generic` leaf. Answered by its own step, `p`
/// closes the trace's own refutation, which needs no `Generic` leaf. Returns
/// whether the refutation rests on one.
fn refutation_rests_on_generic(seeded: SeededP, generic_annotation_for_p: bool) -> bool {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let mut lemma_proofs: HashMap<Vec<TermId>, TheoryLemmaProof> = HashMap::default();
    lemma_proofs.insert(vec![q], generic(vec![q]));
    if generic_annotation_for_p {
        lemma_proofs.insert(vec![p], generic(vec![p]));
    }
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);
    manager.set_theory_lemma_proofs(&lemma_proofs);

    let mut proof = Proof::new();
    match seeded {
        SeededP::Assumed => {
            proof.add_assume(p, Some("h0".to_string()));
        }
        SeededP::CertifiedLemma => {
            proof.add_theory_lemma_with_farkas_and_kind_opt(
                "theory",
                vec![p],
                None,
                TheoryLemmaKind::EufTransitive,
            );
        }
    }
    proof.add_assume(negations[&p], Some("h1".to_string()));
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(1))], true);
    trace.add_clause(2, vec![Literal::negative(Variable::new(1))], true);
    trace.add_clause(3, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(4, vec![Literal::negative(Variable::new(0))], true);
    trace.add_clause_with_hints(5, Vec::new(), false, vec![3, 4]);

    let empty_id = manager
        .process_trace(&trace, &mut proof)
        .expect("the trace refutes p and not p");
    assert!(matches!(
        proof.get_step(empty_id),
        Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
    ));
    premise_closure(&proof, empty_id).into_iter().any(|id| {
        matches!(
            proof.get_step(id),
            Some(ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            })
        )
    })
}

#[test]
fn unannotated_original_is_not_rederived_through_an_unjustified_leaf() {
    assert!(
        !refutation_rests_on_generic(SeededP::Assumed, false),
        "the refutation must not rest on the Generic leaf"
    );
}

/// A `Generic` annotation keyed by `p`'s content does not make `p` a target
/// while the proof carries `p` as an authored assumption.
#[test]
fn generic_annotated_original_seeded_as_an_assumption_keeps_its_step() {
    assert!(
        !refutation_rests_on_generic(SeededP::Assumed, true),
        "the refutation must not rest on the Generic leaf"
    );
}

/// Nor while the proof carries `p` as a certified theory lemma.
#[test]
fn generic_annotated_original_seeded_as_a_certified_lemma_keeps_its_step() {
    assert!(
        !refutation_rests_on_generic(SeededP::CertifiedLemma, true),
        "the refutation must not rest on the Generic leaf"
    );
}
