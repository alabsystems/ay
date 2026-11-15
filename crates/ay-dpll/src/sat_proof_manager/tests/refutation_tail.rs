// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `process_trace` ends at its refutation (`refutation_tail`): a replay that
//! proves the empty clause before the trace ends leaves it as the proof's last
//! step, so the UNSAT assembly's partial check does not read the replayed
//! proof as a broken chain, and the steps the refutation rests on stay.

use super::*;

fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable::new(var))
    } else {
        Literal::negative(Variable::new(var))
    }
}

/// The authored `p` and `¬p`, and a trace over them: the learned clause `q`
/// (hints 1, 2), whose replay proves the empty clause, a strict subclause,
/// then the trace's own empty clause (hint 3). The input clause `¬q ∨ p`,
/// which the proof does not carry, is answered by an `assume` of its
/// disjunction and an `or` step, and is traced before or after `q`.
fn replay(input_clause_after_the_refutation: bool) -> (Proof, ProofId, TermStore) {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let p = var_to_term[&0];
    let mut proof = Proof::new();
    proof.add_assume(p, Some("h0".to_string()));
    proof.add_assume(negations[&p], Some("h1".to_string()));
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![lit(0, true)], true);
    trace.add_clause(2, vec![lit(0, false)], true);
    let input_clause = vec![lit(1, false), lit(0, true)];
    if !input_clause_after_the_refutation {
        trace.add_clause(4, input_clause.clone(), true);
    }
    trace.add_clause_with_hints(3, vec![lit(1, true)], false, vec![1, 2]);
    if input_clause_after_the_refutation {
        trace.add_clause(4, input_clause, true);
    }
    trace.add_clause_with_hints(5, Vec::new(), false, vec![3]);
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);
    let root = manager
        .process_trace(&trace, &mut proof)
        .expect("the trace refutes p and not p");
    (proof, root, terms)
}

fn or_steps(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Or,
                    ..
                }
            )
        })
        .count()
}

fn assert_refutation_closes_the_proof(proof: &Proof, root: ProofId, terms: &TermStore) {
    assert!(matches!(
        proof.get_step(root),
        Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
    ));
    assert_eq!(
        usize::try_from(root.0).map(|root| root + 1),
        Ok(proof.steps.len()),
        "the refutation is the proof's last step"
    );
    let (_, error) = ay_proof::check_proof_partial(proof, terms);
    assert!(error.is_none(), "{error:?}");
}

/// Fails when the replay keeps the `assume`/`or` pair it emits for the input
/// clause traced after the refutation: the partial checker then reports
/// `FinalClauseNotEmpty`, which the assembly reads as a broken chain.
#[test]
fn a_refutation_proved_before_the_trace_ends_is_the_last_step() {
    let (proof, root, terms) = replay(true);
    assert_refutation_closes_the_proof(&proof, root, &terms);
    assert_eq!(or_steps(&proof), 0, "no premise of the refutation");
}

/// The twin: the same input clause traced before the refutation keeps its
/// steps; only what follows the refutation is dropped.
#[test]
fn steps_emitted_before_the_refutation_are_kept() {
    let (proof, root, terms) = replay(false);
    assert_refutation_closes_the_proof(&proof, root, &terms);
    assert_eq!(or_steps(&proof), 1);
}
