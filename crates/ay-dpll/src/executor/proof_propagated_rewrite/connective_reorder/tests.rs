// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The reorder bridge is linear in the connective's arity, with no arity cap:
//! a 1,000-argument `or`/`and` reversed is ONE gate step, one projection per
//! argument and ONE resolution, every clause of constant width but the gate,
//! and the strict checker accepts it. The binary chain it replaced re-stated
//! the shrinking clause at every step (`Θ(k²)` literals) behind a 64-argument
//! cap, above which the reach-encoded join fell back to the replay lane.

use super::*;

fn reversed_connective_implication(arity: usize, connective: Connective, head: &str) {
    let mut terms = TermStore::new();
    let args: Vec<TermId> = (0..arity)
        .map(|index| terms.mk_var(format!("wide_{index}"), Sort::Bool))
        .collect();
    let reversed: Vec<TermId> = args.iter().rev().copied().collect();
    let from = terms.mk_app(Symbol::named(head), args, Sort::Bool);
    let to = terms.mk_app(Symbol::named(head), reversed, Sort::Bool);
    let set = HashSet::default();
    let roots: [TermId; 0] = [];
    let records = HashMap::default();
    let entries = HashMap::default();
    let mut cx = PlanCx::new(&set, &roots, &records, &entries, &[], false);
    let implication = PropagationChainPlanner { terms: &mut terms }
        .plan_connective_implication(&mut cx, connective, from, to)
        .expect("a permutation of the same argument set bridges");

    assert_eq!(
        cx.chain.steps.len(),
        arity + 2,
        "one gate, one projection per argument, one resolution"
    );
    let literals: usize = cx
        .chain
        .steps
        .iter()
        .map(|step| match step {
            ProofStep::Step { clause, .. } => clause.len(),
            _ => 0,
        })
        .sum();
    assert!(
        literals <= 3 * arity + 4,
        "{literals} literals for arity {arity}"
    );

    let not_from = terms.mk_not_raw(from);
    let expected = match connective {
        Connective::And => [to, not_from],
        Connective::Or => [not_from, to],
    };
    let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        &cx.chain,
        &terms,
        None,
        None,
        &roots,
        &mut |_, _| true,
    )
    .expect("every bridge step is a checked rule instance");
    assert_eq!(checked.clause(implication), Some(expected.as_slice()));
}

#[test]
fn a_thousand_argument_or_reorder_is_one_linear_resolution() {
    reversed_connective_implication(1_000, Connective::Or, "or");
}

#[test]
fn a_thousand_argument_and_reorder_is_one_linear_resolution() {
    reversed_connective_implication(1_000, Connective::And, "and");
}
