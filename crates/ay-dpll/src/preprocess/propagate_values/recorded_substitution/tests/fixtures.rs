// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

pub(super) fn wrapper(
    progress: Box<dyn FnMut(usize, usize) -> bool>,
) -> (
    RecordedVariableSubstitution,
    Arc<Mutex<VariableSubstitution>>,
    Arc<Mutex<PropagateValues>>,
) {
    let substitution = Arc::new(Mutex::new(VariableSubstitution::new()));
    let propagation = Arc::new(Mutex::new(PropagateValues::new()));
    let wrapper = RecordedVariableSubstitution::new(
        Arc::clone(&substitution),
        Arc::clone(&propagation),
        progress,
    );
    (wrapper, substitution, propagation)
}

pub(super) fn array_roots(terms: &mut TermStore) -> Vec<TermId> {
    let value = terms.mk_var("payload", Sort::bitvec(129));
    let bound = terms.mk_var("bound", Sort::bitvec(129));
    let fill = terms.mk_bitvec(3.into(), 129);
    let base = terms.mk_const_array(Sort::Bool, fill);
    let array = terms.mk_var("array", terms.sort(base).clone());
    let key = terms.false_term();
    let stored = terms.mk_app(
        Symbol::named("store"),
        [base, key, value],
        terms.sort(base).clone(),
    );
    let source = eq(terms, array, stored);
    let read = terms.mk_app(Symbol::named("select"), [array, key], Sort::bitvec(129));
    let query = terms.mk_app(Symbol::named("bvult"), [read, bound], Sort::Bool);
    vec![source, query]
}

pub(super) fn replay(
    terms: &mut TermStore,
    originals: &[TermId],
    records: &PropagationRecords,
    target: TermId,
) -> Option<(ay_core::Proof, ay_core::ProofId)> {
    use crate::executor::proof_propagated_rewrite::{PlanCx, PropagationChainPlanner};
    let original_set = originals.iter().copied().collect();
    let mut rewrites = HashMap::default();
    let mut entries = HashMap::default();
    for rewrite in &records.rewrites {
        rewrites
            .entry(rewrite.after)
            .or_insert((rewrite.before, rewrite.stamp));
    }
    for entry in &records.entries {
        entries
            .entry(entry.expr)
            .or_insert((entry.value, entry.source_assertion, entry.stamp));
    }
    let mut context = PlanCx::new(&original_set, originals, &rewrites, &entries, &[], false);
    let mut planner = PropagationChainPlanner { terms };
    let conclusion = planner.plan_derive_clause(&mut context, target)?;
    Some((context.chain, conclusion))
}

pub(super) fn authenticated(
    terms: &TermStore,
    originals: &[TermId],
    proof: &ay_core::Proof,
    conclusion: ay_core::ProofId,
    target: TermId,
) -> bool {
    ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        proof,
        terms,
        None,
        None,
        originals,
        &mut |_, _| true,
    )
    .is_ok_and(|checked| checked.clause(conclusion) == Some([target].as_slice()))
}
