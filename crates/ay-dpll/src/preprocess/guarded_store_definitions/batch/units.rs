// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::AletheRule;

use super::*;

pub(super) fn derive(
    terms: &mut TermStore,
    originals: &[TermId],
    unit: discovery::Unit,
    progress: Progress<'_>,
) -> Option<CheckedActivatedUnit> {
    if !progress(64, 8192) {
        return None;
    }
    let mut proof = Proof::new();
    let source = proof.add_assume(unit.source, None);
    let not_activation = terms.mk_not_raw(unit.activation);
    let mut current = proof.add_rule_step(
        AletheRule::Or,
        vec![not_activation, unit.path.body],
        vec![source],
        Vec::new(),
    );
    for &(parent, position, child) in &unit.path.edges {
        if !progress(4, 2048) {
            return None;
        }
        let not_parent = terms.mk_not_raw(parent);
        let projected = proof.add_rule_step(
            AletheRule::AndPos(position),
            vec![not_parent, child],
            Vec::new(),
            vec![parent],
        );
        current = proof.add_rule_step(
            AletheRule::ThResolution,
            vec![not_activation, child],
            vec![current, projected],
            Vec::new(),
        );
    }
    let activation = proof.add_assume(unit.activation, None);
    let conclusion = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![unit.path.target],
        vec![current, activation],
        Vec::new(),
    );
    let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        &proof, terms, None, None, originals, progress,
    )
    .ok()?;
    if authenticated.clause(conclusion)? != [unit.path.target] || !progress(0, 0) {
        return None;
    }
    Some(CheckedActivatedUnit {
        unit: unit.path.target,
        proof,
        conclusion,
    })
}
