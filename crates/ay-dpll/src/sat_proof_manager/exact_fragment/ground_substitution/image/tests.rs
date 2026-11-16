// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_sat::ResolutionValidationResource;

#[test]
fn ground_substitution_image_refuses_deep_or_wide_inputs() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("bounded_p", Sort::Bool);
    let mut root = p;
    for _ in 0..MAX_IMAGE_DEPTH {
        root = terms.mk_not_raw(root);
    }
    assert!(bounded_order(&terms, root).is_some());
    root = terms.mk_not_raw(root);
    assert!(bounded_order(&terms, root).is_none());
    let wide = terms.mk_app(Symbol::named("and"), vec![p; MAX_IMAGE_VISITS], Sort::Bool);
    assert!(bounded_order(&terms, wide).is_none());
}

#[test]
fn ground_substitution_image_precharges_before_interning_or_proof_emission() {
    let mut terms = TermStore::new();
    let len = terms.mk_var("budget_len", Sort::Int);
    let one = terms.mk_int(1.into());
    let p = terms.mk_var("budget_p", Sort::Bool);
    let q = terms.mk_var("budget_q", Sort::Bool);
    let hyp = terms.mk_app(Symbol::named("="), [len, one], Sort::Bool);
    let not_hyp = terms.mk_not_raw(hyp);
    let body = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let source = terms.mk_app(Symbol::named("or"), [not_hyp, body], Sort::Bool);
    let baseline = terms.true_memory_bytes();
    let mut proof = Proof::new();
    let mut charged = 0;
    let mut progress = |_work, bytes| {
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            limit: 0,
            actual: bytes as u128,
        })
    };
    let vars = DetHashMap::default();
    let mut state = GroundSubstitutionState {
        proof: &mut proof,
        unit: p,
        authored_equalities: vec![(hyp, len)],
        term_store_baseline: baseline,
        charged_term_store_growth: &mut charged,
        progress: &mut progress,
    };
    let result = SatProofManager::new(&vars, &mut terms).ground_image_plan(
        source,
        &[(len, one)],
        &mut state,
    );
    assert!(matches!(
        result,
        Err(ExactOriginalProofError::Resource(
            ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            }
        ))
    ));
    assert_eq!(terms.true_memory_bytes(), baseline);
    assert_eq!(proof.steps, [] as [ay_core::ProofStep; 0]);
}
