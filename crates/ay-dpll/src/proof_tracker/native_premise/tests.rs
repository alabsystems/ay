// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source_fragment(terms: &mut TermStore) -> (TermId, TermId, Proof) {
    let x = terms.mk_var("registered_source_bound", Sort::Bool);
    let root = terms.mk_forall(vec![("registered_source_bound".into(), Sort::Bool)], x);
    let target = terms.false_term();
    let negative = terms.mk_not_raw(root);
    let packed = terms.mk_app(Symbol::named("or"), [negative, target], Sort::Bool);
    let mut fragment = Proof::new();
    let source = fragment.add_assume(root, None);
    let inst = fragment.add_rule_step(AletheRule::ForallInst, vec![packed], vec![], vec![target]);
    let unpacked =
        fragment.add_rule_step(AletheRule::Or, vec![negative, target], vec![inst], vec![]);
    fragment.add_resolution(vec![target], root, unpacked, source);
    (root, target, fragment)
}

#[test]
fn native_premise_import_rebases_all_references_and_reuses_derived_assumption() {
    let mut terms = TermStore::new();
    let (root, target, fragment) = source_fragment(&mut terms);
    let checked = ay_proof::authenticate_premise_clauses_strict_with_context(
        &fragment,
        &terms,
        None,
        None,
        &[root],
    )
    .unwrap();
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.add_assumption(root, None);
    let derived = tracker
        .append_native_premise(fragment, &checked, target, &mut |_, _| true)
        .unwrap();
    assert_eq!(
        tracker.add_assumption(target, None),
        Some(derived),
        "ordinary solving must consume the existing derivation, not a working Assume"
    );
    let mut proof = tracker.take_proof();
    let not_false = terms.mk_not_raw(target);
    let false_axiom = proof.add_rule_step(AletheRule::False, vec![not_false], vec![], vec![]);
    proof.add_resolution(vec![], target, derived, false_axiom);
    assert!(
        ay_proof::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[root]))
            .unwrap()
            .is_complete()
    );
    assert!(proof
        .steps
        .iter()
        .all(|s| !matches!(s,ProofStep::Assume(id) if *id!=root)));
}

#[test]
fn native_premise_import_refuses_wrong_conclusion_backreference_and_stopped_owner() {
    for mode in 0..3 {
        let mut terms = TermStore::new();
        let (root, target, mut fragment) = source_fragment(&mut terms);
        let checked = ay_proof::authenticate_premise_clauses_strict_with_context(
            &fragment,
            &terms,
            None,
            None,
            &[root],
        )
        .unwrap();
        let mut tracker = ProofTracker::new();
        tracker.enable();
        let requested = if mode == 0 { terms.true_term() } else { target };
        if mode == 1 {
            let ProofStep::Resolution { clause1, .. } = fragment.steps.last_mut().unwrap() else {
                panic!("resolution")
            };
            *clause1 = ProofId(u32::MAX);
        }
        assert!(tracker
            .append_native_premise(fragment, &checked, requested, &mut |_, _| mode != 2)
            .is_none());
        assert_eq!(tracker.num_steps(), 0);
        assert!(tracker.assumption_map.is_empty());
    }
}
