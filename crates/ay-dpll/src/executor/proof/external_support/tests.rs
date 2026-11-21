// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::proofs::{
    native_support_test_executor as exec, native_support_test_executor_mut as exec_mut,
};
use crate::api::{Logic, Solver, StrictProofVerdict};
use ay_core::{ProofId, Sort};

fn native_fixture(duplicate: bool, self_check: bool) -> Solver {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    exec_mut(&mut solver).set_self_check(self_check);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    solver
        .try_declare_const("unused_sequence", Sort::Seq(Box::new(Sort::Int)))
        .unwrap();
    let p = solver.try_declare_const("native_p", Sort::Bool).unwrap();
    let not_p = solver.try_not(p).unwrap();
    solver.try_assert_term(p).unwrap();
    if duplicate {
        solver.try_assert_term(p).unwrap();
    }
    solver.try_assert_term(not_p).unwrap();
    let result = solver.check_sat();
    assert!(result.is_unsat(), "{result:?}");
    solver
}

fn support(solver: &Solver) -> Arc<CheckedExternalProofSupport> {
    exec(solver)
        .checked_external_proof_support_for_current_proof()
        .expect("native proof must acquire a checked paired surface")
}

#[test]
fn native_support_is_prepared_before_self_check_and_carried_when_transport_is_omitted() {
    let solver = native_fixture(false, true);
    assert!(exec(&solver)
        .checked_external_proof_support
        .borrow()
        .is_some());
    let checked = support(&solver);
    assert_eq!(
        exec(&solver).strict_gate_carcara_surface(),
        Some(checked.surface().clone())
    );
    for artifact in [
        solver.export_last_unsat_artifact().unwrap(),
        solver
            .export_last_unsat_artifact_without_problem_transport()
            .unwrap(),
    ] {
        assert!(matches!(
            artifact.strict_verdict,
            StrictProofVerdict::Verified(_)
        ));
        assert_eq!(artifact.alethe, checked.proof_text());
        assert_eq!(
            artifact.alethe_problem_smt2.as_deref(),
            Some(checked.problem_text())
        );
        assert_eq!(artifact.carcara_surface, *checked.surface());
        let description = artifact.external_support().unwrap();
        assert_eq!(description, checked.disclosure());
        assert_eq!(description.original_assertion_count(), 2);
        assert_eq!(
            description.proof_sha256(),
            <[u8; 32]>::from(Sha256::digest(artifact.alethe.as_bytes()))
        );
        assert_eq!(
            description.supported_problem_sha256(),
            <[u8; 32]>::from(Sha256::digest(checked.problem_text().as_bytes()))
        );
        assert!(!checked.problem_text().contains("unused_sequence"));
        assert!(!checked.problem_text().contains("Seq"));
    }
}

#[test]
fn native_support_maps_every_emitted_assume_to_the_earliest_duplicate_occurrence() {
    let solver = native_fixture(true, false);
    let checked = support(&solver);
    let source = exec(&solver).native_proof_source_scope.as_ref().unwrap();
    let proof = exec(&solver).last_proof.as_ref().unwrap();
    assert_eq!(source.roots().len(), 3);
    assert_eq!(source.roots()[0], source.roots()[1]);
    let emitted: Vec<_> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(index, step)| {
            let ProofStep::Assume(term) = step else {
                return None;
            };
            Some((u32::try_from(index).unwrap(), *term))
        })
        .collect();
    assert_eq!(emitted.len(), checked.disclosure().assumptions().len());
    for ((step, term), mapping) in emitted.iter().zip(checked.disclosure().assumptions()) {
        assert_eq!(*step, mapping.proof_step());
        assert_eq!(source.roots()[mapping.original_assertion_index()], *term);
        assert_eq!(
            mapping.original_assertion_index(),
            source.roots().iter().position(|root| root == term).unwrap()
        );
    }
}

#[test]
fn native_support_refuses_even_an_unused_foreign_assume() {
    let mut solver = native_fixture(false, false);
    let _original = support(&solver);
    let foreign = exec_mut(&mut solver)
        .ctx
        .terms
        .mk_fresh_var("unused_foreign", Sort::Bool);
    let proof = exec_mut(&mut solver).last_proof.as_mut().unwrap();
    proof
        .steps
        .insert(proof.steps.len() - 1, ProofStep::Assume(foreign));
    let unchanged = proof.clone();
    assert!(exec(&solver)
        .checked_external_proof_support_for_current_proof()
        .is_none());
    assert_eq!(exec(&solver).last_proof.as_ref(), Some(&unchanged));
    assert!(!exec(&solver)
        .strict_gate_carcara_surface()
        .unwrap()
        .is_supported());
}

#[test]
fn native_support_refuses_anchor_local_assumes_even_when_the_term_is_an_original_root() {
    let solver = native_fixture(false, false);
    let source = exec(&solver).native_proof_source_scope.as_ref().unwrap();
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(2),
        variables: Vec::new(),
    });
    proof.steps.push(ProofStep::Assume(source.roots()[0]));
    assert!(select_assumptions(source, &proof, &mut |_, _| true).is_none());
}

#[test]
fn native_support_refreshes_after_literal_proof_repair() {
    let mut solver = native_fixture(false, false);
    let previous = support(&solver);
    let original = exec(&solver)
        .native_proof_source_scope
        .as_ref()
        .unwrap()
        .roots()[0];
    let proof = exec_mut(&mut solver).last_proof.as_mut().unwrap();
    proof
        .steps
        .insert(proof.steps.len() - 1, ProofStep::Assume(original));
    let checked = support(&solver);
    assert!(!Arc::ptr_eq(&previous, &checked));
    assert_eq!(
        checked.disclosure().assumptions().len(),
        previous.disclosure().assumptions().len() + 1
    );
    assert_ne!(checked.proof_text(), previous.proof_text());
}

#[test]
fn native_support_survives_append_only_proof_terms_but_rejects_checker_metadata_changes() {
    let mut solver = native_fixture(false, false);
    let previous = support(&solver);
    let _fresh = exec_mut(&mut solver)
        .ctx
        .terms
        .mk_fresh_var("unread_proof_temporary", Sort::Int);
    assert!(Arc::ptr_eq(&previous, &support(&solver)));
    exec_mut(&mut solver).ctx.terms.mark_to_real_shadowed();
    assert!(exec(&solver)
        .checked_external_proof_support_for_current_proof()
        .is_none());
}

#[test]
fn native_support_does_not_cross_identical_public_query_epochs() {
    let mut solver = native_fixture(false, false);
    let previous = support(&solver);
    assert!(solver.check_sat().is_unsat());
    let current = support(&solver);
    assert!(!Arc::ptr_eq(&previous, &current));
    assert!(!previous.source.is_current_after_proof_growth(exec(&solver)));
}

#[test]
fn native_support_refuses_changed_declarations_and_surface_overrides() {
    let mut declarations = native_fixture(false, false);
    let _ = support(&declarations);
    declarations.try_declare_const("later", Sort::Int).unwrap();
    assert!(exec(&declarations)
        .checked_external_proof_support_for_current_proof()
        .is_none());

    let mut overrides = native_fixture(false, false);
    let _ = support(&overrides);
    let term = exec(&overrides)
        .native_proof_source_scope
        .as_ref()
        .unwrap()
        .roots()[0];
    let mut table = DetHashMap::default();
    table.insert(term, "changed_free_symbol".to_owned());
    exec_mut(&mut overrides).last_proof_term_overrides = Some(table);
    assert!(exec(&overrides)
        .checked_external_proof_support_for_current_proof()
        .is_none());
}

#[test]
fn native_support_cache_does_not_override_a_stopping_caller() {
    let mut solver = native_fixture(false, false);
    let _ = support(&solver);
    let interrupt = solver.interrupt_handle();
    // The public solve has retired its controls. Install the same actual
    // caller handle for this independent executor operation before stopping it.
    exec_mut(&mut solver).set_solve_controls(Some(interrupt), None);
    solver.interrupt();
    assert!(exec(&solver)
        .checked_external_proof_support_for_current_proof()
        .is_none());
}

#[test]
fn native_support_prices_ignored_nested_hint_payload_before_clone_or_cache_equality() {
    use ay_core::{CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation, TheoryLemmaKind};

    let mut solver = native_fixture(false, false);
    let _cached = support(&solver);
    let zero = exec_mut(&mut solver).ctx.terms.mk_int(0.into());
    let truth = exec_mut(&mut solver).ctx.terms.mk_app(
        ay_core::Symbol::named("="),
        [zero, zero],
        Sort::Bool,
    );
    let proof = exec_mut(&mut solver).last_proof.as_mut().unwrap();
    proof.steps.insert(
        proof.steps.len() - 1,
        ProofStep::TheoryLemma {
            theory: "LIA".to_owned(),
            clause: vec![truth],
            farkas: None,
            kind: TheoryLemmaKind::ArithClauseTautology,
            lia: Some(LiaAnnotation::CuttingPlane(CuttingPlaneAnnotation {
                farkas: FarkasAnnotation::new(vec![
                    num_rational::Rational64::from_integer(1);
                    MAX_SUPPORT_PAYLOAD + 1
                ]),
                divisor: 1,
            })),
        },
    );
    // This hint is not semantic authority for this independently checked
    // tautology. Its retained heap still needs pricing before Eq or clone.
    let proof = exec(&solver).last_proof.as_ref().unwrap();
    assert!(exec(&solver)
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(payload::preflight(proof, &mut |_, _| true).is_none());
    assert!(exec(&solver)
        .checked_external_proof_support_for_current_proof()
        .is_none());
}

#[test]
fn native_support_refuses_a_strict_native_proof_with_an_honest_wire_hole() {
    use ay_core::TheoryLemmaKind;

    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .try_declare_const("unused_sequence", Sort::Seq(Box::new(Sort::Int)))
        .unwrap();
    let p = solver.try_declare_const("p", Sort::Bool).unwrap();
    let not_p = solver.not(p);
    let array = solver
        .try_declare_const("a", Sort::array(Sort::Int, Sort::Int))
        .unwrap();
    let i = solver.try_declare_const("i", Sort::Int).unwrap();
    let j = solver.try_declare_const("j", Sort::Int).unwrap();
    let x = solver.try_declare_const("x", Sort::Int).unwrap();
    let w = solver.try_declare_const("w", Sort::Int).unwrap();
    let at_i = solver.select(array, i);
    let at_j = solver.select(array, j);
    let first_root = solver.eq(at_i, x);
    let second_root = solver.eq(at_j, w);
    for root in [first_root, second_root, p, not_p] {
        solver.try_assert_term(root).unwrap();
    }
    assert!(solver.check_sat().is_unsat());
    let left_first = solver.store(array, i, x);
    let left = solver.store(left_first, j, w);
    let right_first = solver.store(array, j, w);
    let right = solver.store(right_first, i, x);
    let same_index = solver.eq(i, j);
    let permutation = solver.eq(left, right);
    let mut proof = Proof::new();
    // Keep these exact original premises as unused emitted assumptions so
    // their declared symbols also belong to the printer's premise scope.
    // The native Bool contradiction alone still closes the empty clause.
    proof.add_assume(first_root.id(), None);
    proof.add_assume(second_root.id(), None);
    let yes = proof.add_assume(p.id(), None);
    let no = proof.add_assume(not_p.id(), None);
    proof.add_theory_lemma_with_kind(
        "arrays",
        vec![same_index.id(), permutation.id()],
        TheoryLemmaKind::ArrayStorePermutation,
    );
    proof.add_resolution(Vec::new(), p.id(), yes, no);
    assert!(exec(&solver)
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let source = exec(&solver).native_proof_source_scope.as_ref().unwrap();
    let (_, selected, terms) = select_assumptions(source, &proof, &mut |_, _| true).unwrap();
    assert_eq!(selected.len(), 4);
    assert!(exec(&solver)
        .render_external_support_problem(&selected, &terms, source, None)
        .is_some());
    let wire = ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        exec(&solver).terms(),
        &selected,
        None,
        Some(MAX_SUPPORT_RENDER_WORK),
    )
    .unwrap();
    assert!(wire.contains(":rule hole"), "{wire}");
    exec_mut(&mut solver).last_proof = Some(proof);
    assert!(exec(&solver)
        .checked_external_proof_support_for_current_proof()
        .is_none());
    assert!(!exec(&solver)
        .strict_gate_carcara_surface()
        .unwrap()
        .is_supported());
    assert!(exec(&solver).proof_has_known_wire_gap(exec(&solver).last_proof.as_ref().unwrap()));
    let artifact = solver.export_last_unsat_artifact().unwrap();
    assert!(artifact.external_support().is_none());
    assert!(!artifact.carcara_surface.is_supported());
    assert!(artifact.alethe.contains(":rule hole"));
}

#[test]
fn native_support_preserves_text_and_mixed_context_d7_disclosure() {
    for mixed in [false, true] {
        let mut solver = Solver::new(Logic::All);
        solver.set_produce_proofs(true);
        let p = solver.try_declare_const("p", Sort::Bool).unwrap();
        solver
            .parse_smtlib2("(declare-const unused_sequence (Seq Int))(assert p)")
            .unwrap();
        if mixed {
            let not_p = solver.try_not(p).unwrap();
            solver.try_assert_term(not_p).unwrap();
        } else {
            solver.parse_smtlib2("(assert (not p))").unwrap();
        }
        assert!(solver.check_sat().is_unsat());
        assert!(exec(&solver).native_proof_source_scope.is_none());
        assert!(exec(&solver)
            .checked_external_proof_support_for_current_proof()
            .is_none());
        let artifact = solver.export_last_unsat_artifact().unwrap();
        assert!(artifact.external_support().is_none());
        assert!(!artifact.carcara_surface.is_supported());
        assert!(artifact.alethe_problem_smt2.unwrap().contains("Seq"));
    }
}
