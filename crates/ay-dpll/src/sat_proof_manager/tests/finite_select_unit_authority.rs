// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheoryLemmaKind;

struct BoolSelectFixture {
    terms: TermStore,
    foreign_array: TermId,
    index: TermId,
    symbolic_select: TermId,
    true_select: TermId,
    false_select: TermId,
}

fn bool_select_fixture() -> BoolSelectFixture {
    let mut terms = TermStore::new();
    // Match the mandatory QF_AX regression: the selected value is itself an
    // array, so the generated equality is kept structural.
    let cell_sort = Sort::array(Sort::Bool, Sort::Bool);
    let outer_sort = Sort::array(Sort::Bool, cell_sort);
    let array = terms.mk_var("finite_select_outer", outer_sort.clone());
    let foreign_array = terms.mk_var("finite_select_foreign", outer_sort);
    let index = terms.mk_var("finite_select_index", Sort::Bool);
    let true_term = terms.mk_bool(true);
    let false_term = terms.mk_bool(false);
    let symbolic_select = terms.mk_select(array, index);
    let true_select = terms.mk_select(array, true_term);
    let false_select = terms.mk_select(array, false_term);
    BoolSelectFixture {
        terms,
        foreign_array,
        index,
        symbolic_select,
        true_select,
        false_select,
    }
}

fn branch_equality(terms: &mut TermStore, value: TermId, symbolic_select: TermId) -> TermId {
    terms.mk_eq_coerce_no_ite_expand(value, symbolic_select)
}

fn build_fragment_for_unit(
    terms: &mut TermStore,
    unit: TermId,
) -> Result<ExactOriginalProofFragment, ExactOriginalProofError> {
    let var_to_term = HashMap::from_iter([(0, unit)]);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    SatProofManager::new(&var_to_term, terms).build_exact_original_proof_fragment(&trace, &[])
}

#[test]
fn exact_fragment_checks_complete_bool_select_expansion() {
    let BoolSelectFixture {
        mut terms,
        index,
        symbolic_select,
        true_select,
        false_select,
        ..
    } = bool_select_fixture();
    let true_branch = branch_equality(&mut terms, true_select, symbolic_select);
    let false_branch = branch_equality(&mut terms, false_select, symbolic_select);
    let axiom = terms.mk_ite_raw(index, true_branch, false_branch);
    assert!(ay_proof::recognize_array_finite_select_expansion(
        &terms,
        &[axiom]
    ));

    let fragment = build_fragment_for_unit(&mut terms, axiom)
        .expect("a complete Bool-select expansion has intrinsic authority");
    let binding = fragment
        .bindings
        .get(&1)
        .expect("binding for original ID 1");
    let proof_id = binding.proof_id;
    assert!(matches!(
        fragment.proof.get_step(proof_id),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayFiniteSelectExpansion,
            clause,
            ..
        }) if clause == &vec![axiom]
    ));

    // Exercise the actual strict checker, not merely the producer-side
    // classifier: close the checked tautology against a test assumption.
    let mut proof = fragment.proof;
    let not_axiom = terms.mk_not_raw(axiom);
    let negated = proof.add_assume(not_axiom, None);
    proof.add_resolution(Vec::new(), axiom, proof_id, negated);
    let quality = ay_proof::check_proof_strict(&proof, &terms)
        .expect("the exact-fragment lemma must pass strict checking");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn exact_fragment_rejects_duplicate_bool_select_branch() {
    let BoolSelectFixture {
        mut terms,
        index,
        symbolic_select,
        true_select,
        ..
    } = bool_select_fixture();
    let true_branch = branch_equality(&mut terms, true_select, symbolic_select);
    let forged = terms.mk_ite_raw(index, true_branch, true_branch);
    assert!(!ay_proof::recognize_array_finite_select_expansion(
        &terms,
        &[forged]
    ));

    assert_eq!(
        build_fragment_for_unit(&mut terms, forged)
            .expect_err("a duplicated branch must remain unauthenticated"),
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![forged],
        }
    );
}

#[test]
fn exact_fragment_rejects_foreign_array_select_branch() {
    let BoolSelectFixture {
        mut terms,
        foreign_array,
        index,
        symbolic_select,
        true_select,
        false_select,
    } = bool_select_fixture();
    let false_term = terms.mk_bool(false);
    let foreign_false_select = terms.mk_select(foreign_array, false_term);
    let true_branch = branch_equality(&mut terms, true_select, symbolic_select);
    let false_branch = branch_equality(&mut terms, foreign_false_select, symbolic_select);
    let forged = terms.mk_ite_raw(index, true_branch, false_branch);
    // Pin that merely retaining another valid domain point from the source
    // array does not accidentally make the foreign branch acceptable.
    assert_ne!(foreign_false_select, false_select);
    assert!(!ay_proof::recognize_array_finite_select_expansion(
        &terms,
        &[forged]
    ));

    assert_eq!(
        build_fragment_for_unit(&mut terms, forged)
            .expect_err("a branch from a foreign array must remain unauthenticated"),
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![forged],
        }
    );
}
