// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-parse binding tests for portable strict proof bundles.

use crate::api::*;

const FOLDED_FALSE: &str = r#"
    (define-fun Inv ((__p0_a0 Int)) Bool
      (and (>= __p0_a0 0) (not (> __p0_a0 10))))
    (declare-const x Int)
    (assert (and (>= x 0) (not (> x 10)) (> x 10)))
    (check-sat)
    (exit)
"#;

const SIMPLE_UNSAT: &str = r#"
    (declare-const x Int)
    (assert (> x 5))
    (assert (< x 3))
    (check-sat)
"#;

fn proof_solver() -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict proof option");
    solver
}

#[test]
fn source_folded_false_bundle_is_bound_through_exact_parse_provenance() {
    let mut solver = proof_solver();
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(FOLDED_FALSE)
        .expect("exact folded-false parse");
    assert_eq!(binding.assertions().len(), 1);
    assert!(solver.check_sat().is_unsat());

    let bundle = solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .expect("source-rebuilt Assume must remain bound to its exact folded root");
    let checked = re_check_bundle_strict(&bundle).expect("bound bundle recheck");
    assert!(checked.quality.is_complete());
    assert!(!checked.assume_terms.is_empty());
    assert_eq!(checked.assume_terms, bundle.obligation_assertions);
    assert_ne!(
        bundle.obligation_assertions,
        binding
            .assertions()
            .iter()
            .map(|term| term.id())
            .collect::<Vec<_>>(),
        "fixture must exercise an authenticated source-rebuild id distinct from the folded root"
    );

    let mut missing_authority = bundle.clone();
    missing_authority.obligation_assertions.clear();
    assert!(re_check_bundle_strict(&missing_authority).is_err());
    let mut mutated_proof = bundle;
    mutated_proof.steps.pop().expect("non-empty proof");
    assert!(re_check_bundle_strict(&mutated_proof).is_err());
}

#[test]
fn exact_query_binding_rejects_foreign_stale_or_mutated_tokens() {
    let mut solver = proof_solver();
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("exact parse");
    assert!(solver.check_sat().is_unsat());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_some());

    let mut sibling = proof_solver();
    let sibling_binding = sibling
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("sibling exact parse");
    assert!(sibling.check_sat().is_unsat());
    assert!(sibling
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&sibling_binding)
        .is_none());

    let mut missing = binding.clone();
    missing.assertions.clear();
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&missing)
        .is_none());
    let mut duplicated = binding.clone();
    duplicated.assertions.push(duplicated.assertions[0]);
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&duplicated)
        .is_none());

    solver.try_reset().expect("full reset");
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
}

#[test]
fn exact_query_binding_rejects_post_parse_assertion_or_declaration() {
    let mut assertion_mutated = proof_solver();
    let assertion_binding = assertion_mutated
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("exact parse");
    assertion_mutated
        .parse_smtlib2("(assert true)")
        .expect("post-parse assertion");
    assert!(assertion_mutated.check_sat().is_unsat());
    assert!(assertion_mutated
        .export_last_unsat_bundle_for_exact_query(&assertion_binding)
        .is_none());

    let mut declaration_mutated = proof_solver();
    let declaration_binding = declaration_mutated
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("exact parse");
    declaration_mutated
        .try_declare_const("late", Sort::Int)
        .expect("post-parse declaration");
    assert!(declaration_mutated.check_sat().is_unsat());
    assert!(declaration_mutated
        .export_last_unsat_bundle_for_exact_query(&declaration_binding)
        .is_none());
}

#[test]
fn exact_query_binding_requires_an_initially_empty_plain_formula_state() {
    let mut solver = proof_solver();
    solver
        .parse_smtlib2("(assert true)")
        .expect("pre-existing assertion");
    assert!(solver
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .is_err());
}
