// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::{NativeReplayArtifact, Solver};
use crate::executor::model::SymbolicRecoveryScope;
use sha2::{Digest, Sha256};

mod lease_tests;
mod owner_output_tests;
mod owner_tests;

fn source_term(executor: &mut Executor, text: &str) -> TermId {
    let commands = ay_frontend::parse(&format!("(get-value ({text}))")).unwrap();
    let ay_frontend::Command::GetValue(terms) = &commands[0] else {
        panic!("source term")
    };
    executor.ctx.elaborate_surface_subterm(&terms[0].1).unwrap()
}

fn fixture(declarations: &str, assertions: &[&str]) -> (Executor, Vec<TermId>) {
    let mut executor = Executor::new();
    executor
        .execute_all(&ay_frontend::parse(declarations).unwrap())
        .unwrap();
    let mut roots = Vec::new();
    for assertion in assertions {
        let root = source_term(&mut executor, assertion);
        // A native context can retain an authored TermId directly. This
        // isolates the candidate builder from the separate macro adopter.
        executor.ctx.add_native_assertion_with_parsed(
            root,
            ay_frontend::Term::Symbol("__ay_api_assertion__".to_owned()),
        );
        roots.push(root);
    }
    executor.independent_gate_authored_assertions = Some(roots.clone());
    (executor, roots)
}

fn candidate(
    executor: &mut Executor,
    roots: &[TermId],
) -> (SymbolicRecoveryScope, SymbolicUfModel) {
    let scope = SymbolicRecoveryScope::enter(executor, Box::new(|_, _| true)).unwrap();
    let package = executor
        .qmc_symbolic_candidate(roots, &scope.admission())
        .unwrap();
    (scope, package)
}

#[test]
fn symbolic_uf_actual_reference_and_mapping_issued_inputs_replay_to_validated_sat() {
    for (bytes, digest) in [
        (
            include_str!("fixtures/reference-current-final.native.json"),
            "4ebf6f0d09bd9c7d613ed78641e71ba9d1c043b71281829b80857c7bb45f7877",
        ),
        (
            include_str!("fixtures/mapping-valid-key-difference.native.json"),
            "3dc3cc19b224856beacba0539fe6b541dd96f378ce3fa079c67f071e004d75e7",
        ),
    ] {
        let actual: String = Sha256::digest(bytes.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        assert_eq!(
            actual, digest,
            "fixture byte identity is not solve authority"
        );
        let artifact = NativeReplayArtifact::from_json_str(bytes).unwrap();
        assert_eq!(artifact.timeout_ms, None);
        assert_eq!(artifact.assertions.len(), 5);
        let details = Solver::replay_native_replay_artifact(&artifact).unwrap();
        assert!(
            details.result.is_sat(),
            "input_sha256={digest} timeout_ms={:?} roots={} result={:?} unknown_reason={:?}",
            artifact.timeout_ms,
            artifact.assertions.len(),
            details.result,
            details.unknown_reason
        );
        assert!(
            details.result.was_model_validated(),
            "input_sha256={digest} result={:?}",
            details.result
        );
        assert!(
            details.result.has_sat_emission_witness(),
            "input_sha256={digest} result={:?}",
            details.result
        );
        assert!(
            details.accept_for_consumer().is_ok(),
            "input_sha256={digest} result={:?}",
            details.result
        );
        eprintln!("symbolic issued SAT input_sha256={digest} timeout_ms={:?} roots={} validated=true consumer=accepted",artifact.timeout_ms,artifact.assertions.len());
    }
}

#[test]
fn symbolic_uf_non_membership_names_ranges_multiargument_and_acyclic_dependencies_are_general() {
    let (mut executor, roots) = fixture(
        "(set-logic AUFLIA)(declare-fun weather (Int) Bool)(declare-fun shift (Int Int) Int)",
        &[
            "(forall ((x Int)) (= (weather x) (and (<= (- 403) x) (< x 92))))",
            "(forall ((right Int) (left Int)) (= (shift left right) (- left right)))",
        ],
    );
    let (scope, package) = candidate(&mut executor, &roots);
    assert_eq!(package.definitions().len(), 2);
    assert_eq!(package.source_roots(), roots);
    assert!(package.is_current(&executor));
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &scope.admission())
        .unwrap();
    for (text, expected) in [
        ("(weather (- 403))", true),
        ("(weather 92)", false),
        ("(= (shift 7 2) 5)", true),
        ("(= (shift 2 7) (- 5))", true),
    ] {
        let term = source_term(&mut executor, text);
        let goal = if expected {
            term
        } else {
            executor.ctx.terms.mk_not(term)
        };
        assert!(executor.symbolic_residual_holds(&model, &[goal]));
    }
}

#[test]
fn symbolic_uf_array_parameters_and_real_bodies_preserve_exact_types() {
    let (mut executor,roots)=fixture(
        "(set-logic ALL)(declare-fun at ((Array Int Bool) Int) Bool)(declare-fun half (Real) Real)(declare-fun positive_half (Real) Bool)",
        &["(forall ((a (Array Int Bool)) (i Int)) (= (at a i) (select a i)))",
          "(forall ((r Real)) (= (half r) (/ r 2.0)))",
          "(forall ((r Real)) (= (positive_half r) (> (half r) 0.0)))"],
    );
    let (scope, package) = candidate(&mut executor, &roots);
    assert_eq!(package.definitions().len(), 3);
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &scope.admission())
        .unwrap();
    for (text, expected) in [
        (
            "(at (store ((as const (Array Int Bool)) false) 7 true) 7)",
            true,
        ),
        (
            "(at (store ((as const (Array Int Bool)) false) 7 true) 8)",
            false,
        ),
        ("(= (half 7.0) 3.5)", true),
        ("(positive_half (- 1.0))", false),
    ] {
        let term = source_term(&mut executor, text);
        let goal = if expected {
            term
        } else {
            executor.ctx.terms.mk_not(term)
        };
        let result = executor.symbolic_residual_check(&model, &[goal]);
        assert!(result.is_ok(), "{text}: {result:?}");
    }
}

#[test]
fn symbolic_uf_real_rational_definitions_are_total_and_exact() {
    let (mut executor, roots) = fixture(
        "(set-logic ALL)(declare-fun half (Real) Real)(declare-fun positive_half (Real) Bool)",
        &[
            "(forall ((r Real)) (= (half r) (/ r 2.0)))",
            "(forall ((r Real)) (= (positive_half r) (> (half r) 0.0)))",
        ],
    );
    let (scope, package) = candidate(&mut executor, &roots);
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &scope.admission())
        .unwrap();
    for text in [
        "(= (half 7.0) 3.5)",
        "(= (half 0.0) 0.0)",
        "(not (positive_half (- 1.0)))",
        "(positive_half 0.25)",
    ] {
        let term = source_term(&mut executor, text);
        let result = executor.symbolic_residual_check(&model, &[term]);
        assert!(result.is_ok(), "{text}: {result:?}");
    }
}

#[test]
fn symbolic_uf_source_reentry_epoch_pop_and_foreign_context_do_not_reuse_a_candidate() {
    let (mut executor, roots) = fixture(
        "(set-logic AUFLIA)(declare-fun f (Int) Bool)",
        &["(forall ((x Int)) (= (f x) (<= 4 x)))"],
    );
    let (scope, package) = candidate(&mut executor, &roots);
    let foreign = Executor::new();
    assert!(!package.is_current(&foreign));
    executor.advance_query_authority_epoch();
    assert!(!package.is_current(&executor));
    drop(scope);
    let (_scope, package) = candidate(&mut executor, &roots);
    executor
        .execute_all(&ay_frontend::parse("(push 1)(pop 1)").unwrap())
        .unwrap();
    assert!(!package.is_current(&executor));
}

#[test]
fn symbolic_uf_working_only_equations_cycles_free_capture_and_foreign_sorts_refuse() {
    for (declarations, assertions) in [
        (
            "(set-logic AUFLIA)(declare-fun f (Int) Int)(declare-fun g (Int) Int)",
            vec![
                "(forall ((x Int)) (= (f x) (g x)))",
                "(forall ((x Int)) (= (g x) (f x)))",
            ],
        ),
        (
            "(set-logic AUFLIA)(declare-fun f (Int) Int)(declare-const free Int)",
            vec!["(forall ((x Int)) (= (f x) free))"],
        ),
        (
            "(set-logic AUFLIA)(declare-sort Foreign 0)(declare-fun f (Foreign) Bool)",
            vec!["(forall ((x Foreign)) (f x))"],
        ),
        (
            "(set-logic AUFLIA)(declare-fun f (Int) Bool)",
            vec![
                "(forall ((x Int)) (= (f x) (< x 3)))",
                "(forall ((x Int)) (= (f x) (> x 8)))",
            ],
        ),
    ] {
        let (mut executor, roots) = fixture(declarations, &assertions);
        let scope = SymbolicRecoveryScope::enter(&executor, Box::new(|_, _| true)).unwrap();
        assert!(executor
            .qmc_symbolic_candidate(&roots, &scope.admission())
            .is_none());
    }
    let (mut executor, roots) = fixture(
        "(set-logic AUFLIA)(declare-fun f (Int) Bool)",
        &["(forall ((x Int)) (= (f x) (< x 3)))"],
    );
    executor.independent_gate_authored_assertions = None;
    let scope = SymbolicRecoveryScope::enter(&executor, Box::new(|_, _| true)).unwrap();
    assert!(executor
        .qmc_symbolic_candidate(&roots, &scope.admission())
        .is_none());
}

#[test]
fn symbolic_uf_candidates_never_turn_a_false_residual_into_a_model_fact() {
    let (mut executor, roots) = fixture(
        "(set-logic AUFLIA)(declare-fun weather (Int) Bool)",
        &["(forall ((x Int)) (= (weather x) (and (<= (- 403) x) (< x 92))))"],
    );
    let (scope, package) = candidate(&mut executor, &roots);
    let retained = package.clone();
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &scope.admission())
        .unwrap();
    let false_residual = source_term(&mut executor, "(weather 92)");
    assert!(!executor.symbolic_residual_holds(&model, &[false_residual]));
    assert!(
        executor.last_model.is_none(),
        "candidate data did not install SAT authority"
    );
    executor.independent_gate_authored_assertions = Some(vec![]);
    assert!(!retained.is_current(&executor));
    assert!(!executor.symbolic_residual_holds(&model, &[false_residual]));
}

#[test]
fn symbolic_uf_general_source_equation_contradictions_require_strict_checked_unsat() {
    use crate::api::{AletheDialect, Logic, ProofAcceptanceMode};
    for source in [
        "(set-logic AUFLIA)(declare-fun weather (Int) Bool) \
         (assert (forall ((x Int)) (= (weather x) (and (<= (- 403) x) (< x 92))))) \
         (assert (not (weather (- 403))))",
        "(set-logic AUFLIA)(declare-fun shift (Int Int) Int) \
         (assert (forall ((right Int) (left Int)) (= (shift left right) (- left right)))) \
         (assert (not (= (shift 7 2) 5)))",
    ] {
        let mut solver = Solver::try_new(Logic::Auflia).unwrap();
        solver.set_produce_proofs(true);
        solver.set_alethe_dialect(AletheDialect::PinnedCarcara);
        solver.parse_smtlib2(source).unwrap();
        let details = solver.check_sat_with_details();
        assert!(details.result.is_unsat(), "{details:#?}");
        let artifact = solver.export_last_unsat_artifact().unwrap();
        artifact
            .accept_for_consumer(ProofAcceptanceMode::Strict)
            .unwrap();
        crate::api::check_paired_document_for_test(
            artifact
                .alethe_problem_smt2
                .as_deref()
                .expect("strict proof retains exact paired problem"),
            &artifact.alethe,
        );
    }
}
