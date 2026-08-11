// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conformance pin for mandatory public UNSAT certification.

use std::path::PathBuf;

use ay_dpll::api::{Logic, Solver, Sort};

fn read(rel: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()))
}

#[test]
fn public_boolean_unsat_carries_strict_emission_witness() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "a strict-valid contradiction must remain UNSAT"
    );
    assert!(
        result.has_unsat_emission_witness(),
        "public UNSAT must consume the private exact-query capability"
    );
    assert_eq!(result.accept_for_consumer(), Ok(result.result()));
}

#[test]
fn assumption_unsat_certificate_is_bound_to_temporary_literal() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);
    let not_p = solver.not(p);

    let result = solver.check_sat_assuming(&[not_p]);
    assert!(result.is_unsat());
    assert!(result.has_unsat_emission_witness());

    // The assumption is query-local. Its removal must start a different epoch
    // and may not reuse the preceding UNSAT capability.
    let followup = solver.check_sat();
    assert!(followup.is_sat());
    assert!(!followup.has_unsat_emission_witness());
}

#[test]
fn token_is_minted_only_after_epoch_and_strict_proof_checks() {
    let source = read("src/executor/unsat_cert.rs");
    assert_eq!(
        source.matches("UnsatCertificate(epoch.id)").count(),
        1,
        "the private UNSAT capability must have one mint site"
    );
    let mint = source
        .find("fn mint_unsat_certificate(")
        .expect("mandatory mint function must exist");
    let funnel = source
        .find("pub(crate) fn certify_unsat_for_publication(")
        .expect("public UNSAT funnel must exist");
    let body = &source[mint..funnel];
    let bound = body
        .find("if bound != assumptions")
        .expect("mint must bind exact assumptions");
    let provenance = body
        .find("provenance.original_problem_assertions != epoch.assertions")
        .expect("mint must bind exact authored assertions");
    let proof = body
        .find("self.check_proof_strict_with_datatypes(proof)")
        .expect("mint must invoke the strict proof checker");
    let capability = body
        .find("UnsatCertificate(epoch.id)")
        .expect("mint must construct the capability");
    assert!(
        bound < provenance && provenance < proof && proof < capability,
        "exact assumptions/assertions and strict proof must be checked before minting"
    );
}

#[test]
fn cli_and_native_public_paths_route_through_unsat_funnel() {
    let executor = read("src/executor.rs");
    assert!(
        executor
            .matches("self.certify_unsat_for_publication(sat_result,")
            .count()
            >= 2,
        "both SMT-LIB check-sat variants must use the UNSAT funnel"
    );

    let native = read("src/api/solving/check.rs");
    assert!(
        native
            .matches(".certify_unsat_for_publication(result,")
            .count()
            >= 3,
        "plain, interruptible, and assumption native checks must use the funnel"
    );
    assert!(
        native.contains("pub(super) fn finish_verified_result(")
            && native.contains("let unsat_certificate = self.executor.take_unsat_certificate();"),
        "the sole native result boundary must consume the one-shot token"
    );

    let result = read("src/api/types/results.rs");
    assert!(
        result.contains("pub(crate) fn certified_unsat(")
            && result.contains("_certificate: UnsatCertificate")
            && !result.contains("pub(crate) fn from_validated("),
        "VerifiedSolveResult must have no token-free definite UNSAT constructor"
    );
}

#[test]
fn proof_output_opt_out_does_not_disable_internal_certification() {
    let lifecycle = read("src/executor/lifecycle.rs");
    let begin = lifecycle
        .find("pub(crate) fn begin_public_solve(")
        .expect("public solve lifecycle entry must exist");
    let mutation = lifecycle[begin..]
        .find("pub(crate) fn note_api_assertion_mutation")
        .map(|offset| begin + offset)
        .expect("public solve entry must have a bounded source region");
    let body = &lifecycle[begin..mutation];
    let tracking = body
        .find("self.proof_tracker.enable();")
        .expect("public solve must enable mandatory internal proof tracking");
    let epoch = body
        .find("self.begin_unsat_query_epoch(&authored_assertions);")
        .expect("public solve must freeze the UNSAT query epoch");
    let provenance = body
        .find("self.install_proof_source_provenance(&authored_assertions);")
        .expect("public solve must install authored proof provenance");
    assert!(tracking < epoch && epoch < provenance);

    let proof = read("src/executor/proof.rs");
    assert!(
        proof.contains("if !self.is_producing_proofs()"),
        "mandatory internal tracking must not opt users into `(get-proof)`"
    );
}
