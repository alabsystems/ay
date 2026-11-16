// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::api::SerializableProofBundle;

const DATATYPE: &str = "(declare-datatype D ((a) (b))) (declare-const x D) \
    (assert (= x a)) (assert (= x b)) (check-sat)";
const DATATYPE_SAT: &str = "(declare-datatype D ((a) (b))) (declare-const x D) \
    (assert (= x a)) (check-sat)";

#[derive(Clone, Copy)]
enum AdapterMode {
    Deadline,
    Cancellable,
}

fn certificate(source: &str, mode: AdapterMode) -> Option<StrictUnsatCert> {
    match mode {
        AdapterMode::Deadline => {
            smtlib_strict_unsat_cert_via_executor_until(source, hang_deadline())
        }
        AdapterMode::Cancellable => {
            let parent = crate::CancellationToken::new();
            let cancellation = ReplayCancellation::new(&parent.child());
            let cert = smtlib_strict_unsat_cert_via_executor_with_limit(
                source,
                ReplayLimit::Cancellable {
                    deadline: hang_deadline(),
                    cancellation: &cancellation,
                },
            );
            assert!(!parent.is_cancelled());
            assert!(!cancellation.is_cancelled());
            cert
        }
    }
}

fn assert_native_bundle(bundle: &SerializableProofBundle) {
    let checked = ay_dpll::api::re_check_bundle_strict(bundle).unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(bundle.obligation_assertions.len(), 2);
    assert_eq!(
        ordered_unique_assumes(&checked.assume_terms),
        bundle.obligation_assertions
    );
    assert!(bundle.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::DatatypeDistinct,
            ..
        }
    )));
}

fn native_bundle() -> SerializableProofBundle {
    let query = parse_plain_query(DATATYPE, ReplayLimit::Until(hang_deadline())).unwrap();
    let mut solver = Solver::try_new_with_config(query.logic, solver_config()).unwrap();
    solver.set_produce_proofs(true);
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(&query.body)
        .unwrap();
    assert!(solver.check_sat().is_unsat());
    let bundle = solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut |_, _| true)
        .unwrap()
        .unwrap();
    bundle
}

#[test]
fn native_datatype_authority_and_retained_bundle_replay_work_in_all_adapter_modes() {
    for mode in [AdapterMode::Deadline, AdapterMode::Cancellable] {
        let cert = certificate(DATATYPE, mode).expect("native datatype proof must be available");
        assert!(matches!(
            cert.strict_verdict,
            ay_dpll::api::StrictProofVerdict::Verified(ref quality) if quality.is_complete()
        ));
        assert_native_bundle(&cert.bundle);
        // Use the actual offline native bundle reader; no external wire rule
        // licenses this proof.
        let bytes = serde_json::to_vec(&cert.bundle).unwrap();
        let retained: SerializableProofBundle = serde_json::from_slice(&bytes).unwrap();
        assert_native_bundle(&retained);
        assert_eq!(serde_json::to_vec(&retained).unwrap(), bytes);
    }
}

#[test]
fn explicit_datatype_wire_request_and_satisfiable_neighbor_still_refuse() {
    let wire = format!("(set-option :check-proofs-strict true) {DATATYPE}");
    for mode in [AdapterMode::Deadline, AdapterMode::Cancellable] {
        assert!(certificate(&wire, mode).is_none());
        assert!(certificate(DATATYPE_SAT, mode).is_none());
    }
}

#[test]
fn consumer_replay_rejects_datatype_registry_signature_source_and_proof_mutations() {
    let bundle = native_bundle();
    assert_native_bundle(&bundle);
    let mut registry = bundle.clone();
    registry.datatype_declarations.clear();
    let mut signature = bundle.clone();
    signature.datatype_member_signatures[0].result_sort = ay_core::Sort::Bool;
    let mut source = bundle.clone();
    source.obligation_assertions.clear();
    let mut proof = bundle.clone();
    proof.steps.pop().expect("the original proof is nonempty");
    for altered in [registry, signature, source, proof] {
        assert!(ay_dpll::api::re_check_bundle_strict(&altered).is_err());
        let limit = ReplayLimit::Until(hang_deadline());
        let mut progress = ProofProgress::new(limit, ReplayMemory::capture(None));
        assert!(checked_certificate(altered, limit, &mut progress).is_none());
    }
    let limit = ReplayLimit::Until(hang_deadline());
    let mut progress = ProofProgress::new(limit, ReplayMemory::capture(None));
    assert!(checked_certificate(bundle, limit, &mut progress).is_some());
}

#[test]
fn native_datatype_cancellation_zero_memory_and_expiry_never_admit_a_certificate() {
    let bundle = native_bundle();
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let limit = ReplayLimit::Cancellable {
        deadline: hang_deadline(),
        cancellation: &cancellation,
    };
    let mut progress = ProofProgress::new(limit, ReplayMemory::capture(None));
    parent.cancel();
    assert!(checked_certificate(bundle.clone(), limit, &mut progress).is_none());
    parent.reset();
    assert!(checked_certificate(bundle, limit, &mut progress).is_none());
    assert!(cancellation.is_cancelled());
    assert!(smtlib_strict_unsat_cert_via_executor_until(DATATYPE, Instant::now()).is_none());
    {
        let _scope = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        for mode in [AdapterMode::Deadline, AdapterMode::Cancellable] {
            assert!(certificate(DATATYPE, mode).is_none());
        }
    }
    assert_native_bundle(
        &certificate(DATATYPE, AdapterMode::Cancellable)
            .unwrap()
            .bundle,
    );
}
