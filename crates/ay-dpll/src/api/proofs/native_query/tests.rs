// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::{Logic, NativeReplayExportLimits, Sort};
use std::time::Duration;

fn contradiction() -> Solver {
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);
    solver.set_timeout(Some(Duration::from_secs(2)));
    let p = solver.declare_const("native_subject", Sort::Bool);
    let not_p = solver.try_not(p).unwrap();
    solver.try_assert_term(p).unwrap();
    solver.try_assert_term(not_p).unwrap();
    solver
}

fn input_budget() -> NativeReplayExportBudget {
    NativeReplayExportBudget::new(NativeReplayExportLimits::new(
        64 << 20,
        64 << 20,
        64 << 20,
        128,
    ))
}

fn document_limits() -> ay_proof::RetainedProofTransportLimits {
    ay_proof::RetainedProofTransportLimits {
        max_json_bytes: 64 << 20,
        max_storage_bytes: 64 << 20,
        max_work: 64 << 20,
    }
}

#[test]
fn native_query_diagnostic_pairs_issued_input_with_the_actual_attempt() {
    let mut solver = contradiction();
    let end = Instant::now() + Duration::from_secs(2);
    let mut budget = input_budget();
    let result = solver
        .check_sat_with_native_query_diagnostic(end, &mut budget, &mut |_, _| true)
        .unwrap();
    assert!(result.solve().result.is_unsat());
    let evidence = result.proof().expect("complete native contradiction");
    let issued: serde_json::Value =
        serde_json::from_str(evidence.issued_input_json().unwrap()).unwrap();
    assert_eq!(issued["assertions"].as_array().unwrap().len(), 2);
    assert_eq!(evidence.original_assertion_count(), 2);
    assert!(budget.usage().output_bytes > 0);
    let document = evidence
        .encode_diagnostic_document_with_resource_control(
            &solver,
            document_limits(),
            end,
            &mut |_, _| true,
        )
        .unwrap()
        .unwrap();
    let checked = evidence
        .recheck_diagnostic_document_against_live_query_with_resource_control(
            &solver,
            document.issued_input_json(),
            document.retained_proof_bytes(),
            document_limits(),
            end,
            &mut |_, _| true,
        )
        .unwrap()
        .unwrap();
    assert!(checked.quality.is_complete());
    let mut wrong_input = document.issued_input_json().to_owned();
    wrong_input.push(' ');
    assert!(
        evidence
            .recheck_diagnostic_document_against_live_query_with_resource_control(
                &solver,
                &wrong_input,
                document.retained_proof_bytes(),
                document_limits(),
                end,
                &mut |_, _| true,
            )
            .unwrap()
            .is_none(),
        "equivalent unowned source bytes do not acquire this issued-input owner"
    );
    assert!(evidence
        .recheck_against_live_query_with_resource_control(&solver, end, &mut |_, _| true)
        .unwrap()
        .unwrap()
        .quality
        .is_complete());
    let _ = solver.check_sat_with_details();
    assert!(evidence
        .recheck_against_live_query_with_resource_control(&solver, end, &mut |_, _| true)
        .unwrap()
        .is_none());
    assert!(
        evidence
            .recheck_diagnostic_document_against_live_query_with_resource_control(
                &solver,
                document.issued_input_json(),
                document.retained_proof_bytes(),
                document_limits(),
                end,
                &mut |_, _| true,
            )
            .unwrap()
            .is_none(),
        "transported evidence cannot refresh an old attempt"
    );
}

#[test]
fn native_query_diagnostic_input_budget_refusal_is_sticky_and_cannot_publish_evidence() {
    let mut solver = contradiction();
    let mut zero = NativeReplayExportBudget::new(NativeReplayExportLimits::new(0, 0, 0, 0));
    let result = solver.check_sat_with_native_query_diagnostic(
        Instant::now() + Duration::from_secs(2),
        &mut zero,
        &mut |_, _| true,
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    let first_refusal = zero.refusal();
    assert!(first_refusal.is_some());
    let result = solver.check_sat_with_native_query_diagnostic(
        Instant::now() + Duration::from_secs(2),
        &mut zero,
        &mut |_, _| true,
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(zero.refusal(), first_refusal);
}

#[test]
fn native_query_live_recheck_refuses_internally_valid_foreign_source_with_identical_ids() {
    let mut solver = contradiction();
    let end = Instant::now() + Duration::from_secs(2);
    assert!(solver.check_sat_with_details().result.is_unsat());
    let binding = solver
        .native_query_binding_with_resource_control(&mut |_, _| true)
        .unwrap()
        .unwrap();
    let roots = binding.source.roots().to_vec();
    let mut envelope = solver
        .export_native_query_retained_envelope_with_resource_control(binding, end, &mut |_, _| true)
        .unwrap()
        .unwrap();
    let proof = solver.executor.last_proof().unwrap();
    let mut foreign = ay_proof::SerializableProofBundle::from_proof(proof, solver.terms(), roots);
    let (_, (data, _)) = foreign.term_entries.iter_mut().enumerate()
        .find(|(_, (data, _))| matches!(data, ay_core::TermData::Var(name, _) if name == "native_subject"))
        .expect("actual original free variable");
    let ay_core::TermData::Var(name, _) = data else {
        unreachable!()
    };
    *name = "different_native_subject".into();
    let capture =
        capture_strict_retained_bundle_with_resource_control(foreign, end, &mut |_, _| true)
            .unwrap();
    assert!(
        capture.first_check().quality.is_complete(),
        "foreign p and not-p still form an internally valid proof"
    );
    let (foreign, checked) = capture
        .finish_exact_with_resource_control(&mut |_, _| true)
        .unwrap();
    assert!(checked.quality.is_complete());
    envelope.proof = foreign;
    assert!(
        envelope
            .recheck_against_live_query_with_resource_control(&solver, end, &mut |_, _| true,)
            .unwrap()
            .is_none(),
        "numeric root ids and internal validity cannot replace exact source binding"
    );
}

#[test]
fn native_query_document_reader_refuses_valid_foreign_source_with_identical_ids() {
    let mut solver = contradiction();
    let end = Instant::now() + Duration::from_secs(2);
    let (mut work, mut bytes, mut live) = (64usize << 20, 64usize << 20, true);
    let mut progress = |w, b| {
        live &= w <= work && b <= bytes;
        if live {
            work -= w;
            bytes -= b;
        }
        live
    };
    let outcome = solver
        .check_sat_with_native_query_diagnostic(end, &mut input_budget(), &mut progress)
        .unwrap();
    assert!(outcome.solve().result.is_unsat());
    let envelope = outcome.proof().expect("actual issued native proof");
    let document = envelope
        .encode_diagnostic_document_with_resource_control(
            &solver,
            document_limits(),
            end,
            &mut progress,
        )
        .unwrap()
        .unwrap();
    let positive = envelope
        .recheck_diagnostic_document_against_live_query_with_resource_control(
            &solver,
            document.issued_input_json(),
            document.retained_proof_bytes(),
            document_limits(),
            end,
            &mut progress,
        )
        .unwrap()
        .expect("same-owner document remains accepted");
    assert!(positive.quality.is_complete());
    assert_eq!(positive.quality.trust_count, 0);
    assert_eq!(positive.quality.hole_count, 0);

    let roots = envelope.binding.source.roots().to_vec();
    let mut snapshot = ay_proof::SerializableProofBundle::from_proof(
        solver
            .executor
            .last_proof()
            .expect("actual proof remains available"),
        solver.terms(),
        roots.clone(),
    );
    let (source_index, (data, _)) = snapshot.term_entries.iter_mut().enumerate()
        .find(|(_, (data, _))| matches!(data, ay_core::TermData::Var(name, _) if name == "native_subject"))
        .expect("actual original free variable");
    let original_id = ay_core::TermId(u32::try_from(source_index).unwrap());
    let ay_core::TermData::Var(name, _) = data else {
        unreachable!()
    };
    // Only the source atom changes. Every positional id, sort, assertion and
    // proof reference stays identical, so this still proves foreign p/!p.
    *name = "foreign_document_subject".into();
    assert!(roots.contains(&original_id));
    assert_eq!(snapshot.obligation_assertions, roots);
    let capture =
        capture_strict_retained_bundle_with_resource_control(snapshot, end, &mut progress).unwrap();
    assert!(capture.first_check().quality.is_complete());
    let (foreign, second) = capture
        .finish_exact_with_resource_control(&mut progress)
        .unwrap();
    assert!(second.quality.is_complete());
    let foreign_bytes = foreign
        .encode_with_resource_control(document_limits(), end, &mut progress)
        .unwrap();

    // Exercise the real untrusted-byte decoder and TWO independent no-search
    // checks before asking the source owner to bind this foreign document.
    let (decoded, first) = ay_proof::read_retained_proof_bundle_with_resource_control(
        &foreign_bytes,
        document_limits(),
        end,
        &mut progress,
    )
    .unwrap();
    let second = decoded
        .replay_exact_with_resource_control(end, &mut progress)
        .unwrap();
    for checked in [&first, &second] {
        assert!(checked.quality.is_complete());
        assert_eq!(checked.quality.trust_count, 0);
        assert_eq!(checked.quality.hole_count, 0);
        assert_eq!(checked.assume_terms.len(), positive.assume_terms.len());
        assert!(checked
            .assume_terms
            .iter()
            .all(|id| positive.assume_terms.contains(id)));
    }
    assert!(
        envelope
            .recheck_diagnostic_document_against_live_query_with_resource_control(
                &solver,
                document.issued_input_json(), // EXACT original bytes, not foreign input.
                &foreign_bytes,
                document_limits(),
                end,
                &mut progress,
            )
            .unwrap()
            .is_none(),
        "valid decoded evidence with the same numeric ids cannot replace the owned source"
    );
    assert!(
        envelope
            .recheck_diagnostic_document_against_live_query_with_resource_control(
                &solver,
                document.issued_input_json(),
                document.retained_proof_bytes(),
                document_limits(),
                end,
                &mut progress,
            )
            .unwrap()
            .is_some(),
        "foreign-source refusal does not alter the valid same-owner evidence"
    );
}

#[test]
fn native_query_envelope_rechecks_exact_issued_source_and_both_retained_phases() {
    let mut solver = contradiction();
    let mut work = 64usize << 20;
    let mut bytes = 64usize << 20;
    let mut admitted = true;
    let mut progress = |w, b| {
        admitted &= work >= w && bytes >= b;
        if admitted {
            work -= w;
            bytes -= b;
        }
        admitted
    };
    assert!(solver
        .native_query_binding_with_resource_control(&mut progress)
        .unwrap()
        .is_none());
    let deadline = Instant::now() + Duration::from_secs(2);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:?}");
    let binding = solver
        .native_query_binding_with_resource_control(&mut progress)
        .unwrap()
        .unwrap();
    assert_eq!(binding.original_assertion_count(), 2);
    let envelope = solver
        .export_native_query_retained_envelope_with_resource_control(
            binding,
            deadline,
            &mut progress,
        )
        .unwrap()
        .unwrap();
    assert_eq!(
        envelope.proof_schema(),
        ay_proof::RETAINED_PROOF_BUNDLE_SCHEMA
    );
    assert_eq!(envelope.original_assertion_count(), 2);
    assert!(
        envelope.issued_input_json().is_none(),
        "post-solve export cannot claim an issued input"
    );
    let checked = envelope
        .recheck_against_live_query_with_resource_control(&solver, deadline, &mut progress)
        .unwrap()
        .unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(checked.quality.trust_count, 0);
    assert_eq!(checked.quality.hole_count, 0);
    assert_eq!(checked.assume_terms.len(), 2);
    let sibling = contradiction();
    assert!(envelope
        .recheck_against_live_query_with_resource_control(&sibling, deadline, &mut progress)
        .unwrap()
        .is_none());
    solver.check_sat_with_details();
    assert!(
        envelope
            .recheck_against_live_query_with_resource_control(&solver, deadline, &mut progress)
            .unwrap()
            .is_none(),
        "a later byte-identical solve is a different attempt"
    );
}

#[test]
fn native_query_binding_and_export_preserve_sticky_resource_refusal() {
    let mut solver = contradiction();
    assert!(solver.check_sat_with_details().result.is_unsat());
    let mut calls = 0;
    assert!(matches!(
        solver.native_query_binding_with_resource_control(&mut |_, _| {
            calls += 1;
            false
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 1);
    let binding = solver
        .native_query_binding_with_resource_control(&mut |_, _| true)
        .unwrap()
        .unwrap();
    let mut calls = 0;
    assert!(matches!(
        solver.export_native_query_retained_envelope_with_resource_control(
            binding,
            Instant::now() + Duration::from_secs(2),
            &mut |_, _| {
                calls += 1;
                false
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(
        calls, 1,
        "the shared retained owner never re-enters a refusing callback"
    );
}

#[test]
fn native_query_diagnostic_retains_typed_seq_refutation_without_public_credit() {
    use crate::api::{DatatypeConstructor, DatatypeField, DatatypeSort, UnknownReason};
    let mut solver = Solver::new(Logic::All);
    solver.set_timeout(Some(Duration::from_secs(2)));
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    let declaration = DatatypeSort::new(
        "DiagnosticOwned",
        vec![DatatypeConstructor::new(
            "diagnostic_owned",
            vec![DatatypeField::new(
                "diagnostic_children",
                Sort::seq(Sort::Uninterpreted("DiagnosticOwned".into())),
            )],
        )],
    );
    solver.try_declare_datatype(&declaration).unwrap();
    let r = solver.declare_const("diagnostic_cycle", Sort::Datatype(declaration.clone()));
    let children = solver.try_seq_unit(r).unwrap();
    let parent = solver
        .try_datatype_constructor(&declaration, "diagnostic_owned", &[children])
        .unwrap();
    let root = solver.try_eq(r, parent).unwrap();
    solver.try_assert_term(root).unwrap();
    let mut work = 64usize << 20;
    let mut bytes = 64usize << 20;
    let mut live = true;
    let mut progress = |w, b| {
        live &= w <= work && b <= bytes;
        if live {
            work -= w;
            bytes -= b;
        }
        live
    };
    let deadline = Instant::now() + Duration::from_secs(2);
    let mut input_budget = NativeReplayExportBudget::new(NativeReplayExportLimits::new(
        64 << 20,
        64 << 20,
        64 << 20,
        128,
    ));
    let outcome = solver
        .check_sat_with_native_query_diagnostic(deadline, &mut input_budget, &mut progress)
        .unwrap();
    assert!(
        outcome.solve.result.is_unknown(),
        "native evidence does not promote unsupported Seq presentation"
    );
    assert_eq!(
        outcome.solve.unknown_reason,
        Some(UnknownReason::ProofTrusted)
    );
    assert!(
        solver.export_last_unsat_bundle().is_none(),
        "the revoked public artifact stays revoked"
    );
    let evidence = outcome.proof.expect(
        "actual producer's typed native proof must be independently retained before revocation",
    );
    let issued = evidence
        .issued_input_json()
        .expect("input captured at the actual check entry");
    let input: serde_json::Value = serde_json::from_str(issued).unwrap();
    assert_eq!(input["assertions"].as_array().unwrap().len(), 1);
    let checked = evidence
        .recheck_against_live_query_with_resource_control(&solver, deadline, &mut progress)
        .unwrap()
        .unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(checked.quality.trust_count, 0);
    assert_eq!(checked.quality.hole_count, 0);
    assert_eq!(evidence.original_assertion_count(), 1);
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::ProofTrusted));
    solver.try_reset_assertions().unwrap();
    assert!(
        evidence
            .recheck_against_live_query_with_resource_control(&solver, deadline, &mut progress)
            .unwrap()
            .is_none(),
        "old evidence cannot acquire a new assertion scope"
    );
}
