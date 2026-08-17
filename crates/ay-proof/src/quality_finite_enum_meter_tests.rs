// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource-meter regressions for the bounded finite-enum proof lane.

use super::*;
use ay_core::FarkasAnnotation;

const B83_MEMBERS: usize = 146;
const B83_CHECK_WORK: usize = 250_000_000;
const B83_CHECK_BYTES: usize = 512 * 1024 * 1024;

struct FiniteEnumFixture {
    terms: TermStore,
    proof: Proof,
    assumptions: Vec<TermId>,
    datatype_decls: Vec<(String, Vec<String>)>,
    selector_decls: Vec<(String, Vec<String>)>,
    member_signatures: Vec<DatatypeMemberSignature>,
}

fn finite_enum_fixture(member_count: usize) -> FiniteEnumFixture {
    let sort_name = format!("MeteredEnum{member_count}");
    let enum_sort = Sort::Uninterpreted(sort_name.clone());
    let mut terms = TermStore::new();
    let members: Vec<TermId> = (0..member_count)
        .map(|index| terms.mk_var(format!("metered_enum_member_{index}"), enum_sort.clone()))
        .collect();
    let mut equalities = Vec::new();
    let mut assumptions = Vec::new();
    for left in 0..member_count {
        for right in left + 1..member_count {
            let equality = terms.mk_app(
                Symbol::named("="),
                [members[left], members[right]],
                Sort::Bool,
            );
            equalities.push(equality);
            assumptions.push(terms.mk_not_raw(equality));
        }
    }

    let constructors: Vec<String> = (0..member_count - 1)
        .map(|index| format!("MeteredCtor{index}"))
        .collect();
    let constructor_terms: Vec<TermId> = constructors
        .iter()
        .map(|constructor| terms.mk_var(constructor.clone(), enum_sort.clone()))
        .collect();
    let member_signatures: Vec<DatatypeMemberSignature> = constructors
        .iter()
        .zip(constructor_terms)
        .flat_map(|(constructor, constructor_term)| {
            [
                DatatypeMemberSignature {
                    identity: constructor.clone(),
                    argument_sorts: Vec::new(),
                    result_sort: enum_sort.clone(),
                    nullary_term: Some(constructor_term),
                },
                DatatypeMemberSignature {
                    identity: format!("is-{constructor}"),
                    argument_sorts: vec![enum_sort.clone()],
                    result_sort: Sort::Bool,
                    nullary_term: None,
                },
            ]
        })
        .collect();
    let selector_decls = constructors
        .iter()
        .cloned()
        .map(|constructor| (constructor, Vec::new()))
        .collect();
    let datatype_decls = vec![(sort_name, constructors)];

    let mut proof = Proof::new();
    let lemma =
        proof.add_theory_lemma_with_kind("DT", equalities, TheoryLemmaKind::DatatypeEnumPigeonhole);
    let mut premises = Vec::with_capacity(assumptions.len() + 1);
    premises.push(lemma);
    for &assumption in &assumptions {
        premises.push(proof.add_assume(assumption, None));
    }
    proof.add_rule_step(AletheRule::Resolution, Vec::new(), premises, Vec::new());

    FiniteEnumFixture {
        terms,
        proof,
        assumptions,
        datatype_decls,
        selector_decls,
        member_signatures,
    }
}

#[test]
fn argument_free_unit_tail_gets_linear_charge_but_annotated_tail_does_not() {
    let mut terms = TermStore::new();
    let atoms: Vec<TermId> = (0..128)
        .map(|index| terms.mk_var(format!("metered_unit_tail_{index}"), Sort::Bool))
        .collect();
    let mut derived = Vec::with_capacity(atoms.len() + 1);
    derived.push(Some(atoms.clone()));
    for &atom in &atoms {
        derived.push(Some(vec![terms.mk_not_raw(atom)]));
    }
    let premises: Vec<ProofId> = (0..derived.len())
        .map(|index| ProofId(index as u32))
        .collect();
    let plain = ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: premises.clone(),
        args: Vec::new(),
    };
    let yes = terms.mk_bool(true);
    let annotated_args: Vec<TermId> = atoms.iter().flat_map(|&atom| [atom, yes]).collect();
    let annotated = ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises,
        args: annotated_args,
    };
    let payload = PayloadStats {
        work: 1024,
        bytes: 4096,
        unfolded_work: 8192,
        order_assignments: 0,
    };

    assert!(is_argument_free_unit_tail_resolution(&plain, &derived));
    assert!(!is_argument_free_unit_tail_resolution(&annotated, &derived));
    let plain_charge = strict_step_charge(&terms, &plain, &derived, atoms.len() * 2, payload)
        .expect("linear unit-tail charge fits usize");
    let annotated_charge =
        strict_step_charge(&terms, &annotated, &derived, atoms.len() * 2, payload)
            .expect("conservative annotated charge fits usize");

    assert!(plain_charge.0 >= payload.unfolded_work);
    assert!(
        plain_charge.1 >= atoms.len() * (size_of::<(TermId, bool)>() + 32),
        "the live accumulator hash-set scratch must be charged"
    );
    assert!(annotated_charge.0 > plain_charge.0 * 100);
}

#[test]
fn datatype_enum_charge_covers_registry_scans_and_hash_scratch() {
    let payload = PayloadStats {
        work: 101,
        bytes: 2048,
        unfolded_work: 73,
        order_assignments: 0,
    };
    let datatype_registry = RegistryPayloadStats {
        work: 37,
        bytes: 512,
    };
    let selector_registry = RegistryPayloadStats {
        work: 19,
        bytes: 256,
    };
    let step = ProofStep::TheoryLemma {
        theory: "DT".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::DatatypeEnumPigeonhole,
        lia: None,
    };

    let registry = datatype_registry_charge(&step, payload, datatype_registry, selector_registry)
        .expect("small enum registry charge fits usize");
    let semantic =
        semantic_validator_charge(&step, payload, SemanticChargeClass::DatatypeEnumPigeonhole)
            .expect("small enum semantic charge fits usize");

    assert_eq!(registry.0, 37 + 19 * datatype_registry.work);
    assert!(registry.1 >= payload.unfolded_work * 64);
    assert_eq!(semantic.0, payload.work * 8);
    assert_eq!(semantic.1, payload.bytes);
}

#[test]
fn b83_scale_finite_enum_progress_fits_and_enforces_the_bounded_envelope() {
    let fixture = finite_enum_fixture(B83_MEMBERS);
    assert_eq!(fixture.assumptions.len(), 10_585);
    let (mut work, mut bytes) = (0usize, 0usize);
    let quality = check_proof_strict_with_typed_context_and_progress(
        &fixture.proof,
        &fixture.terms,
        Some(&fixture.datatype_decls),
        Some(&fixture.selector_decls),
        &fixture.member_signatures,
        Some(&fixture.assumptions),
        &mut |work_delta, byte_delta| {
            let Some(next_work) = work.checked_add(work_delta) else {
                return false;
            };
            let Some(next_bytes) = bytes.checked_add(byte_delta) else {
                return false;
            };
            if next_work > B83_CHECK_WORK || next_bytes > B83_CHECK_BYTES {
                return false;
            }
            work = next_work;
            bytes = next_bytes;
            true
        },
    )
    .expect("the bounded direct-clique proof must fit its published envelope");
    assert!(quality.is_complete());
    assert!(work > fixture.assumptions.len());
    assert!(bytes > fixture.assumptions.len() * size_of::<TermId>());

    let cutoff = work - 1;
    let mut replay_work = 0usize;
    let error = check_proof_strict_with_typed_context_and_progress(
        &fixture.proof,
        &fixture.terms,
        Some(&fixture.datatype_decls),
        Some(&fixture.selector_decls),
        &fixture.member_signatures,
        Some(&fixture.assumptions),
        &mut |work_delta, _| {
            let Some(next) = replay_work.checked_add(work_delta) else {
                return false;
            };
            if next > cutoff {
                return false;
            }
            replay_work = next;
            true
        },
    )
    .expect_err("one less work unit than the reported total must fail closed");
    assert_eq!(error, ProofCheckError::ResourceLimit);
}

#[test]
fn farkas_without_a_progress_meter_keeps_the_static_polynomial_byte_charge() {
    // A Farkas route that cannot prove it uses the dynamic progress meter must
    // retain the conservative static scratch bound. Only
    // `SemanticChargeClass::ProgressFarkas` may remove this byte precharge.
    let step = ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: Vec::new(),
        farkas: Some(FarkasAnnotation::from_ints(&[])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    };
    let payload = PayloadStats {
        work: 1_321,
        bytes: 24_786,
        unfolded_work: 100,
        order_assignments: 0,
    };
    let (work, bytes) = semantic_validator_charge(&step, payload, SemanticChargeClass::General)
        .expect("measured Farkas charge fits usize");

    assert_eq!(work, 1_321 * 100 * 100);
    // The static byte reservation is the LINEAR full-validator bound (see
    // FARKAS_FULL_VALIDATOR_BYTE_FACTOR), capped by the legacy quadratic
    // product: min(24_786 * 128, 24_786 * 100^2). It remains a-priori and
    // strictly positive — only ProgressFarkas may remove the byte precharge.
    assert_eq!(bytes, 24_786 * 128);
    assert!(bytes > 0, "the static reservation must remain");
}
