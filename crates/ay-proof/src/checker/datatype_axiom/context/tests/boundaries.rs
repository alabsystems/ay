// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn sequence(depth: usize) -> Sort {
    let mut sort = Sort::Int;
    for _ in 0..depth {
        sort = Sort::Seq(Box::new(sort));
    }
    sort
}

#[test]
fn sort_depth_boundary_applies_before_recursive_equality() {
    let mut progress = |_, _| true;
    let mut meter = ContextMeter::new(&mut progress);
    let allowed = sequence(256);
    assert!(meter.equal_sorts(&allowed, &allowed).unwrap());
    let deep = sequence(257);
    assert!(matches!(
        meter.equal_sorts(&deep, &Sort::Int),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(matches!(
        meter.sort(&Sort::Int, usize::MAX),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn overdeep_declared_and_unused_signature_sorts_are_refused() {
    for position in 0..3 {
        let mut fixture = fixture();
        match position {
            0 => fixture.signatures[0].argument_sorts[0] = sequence(257),
            1 => fixture.signatures[2].result_sort = sequence(257),
            _ => fixture.signatures.push(DatatypeMemberSignature {
                identity: "unused-deep".into(),
                argument_sorts: vec![],
                result_sort: sequence(257),
                nullary_term: None,
            }),
        }
        assert!(matches!(
            check(&fixture, &mut |_, _| true),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
}

#[test]
fn overdeep_raw_argument_sort_is_refused_before_equality_or_diagnostic_display() {
    let mut fixture = fixture();
    let mut entries = fixture.terms.entries_snapshot();
    let argument = TermId::new(u32::try_from(entries.len()).unwrap());
    entries.push((TermData::Var("deep-argument".into(), 77), sequence(257)));
    entries.push((
        TermData::App(Symbol::named("meter-mk"), vec![argument]),
        Sort::Uninterpreted("MeterBox".into()),
    ));
    let (true_term, false_term) = fixture.terms.boolean_constant_ids();
    fixture.terms = TermStore::from_entries(entries, true_term, false_term, 0);
    assert!(matches!(
        check(&fixture, &mut |_, _| true),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn diagnostics_and_first_registry_allocation_are_refusable() {
    let mut fixture = fixture();
    assert!(matches!(
        check(&fixture, &mut |_, b| b == 0),
        Err(ProofCheckError::ResourceLimit)
    ));
    fixture.signatures[0].identity = "duplicate-diagnostic".repeat(256);
    fixture.signatures.push(fixture.signatures[0].clone());
    let (mut polls, mut last_bytes) = (0, 0);
    assert_invalid(check(&fixture, &mut |_, b| {
        polls += 1;
        last_bytes = b;
        true
    }));
    assert!(last_bytes >= fixture.signatures[0].identity.len());
    let mut calls = 0;
    let result = check(&fixture, &mut |_, _| {
        calls += 1;
        calls != polls
    });
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls, polls);
}

#[test]
fn unused_nonmember_names_are_still_charged_during_the_global_scan() {
    let mut fixture = fixture();
    let (baseline_work, _, _) = usage(&fixture);
    fixture
        .terms
        .mk_var("unused-global-name".repeat(4096), Sort::Int);
    let (large_work, _, _) = usage(&fixture);
    assert!(large_work >= baseline_work + 4096 * "unused-global-name".len());
    let mut spent = 0;
    let result = check(&fixture, &mut |work, _| {
        spent += work;
        spent <= baseline_work
    });
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn a_thousand_member_context_fits_a_reasonable_shared_allocation_envelope() {
    let mut fixture = fixture();
    fixture.terms = TermStore::new();
    fixture.selectors[0].1 = (0..1000).map(|index| format!("field-{index:04}")).collect();
    fixture.signatures.truncate(2);
    fixture.signatures[0].argument_sorts = vec![Sort::Int; 1000];
    for identity in &fixture.selectors[0].1 {
        fixture.signatures.push(DatatypeMemberSignature {
            identity: identity.clone(),
            argument_sorts: vec![Sort::Uninterpreted("MeterBox".into())],
            result_sort: Sort::Int,
            nullary_term: None,
        });
    }
    let (mut work, mut bytes) = (0, 0);
    check(&fixture, &mut |w, b| {
        work += w;
        bytes += b;
        work <= 64 * 1024 * 1024 && bytes <= 64 * 1024 * 1024
    })
    .unwrap();
    assert!(bytes > 1000 * std::mem::size_of::<String>());
}

#[test]
fn checked_tree_accounting_overflow_refuses_before_callback() {
    let mut calls = 0;
    let mut progress = |_, _| {
        calls += 1;
        true
    };
    let mut meter = ContextMeter::new(&mut progress);
    assert!(matches!(
        meter.lookup("x", usize::MAX),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(matches!(
        meter.iterate(usize::MAX),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 0);
}

#[test]
fn strict_quality_checks_the_same_unused_typed_context_with_progress() {
    let mut fixture = fixture();
    let (context_work, context_bytes, _) = usage(&fixture);
    let mut proof = ay_core::Proof::new();
    let positive = fixture.terms.mk_var("context-proof-p", Sort::Bool);
    let negative = fixture.terms.mk_not(positive);
    let left = proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_resolution(vec![], positive, left, right);
    let (mut work, mut bytes) = (0, 0);
    let quality = crate::check_proof_strict_with_typed_context_and_progress(
        &proof,
        &fixture.terms,
        Some(&fixture.declarations),
        Some(&fixture.selectors),
        &fixture.signatures,
        Some(&[positive, negative]),
        &mut |w, b| {
            work += w;
            bytes += b;
            true
        },
    )
    .unwrap();
    assert_eq!(quality.resolution_count, 1);
    assert!(work >= context_work && bytes >= context_bytes);
}

#[test]
fn an_empty_signature_context_does_not_scan_the_term_store() {
    // No member signature can match any node, so the global occurrence walk
    // is vacuous: its cost must not grow with unrelated terms (an incremental
    // session's term store grows with every check-sat).
    let empty = |terms: &TermStore| {
        let mut work = 0;
        validate_datatype_signature_context_with_progress(terms, None, None, &[], &mut |w, _| {
            work += w;
            true
        })
        .expect("an empty datatype context is valid");
        work
    };
    let mut terms = TermStore::new();
    let baseline = empty(&terms);
    for index in 0..10_000 {
        terms.mk_var(format!("unrelated-{index}"), Sort::Int);
    }
    assert_eq!(empty(&terms), baseline);

    // With a registered member the walk (and its metering) still covers every
    // node, including the ones unrelated to the member.
    let mut fixture = fixture();
    let (with_members, _, _) = usage(&fixture);
    for index in 0..1_000 {
        fixture
            .terms
            .mk_var(format!("unrelated-{index}"), Sort::Int);
    }
    let (grown, _, _) = usage(&fixture);
    assert!(grown >= with_members + 1_000);
}
