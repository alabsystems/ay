// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn rejects_wrong_indices_and_source_polarity() {
    let (terms, clause, mut cert) = quartic();
    cert.terms[0].origin = NraSosOrigin::ClauseLiteral { position: 1 };
    assert!(validate(&terms, &clause, &cert).is_err());
    cert.terms[0].origin = NraSosOrigin::ClauseLiteral { position: 0 };
    let ay_core::TermData::Not(atom) = terms.get(clause[0]) else {
        panic!("fixture")
    };
    assert!(validate(&terms, &[*atom], &cert).is_err());
}

#[test]
fn rejects_changed_source_and_unbound_basis() {
    let (mut terms, clause, mut cert) = quartic();
    let outsider = terms.mk_var("outsider", Sort::Real);
    cert.basis[1] = vec![outsider, outsider];
    assert!(validate(&terms, &clause, &cert).is_err());
    let zero = real(&mut terms, 0);
    let assertion = terms.mk_lt(outsider, zero);
    let changed = terms.mk_not_raw(assertion);
    assert!(validate(&terms, &[changed], &cert).is_err());
}

#[test]
fn rejects_non_psd_asymmetric_and_malformed_gram() {
    let (terms, clause, cert) = quartic();
    let mut changed = cert.clone();
    changed.gram[1][1] = rat(-1);
    assert!(validate(&terms, &clause, &changed).is_err());
    let mut changed = cert.clone();
    changed.gram[1][2] = rat(0);
    assert!(validate(&terms, &clause, &changed).is_err());
    let mut changed = cert.clone();
    changed.gram[0][1] = rat(1);
    changed.gram[1][0] = rat(1);
    assert!(validate(&terms, &clause, &changed).is_err());
    let mut changed = cert;
    changed.gram[0].pop();
    assert!(validate(&terms, &clause, &changed).is_err());
}

#[test]
fn rejects_bad_multiplier_rhs_and_noncanonical_rationals() {
    let (terms, clause, cert) = quartic();
    for bad in [
        rat(-1),
        NraSosRational {
            numerator: 2.into(),
            denominator: 2.into(),
        },
        NraSosRational {
            numerator: 1.into(),
            denominator: 0.into(),
        },
        NraSosRational {
            numerator: (-1).into(),
            denominator: (-1).into(),
        },
    ] {
        let mut changed = cert.clone();
        changed.terms[0].multiplier = bad;
        assert!(validate(&terms, &clause, &changed).is_err());
    }
    for rhs in [1, -1] {
        let mut changed = cert.clone();
        changed.rhs = rat(rhs);
        assert!(validate(&terms, &clause, &changed).is_err());
    }
}

#[test]
fn rejects_duplicate_unsorted_and_overdegree_basis() {
    let (terms, clause, cert) = quartic();
    let mut changed = cert.clone();
    changed.basis[2] = changed.basis[1].clone();
    assert!(validate(&terms, &clause, &changed).is_err());
    let mut changed = cert.clone();
    changed.basis[1] = vec![cert.basis[2][0], cert.basis[1][0]];
    assert!(validate(&terms, &clause, &changed).is_err());
    let mut changed = cert;
    let repeated = changed.basis[1][0];
    changed.basis[1].push(repeated);
    assert!(validate(&terms, &clause, &changed).is_err());
}

#[test]
fn rejects_boolean_packing_and_disequality_factor() {
    let (mut terms, clause, cert) = linear();
    let packed = terms.mk_or(clause.clone());
    assert!(validate(&terms, &[packed], &cert).is_err());
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let equality = terms.mk_eq(x, zero);
    assert!(validate(&terms, &[equality, clause[1]], &cert).is_err());
}

#[test]
fn rejects_oversized_payload_as_resource_limit() {
    let (terms, clause, mut cert) = quartic();
    cert.rhs.numerator = num_bigint::BigInt::one() << 1_024usize;
    assert_eq!(
        validate(&terms, &clause, &cert),
        Err(ProofCheckError::ResourceLimit)
    );
    let (terms, clause, mut cert) = quartic();
    cert.terms = vec![term(0, 1); NraSosCertificate::MAX_TERMS + 1];
    assert_eq!(
        validate(&terms, &clause, &cert),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn cancellation_dominates_at_entry_mid_replay_and_final_poll() {
    let (terms, clause, cert) = quartic();
    let mut calls = 0usize;
    validate_nra_sos_with_progress(&terms, ProofId(0), &clause, &cert, &mut |_, _| {
        calls += 1;
        true
    })
    .unwrap();
    assert!(calls > 10);
    for allowed in [0, 2, calls / 2, calls - 1] {
        let mut seen = 0;
        let result =
            validate_nra_sos_with_progress(&terms, ProofId(0), &clause, &cert, &mut |_, _| {
                seen += 1;
                seen <= allowed
            });
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    }
}

#[test]
fn gram_replay_polls_and_accounts_scratch() {
    let (_, _, cert) = quartic();
    let mut bytes = 0;
    let mut callback = |_: usize, allocated: usize| {
        bytes += allocated;
        bytes < 100
    };
    let mut meter = WorkMeter::with_progress(&mut callback);
    assert_eq!(
        gram::decode_and_check(&cert.gram, &mut meter),
        Err(WORK_METER_RESOURCE_LIMIT.to_string())
    );
}

#[test]
fn source_variables_are_not_merged_by_opaque_function_name() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let fx = terms.mk_app(Symbol::Named("f".into()), [x], Sort::Real);
    let fy = terms.mk_app(Symbol::Named("f".into()), [y], Sort::Real);
    let one = real(&mut terms, 1);
    let zero = real(&mut terms, 0);
    let lower = terms.mk_ge(fx, one);
    let upper = terms.mk_le(fy, zero);
    let clause = [terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
    let cert = certificate(vec![vec![]], &[&[0]], vec![term(0, 1), term(1, 1)], -1);
    assert!(validate(&terms, &clause, &cert).is_err());
}

#[test]
fn source_degree_and_variable_caps_are_enforced() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let sixth_power = terms.mk_mul(vec![x; 6]);
    let assertion = terms.mk_lt(sixth_power, zero);
    let clause = [terms.mk_not_raw(assertion)];
    let cert = certificate(vec![vec![]], &[&[0]], vec![term(0, 1)], 0);
    assert_eq!(
        validate(&terms, &clause, &cert),
        Err(ProofCheckError::ResourceLimit)
    );
    let mut clause = Vec::new();
    for index in 0..9 {
        let variable = terms.mk_var(format!("v{index}"), Sort::Real);
        let assertion = terms.mk_ge(variable, zero);
        clause.push(terms.mk_not_raw(assertion));
    }
    assert_eq!(
        validate(&terms, &clause, &cert),
        Err(ProofCheckError::ResourceLimit)
    );
}
