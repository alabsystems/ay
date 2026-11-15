// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{NraSosOrigin, NraSosTerm};
use num_bigint::BigInt;

use super::*;

fn classification(result: Result<(), ProofCheckError>) -> u8 {
    match result {
        Ok(()) => 0,
        Err(ProofCheckError::MalformedProofBundle { .. }) => 1,
        Err(ProofCheckError::ResourceLimit) => 2,
        Err(error) => panic!("unexpected error: {error}"),
    }
}

fn compare_oracle(clause: &[TermId], certificate: NraSosCertificate, expected: u8) {
    let entries = entries();
    let legacy = crate::bundle::nra_sos::validate(&entries, 0, clause, &certificate);
    let steps = [ProofStep::NraSos {
        clause: clause.to_vec(),
        certificate,
    }];
    let metered = validate_proof_snapshot_with_progress(&steps, &entries, &mut |_, _| true);
    assert_eq!(classification(legacy), expected);
    assert_eq!(classification(metered), expected);
}

#[test]
fn metered_sos_matches_legacy_dimensions_and_numeric_shape_policy() {
    compare_oracle(&[TermId(0)], certificate(), 0);
    let mut cases = Vec::new();
    let mut empty = certificate();
    empty.basis.clear();
    cases.push((empty, 1));
    let mut missing_constant = certificate();
    missing_constant.basis[0] = vec![TermId(2)];
    cases.push((missing_constant, 1));
    let mut oversized = certificate();
    oversized.basis = vec![vec![]; 46];
    cases.push((oversized, 2));
    let mut degree = certificate();
    degree.basis[1] = vec![TermId(2); 3];
    cases.push((degree, 2));
    let mut duplicate = certificate();
    duplicate.basis[1].clear();
    cases.push((duplicate, 1));
    let mut descending = certificate();
    descending.basis[1] = vec![TermId(2), TermId(1)];
    cases.push((descending, 1));
    let mut missing_row = certificate();
    missing_row.gram.pop();
    cases.push((missing_row, 1));
    let mut oversized_row = certificate();
    oversized_row.gram[0] = vec![rational(0); 46];
    cases.push((oversized_row, 2));
    let mut short_row = certificate();
    short_row.gram[0].pop();
    cases.push((short_row, 1));
    for denominator in [0, -1] {
        let mut malformed = certificate();
        malformed.rhs.denominator = denominator.into();
        cases.push((malformed, 1));
    }
    let mut big = certificate();
    big.gram[0][0].numerator = BigInt::from(1) << 1024usize;
    cases.push((big, 2));
    let mut many_terms = certificate();
    many_terms.terms = vec![
        NraSosTerm {
            origin: NraSosOrigin::ClauseLiteral { position: 0 },
            multiplier: rational(0)
        };
        401
    ];
    cases.push((many_terms, 2));
    for (certificate, expected) in cases {
        compare_oracle(&[TermId(0)], certificate, expected);
    }
}

#[test]
fn metered_sos_preserves_raw_fraction_and_basis_order_compatibility() {
    let mut cert = certificate();
    cert.rhs.numerator = BigInt::from(1) << 1023usize;
    cert.rhs.denominator = BigInt::from(2);
    compare_oracle(&[TermId(0)], cert.clone(), 0);
    // Nonreduced fractions and nonlexicographic basis order are structural
    // inputs; canonical rational/semantic identity checks happen in replay.
    cert.basis = vec![vec![], vec![TermId(2), TermId(2)], vec![TermId(2)]];
    cert.gram = vec![vec![rational(0); 3]; 3];
    compare_oracle(&[TermId(0)], cert, 0);
}

#[test]
fn sos_embedded_roots_and_actual_clause_positions_are_checked_exactly() {
    compare_oracle(&[TermId(2)], certificate(), 1);
    compare_oracle(&[TermId(u32::MAX)], certificate(), 1);
    for variable in [TermId(0), TermId(u32::MAX)] {
        let mut cert = certificate();
        cert.basis[1] = vec![variable];
        compare_oracle(&[TermId(0)], cert, 1);
    }
    for origin in [
        NraSosOrigin::ClauseLiteral { position: 1 },
        NraSosOrigin::Product { left: 0, right: 1 },
    ] {
        let mut cert = certificate();
        cert.terms.push(NraSosTerm {
            origin,
            multiplier: rational(1),
        });
        compare_oracle(&[TermId(0)], cert.clone(), 1);
        // Duplicate literal identities are still TWO ordered source slots.
        compare_oracle(&[TermId(0), TermId(0)], cert, 0);
    }
    for position in [1024, u32::MAX] {
        let mut cert = certificate();
        cert.terms.push(NraSosTerm {
            origin: NraSosOrigin::ClauseLiteral { position },
            multiplier: rational(1),
        });
        compare_oracle(&[TermId(0)], cert, 2);
    }
    compare_oracle(&vec![TermId(0); 1024], certificate(), 0);
    compare_oracle(&vec![TermId(0); 1025], certificate(), 2);
}

#[test]
fn sos_shape_scans_and_oracle_error_paths_obey_cancellation() {
    let mut cert = certificate();
    cert.terms = vec![
        NraSosTerm {
            origin: NraSosOrigin::ClauseLiteral { position: 0 },
            multiplier: rational(1)
        };
        400
    ];
    let steps = [ProofStep::NraSos {
        clause: vec![TermId(0)],
        certificate: cert,
    }];
    let entries = entries();
    let (calls, _, bytes) = measurements(&steps, &entries);
    assert!(calls > 800);
    assert_eq!(bytes, 0, "borrowed SOS inspection allocates nothing");
    for reject_at in [5, 15, calls / 2, calls] {
        let mut calls = 0;
        let result = validate_proof_snapshot_with_progress(&steps, &entries, &mut |_, _| {
            calls += 1;
            calls != reject_at
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, reject_at);
    }
}
