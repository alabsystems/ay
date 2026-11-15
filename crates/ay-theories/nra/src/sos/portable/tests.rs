// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Private producer conversion tests. These do not confer independent proof
//! authority; the public ay-proof checker must still authenticate every DTO.

use super::*;
use ay_core::{Constant, Sort, Symbol, TermData};

mod source_boundaries;

fn real(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(value.into()))
}

fn literal(terms: &mut TermStore, relation: &str, left: TermId, right: TermId) -> TermId {
    let atom = terms.mk_app(Symbol::named(relation), [left, right], Sort::Bool);
    terms.mk_not_raw(atom)
}

fn linear() -> (TermStore, Vec<TermId>, SosCertificate) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let two = real(&mut terms, 2);
    let twice_x = terms.mk_mul(vec![two, x]);
    let clause = vec![
        literal(&mut terms, ">=", twice_x, two),
        literal(&mut terms, "<=", x, zero),
    ];
    let candidate = SosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![BigRational::zero()]],
        terms: vec![
            CertTerm {
                origin: CertOrigin::Constraint(0),
                multiplier: BigRational::one(),
            },
            CertTerm {
                origin: CertOrigin::Constraint(1),
                multiplier: BigRational::from_integer(2.into()),
            },
        ],
        rhs: BigRational::from_integer((-2).into()),
    };
    (terms, clause, candidate)
}

fn source<'a>(terms: &'a TermStore, clause: &[TermId]) -> SosClauseSource<'a> {
    SosClauseSource::from_clause(terms, clause, &mut SosPolynomialBudget::default())
        .expect("admitted exact arithmetic clause")
}

fn convert(source: &SosClauseSource<'_>, candidate: &SosCertificate) -> Option<ProofStep> {
    source.convert_candidate(candidate, &mut SosProgress::new(&mut |_, _| true))
}

#[test]
fn converts_linear_candidate_with_exact_clause_and_raw_rationals() {
    let (terms, clause, candidate) = linear();
    let source = source(&terms, &clause);
    let ProofStep::NraSos {
        clause: output,
        certificate,
    } = convert(&source, &candidate).unwrap()
    else {
        panic!("typed SOS candidate")
    };
    assert_eq!(output, clause);
    assert_eq!(
        certificate.terms[0].origin,
        NraSosOrigin::ClauseLiteral { position: 0 }
    );
    assert_eq!(certificate.terms[1].multiplier.numerator, BigInt::from(2));
    assert_eq!(certificate.rhs.numerator, BigInt::from(-2));
    assert_eq!(certificate.rhs.denominator, BigInt::one());
    certificate.validate_shape().unwrap();
}

#[test]
fn retains_constant_and_duplicate_slots_without_reindexing() {
    let (mut terms, mut clause, mut candidate) = linear();
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    clause.insert(0, literal(&mut terms, "<", zero, one));
    clause.push(clause[1]);
    let source = source(&terms, &clause);
    assert_eq!(source.constraints().len(), 4);
    assert_eq!(
        source.constraints()[0].poly.terms,
        vec![(vec![], -BigRational::one())]
    );
    assert_eq!(
        source.constraints()[1].poly.terms,
        source.constraints()[3].poly.terms
    );
    assert!(convert(&source, &candidate).is_none());
    for term in &mut candidate.terms {
        let CertOrigin::Constraint(index) = &mut term.origin else {
            panic!("linear")
        };
        *index += 1;
    }
    let ProofStep::NraSos {
        clause: output,
        certificate,
    } = convert(&source, &candidate).unwrap()
    else {
        panic!("typed candidate")
    };
    assert_eq!(output, clause);
    assert_eq!(
        certificate.terms[0].origin,
        NraSosOrigin::ClauseLiteral { position: 1 }
    );
    assert_eq!(
        certificate.terms[1].origin,
        NraSosOrigin::ClauseLiteral { position: 2 }
    );
}

#[test]
fn converts_shifted_quartic_basis_without_linearizing_source_variables() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = real(&mut terms, 1);
    let zero = real(&mut terms, 0);
    let xy = terms.mk_mul(vec![x, y]);
    let shifted = terms.mk_sub(vec![xy, one]);
    let square = terms.mk_mul(vec![shifted, shifted]);
    let clause = vec![literal(&mut terms, "<", square, zero)];
    let source = source(&terms, &clause);
    assert_eq!(source.variables(), &[x, y]);
    let candidate = SosCertificate {
        basis: vec![vec![], vec![x, y]],
        gram: vec![
            vec![BigRational::one(), -BigRational::one()],
            vec![-BigRational::one(), BigRational::one()],
        ],
        terms: vec![CertTerm {
            origin: CertOrigin::Constraint(0),
            multiplier: BigRational::one(),
        }],
        rhs: BigRational::zero(),
    };
    let ProofStep::NraSos { certificate, .. } = convert(&source, &candidate).unwrap() else {
        panic!("quartic candidate")
    };
    assert_eq!(certificate.basis, candidate.basis);
}

#[test]
fn rejects_reordered_polarity_changed_or_wrong_slot_candidates() {
    let (terms, clause, mut candidate) = linear();
    let reordered = source(&terms, &[clause[1], clause[0]]);
    assert!(convert(&reordered, &candidate).is_none());
    let TermData::Not(atom) = terms.get(clause[0]) else {
        panic!("literal")
    };
    let changed = source(&terms, &[*atom, clause[1]]);
    assert!(convert(&changed, &candidate).is_none());
    candidate.terms[0].origin = CertOrigin::Constraint(2);
    assert!(convert(&source(&terms, &clause), &candidate).is_none());
}

#[test]
fn product_origins_keep_exact_source_slots_and_both_strict_requirement() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = real(&mut terms, 0);
    let xy = terms.mk_mul(vec![x, y]);
    let mut clause = vec![
        literal(&mut terms, ">", x, zero),
        literal(&mut terms, ">", y, zero),
        literal(&mut terms, "<=", xy, zero),
    ];
    let candidate = SosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![BigRational::zero()]],
        rhs: BigRational::zero(),
        terms: vec![
            CertTerm {
                origin: CertOrigin::Product(0, 1),
                multiplier: one(),
            },
            CertTerm {
                origin: CertOrigin::Constraint(2),
                multiplier: one(),
            },
        ],
    };
    let ProofStep::NraSos { certificate, .. } =
        convert(&source(&terms, &clause), &candidate).unwrap()
    else {
        panic!("product")
    };
    assert_eq!(
        certificate.terms[0].origin,
        NraSosOrigin::Product { left: 0, right: 1 }
    );
    clause[0] = literal(&mut terms, ">=", x, zero);
    assert!(convert(&source(&terms, &clause), &candidate).is_none());
}

#[test]
fn retains_constant_false_source_but_does_not_invent_a_search_decision() {
    let mut terms = TermStore::new();
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    let clause = [literal(&mut terms, ">", zero, one)];
    let source = source(&terms, &clause);
    assert_eq!(source.constraints().len(), 1);
    assert!(source.variables().is_empty());
    assert!(super::super::search(source.constraints(), source.variables()).is_none());
}

#[test]
fn refuses_noncanonical_and_over_cap_private_payloads() {
    let (terms, clause, candidate) = linear();
    let source = source(&terms, &clause);
    let mut changed = candidate.clone();
    changed.terms = vec![changed.terms[0].clone(); NraSosCertificate::MAX_TERMS + 1];
    assert!(convert(&source, &changed).is_none());
    let mut changed = candidate.clone();
    changed.terms[0].multiplier = BigRational::new_raw(2.into(), 2.into());
    assert!(convert(&source, &changed).is_none());
    let mut changed = candidate.clone();
    changed.gram[0].push(zero());
    assert!(convert(&source, &changed).is_none());
    let mut changed = candidate;
    changed.rhs = BigRational::from_integer(BigInt::one() << 1_024usize);
    assert!(convert(&source, &changed).is_none());
}

#[test]
fn source_caps_and_foreign_grammar_refuse_before_conversion() {
    let (mut terms, clause, _) = linear();
    assert!(SosClauseSource::from_clause(
        &terms,
        &vec![clause[0]; 1_025],
        &mut SosPolynomialBudget::default()
    )
    .is_none());
    let opaque = terms.mk_app(Symbol::named("f"), [], Sort::Real);
    let zero = real(&mut terms, 0);
    let foreign = literal(&mut terms, ">", opaque, zero);
    assert!(
        SosClauseSource::from_clause(&terms, &[foreign], &mut SosPolynomialBudget::default())
            .is_none()
    );
    let mut entries = terms.entries_snapshot();
    entries[opaque.index()].0 = TermData::Const(Constant::BitVec {
        value: 0.into(),
        width: u32::MAX,
    });
    let restored = TermStore::from_entries(entries, None, None, 0);
    assert!(SosClauseSource::from_clause(
        &restored,
        &[foreign],
        &mut SosPolynomialBudget::default()
    )
    .is_none());
}

#[test]
fn cancellation_refuses_before_source_allocation_and_at_conversion_completion(
) -> Result<(), Box<dyn std::error::Error>> {
    let (terms, clause, candidate) = linear();
    let mut refuse = |_, _| false;
    let mut progress = SosProgress::new(&mut refuse);
    let mut budget = SosPolynomialBudget::with_progress(&mut progress);
    assert!(SosClauseSource::from_clause(&terms, &clause, &mut budget).is_none());

    let source = source(&terms, &clause);
    let mut calls = 0usize;
    assert!(source
        .convert_candidate(
            &candidate,
            &mut SosProgress::new(&mut |_, _| {
                calls = calls.saturating_add(1);
                true
            })
        )
        .is_some());
    let last = calls
        .checked_sub(1)
        .ok_or("conversion completed without a progress poll")?;
    for allowed in [0, calls / 2, last] {
        let mut seen = 0usize;
        let mut callback = |_, _| {
            seen = seen.saturating_add(1);
            seen <= allowed
        };
        let mut progress = SosProgress::new(&mut callback);
        assert!(source
            .convert_candidate(&candidate, &mut progress)
            .is_none());
        assert!(progress.refused());
    }
    Ok(())
}
