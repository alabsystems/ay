// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! A registered user function keeps its semantics regardless of spelling.
use super::*;
use ay_core::{Proof, ProofStep, TheoryLemmaKind};

#[derive(Clone, Copy)]
enum Case {
    Neg,
    Add,
    MulOne,
    Square,
    BitSum,
    Equality,
    Conjunction,
}
#[derive(Clone, Copy)]
enum Registration {
    Builtin,
    User,
}
#[derive(Clone, Copy)]
enum Certificate {
    Theory(TheoryLemmaKind),
    Owned([u32; 2]),
}

fn fixture(case: Case, registration: Registration) -> (TermStore, Vec<TermId>, Option<[u32; 2]>) {
    let mut terms = TermStore::new();
    let field = ay_core::FiniteFieldSort::new(7).unwrap();
    let x = terms.mk_var("x", Sort::FiniteField(field));
    let zero = terms.mk_finite_field(0, field);
    let one = terms.mk_finite_field(1, field);
    let (name, args, coefficients) = match case {
        Case::Neg => ("ff.neg", vec![x], Some([1, 1])),
        Case::Add => ("ff.add", vec![x, zero], Some([1, 6])),
        Case::MulOne => ("ff.mul", vec![x, one], Some([1, 6])),
        Case::Square => ("ff.mul", vec![x, x], None),
        Case::BitSum => ("ff.bitsum", vec![x, zero], Some([1, 6])),
        Case::Equality => ("=", vec![x, zero], Some([1, 6])),
        Case::Conjunction => ("and", Vec::new(), None),
    };
    let roots = match case {
        Case::Equality => vec![
            terms.mk_app(Symbol::Named("=".into()), &[x, zero], Sort::Bool),
            terms.mk_app(Symbol::Named("=".into()), &[x, one], Sort::Bool),
        ],
        Case::Conjunction => {
            let eq = terms.mk_eq(x, zero);
            let no = terms.mk_bool(false);
            vec![terms.mk_app(Symbol::Named(name.into()), &[eq, no], Sort::Bool)]
        }
        _ => {
            let app = terms.mk_app(Symbol::Named(name.into()), &args, Sort::FiniteField(field));
            vec![
                terms.mk_app(Symbol::Named("=".into()), &[app, one], Sort::Bool),
                terms.mk_app(Symbol::Named("=".into()), &[x, zero], Sort::Bool),
            ]
        }
    };
    if matches!(registration, Registration::User) {
        terms.register_declared_function(name);
    }
    (terms, roots, coefficients)
}
fn certificates(coefficients: Option<[u32; 2]>) -> Vec<Certificate> {
    let mut out = [
        TheoryLemmaKind::FiniteFieldExhaustive,
        TheoryLemmaKind::FiniteFieldQuadratic,
        TheoryLemmaKind::FiniteFieldUnivariate,
        TheoryLemmaKind::FiniteFieldIdeal,
    ]
    .into_iter()
    .map(Certificate::Theory)
    .collect::<Vec<_>>();
    if let Some([a, b]) = coefficients {
        out.push(Certificate::Theory(TheoryLemmaKind::FiniteFieldLinear([
            a as u8, b as u8, 0, 0, 0, 0, 0, 0,
        ])));
        out.push(Certificate::Theory(TheoryLemmaKind::FiniteFieldLinearWide(
            [a, b, 0, 0, 0, 0, 0, 0],
        )));
        out.push(Certificate::Owned([a, b]));
    }
    out
}
fn check(
    terms: &mut TermStore,
    roots: &[TermId],
    certificate: Certificate,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<crate::ProofQuality, ProofCheckError> {
    let mut clause = roots
        .iter()
        .map(|&root| terms.mk_not_raw(root))
        .collect::<Vec<_>>();
    let mut proof = Proof::new();
    let mut prior = proof.add_step(match certificate {
        Certificate::Theory(kind) => ProofStep::TheoryLemma {
            theory: "FiniteField".into(),
            clause: clause.clone(),
            farkas: None,
            kind,
            lia: None,
        },
        Certificate::Owned(multipliers) => ProofStep::FiniteFieldLinear {
            clause: clause.clone(),
            multipliers: multipliers.to_vec(),
        },
    });
    for &root in roots {
        let assume = proof.add_assume(root, None);
        clause.remove(0);
        prior = proof.add_resolution(clause.clone(), root, assume, prior);
    }
    crate::check_proof_strict_with_context_and_progress(
        &proof,
        terms,
        None,
        None,
        Some(roots),
        progress,
    )
}
#[test]
fn field_certificates_reject_registered_operator_identities_and_keep_actual_builtin_proofs() {
    for case in [
        Case::Neg,
        Case::Add,
        Case::MulOne,
        Case::Square,
        Case::BitSum,
        Case::Equality,
        Case::Conjunction,
    ] {
        let (mut builtin, roots, coefficients) = fixture(case, Registration::Builtin);
        for certificate in certificates(coefficients) {
            assert!(
                check(&mut builtin, &roots, certificate, &mut |_, _| true)
                    .is_ok_and(|quality| quality.is_complete()),
                "real field arithmetic must still be independently checked"
            );
        }
        let (mut user, roots, coefficients) = fixture(case, Registration::User);
        // SAT: x=0, each registered field-valued function takes value1 at
        // its queried tuple; registered '='/'and' take Boolean true.
        for certificate in certificates(coefficients) {
            assert!(
                check(&mut user, &roots, certificate, &mut |_, _| true).is_err(),
                "user declarations cannot acquire field/Boolean theory semantics"
            );
            assert!(
                check(&mut user.clone(), &roots, certificate, &mut |_, _| true).is_err(),
                "cloning cannot erase declaration provenance"
            );
        }
    }
}
#[test]
fn field_namespace_validation_obeys_original_progress_refusal() {
    let (mut terms, roots, coefficients) = fixture(Case::Add, Registration::Builtin);
    for certificate in certificates(coefficients) {
        assert!(check(&mut terms, &roots, certificate, &mut |_, _| false).is_err());
    }
}
