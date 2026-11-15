// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use ay_core::{NraSosOrigin, NraSosRational, NraSosTerm};
use num_rational::BigRational;

fn number(terms: &mut TermStore, real: bool, value: i64) -> TermId {
    if real {
        terms.mk_rational(BigRational::from_integer(value.into()))
    } else {
        terms.mk_int(value.into())
    }
}

fn negative_square(real: bool) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let sort = if real { Sort::Real } else { Sort::Int };
    let x = terms.mk_var("sos_builder_x", sort.clone());
    let square = terms.mk_app(Symbol::named("*"), [x, x], sort);
    let zero = number(&mut terms, real, 0);
    let root = terms.mk_app(Symbol::named("<"), [square, zero], Sort::Bool);
    (terms, root)
}

fn repeated_linear() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("sos_builder_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let tautology = terms.mk_app(Symbol::named("="), [one, one], Sort::Bool);
    let lower = terms.mk_app(Symbol::named(">="), [x, one], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
    let not_lower = terms.mk_not_raw(lower);
    let alias = terms.mk_not_raw(not_lower);
    (terms, vec![tautology, lower, upper, lower, alias, upper])
}

fn rational(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: value.into(),
        denominator: 1.into(),
    }
}

fn linear_lemma(source: &Source) -> ProofStep {
    ProofStep::NraSos {
        clause: source.clause.clone(),
        certificate: NraSosCertificate {
            basis: vec![vec![]],
            gram: vec![vec![rational(0)]],
            terms: [1, 2]
                .map(|position| NraSosTerm {
                    origin: NraSosOrigin::ClauseLiteral { position },
                    multiplier: rational(1),
                })
                .to_vec(),
            rhs: rational(-1),
        },
    }
}

#[test]
fn actual_integer_and_real_square_candidates_produce_freshly_replayed_proofs() {
    for real in [false, true] {
        let (mut terms, root) = negative_square(real);
        let built = build(&mut terms, &[root], &[], &mut |_, _| true)
            .unwrap()
            .expect("bounded exact SOS candidate");
        assert_eq!(built.bundle.obligation_assertions, vec![root]);
        assert_eq!(built.candidate.steps.len(), 3);
        assert!(built.quality.is_complete());
        assert_eq!(built.quality.theory_lemma_count, 1);
        assert_eq!(built.quality.assume_count, 1);
        assert!(built
            .evidence
            .is_current_for_with_progress(&terms, &[root], &[], &mut |_, _| true)
            .unwrap());
        assert!(!built
            .evidence
            .is_current_for_with_progress(&terms, &[], &[root], &mut |_, _| true)
            .unwrap());
    }
}

#[test]
fn actual_builder_preserves_constant_duplicate_and_parity_alias_source_slots() {
    let (mut terms, roots) = repeated_linear();
    let built = build(&mut terms, &roots[..3], &roots[3..], &mut |_, _| true)
        .unwrap()
        .expect("same exact factor namespace despite duplicated source slots");
    assert_eq!(built.bundle.obligation_assertions, roots);
    assert_eq!(built.candidate.steps.len(), roots.len() + 1 + 3);
    for (step, &root) in built.candidate.steps.iter().zip(&roots) {
        assert!(matches!(step, ProofStep::Assume(actual) if *actual == root));
    }
    let ProofStep::NraSos { clause, .. } = &built.candidate.steps[roots.len()] else {
        panic!("unchanged positional SOS lemma")
    };
    assert_eq!(clause.len(), roots.len());
    for (&literal, &root) in clause.iter().zip(&roots) {
        assert!(matches!(terms.get(literal), TermData::Not(inner) if *inner == root));
    }
    assert_ne!(
        clause[1], clause[4],
        "raw one-not and three-not remain distinct"
    );
    assert!(built
        .evidence
        .is_current_for_with_progress(&terms, &roots[..3], &roots[3..], &mut |_, _| true)
        .unwrap());
}

#[test]
fn fixed_independent_linear_certificate_closes_every_parity_occurrence_together() {
    let (mut terms, roots) = repeated_linear();
    let source = source(&mut terms, &roots, &[], &mut |_, _| true)
        .unwrap()
        .unwrap();
    let proof = complete_proof(linear_lemma(&source), &source, &mut |_, _| true).unwrap();
    let suffix = &proof.steps[roots.len() + 1..];
    let expected = [
        source.clause[1..].to_vec(),
        vec![source.clause[2], source.clause[5]],
        vec![],
    ];
    for (step, expected) in suffix.iter().zip(expected) {
        assert!(matches!(step, ProofStep::Resolution { clause, .. } if *clause == expected));
    }
    assert_eq!(suffix.len(), 3);
    let bundle =
        SerializableProofBundle::from_proof_with_progress(&proof, &terms, &roots, &mut |_, _| true)
            .unwrap();
    let checked = re_check_bundle_strict_with_cancellation(&bundle, &mut || true).unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(checked.assume_terms, roots);
}

#[test]
fn opposite_source_polarities_remain_distinct_resolution_pivots() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("opposite_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let positive = terms.mk_app(Symbol::named(">="), [x, zero], Sort::Bool);
    let negative = terms.mk_not_raw(positive);
    let built = build(&mut terms, &[positive], &[negative], &mut |_, _| true)
        .unwrap()
        .expect("x>=0 and x<0 have an exact strict SOS refutation");
    assert_eq!(built.candidate.steps.len(), 5);
    assert_eq!(built.quality.resolution_count, 2);
    assert_eq!(built.bundle.obligation_assertions, vec![positive, negative]);
    let ProofStep::NraSos { clause, .. } = &built.candidate.steps[2] else {
        panic!("source-bound lemma")
    };
    assert_eq!(clause[0], negative);
    assert!(matches!(terms.get(clause[1]), TermData::Not(inner) if *inner == negative));
    assert!(
        matches!(&built.candidate.steps[3], ProofStep::Resolution { clause: residual, pivot, .. }
        if residual == &clause[1..] && *pivot == positive)
    );
    assert!(
        matches!(&built.candidate.steps[4], ProofStep::Resolution { clause, pivot, .. }
        if clause.is_empty() && *pivot == negative)
    );
}

#[test]
fn unsupported_roots_and_excess_slots_decline_without_rewriting_the_source() {
    let (mut terms, root) = negative_square(false);
    let boolean = terms.true_term();
    let variable = terms.mk_var("uninterpreted_bool", Sort::Bool);
    let non_boolean = terms.mk_int(3.into());
    let boolean_equality = terms.mk_app(Symbol::named("="), [variable, variable], Sort::Bool);
    for roots in [
        vec![],
        vec![root, boolean],
        vec![root, variable],
        vec![boolean_equality],
        vec![non_boolean],
        vec![TermId(u32::MAX)],
        vec![root; NraSosCertificate::MAX_CLAUSE_SLOTS + 1],
    ] {
        let stamp = terms.snapshot_stamp();
        assert!(!supports_source(&terms, &roots, &[], &mut |_, _| true).unwrap());
        assert!(build(&mut terms, &roots, &[], &mut |_, _| true)
            .unwrap()
            .is_none());
        assert_eq!(terms.snapshot_stamp(), stamp);
    }
}

#[test]
fn source_preflight_is_read_only_and_refusal_is_terminal_at_each_callback() {
    let (terms, roots) = repeated_linear();
    let stamp = terms.snapshot_stamp();
    let mut calls = 0;
    assert!(
        supports_source(&terms, &roots[..3], &roots[3..], &mut |_, _| {
            calls += 1;
            true
        })
        .unwrap()
    );
    assert!(calls > roots.len());
    for stop in 1..=calls {
        let mut observed = 0;
        let result = supports_source(&terms, &roots[..3], &roots[3..], &mut |_, _| {
            observed += 1;
            observed != stop
        });
        assert!(matches!(result, Err(BuildError::ResourceLimit)));
        assert_eq!(observed, stop);
    }
    assert_eq!(terms.snapshot_stamp(), stamp);
}

#[test]
fn every_source_and_composer_poll_refuses_without_a_partial_result() {
    let (mut terms, roots) = repeated_linear();
    let mut calls = 0;
    let source = source(&mut terms, &roots, &[], &mut |_, _| {
        calls += 1;
        true
    })
    .unwrap()
    .unwrap();
    for stop in 1..=calls {
        let mut observed = 0;
        let outcome = super::source(&mut terms, &roots, &[], &mut |_, _| {
            observed += 1;
            observed != stop
        });
        assert!(matches!(outcome, Err(BuildError::ResourceLimit)));
        assert_eq!(observed, stop);
    }
    let mut calls = 0;
    complete_proof(linear_lemma(&source), &source, &mut |_, _| {
        calls += 1;
        true
    })
    .unwrap();
    for stop in 1..=calls {
        let mut observed = 0;
        let outcome = complete_proof(linear_lemma(&source), &source, &mut |_, _| {
            observed += 1;
            observed != stop
        });
        assert!(matches!(outcome, Err(BuildError::ResourceLimit)));
        assert_eq!(observed, stop);
    }
}

#[test]
fn precancellation_and_the_final_postcleanup_poll_cannot_publish_a_proof() {
    let (mut terms, root) = negative_square(false);
    let stamp = terms.snapshot_stamp();
    assert!(matches!(
        build(&mut terms, &[root], &[], &mut |_, _| false),
        Err(BuildError::ResourceLimit)
    ));
    assert_eq!(terms.snapshot_stamp(), stamp);
    // Warm only the raw complements, so both attempts copy the same snapshot.
    terms.mk_not_raw(root);
    let mut calls = 0;
    let success = build(&mut terms, &[root], &[], &mut |_, _| {
        calls += 1;
        true
    })
    .unwrap()
    .unwrap();
    assert!(calls > 2);
    let mut observed = 0;
    let outcome = build(&mut terms, &[root], &[], &mut |_, _| {
        observed += 1;
        observed != calls
    });
    assert!(matches!(outcome, Err(BuildError::ResourceLimit)));
    assert_eq!(observed, calls);
    let retry = build(&mut terms, &[root], &[], &mut |_, _| true)
        .unwrap()
        .unwrap();
    assert_eq!(retry.candidate.steps, success.candidate.steps);
}

#[test]
fn allocation_overflow_refuses_before_attempting_reservation() {
    let mut calls = 0;
    assert!(matches!(
        vector::<TermId>(usize::MAX, &mut |_, _| {
            calls += 1;
            true
        }),
        Err(BuildError::ResourceLimit)
    ));
    assert_eq!(calls, 0);
}
