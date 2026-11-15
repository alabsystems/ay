// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end candidate generation checked by the independent proof crate.

use super::*;
use ay_core::{NraSosOrigin, Proof, Sort, Symbol};
use ay_proof::{re_check_bundle_strict, SerializableProofBundle};
use num_rational::BigRational;

struct Fixture {
    terms: TermStore,
    assertions: Vec<TermId>,
    clause: Vec<TermId>,
}

fn real(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(value.into()))
}

impl Fixture {
    fn linear() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("candidate_x", Sort::Real);
        let zero = real(&mut terms, 0);
        let two = real(&mut terms, 2);
        let twice_x = terms.mk_mul(vec![two, x]);
        let lower = terms.mk_ge(twice_x, two);
        let upper = terms.mk_le(x, zero);
        Self::new(terms, vec![lower, upper])
    }

    fn quartic() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("candidate_x", Sort::Real);
        let y = terms.mk_var("candidate_y", Sort::Real);
        let zero = real(&mut terms, 0);
        let one = real(&mut terms, 1);
        let product = terms.mk_mul(vec![x, y]);
        let shifted = terms.mk_sub(vec![product, one]);
        let square = terms.mk_mul(vec![shifted, shifted]);
        let negative = terms.mk_lt(square, zero);
        Self::new(terms, vec![negative])
    }

    fn new(mut terms: TermStore, assertions: Vec<TermId>) -> Self {
        let clause = assertions
            .iter()
            .map(|&atom| terms.mk_not_raw(atom))
            .collect();
        Self {
            terms,
            assertions,
            clause,
        }
    }

    fn candidate(&self) -> ProofStep {
        find_sos_refutation_candidate(&self.terms, &self.clause, &mut |_, _| true)
            .expect("caller permits bounded generation")
            .expect("supported analytic refutation")
    }

    fn bundle(&self, candidate: ProofStep) -> SerializableProofBundle {
        let ProofStep::NraSos { clause, .. } = &candidate else {
            panic!("dedicated SOS candidate")
        };
        assert_eq!(clause, &self.clause);
        let mut proof = Proof::new();
        let mut tail = proof.add_step(candidate);
        let mut remaining = self.clause.clone();
        for (index, &assertion) in self.assertions.iter().enumerate() {
            let negated = self.clause[index];
            if !remaining.contains(&negated) {
                continue; // A previous resolution already removed this duplicate.
            }
            remaining.retain(|literal| *literal != negated);
            let assume = proof.add_assume(assertion, None);
            tail = proof.add_resolution(remaining.clone(), assertion, tail, assume);
        }
        assert!(remaining.is_empty());
        SerializableProofBundle::from_proof(&proof, &self.terms, self.assertions.clone())
    }
}

#[test]
fn generated_linear_and_quartic_candidates_replay_independently() {
    for fixture in [Fixture::linear(), Fixture::quartic()] {
        let before = fixture.terms.entries_snapshot();
        let stamp = fixture.terms.snapshot_stamp();
        let bundle = fixture.bundle(fixture.candidate());
        let checked = re_check_bundle_strict(&bundle).expect("independent exact proof replay");
        assert_eq!(checked.quality.theory_lemma_count, 1);
        assert_eq!(checked.quality.trust_count, 0);
        assert_eq!(checked.quality.hole_count, 0);
        assert_eq!(checked.assume_terms, fixture.assertions);
        assert_eq!(fixture.terms.entries_snapshot(), before);
        assert_eq!(fixture.terms.snapshot_stamp(), stamp);
    }
}

#[test]
fn generated_candidates_keep_constant_and_duplicate_source_slots() {
    let mut fixture = Fixture::linear();
    let one = real(&mut fixture.terms, 1);
    let tautology = fixture
        .terms
        .mk_app(Symbol::named("="), [one, one], Sort::Bool);
    fixture.assertions.insert(0, tautology);
    fixture.assertions.push(fixture.assertions[1]);
    let fixture = Fixture::new(fixture.terms, fixture.assertions);
    let bundle = fixture.bundle(fixture.candidate());
    re_check_bundle_strict(&bundle).expect("constant and duplicate slots survive both readers");
    let mut forged = bundle.clone();
    let ProofStep::NraSos { certificate, .. } = &mut forged.steps[0] else {
        panic!("SOS candidate")
    };
    // Redirect every selected constraint/product to the preserved tautology.
    // A false filtered-index assumption must not survive independent replay.
    for term in &mut certificate.terms {
        term.origin = NraSosOrigin::ClauseLiteral { position: 0 };
    }
    assert!(re_check_bundle_strict(&forged).is_err());
}

#[test]
fn satisfiable_and_unsupported_sources_do_not_produce_candidates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("candidate_x", Sort::Real);
    let zero = real(&mut terms, 0);
    let square = terms.mk_mul(vec![x, x]);
    let nonpositive = terms.mk_le(square, zero); // x=0 is a model.
    let fixture = Fixture::new(terms, vec![nonpositive]);
    assert_eq!(
        find_sos_refutation_candidate(&fixture.terms, &fixture.clause, &mut |_, _| true),
        Ok(None)
    );
    for clause in [
        vec![],
        vec![fixture.terms.true_term()],
        vec![TermId(u32::MAX)],
    ] {
        assert_eq!(
            find_sos_refutation_candidate(&fixture.terms, &clause, &mut |_, _| true),
            Ok(None)
        );
    }
}

#[test]
fn caller_refusal_is_sticky_even_if_the_callback_would_resume() {
    let fixture = Fixture::linear();
    let mut calls = 0i32;
    let result = find_sos_refutation_candidate(&fixture.terms, &fixture.clause, &mut |_, _| {
        calls = calls.saturating_add(1);
        calls != 1
    });
    assert_eq!(result, Err(SosCandidateError::ResourceLimit));
    assert_eq!(calls, 1);
}

#[test]
fn cancellation_before_during_and_after_search_withholds_the_candidate() {
    let fixture = Fixture::quartic();
    let (mut calls, mut work, mut bytes) = (0usize, 0usize, 0usize);
    let candidate = find_sos_refutation_candidate(&fixture.terms, &fixture.clause, &mut |w, b| {
        calls = calls.saturating_add(1);
        work = work.saturating_add(w);
        bytes = bytes.saturating_add(b);
        true
    })
    .expect("permitted")
    .expect("quartic witness");
    re_check_bundle_strict(&fixture.bundle(candidate)).expect("independent positive control");
    assert!(calls > 10 && work > 0 && bytes > 0);
    for permitted in [0, 2, calls / 2, calls - 1] {
        let mut seen = 0usize;
        let result = find_sos_refutation_candidate(&fixture.terms, &fixture.clause, &mut |_, _| {
            seen = seen.saturating_add(1);
            seen <= permitted
        });
        assert_eq!(result, Err(SosCandidateError::ResourceLimit));
    }
}

#[test]
fn zero_work_or_allocation_allowance_refuses_generation() {
    let fixture = Fixture::linear();
    for reject_work in [true, false] {
        let result = find_sos_refutation_candidate(&fixture.terms, &fixture.clause, &mut |w, b| {
            if reject_work {
                w == 0
            } else {
                b == 0
            }
        });
        assert_eq!(result, Err(SosCandidateError::ResourceLimit));
    }
}
