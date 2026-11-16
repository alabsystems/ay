// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::{meter::ProofMeter, safety};
use super::*;

struct Fixture {
    entries: Vec<(TermData, Sort)>,
    clause: [TermId; 3],
}

impl Fixture {
    fn new(eb: u32, sb: u32) -> Self {
        let fp = Sort::FloatingPoint(eb, sb);
        Self {
            entries: vec![
                (TermData::Const(Constant::Bool(true)), Sort::Bool),
                (TermData::Const(Constant::Bool(false)), Sort::Bool),
                (TermData::Var("preflight_nan_x".into(), 0), fp.clone()),
                (TermData::Var("preflight_nan_y".into(), 1), fp),
                (
                    TermData::App(Symbol::named("fp.isNaN"), vec![TermId(2)]),
                    Sort::Bool,
                ),
                (
                    TermData::App(Symbol::named("fp.isNaN"), vec![TermId(3)]),
                    Sort::Bool,
                ),
                (TermData::Not(TermId(4)), Sort::Bool),
                (TermData::Not(TermId(5)), Sort::Bool),
                (
                    TermData::App(Symbol::named("="), vec![TermId(2), TermId(3)]),
                    Sort::Bool,
                ),
            ],
            clause: [TermId(6), TermId(7), TermId(8)],
        }
    }

    fn steps(&self) -> [ProofStep; 1] {
        [lemma(self.clause.to_vec(), kind())]
    }

    fn run(&self, progress: &mut dyn FnMut(usize, usize) -> bool) -> Result<(), ProofCheckError> {
        // Isolate the actual safety hook so zero scratch allocation and exact
        // schema work cannot be hidden by unrelated proof-step bookkeeping.
        safety::validate(
            &self.entries,
            0,
            &self.clause,
            &kind(),
            &mut ProofMeter::new(progress),
        )
    }

    fn bundle(&self) -> SerializableProofBundle {
        let terms =
            TermStore::from_entries(self.entries.clone(), Some(TermId(0)), Some(TermId(1)), 2);
        SerializableProofBundle::from_proof(
            &Proof::from_steps(self.steps().to_vec()),
            &terms,
            vec![],
        )
    }
}

fn kind() -> TheoryLemmaKind {
    TheoryLemmaKind::FpClassification {
        operation: FpOp::IsNaN,
    }
}

fn usage(fixture: &Fixture) -> (usize, usize, usize) {
    let (mut calls, mut work, mut bytes) = (0, 0, 0);
    fixture
        .run(&mut |w, b| {
            calls += 1;
            work += w;
            bytes += b;
            true
        })
        .unwrap();
    (calls, work, bytes)
}

#[test]
fn nan_preflight_exact_schema_has_width_independent_reads_and_no_scratch_allocation() {
    let mut expected = None;
    for (eb, sb) in [(5, 11), (8, 24), (11, 53), (31, 1 << 20)] {
        let fixture = Fixture::new(eb, sb);
        let measured = usage(&fixture);
        // Seven charged reads; one shape count, two 19-debit negative atoms,
        // one 10-debit equality, and 15 final endpoint/matching debits = 64.
        assert_eq!(measured.1, 64);
        assert_eq!(measured.2, 0);
        if let Some(previous) = expected {
            assert_eq!(measured, previous);
        }
        expected = Some(measured);
        assert!(validate_proof_snapshot(&fixture.steps(), &fixture.entries).is_ok());
    }
}

#[test]
fn nan_preflight_every_transient_stop_including_final_poll_is_terminal() {
    let fixture = Fixture::new(11, 53);
    let expected_entries = fixture.entries.clone();
    let (calls, _, _) = usage(&fixture);
    for reject in 1..=calls {
        let mut seen = 0;
        let result = fixture.run(&mut |_, _| {
            seen += 1;
            seen != reject // Would approve any later callback.
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(seen, reject);
        assert_eq!(fixture.entries, expected_entries);
    }
    // Exercise the public-to-this-module proof preflight path as well: a
    // resource error is not converted to a nonmatch and an enumerator retry.
    let (calls, _, _) = measurements(&fixture.steps(), &fixture.entries);
    for reject in 1..=calls {
        let mut seen = 0;
        let result = validate_proof_snapshot_with_progress(
            &fixture.steps(),
            &fixture.entries,
            &mut |_, _| {
                seen += 1;
                seen != reject
            },
        );
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(seen, reject);
    }
}

#[test]
fn nan_preflight_exact_shared_work_budget_cannot_reset_between_theorems() {
    let fixture = Fixture::new(8, 24);
    let (_, work, bytes) = usage(&fixture);
    assert_eq!(bytes, 0);
    for (limit, accepted) in [(work, true), (work - 1, false), (0, false)] {
        let mut spent = 0;
        let result = fixture.run(&mut |w, b| {
            assert_eq!(b, 0);
            spent += w;
            spent <= limit
        });
        assert_eq!(result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        }
    }
    let mut remaining = work;
    let mut progress = |w, _: usize| match remaining.checked_sub(w) {
        Some(next) => {
            remaining = next;
            true
        }
        None => false,
    };
    assert!(fixture.run(&mut progress).is_ok());
    assert!(matches!(
        fixture.run(&mut progress),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn nan_preflight_nonmatches_keep_enumerator_limits_and_missing_reads_fail_closed() {
    for symbol in [Symbol::named("fp.eq"), Symbol::indexed("=", vec![0])] {
        let mut fixture = Fixture::new(8, 24);
        fixture.entries[8].0 = TermData::App(symbol, vec![TermId(2), TermId(3)]);
        assert_malformed(&fixture.steps(), &fixture.entries);
    }
    let mut mismatch = Fixture::new(8, 24);
    mismatch.entries[8].0 = TermData::App(Symbol::named("="), vec![TermId(2), TermId(2)]);
    assert_malformed(&mismatch.steps(), &mismatch.entries);
    for indexed in [false, true] {
        let mut fixture = Fixture::new(8, 24);
        if indexed {
            fixture.entries[4].0 =
                TermData::App(Symbol::indexed("fp.isNaN", vec![0]), vec![TermId(2)]);
        } else {
            fixture.entries[4].0 = TermData::Not(TermId(5));
        }
        assert_malformed(&fixture.steps(), &fixture.entries);
    }
    // The separate existing class-exclusion schema does not acquire a blanket
    // wide-FP preflight exception from this exact three-literal rule.
    let mut exclusion = Fixture::new(8, 24);
    exclusion.entries[5].0 = TermData::App(Symbol::named("fp.isZero"), vec![TermId(2)]);
    assert_malformed(
        &[lemma(vec![TermId(6), TermId(7)], kind())],
        &exclusion.entries,
    );
    for location in [4, 6, 8] {
        let mut fixture = Fixture::new(8, 24);
        fixture.entries[location].0 = match location {
            4 => TermData::App(Symbol::named("fp.isNaN"), vec![TermId(u32::MAX)]),
            6 => TermData::Not(TermId(u32::MAX)),
            _ => TermData::App(Symbol::named("="), vec![TermId(2), TermId(u32::MAX)]),
        };
        assert_malformed(&fixture.steps(), &fixture.entries);
    }
    let mut matched_missing = Fixture::new(8, 24);
    matched_missing.entries[5].0 = TermData::App(Symbol::named("fp.isNaN"), vec![TermId(u32::MAX)]);
    matched_missing.entries[8].0 =
        TermData::App(Symbol::named("="), vec![TermId(2), TermId(u32::MAX)]);
    assert_malformed(&matched_missing.steps(), &matched_missing.entries);
}

#[test]
fn nan_preflight_global_snapshot_validation_remains_prior_and_mandatory() {
    let fixture = Fixture::new(8, 24);
    let bundle = fixture.bundle();
    let preflight = |bundle: &SerializableProofBundle| {
        preflight::preflight_bundle_with_progress(bundle, &mut |_, _| true)
    };
    assert!(preflight(&bundle).is_ok());
    // This shape-only proof is deliberately not closed; shape preflight is
    // separate from strict replay and cannot itself create proof authority.
    assert!(re_check_bundle_strict(&bundle).is_err());
    let mut descendant = bundle.clone();
    descendant.term_entries[2].0 = TermData::App(Symbol::named("fp.neg"), vec![TermId(u32::MAX)]);
    let shallow = Fixture {
        entries: descendant.term_entries.clone(),
        clause: fixture.clause,
    };
    assert!(shallow.run(&mut |_, _| true).is_ok());
    assert!(preflight(&descendant).is_err());
    let mut bad_signature = bundle.clone();
    bad_signature.term_entries[2].0 = TermData::App(Symbol::named("fp.neg"), vec![TermId(0)]);
    let shallow = Fixture {
        entries: bad_signature.term_entries.clone(),
        clause: fixture.clause,
    };
    assert!(shallow.run(&mut |_, _| true).is_ok());
    assert!(preflight(&bad_signature).is_err());
    let mut unused = bundle.clone();
    unused
        .term_entries
        .push((TermData::Not(TermId(u32::MAX)), Sort::Bool));
    assert!(preflight(&unused).is_err());
    for (eb, sb) in [(1, 24), (8, 1), (65, 24), (8, (1 << 20) + 1)] {
        let mut malformed = bundle.clone();
        for id in [2, 3] {
            malformed.term_entries[id].1 = Sort::FloatingPoint(eb, sb);
        }
        assert!(preflight(&malformed).is_err());
    }
}
