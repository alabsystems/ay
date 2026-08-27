// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Theory-conflict certificate and authority regression tests.
// Textually included by `proof_tracker::tests` to preserve test FQNs.

#[test]
#[cfg(debug_assertions)]
fn test_farkas_coefficient_count_mismatch_panics() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");

    // Farkas annotation has 1 coefficient but clause has 2 literals.
    let clause = vec![TermId(10), TermId(20)];
    let farkas = FarkasAnnotation::from_ints(&[1]); // 1 coeff, 2 lits

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tracker.add_theory_lemma_with_farkas_and_kind(clause, farkas, TheoryLemmaKind::LraFarkas);
    }));
    assert!(
        result.is_err(),
        "Farkas coefficient/clause length mismatch must be caught"
    );
}

#[test]
fn test_record_theory_conflict_unsat_basic() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");

    let mut negations = HashMap::default();
    negations.insert(TermId(10), TermId(11));
    negations.insert(TermId(20), TermId(21));

    let conflict = vec![
        TheoryLit::new(TermId(10), true),
        TheoryLit::new(TermId(20), true),
    ];

    let id = record_theory_conflict_unsat(&mut tracker, None, &negations, &conflict);
    assert!(id.is_some(), "enabled tracker should produce a proof step");
    assert_eq!(tracker.num_steps(), 1);
}

#[test]
fn test_record_theory_conflict_unsat_disabled_returns_none() {
    let mut tracker = ProofTracker::new();
    // Tracker is disabled (default)

    let negations = HashMap::default();
    let conflict = vec![TheoryLit::new(TermId(10), true)];

    let id = record_theory_conflict_unsat(&mut tracker, None, &negations, &conflict);
    assert!(id.is_none(), "disabled tracker must return None");
    assert_eq!(tracker.num_steps(), 0);
}

#[test]
fn test_record_theory_conflict_unsat_integer_bounds_use_lra_farkas_when_unit_certificate_is_valid()
{
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, one);
    let le = terms.mk_le(x, zero);
    let not_ge = terms.mk_not(ge);
    let not_le = terms.mk_not(le);

    let mut negations = HashMap::default();
    negations.insert(ge, not_ge);
    negations.insert(le, not_le);

    let conflict = vec![TheoryLit::new(ge, true), TheoryLit::new(le, true)];
    let id = record_theory_conflict_unsat(&mut tracker, Some(&terms), &negations, &conflict)
        .expect("enabled tracker should record integer arithmetic conflicts");
    assert_eq!(tracker.num_steps(), 1);

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::LraFarkas,
                "Farkas-valid integer conflicts must export la_generic/LraFarkas"
            );
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}

#[test]
fn conflict_trace_annotation_matches_recorded_unit_farkas_authority() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, one);
    let le = terms.mk_le(x, zero);
    let mut negations = HashMap::default();
    negations.insert(ge, terms.mk_not(ge));
    negations.insert(le, terms.mk_not(le));
    let conflict = vec![TheoryLit::new(ge, true), TheoryLit::new(le, true)];

    let (id, annotation) = record_theory_conflict_unsat_with_annotation(
        &mut tracker,
        Some(&terms),
        &negations,
        &conflict,
    );
    let id = id.expect("recorded conflict");
    let annotation = annotation.expect("materialized conflict annotation");
    let proof = tracker.take_proof();
    let Some(ProofStep::TheoryLemma {
        clause,
        kind,
        farkas,
        lia,
        ..
    }) = proof.get_step(id)
    else {
        panic!("expected theory lemma");
    };
    assert_eq!(annotation.clause, *clause);
    assert_eq!(annotation.kind, *kind);
    assert_eq!(annotation.farkas, *farkas);
    assert_eq!(annotation.lia, *lia);
    assert!(annotation.farkas.is_some());
}

#[test]
fn test_record_theory_conflict_unsat_with_invalid_integer_farkas_stays_lia_generic() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, one);
    let le = terms.mk_le(x, zero);
    let not_ge = terms.mk_not(ge);
    let not_le = terms.mk_not(le);

    let mut negations = HashMap::default();
    negations.insert(ge, not_ge);
    negations.insert(le, not_le);

    let conflict = TheoryConflict::with_farkas(
        vec![TheoryLit::new(ge, true), TheoryLit::new(le, true)],
        FarkasAnnotation::from_ints(&[1, 0]),
    );
    let id =
        record_theory_conflict_unsat_with_farkas(&mut tracker, Some(&terms), &negations, &conflict)
            .expect("enabled tracker should record arithmetic conflicts with explicit annotations");

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::LiaGeneric,
                "an annotation that does not derive contradiction must not gain Farkas authority",
            );
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}

#[test]
fn test_record_theory_conflict_unsat_with_strict_integer_bounds_uses_lra_farkas() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let ten = terms.mk_int(BigInt::from(10));
    let five = terms.mk_int(BigInt::from(5));
    let gt = terms.mk_gt(x, ten);
    let lt = terms.mk_lt(x, five);
    let not_gt = terms.mk_not(gt);
    let not_lt = terms.mk_not(lt);

    let mut negations = HashMap::default();
    negations.insert(gt, not_gt);
    negations.insert(lt, not_lt);

    let conflict = vec![TheoryLit::new(gt, true), TheoryLit::new(lt, true)];
    let id = record_theory_conflict_unsat(&mut tracker, Some(&terms), &negations, &conflict)
        .expect("enabled tracker should record strict integer bound conflicts");

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::LraFarkas,
                "strict Farkas-valid integer conflicts must export la_generic/LraFarkas"
            );
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}
