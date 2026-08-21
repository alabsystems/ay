// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registry-aware theory-conflict recording.

use super::*;

/// Record a conflict after datatype-aware classification, preserving the
/// established weakening and trust fallbacks.
pub(crate) fn record_theory_conflict_unsat_with_annotation_and_dt(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    dt: Option<&DatatypeRegistries<'_>>,
) -> (Option<ProofId>, Option<ay_core::TheoryLemmaProof>) {
    if !tracker.is_enabled() {
        return (None, None);
    }
    let Some(clause) = build_blocking_clause_terms(negations, conflict) else {
        let raw_clause = conflict.iter().map(|lit| lit.term).collect::<Vec<_>>();
        return (tracker.add_explicit_trust_lemma(raw_clause), None);
    };
    let (kind, ordered_clause) = if let Some(terms) = terms {
        match classify_whole_conflict(terms, negations, conflict, &clause, dt) {
            Some(result) => result,
            None => {
                if let Some((core_kind, core_clause, full_clause)) =
                    classifiable_core_decomposition(terms, negations, conflict, &clause)
                {
                    let id = tracker.add_theory_lemma_weakened(core_clause, core_kind, full_clause);
                    return (id, None);
                }
                match dt {
                    Some(dt)
                        if clause_mentions_registered_datatype(terms, &clause, dt.datatypes)
                            && ay_proof::recognize_datatype_ground_conflict(
                                terms,
                                &clause,
                                dt.datatypes,
                                dt.ctor_selectors,
                            ) =>
                    {
                        (TheoryLemmaKind::DatatypeGroundConflict, clause)
                    }
                    _ => (TheoryLemmaKind::Generic, clause),
                }
            }
        }
    } else {
        (TheoryLemmaKind::Generic, clause)
    };
    let farkas = matches!(
        kind,
        TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas
    )
    .then(|| FarkasAnnotation::from_ints(&vec![1i64; ordered_clause.len()]));
    let id = match (kind, farkas.as_ref()) {
        (TheoryLemmaKind::Generic, _) => tracker.add_explicit_trust_lemma(ordered_clause.clone()),
        (TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas, Some(unit_farkas)) => tracker
            .add_theory_lemma_with_farkas_and_kind(
                ordered_clause.clone(),
                unit_farkas.clone(),
                kind,
            ),
        _ => tracker.add_theory_lemma_with_kind(ordered_clause.clone(), kind),
    };
    let annotation = id.map(|_| ay_core::TheoryLemmaProof {
        clause: ordered_clause,
        kind,
        farkas,
        lia: None,
    });
    (id, annotation)
}

/// Record a Farkas conflict, delegating certificate-free conflicts to the
/// datatype-aware classifier.
pub(crate) fn record_theory_conflict_unsat_with_farkas_and_annotation_and_dt(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &TheoryConflict,
    dt: Option<&DatatypeRegistries<'_>>,
) -> (Option<ProofId>, Option<ay_core::TheoryLemmaProof>) {
    if !tracker.is_enabled() {
        return (None, None);
    }
    let Some(farkas) = conflict.farkas.clone() else {
        if build_blocking_clause_terms(negations, &conflict.literals).is_none() {
            return (None, None);
        }
        return record_theory_conflict_unsat_with_annotation_and_dt(
            tracker,
            terms,
            negations,
            &conflict.literals,
            dt,
        );
    };
    let Some(clause) = build_blocking_clause_terms(negations, &conflict.literals) else {
        return (None, None);
    };
    let kind = terms.map_or(TheoryLemmaKind::Generic, |terms| {
        classify_arith_conflict_kind(terms, &conflict.literals, Some(&farkas))
    });
    let (id, recorded_farkas) = match kind {
        TheoryLemmaKind::Generic => (tracker.add_explicit_trust_lemma(clause.clone()), None),
        TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas => (
            tracker.add_theory_lemma_with_farkas_and_kind(clause.clone(), farkas.clone(), kind),
            Some(farkas),
        ),
        _ => (
            tracker.add_theory_lemma_with_kind(clause.clone(), kind),
            None,
        ),
    };
    let annotation = id.map(|_| ay_core::TheoryLemmaProof {
        clause,
        kind,
        farkas: recorded_farkas,
        lia: None,
    });
    (id, annotation)
}
