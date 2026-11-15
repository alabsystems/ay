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
                    _ => (integer_residual_kind(terms, conflict, &clause, dt), clause),
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

/// The payload-free integer kind for a certificate-free conflict that every
/// record-time arm (and the core decomposition) declined, or `Generic`.
///
/// Such a conflict used to be recorded as `Generic`/trust and labelled only by
/// the finalize-time `promote_generic_theory_lemma_kinds_after_rewrite`, AFTER
/// the SAT refutation was reconstructed. That is too late for a conflict found
/// at decision level 0: it IS the refutation, no conflict analysis explains the
/// level-0 implications its literals rest on, and the closer that re-derives
/// them (`derive_empty_via_bounded_dpll_theory`) admits only non-trust leaves.
/// The lia-mod lattice closure (`ay_lia::lattice_refute_bridge`) returns
/// exactly such conflicts — an integer-lattice core over carry bounds implied
/// at level 0 — so a refutation the strict checker validates as
/// `IntCgCutChain` closed with a whole-problem trust lemma instead, and
/// `--rigor standard` with `:produce-proofs` answered `unknown`.
///
/// The label is asked of the same funnel finalize uses, so it is the label the
/// lemma would get there, only earlier, and only for the residual: every
/// rational arm above has already declined the conflict. Adopted only for the
/// payload-free integer kinds, whose recognizer IS the strict validator:
/// there is nothing to forge, and the strict checker re-decides the recorded
/// clause. Every other answer (a certificate kind that still needs its
/// evidence, a reordering kind) stays `Generic` for the finalize passes,
/// unchanged, and so does a guarded split the finalize
/// `promote_lia_divisibility_lemmas` upgrades to the certificate-bearing
/// `LiaGeneric` + `Divisibility` (`2y = 7`): a recorded label would let a
/// checked SAT refutation publish before that pass runs.
///
/// The funnel is asked only once its integer arm
/// ([`funnel::integer_lattice_kind`]), the funnel's sole source of the three
/// adoptable kinds, accepts the clause by itself. The arms the funnel runs
/// first include the univariate NRA decision procedure, whose root isolation
/// on a NIA conflict over 64-bit bounds costs tens of milliseconds, and this
/// recorder runs on every conflict of every check-sat, SAT ones included,
/// where no label is ever read: a 4-conflict QF_NIA `u64` overflow query went
/// from 0.05 s to 1.1 s. When the integer arm declines, the funnel cannot
/// answer an adoptable kind, so the label is `Generic` exactly as before; when
/// it accepts, the whole funnel still decides, so every established arm keeps
/// its priority and the label is unchanged.
fn integer_residual_kind(
    terms: &TermStore,
    conflict: &[TheoryLit],
    clause: &[TermId],
    dt: Option<&DatatypeRegistries<'_>>,
) -> TheoryLemmaKind {
    integer_residual_kind_with(terms, conflict, clause, || {
        let (kind, ordered) =
            infer_theory_lemma_kind_from_clause_terms_and_farkas(terms, clause, None, dt);
        (kind, matches!(ordered, Cow::Borrowed(_)))
    })
}

/// [`integer_residual_kind`] over an injected funnel, which answers `(kind,
/// whether it kept the caller's literal order)` and is asked at most once.
fn integer_residual_kind_with(
    terms: &TermStore,
    conflict: &[TheoryLit],
    clause: &[TermId],
    ask_funnel: impl FnOnce() -> (TheoryLemmaKind, bool),
) -> TheoryLemmaKind {
    if !arith_conflict_is_integer(terms, conflict)
        || funnel::integer_lattice_kind(terms, clause).is_none()
    {
        return TheoryLemmaKind::Generic;
    }
    let (kind, in_caller_order) = ask_funnel();
    let adopt = in_caller_order
        && match kind {
            TheoryLemmaKind::IntBoundLatticeGap | TheoryLemmaKind::IntCgCutChain => true,
            TheoryLemmaKind::IntGuardedSplitGap => {
                !ay_core::proof_validation::recognize_lia_divisibility(terms, clause)
            }
            _ => false,
        };
    if adopt {
        kind
    } else {
        TheoryLemmaKind::Generic
    }
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

#[cfg(test)]
#[path = "recording_dt_tests.rs"]
mod tests;
