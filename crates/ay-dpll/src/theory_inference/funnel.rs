// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-checkable classification for materialized theory lemma clauses.

use std::borrow::Cow;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{FarkasAnnotation, TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit};

use crate::proof_tracker::ProofTracker;

use super::{
    arith_conflict_is_integer, blocking_clause_to_conflict_lits, classify_arith_conflict_kind,
    conflict_all_arith_literals, euf, fp_ground_eval_applies, opaque_arith_farkas_valid,
};

/// Owned datatype registry data for the funnel's DT recognition (#trust->0
/// C3): `(datatype registry, constructor→selector registry)` in exactly the
/// shapes `check_proof_strict_with_datatypes` consumes
/// (`datatype_decls_for_strict_proof` / `ctor_selector_decls_for_strict_proof`).
pub(crate) type DatatypeRegistryData = (Vec<(String, Vec<String>)>, Vec<(String, Vec<String>)>);

/// Borrowed view of the datatype registries the funnel's DT recognizers
/// validate against (#trust->0 C3). Runtime datatype terms carry
/// `Sort::Uninterpreted`, so DT recognition is impossible from the `TermStore`
/// alone — callers that hold the elaboration context supply the same
/// registries the mint-time strict check uses; callers that do not pass
/// `None` and DT shapes stay `Generic` there (fail-closed, never a shape-only
/// promotion).
pub(crate) struct DatatypeRegistries<'a> {
    pub(crate) datatypes: &'a [(String, Vec<String>)],
    pub(crate) ctor_selectors: &'a [(String, Vec<String>)],
}

impl<'a> DatatypeRegistries<'a> {
    pub(crate) fn from_data(data: &'a DatatypeRegistryData) -> Self {
        Self {
            datatypes: &data.0,
            ctor_selectors: &data.1,
        }
    }
}

/// Build the funnel's datatype registries from the elaboration context, or
/// `None` when the problem declares no datatypes — the common case, which
/// skips building the two registry `Vec`s per lemma batch (#trust->0 C3).
///
/// A free function over `&Context` (not an `Executor` method) so the pipeline
/// macros can call it with a FIELD borrow of `$self.ctx` while `$self`'s other
/// fields are mutably borrowed. The data is byte-identical to what the
/// mint-time strict check consumes (`datatype_decls_for_strict_proof` /
/// `ctor_selector_decls_for_strict_proof` build from the same two iterators),
/// so funnel acceptance is re-decided identically at certification.
pub(crate) fn dt_funnel_registry_data(ctx: &ay_frontend::Context) -> Option<DatatypeRegistryData> {
    ctx.datatype_iter().next()?;
    Some((
        ctx.datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect(),
        ctx.ctor_selectors_iter()
            .map(|(ctor, selectors)| (ctor.clone(), selectors.clone()))
            .collect(),
    ))
}

/// Record an already-materialized, polarity-exact theory lemma clause through
/// the central classifier funnel and return `(kind, recorded_clause)`
/// (#trust->0 C3).
///
/// Shared recorder for the pipeline-macro residual arms (the C1 sites 1-9):
/// runs [`infer_theory_lemma_kind_from_clause_terms_and_farkas`], ADOPTS the
/// funnel's reordered clause when recognition reordered it (EUF validators are
/// order-sensitive — recording the caller's order under a kind whose
/// validator demands the funnel's order is the C1-review defect class), and
/// records through the tracker exactly as the macro arms historically did.
/// Evidence-requiring arithmetic kinds are normalized to `Generic` here,
/// before both tracker recording and the returned trace annotation, so those
/// two authorities cannot disagree. The caller MUST use the
/// returned clause for any trace-indexed `TheoryLemmaProof` annotation so the
/// recorded artifact is the one the validator accepted.
pub(crate) fn record_funnel_classified_lemma(
    tracker: &mut ProofTracker,
    terms: &TermStore,
    clause: Vec<TermId>,
    dt: Option<&DatatypeRegistryData>,
) -> (TheoryLemmaKind, Vec<TermId>) {
    let dt_view = dt.map(DatatypeRegistries::from_data);
    let (kind, ordered) = infer_theory_lemma_kind_from_clause_terms_and_farkas(
        terms,
        &clause,
        None,
        dt_view.as_ref(),
    );
    let clause = match ordered {
        Cow::Owned(reordered) => reordered,
        Cow::Borrowed(_) => clause,
    };
    let kind = if matches!(
        kind,
        TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric
    ) {
        TheoryLemmaKind::Generic
    } else {
        kind
    };
    match kind {
        TheoryLemmaKind::Generic => {
            let _ = tracker.add_explicit_trust_lemma(clause.clone());
        }
        _ => {
            let _ = tracker.add_theory_lemma_with_kind(clause.clone(), kind);
        }
    }
    (kind, clause)
}

/// Infer the most specific proof kind available for an already-materialized
/// theory lemma clause, using semantic Farkas validation when coefficients are
/// already available, plus datatype-registry-backed DT recognition when the
/// caller can supply the registries (#trust->0 C3).
///
/// Returns `(kind, clause_to_record)`. The second component is
/// `Cow::Borrowed(clause)` whenever the caller's literal order is exactly what
/// the kind's strict validator accepts, and `Cow::Owned` ONLY when recognition
/// had to REORDER the clause (EUF kinds: conclusion-last, premises in
/// validator order). Call sites MUST record the returned clause, never the
/// original, for any `Cow::Owned` result — a kind whose validator rejects the
/// recorded order is the C1-review defect class. The owned clause is always a
/// permutation of the input's literal SET (enforced in
/// [`infer_euf_lemma_from_clause`]), so trace-side set-equivalence
/// authentication is unaffected.
#[must_use]
pub(crate) fn infer_theory_lemma_kind_from_clause_terms_and_farkas<'c>(
    terms: &TermStore,
    clause: &'c [TermId],
    farkas: Option<&FarkasAnnotation>,
    dt: Option<&DatatypeRegistries<'_>>,
) -> (TheoryLemmaKind, Cow<'c, [TermId]>) {
    let kind = infer_theory_lemma_kind_in_caller_order(terms, clause, farkas);
    if kind != TheoryLemmaKind::Generic {
        return (kind, Cow::Borrowed(clause));
    }
    // A positional arithmetic certificate that did not validate as an
    // arithmetic kind must never flow into the EUF/DT recognition arms. Those
    // validators do not consume the payload, while downstream trace rebinding
    // and external printing do; retaining it would create split authority.
    if farkas.is_some() {
        return (TheoryLemmaKind::Generic, Cow::Borrowed(clause));
    }

    // #trust->0 C3: EUF recognition. Runs strictly on the Generic residual so
    // no established kind's priority changes. Recognition may REORDER the
    // clause (validator-canonical order); acceptance is decided by the strict
    // checker's own validator on the reordered clause, never by shape alone.
    if let Some((kind, ordered)) = infer_euf_lemma_from_clause(terms, clause) {
        if ordered == clause {
            return (kind, Cow::Borrowed(clause));
        }
        return (kind, Cow::Owned(ordered));
    }

    // #trust->0 C3: DT recognition, registry-gated fail-closed. The DT
    // validators flatten/match set-wise, so the caller's order IS the
    // validated artifact — no reorder ever happens here.
    if let Some(dt) = dt {
        if let Some(kind) = infer_dt_lemma_kind(terms, clause, dt) {
            return (kind, Cow::Borrowed(clause));
        }
    }

    (TheoryLemmaKind::Generic, Cow::Borrowed(clause))
}

/// The pre-C3 funnel body: every classification that accepts the clause in
/// the CALLER's literal order (arith/array/string/FP/regex/NRA and the
/// opaque-atom Farkas rescue). Split out so the reordering arms in
/// [`infer_theory_lemma_kind_from_clause_terms_and_farkas`] visibly run only
/// on the `Generic` residual.
#[must_use]
fn infer_theory_lemma_kind_in_caller_order(
    terms: &TermStore,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> TheoryLemmaKind {
    let conflict = blocking_clause_to_conflict_lits(terms, clause);

    if let Some(kind) = infer_arithmetic_prefix(terms, &conflict, farkas) {
        return kind;
    }
    if let Some(kind) = infer_closed_theory_kind(terms, clause) {
        return kind;
    }
    if arith_conflict_is_integer(terms, &conflict) {
        return TheoryLemmaKind::LiaGeneric;
    }
    infer_opaque_farkas_kind(terms, &conflict, farkas).unwrap_or(TheoryLemmaKind::Generic)
}

/// Preserve the established arithmetic classifications before the C3
/// recognizers inspect the residual.
fn infer_arithmetic_prefix(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: Option<&FarkasAnnotation>,
) -> Option<TheoryLemmaKind> {
    if let Some(farkas) = farkas {
        let kind = classify_arith_conflict_kind(terms, conflict, Some(farkas));
        if kind != TheoryLemmaKind::Generic {
            return Some(kind);
        }
    }
    if conflict.is_empty() || !conflict_all_arith_literals(terms, conflict) {
        return None;
    }
    let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; conflict.len()]);
    (classify_arith_conflict_kind(terms, conflict, Some(&unit_farkas))
        == TheoryLemmaKind::LraFarkas)
        .then_some(TheoryLemmaKind::LraFarkas)
}

/// Recognize strict-checkable closed theory facts in their historical priority
/// order. Every recognizer is shared with the strict checker.
fn infer_closed_theory_kind(terms: &TermStore, clause: &[TermId]) -> Option<TheoryLemmaKind> {
    if let Some(kind) = ay_proof::recognize_array_theory_lemma(terms, clause) {
        return Some(kind);
    }
    if ay_proof::recognize_string_ground_eval(terms, clause) {
        return Some(TheoryLemmaKind::StringGroundEval);
    }
    if fp_ground_eval_applies(terms, clause) {
        return Some(TheoryLemmaKind::FpGroundEval);
    }
    if ay_proof::recognize_regex_intersect_empty(terms, clause) {
        return Some(TheoryLemmaKind::RegexIntersectEmpty);
    }
    if ay_proof::recognize_nra_univariate_unsat(terms, clause) {
        return Some(TheoryLemmaKind::NraUnivariateUnsat);
    }
    if ay_proof::recognize_nra_interval_unsat(terms, clause) {
        return Some(TheoryLemmaKind::NraIntervalUnsat);
    }
    None
}

/// Run the opaque-atom Farkas rescue only after every earlier classification
/// declined the clause.
fn infer_opaque_farkas_kind(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: Option<&FarkasAnnotation>,
) -> Option<TheoryLemmaKind> {
    let valid = match farkas {
        Some(farkas) => opaque_arith_farkas_valid(terms, conflict, farkas),
        None if !conflict.is_empty() => {
            let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; conflict.len()]);
            opaque_arith_farkas_valid(terms, conflict, &unit_farkas)
        }
        None => false,
    };
    valid.then_some(TheoryLemmaKind::LraFarkas)
}

/// Try to classify a materialized clause as an EUF lemma
/// (congruent-pred / congruent / transitive / reflexive), returning the kind
/// and the VALIDATOR-ORDERED clause (#trust->0 C3).
///
/// The conflict-lane classifier (`euf::infer_euf_lemma`) consumes a
/// `negations` map plus conflict-polarity literals; the funnel has only the
/// materialized clause. Both are reconstructed soundly from the clause
/// itself: a literal `(not X)` IS the negation of `X` by term identity, which
/// covers every lookup the inference performs — it only ever negates terms
/// that were asserted TRUE in the conflict, i.e. exactly the terms appearing
/// `Not`-wrapped in the blocking clause. (This mirrors
/// `blocking_clause_to_conflict_lits`, the inverse of
/// `build_blocking_clause_terms`.)
///
/// Two fail-closed gates keep the classifier equal to the validator:
/// 1. the returned clause must be a permutation of the input's literal SET —
///    an inference that dropped literals (e.g. the reflexive-conclusion
///    shortcut discarding premises) would otherwise silently strengthen a
///    trace-recorded clause and break set-equivalence authentication;
/// 2. the kind is returned ONLY when the strict checker's own validator
///    accepts the reordered clause (`ay_proof::recognize_euf_*`), so a kind
///    whose validator would reject the recorded order — the C1-review defect
///    class — cannot be produced.
fn infer_euf_lemma_from_clause(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    let mut negations: HashMap<TermId, TermId> = HashMap::default();
    for &lit in clause {
        if let TermData::Not(inner) = terms.get(lit) {
            negations.insert(*inner, lit);
        }
    }
    let conflict = blocking_clause_to_conflict_lits(terms, clause);
    let (kind, ordered) = euf::infer_euf_lemma(terms, &negations, &conflict)?;

    // Gate 1: same literal set (order-insensitive, duplicate-insensitive —
    // the same comparison the trace lane's set-equivalence authentication
    // performs).
    let mut input_set: Vec<TermId> = clause.to_vec();
    input_set.sort_unstable();
    input_set.dedup();
    let mut ordered_set: Vec<TermId> = ordered.clone();
    ordered_set.sort_unstable();
    ordered_set.dedup();
    if input_set != ordered_set {
        return None;
    }

    // Gate 2: the strict validator itself accepts the reordered clause.
    let accepted = match kind {
        TheoryLemmaKind::EufCongruent => ay_proof::recognize_euf_congruent(terms, &ordered),
        TheoryLemmaKind::EufCongruentPred => {
            ay_proof::recognize_euf_congruent_pred(terms, &ordered)
        }
        TheoryLemmaKind::EufTransitive => ay_proof::recognize_euf_transitive(terms, &ordered),
        TheoryLemmaKind::EufReflexive => ay_proof::recognize_euf_reflexive(terms, &ordered),
        _ => false,
    };
    accepted.then_some((kind, ordered))
}

/// Try to classify a materialized clause as a strict-checkable datatype
/// lemma under the supplied registries (#trust->0 C3).
///
/// Recognition IS the corresponding strict validator run on exactly this
/// clause with exactly these registries (`validate_*(..).is_ok()` behind each
/// `ay_proof::recognize_datatype_*`), fed from the same elaboration-context
/// helpers the mint-time strict check uses — so acceptance is re-decided
/// identically at certification (the C1.iv precedent). Probe order matches
/// C1.iv (`record_dt_axiom_theory_lemmas`): selector projection, tester
/// evaluation (the `_with_selectors` variant, matching the checker's
/// `DatatypeTesterEval` dispatch which always receives both registries), then
/// constructor distinctness. Everything declined stays `Generic`.
fn infer_dt_lemma_kind(
    terms: &TermStore,
    clause: &[TermId],
    dt: &DatatypeRegistries<'_>,
) -> Option<TheoryLemmaKind> {
    if ay_proof::recognize_datatype_selector_project(terms, clause, dt.ctor_selectors) {
        return Some(TheoryLemmaKind::DatatypeSelectorProject);
    }
    if ay_proof::recognize_datatype_tester_eval_with_selectors(
        terms,
        clause,
        dt.datatypes,
        dt.ctor_selectors,
    ) {
        return Some(TheoryLemmaKind::DatatypeTesterEval);
    }
    if ay_proof::recognize_datatype_distinct(terms, clause, dt.datatypes) {
        return Some(TheoryLemmaKind::DatatypeDistinct);
    }
    // Direct acyclicity (occurs check): the recognizer IS the strict
    // validator with the same registries, so acceptance is re-decided
    // identically at certification.
    if ay_proof::recognize_datatype_acyclic_direct(terms, clause, dt.datatypes) {
        return Some(TheoryLemmaKind::DatatypeAcyclicDirect);
    }
    None
}
