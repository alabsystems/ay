// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-rewrite promotion of generic theory lemmas.

use std::borrow::Cow;

use ay_core::{FarkasAnnotation, Proof, ProofStep, TermStore, TheoryLemmaKind, TheoryLit};

use super::super::Executor;

impl Executor {
    /// Promote `TheoryLemmaKind::Generic` proof steps to a more specific kind
    /// when the post-rewrite clause terms allow it (#6756).
    ///
    /// This handles cases where the theory solver recorded a generic conflict
    /// (e.g., a combined ArrayEUF route) but after surface-syntax rewriting the
    /// clause is a plain integer-arithmetic contradiction that can export as
    /// `lia_generic` instead of `trust`.
    pub(in crate::executor) fn promote_generic_theory_lemma_kinds_after_rewrite(
        terms: &TermStore,
        proof: &mut Proof,
        dt: Option<&crate::theory_inference::DatatypeRegistries<'_>>,
    ) {
        use crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas;

        for step in &mut proof.steps {
            let ProofStep::TheoryLemma {
                kind,
                clause,
                farkas,
                lia,
                ..
            } = step
            else {
                continue;
            };
            if !kind.is_trust() {
                continue;
            }
            let (inferred, ordered) = infer_theory_lemma_kind_from_clause_terms_and_farkas(
                terms,
                clause,
                farkas.as_ref(),
                dt,
            );
            // Evidence-bearing annotations are positional and belong only to
            // their arithmetic certificate families. A Generic step may
            // retain stale Farkas/LIA evidence across earlier rewrites; do not
            // relabel it as EUF/DT while that payload remains authoritative.
            if (farkas.is_some() || lia.is_some())
                && !matches!(
                    inferred,
                    TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric
                )
            {
                continue;
            }
            // #trust->0 C3: a `Cow::Owned` result is the validator-ordered
            // clause an EUF classification demands; it must be adopted with
            // the kind or not at all. With a positional Farkas certificate,
            // reordering would detach it — retain the pre-C3 result instead.
            let reordered = match ordered {
                Cow::Owned(reordered) => {
                    if farkas.is_some() {
                        continue;
                    }
                    Some(reordered)
                }
                Cow::Borrowed(_) => None,
            };
            if matches!(inferred, TheoryLemmaKind::LraFarkas) && farkas.is_none() {
                promote_verified_unit_farkas(terms, clause, farkas, kind, inferred);
                continue;
            }
            if matches!(inferred, TheoryLemmaKind::LiaGeneric) && farkas.is_none() {
                if let Some(synth) =
                    crate::executor::proof_farkas::synthesize_equality_farkas(terms, clause)
                {
                    *farkas = Some(synth);
                    *kind = inferred;
                }
                continue;
            }
            // A POSITIONAL certificate outranks a payload-free integer kind.
            // `synthesize_equality_farkas` turns `(cl (not (= t c1))
            // (not (= t c2)))` into `LiaGeneric` + coefficients the exporter
            // may render as the pinned calculus's own `la_generic`, while
            // `IntGuardedSplitGap` renders as an honest `hole` — and the
            // guarded split ALSO refutes that clause (two equality rows,
            // ground residue `0 = c1 - c2`). Ask the certificate route first
            // so the split can only ever take the residual.
            if matches!(inferred, TheoryLemmaKind::IntGuardedSplitGap) && farkas.is_none() {
                if let Some(synth) =
                    crate::executor::proof_farkas::synthesize_equality_farkas(terms, clause)
                {
                    *farkas = Some(synth);
                    *kind = TheoryLemmaKind::LiaGeneric;
                    continue;
                }
            }
            if !inferred.is_trust() {
                if let Some(reordered) = reordered {
                    // The funnel enforces literal-set equality, so only the
                    // validator-mandated order changes.
                    *clause = reordered;
                }
                *kind = inferred;
            }
        }
    }
}

fn promote_verified_unit_farkas(
    terms: &TermStore,
    clause: &[ay_core::TermId],
    farkas: &mut Option<FarkasAnnotation>,
    kind: &mut TheoryLemmaKind,
    inferred: TheoryLemmaKind,
) {
    // Use exactly the coefficients that the classifier verified. Other
    // pure-LA lemmas retain the reconstruction-and-demotion flow.
    let unit = FarkasAnnotation::from_ints(&vec![1i64; clause.len()]);
    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&lit| {
            let (inner, negated) = super::strip_not_local(terms, lit);
            TheoryLit::new(inner, negated)
        })
        .collect();
    if ay_core::proof_validation::verify_farkas_conflict_lits_linear(terms, &conflict, &unit)
        .is_ok()
    {
        *farkas = Some(unit);
        *kind = inferred;
    }
}
