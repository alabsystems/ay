// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The terms a document can print, for the document-canonical bridge's
//! ancestor guard.
//!
//! [`super::document_canonical`] declines a term that is a strict descendant
//! of an overridden term: that override would keep embedding the authored
//! text around a confined term, so one internal term would ship two spellings
//! in steps that meet (`strict_descendants_of_overridden_terms`). An override
//! on a term the proof never mentions embeds nothing, though: the printer
//! renders only the terms of the proof's own steps and their subterms.
//!
//! The front end records such overrides as a by-product of one authored
//! assertion: `(assert (not (distinct x y)))` elaborates to `(= x y)` and also
//! spells the subterm `(distinct x y)` onto the internal `(not (= x y))`, a
//! strict ANCESTOR of the assumed term. MEASURED at `e9ba9acac` on that
//! assertion with `(assert (> x (+ y 2)))`: the refutation uses `(= x y)` as a
//! `cong` premise and never mentions `(not (= x y))`, yet the guard withheld
//! the bridge, the `assume` printed `(not (distinct x y))` document-wide and
//! the printer refused the publication ("surface congruence premise is not a
//! printed equality"). `(assert (not (not (= (* 3 m1) x1))))` under a `cong`
//! was refused the same way.
//!
//! So the guard reads only overridden terms the proof prints. Planning
//! records the proof's top-level terms only ([`printed_proof_roots`]); the
//! bounded walk below them runs when the document-canonical fallback first
//! asks, exactly where the unfiltered guard ran before, so a refusal that
//! never reaches that fallback pays for no walk. A proof the walk cannot read
//! completely (a binder, a subproof binding variables, a Skolem witness whose
//! `choice` body prints without being a child, an unknown step shape, a walk
//! over its cap) keeps the guard over every override.

use super::*;

/// Node cap on the walk over the proof's terms; over it, every override
/// counts as printed.
const MAX_PRINTED_PROOF_TERMS: usize = 1 << 20;

/// The terms the steps of `proof` mention at top level, or `None` for a step
/// shape this reader does not know.
pub(super) fn printed_proof_roots(proof: &Proof) -> Option<Vec<TermId>> {
    let mut roots: Vec<TermId> = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => roots.push(*term),
            ProofStep::Resolution { clause, pivot, .. } => {
                roots.extend(clause.iter().copied());
                roots.push(*pivot);
            }
            ProofStep::TheoryLemma { clause, .. } => roots.extend(clause.iter().copied()),
            ProofStep::NraSos {
                clause,
                certificate,
            } => {
                roots.extend(clause.iter().copied());
                roots.extend(certificate.basis.iter().flatten().copied());
            }
            ProofStep::Step { clause, args, .. } => {
                roots.extend(clause.iter().copied());
                roots.extend(args.iter().copied());
            }
            // A subproof binding variables prints its steps under binders.
            ProofStep::Anchor { variables, .. } if variables.is_empty() => {}
            _ => return None,
        }
    }
    Some(roots)
}

impl AlethePrinter<'_> {
    /// Every term below `roots` (inclusive), or `None` when the walk is over
    /// its cap or meets a binder, a `let`, or a Skolem witness (whose `choice`
    /// body the document prints without it being a child).
    pub(super) fn printed_terms_below(&self, roots: &[TermId]) -> Option<HashSet<TermId>> {
        let mut stack = roots.to_vec();
        let mut printed: HashSet<TermId> = HashSet::default();
        let mut complete = true;
        while let Some(term) = stack.pop() {
            if !printed.insert(term) {
                continue;
            }
            if printed.len() > MAX_PRINTED_PROOF_TERMS
                || matches!(
                    self.terms.get(term),
                    TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
                )
                || self.terms.skolem_choice(term).is_some()
                || self.skolem_overrides.borrow().contains_key(&term)
            {
                complete = false;
                break;
            }
            stack.extend(self.terms.children(term));
        }
        self.charge(printed.len() as u64);
        complete.then_some(printed)
    }

    /// `strict_descendants_of_overridden_terms` over the overridden terms the
    /// proof below `roots` prints, or over every overridden term when that
    /// proof is not read completely; `None` when a walk exceeds its cap.
    pub(super) fn strict_descendants_of_printed_overridden_terms(
        &self,
        roots: &[TermId],
    ) -> Option<HashSet<TermId>> {
        let Some(printed) = self.printed_terms_below(roots) else {
            return self.strict_descendants_of_overridden_terms();
        };
        let mut descendants: HashSet<TermId> = HashSet::default();
        let Some(overrides) = self.term_overrides else {
            return Some(descendants);
        };
        let mut stack: Vec<TermId> = Vec::new();
        for &root in overrides.keys() {
            if printed.contains(&root) {
                stack.extend(self.terms.children(root));
            }
        }
        while let Some(term) = stack.pop() {
            if !descendants.insert(term) {
                continue;
            }
            if descendants.len() > MAX_PRINTED_PROOF_TERMS {
                return None;
            }
            stack.extend(self.terms.children(term));
        }
        self.charge(descendants.len() as u64);
        Some(descendants)
    }
}
