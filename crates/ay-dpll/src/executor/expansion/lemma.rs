// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The expansion certificate's lemma vocabulary (plan §4.1): the lemma kinds,
//! the deduplicated lemma set and the planner's decline reasons. See
//! [`super::lemma_plan`] for how a plan is built.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;

/// Lemma clauses one certificate may carry.
pub(in crate::executor) const MAX_EXPANSION_LEMMAS: usize = 4096;

/// How the certificate derives a lemma term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::executor) enum LemmaKind {
    /// L1: `(or (not Q) Q_body[v⃗])` by `forall_inst` with arguments `v⃗`.
    ForallInst {
        quantifier: TermId,
        values: Vec<TermId>,
    },
    /// L2's De Morgan half: `(or E F)` by `qnt_neg_exists`.
    NegatedExists { exists: TermId, dual: TermId },
    /// L3/L4: `(= Q Q_body[w])` by `sko` with argument `w`.
    Skolem { quantified: TermId, witness: TermId },
}

/// One lemma: the term the ground probe assumes, and its derivation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::executor) struct Lemma {
    pub(in crate::executor) term: TermId,
    pub(in crate::executor) kind: LemmaKind,
}

/// The certificate's lemma set, in creation order, deduplicated by term.
#[derive(Default, Debug)]
pub(in crate::executor) struct LemmaPlan {
    pub(in crate::executor) lemmas: Vec<Lemma>,
    pub(super) by_term: HashMap<TermId, usize>,
}

impl LemmaPlan {
    /// Replace a lemma's kind in place (mutation tests).
    #[cfg(test)]
    pub(in crate::executor) fn lemma_mut(&mut self, index: usize) -> &mut Lemma {
        &mut self.lemmas[index]
    }

    /// Re-key a lemma after a test mutated its term.
    #[cfg(test)]
    pub(in crate::executor) fn rekey(&mut self) {
        self.by_term = self
            .lemmas
            .iter()
            .enumerate()
            .map(|(at, lemma)| (lemma.term, at))
            .collect();
    }
}

/// Why no plan could be built.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum PlanDecline {
    /// An authored term and its search counterpart do not line up.
    Alignment,
    /// A quantified argument under an operator that is not a connective.
    Connective,
    /// An effective-∃ level with more than one binder (`sko` is single).
    MultiBinderSkolem,
    /// The exact substitution refused an instance.
    Substitution,
    /// A logged tuple mentions a search constant with no surface value.
    Unbound,
    /// A lemma still mentions a search constant.
    SearchConstantLeak,
    /// Too many lemmas or too much alignment work.
    Cap,
}

impl PlanDecline {
    pub(in crate::executor) fn label(self) -> &'static str {
        match self {
            Self::Alignment => "plan-alignment",
            Self::Connective => "plan-connective",
            Self::MultiBinderSkolem => "plan-multi-binder-skolem",
            Self::Substitution => "plan-substitution",
            Self::Unbound => "plan-unbound",
            Self::SearchConstantLeak => "plan-search-constant-leak",
            Self::Cap => "plan-cap",
        }
    }
}
