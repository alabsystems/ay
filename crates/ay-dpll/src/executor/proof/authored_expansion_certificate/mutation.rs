// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test-only certificate mutations that the strict installation boundary
//! must refuse (`executor_tests/quantifier/qlra/m3_unsat_cert.rs`): none of
//! them may ever publish.

use ay_core::term::TermData;

use crate::executor::expansion::lemma_plan::{LemmaKind, LemmaPlan};
use crate::executor::Executor;

/// One armed mutation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum ExpansionCertMutation {
    #[default]
    None,
    /// Every lemma is asserted and "derived" as its bare consequence.
    FlipLemmaToFact,
    /// A lossy proxy map (every proxy renames to the first quantifier); the
    /// round-trip check must catch it.
    LossyProxy,
    /// The same lossy proxy map with the round-trip check DROPPED: the
    /// installation boundary must refuse the mis-renamed proof.
    DropRoundTrip,
    /// Every Real `forall_inst` argument is replaced; the lemma terms (and
    /// so the probe's refutation) are unchanged.
    ForgeTuple,
}

thread_local! {
    static MUTATION: std::cell::Cell<ExpansionCertMutation> =
        const { std::cell::Cell::new(ExpansionCertMutation::None) };
}

/// Arm a certificate mutation on this thread until the guard drops.
pub(crate) fn set_expansion_cert_mutation(mutation: ExpansionCertMutation) -> MutationGuard {
    MUTATION.with(|cell| cell.set(mutation));
    MutationGuard
}

/// Disarms [`set_expansion_cert_mutation`] on drop.
pub(crate) struct MutationGuard;

impl Drop for MutationGuard {
    fn drop(&mut self) {
        MUTATION.with(|cell| cell.set(ExpansionCertMutation::None));
    }
}

/// The armed mutation.
pub(super) fn mutation() -> ExpansionCertMutation {
    MUTATION.with(std::cell::Cell::get)
}

impl Executor {
    /// Apply the armed test mutation to the plan.
    pub(super) fn mutated_expansion_plan(&mut self, mut plan: LemmaPlan) -> LemmaPlan {
        match mutation() {
            ExpansionCertMutation::FlipLemmaToFact => {
                // Every lemma becomes its bare consequence (`Q_body[v⃗]`,
                // `F`, `Q_body[w]`): a STRONGER probe set, still "derived"
                // by the lemma's rule over the wrong clause.
                for index in 0..plan.lemmas.len() {
                    let lemma = plan.lemma_mut(index);
                    if let TermData::App(_, args) = self.ctx.terms.get(lemma.term) {
                        if args.len() == 2 {
                            lemma.term = args[1];
                        }
                    }
                }
                plan.rekey();
            }
            ExpansionCertMutation::ForgeTuple => {
                let forged = self
                    .ctx
                    .terms
                    .mk_rational(num_rational::BigRational::new(7.into(), 3.into()));
                for index in 0..plan.lemmas.len() {
                    let lemma = plan.lemma_mut(index);
                    if let LemmaKind::ForallInst { values, .. } = &mut lemma.kind {
                        for value in values.iter_mut() {
                            if *value != forged
                                && *self.ctx.terms.sort(*value) == ay_core::Sort::Real
                            {
                                *value = forged;
                            }
                        }
                    }
                }
            }
            ExpansionCertMutation::LossyProxy
            | ExpansionCertMutation::DropRoundTrip
            | ExpansionCertMutation::None => {}
        }
        plan
    }
}
