// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Model {
    /// Replace this model's exact certificate-ground projection atomically.
    ///
    /// Every entry is authenticated against the current term arena before any
    /// model state changes. Scoped-binder terms and unknown values are not a
    /// stable ground interpretation and make the whole package fail closed.
    /// Installing the package is a semantic model mutation, so all previously
    /// minted model-identity seals are revoked before the new pins become live.
    pub(in crate::executor) fn install_quantified_certificate_pins<I>(
        &mut self,
        terms: &TermStore,
        pins: I,
    ) -> Option<()>
    where
        I: IntoIterator<Item = (TermId, EvalValue)>,
    {
        let mut stamped = HashMap::default();
        for (term, value) in pins {
            let entry_stamp = terms.entry_stamp(term)?;
            if matches!(&value, EvalValue::Unknown)
                || dt_model::term_depends_on_scoped_binding(terms, term)
                || stamped
                    .insert(term, StampedCertificatePin { entry_stamp, value })
                    .is_some()
            {
                return None;
            }
        }

        self.quantified_confirmation_seal.revoke();
        self.revoke_quantified_grant_model();
        self.certified_total_ufs.cegqi_recompletion_epoch = None;
        self.certified_total_ufs.ground_pins = stamped;
        eval_memo_clear();
        Some(())
    }

    pub(super) fn quantified_certificate_pin(
        &self,
        terms: &TermStore,
        term: TermId,
    ) -> Option<EvalValue> {
        let pin = self.certified_total_ufs.ground_pins.get(&term)?;
        Some(
            if terms.entry_stamp(term) == Some(pin.entry_stamp)
                && !dt_model::term_depends_on_scoped_binding(terms, term)
            {
                pin.value.clone()
            } else {
                EvalValue::Unknown
            },
        )
    }

    /// Whether every certificate-ground pin still names the exact live term
    /// entry for which it was installed and is independent of the active
    /// contextual binder environment.
    ///
    /// Checking one pin lazily during evaluation is sufficient to make that
    /// read fail closed, but publication authority can depend on the package as
    /// a whole. Consumers use this predicate before retaining or installing
    /// such authority so an unvisited stale pin cannot survive in the model.
    pub(in crate::executor) fn quantified_certificate_pins_are_current(
        &self,
        terms: &TermStore,
    ) -> bool {
        self.certified_total_ufs
            .ground_pins
            .iter()
            .all(|(&term, pin)| {
                terms.entry_stamp(term) == Some(pin.entry_stamp)
                    && !dt_model::term_depends_on_scoped_binding(terms, term)
            })
    }

    #[cfg(test)]
    pub(in crate::executor) fn quantified_certificate_pin_count(&self) -> usize {
        self.certified_total_ufs.ground_pins.len()
    }

    /// Seal this exact installed model for the immediately following
    /// independent quantified-leaf handoff.
    pub(in crate::executor) fn seal_quantified_confirmation(
        &mut self,
    ) -> QuantifiedConfirmationModelEpoch {
        let epoch = QuantifiedConfirmationModelEpoch::fresh();
        self.quantified_confirmation_seal.install(&epoch);
        epoch
    }

    /// Revoke a quantified-model seal before discarding its executor-side
    /// capability or mutating theorem-relevant model data.
    pub(in crate::executor) fn revoke_quantified_confirmation(&mut self) {
        self.quantified_confirmation_seal.revoke();
    }

    /// Whether this is still the exact installed model sealed by `epoch`.
    pub(in crate::executor) fn carries_quantified_confirmation(
        &self,
        epoch: &QuantifiedConfirmationModelEpoch,
    ) -> bool {
        self.quantified_confirmation_seal.carries(epoch)
    }

    /// Seal this exact model for a durable model-relative quantified grant.
    pub(in crate::executor) fn seal_quantified_grant_model(&mut self) -> QuantifiedGrantModelEpoch {
        let epoch = QuantifiedGrantModelEpoch::fresh();
        self.quantified_grant_model_seal.install(&epoch);
        epoch
    }

    /// Revoke any durable quantified grant before mutating the exact model it
    /// names. A later theorem may seal the completed model again explicitly.
    pub(in crate::executor) fn revoke_quantified_grant_model(&mut self) {
        self.quantified_grant_model_seal.revoke();
    }

    /// Revoke every exact-model theorem before committing semantic model data.
    ///
    /// Mutation helpers use this single boundary so a direct-confirmation,
    /// durable DT/MBQI grant, or CEGQI recompletion can never outlive an
    /// in-place change to the witness it named.
    pub(in crate::executor) fn revoke_all_quantified_model_seals(&mut self) {
        self.quantified_confirmation_seal.revoke();
        self.quantified_grant_model_seal.revoke();
        self.certified_total_ufs.cegqi_recompletion_epoch = None;
    }

    /// Whether this is still the exact model named by a quantified grant.
    pub(in crate::executor) fn carries_quantified_grant_model(
        &self,
        epoch: &QuantifiedGrantModelEpoch,
    ) -> bool {
        self.quantified_grant_model_seal.carries(epoch)
    }
}
