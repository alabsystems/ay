// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Installation of checked model-bound quantified SAT grants.

use ay_core::TermId;

use super::{QuantifiedProjectionBindings, QuantifiedSatAuthorityGrant};
use crate::executor::mbqi::CheckedMbqiSatAuthority;
use crate::executor::model::QuantifiedGrantModelEpoch;
use crate::executor::quantifier_loop::result_mapping::{
    CheckedExactArrayNegationSatAuthority, CheckedFiniteExpansionSatAuthority,
};
use crate::executor::Executor;

impl Executor {
    /// Consume a successful MBQI solver certificate and install its exact
    /// checked root window.
    ///
    /// The exact structural closed-sentence lane must not call this broad
    /// constructor. It installs only through
    /// [`Self::install_exact_closed_sentence_sat_authority`], which consumes
    /// the checker-minted evidence carrying its immutable root window.
    pub(in crate::executor) fn install_mbqi_sat_authority(
        &mut self,
        evidence: CheckedMbqiSatAuthority,
    ) -> bool {
        self.revoke_mbqi_sat_authority();
        let Some((roots, model_epoch, projection_bindings)) = evidence.into_current_roots(self)
        else {
            return false;
        };
        let bindings = projection_bindings.map_or(
            QuantifiedProjectionBindings::None,
            QuantifiedProjectionBindings::Aggregate,
        );
        self.install_model_bound_mbqi_grant(&roots, model_epoch, bindings)
    }

    /// Consume an independently replayed canonical finite-domain expansion
    /// proof for one exact authored root window and exact retained model.
    pub(in crate::executor) fn install_finite_expansion_sat_authority(
        &mut self,
        evidence: CheckedFiniteExpansionSatAuthority,
    ) -> bool {
        self.revoke_bv_full_domain_sat_authority();
        let Some((roots, model_epoch)) = evidence.into_current_roots(self) else {
            return false;
        };
        let Some(grant) = QuantifiedSatAuthorityGrant::for_checked_model_roots(
            self,
            &roots,
            model_epoch,
            QuantifiedProjectionBindings::None,
        ) else {
            return false;
        };
        self.bv_quantifier_full_domain_proof = true;
        self.bv_quantifier_full_domain_query_grant = Some(grant);
        true
    }

    /// Consume independently replayed pointwise-array-negation authority.
    pub(in crate::executor) fn install_exact_array_negation_sat_authority(
        &mut self,
        evidence: CheckedExactArrayNegationSatAuthority,
    ) -> bool {
        self.revoke_mbqi_sat_authority();
        let Some((roots, model_epoch)) = evidence.into_current_roots(self) else {
            return false;
        };
        self.install_model_bound_mbqi_grant(&roots, model_epoch, QuantifiedProjectionBindings::None)
    }

    fn install_model_bound_mbqi_grant(
        &mut self,
        roots: &[TermId],
        model_epoch: QuantifiedGrantModelEpoch,
        bindings: QuantifiedProjectionBindings,
    ) -> bool {
        let Some(grant) = QuantifiedSatAuthorityGrant::for_checked_model_roots(
            self,
            roots,
            model_epoch,
            bindings,
        ) else {
            return false;
        };
        self.mbqi_sat_cert_grant_active = true;
        self.mbqi_sat_cert_query_grant = Some(grant);
        true
    }
}
