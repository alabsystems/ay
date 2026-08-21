// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Owner arbitration for the terminal finite-model SAT producer.

use ay_core::TermId;

use crate::executor::Executor;

impl Executor {
    /// Establish the finite-model certificate only when no exact-current
    /// quantified owner already controls the publication model.
    ///
    /// A positive FP `exists` can bypass every earlier quantifier-loop
    /// producer and arrive as a ground-core Sat. This helper is called at its
    /// last establishment point before strict validation. It must never
    /// displace a stronger/earlier affine owner or parked certificate model.
    /// Stale routing bits are not owners and retain the funnel's fail-closed
    /// cleanup.
    pub(super) fn try_install_unowned_finite_model_sat_certificate(
        &mut self,
        publication_roots: &[TermId],
    ) -> bool {
        let finite_table_owner_current = self.finite_table_cert_grant_active
            && self
                .finite_table_cert_witness_state
                .as_ref()
                .is_some_and(|state| {
                    state.is_pending_current_for(self, publication_roots)
                        || self.last_model.as_ref().is_some_and(|model| {
                            state.is_installed_current_for(self, publication_roots, model)
                        })
                });
        let const_interp_owner_current = self.const_interp_cert_grant_active
            && self
                .const_interp_cert_witness_state
                .as_ref()
                .is_some_and(|state| {
                    state.is_pending_current_for(self, publication_roots)
                        || self.last_model.as_ref().is_some_and(|model| {
                            state.is_installed_current_for(self, publication_roots, model)
                        })
                });
        let bv_owner_current = self.bv_quantifier_full_domain_proof
            && self
                .bv_quantifier_full_domain_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, publication_roots));
        let cegqi_owner_current = self
            .cegqi_uf_recompletion_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(self, publication_roots));
        let quantified_owner_current = self
            .has_current_model_free_mbqi_sat_authority(publication_roots)
            || self.has_current_model_bound_quantified_sat_authority(publication_roots)
            || finite_table_owner_current
            || const_interp_owner_current
            || bv_owner_current
            || cegqi_owner_current;
        !quantified_owner_current && self.try_finite_model_sat_certificate()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FINITE_ELIGIBLE: &str = r#"
        (set-logic BVFPLRA)
        (declare-fun Y () (_ FloatingPoint 8 24))
        (declare-fun S () (_ FloatingPoint 8 24))
        (assert (not (and (exists ((d (_ FloatingPoint 8 24)))
                            (and (fp.geq d (_ +zero 8 24))
                                 (fp.leq d ((_ to_fp 8 24) RNE 16.0))
                                 (= (fp.sub RNE ((_ to_fp 8 24) RNE (_ bv0 32)) d) Y)))
                          (= ((_ to_fp 8 24) RNE (_ bv0 32)) S))))
    "#;

    fn fixture() -> Executor {
        let commands = ay_frontend::parse(FINITE_ELIGIBLE).expect("parse owner fixture");
        let mut executor = Executor::new();
        for command in &commands {
            assert!(
                executor
                    .execute(command)
                    .expect("execute owner fixture")
                    .is_none(),
                "fixture contains declarations and assertions only"
            );
        }
        executor.last_model = Some(crate::executor::model::Model::empty());
        executor.last_model_validated = true;
        executor
    }

    #[test]
    fn stronger_current_authority_prevents_finite_producer_replacement() {
        // Positive control: this exact state really would install the finite
        // witness without an owner. The owner subcases below therefore
        // discriminate the guard from an incidental producer decline.
        let mut unowned = fixture();
        let roots = unowned.ctx.assertions.clone();
        assert!(unowned.try_install_unowned_finite_model_sat_certificate(&roots));
        assert!(unowned.has_current_model_bound_quantified_sat_authority(&roots));

        let mut model_bound = fixture();
        let roots = model_bound.ctx.assertions.clone();
        let evidence =
            crate::executor::mbqi::CheckedDtSatAuthority::for_test(&mut model_bound, &roots)
                .expect("test model can carry a model-bound owner");
        assert!(model_bound.install_dt_sat_authority(evidence));
        assert!(!model_bound.try_install_unowned_finite_model_sat_certificate(&roots));
        assert!(model_bound.dt_cert_grant_active);
        assert!(model_bound
            .dt_cert_query_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(&model_bound, &roots)));
        assert!(!model_bound.bv_quantifier_full_domain_proof);

        let mut model_free_bv = fixture();
        let roots = model_free_bv.ctx.assertions.clone();
        let evidence = crate::executor::bv_mbqi::CheckedBvFullDomainSatAuthority::for_test(
            &model_free_bv,
            &roots,
        );
        assert!(model_free_bv.install_bv_full_domain_sat_authority(evidence));
        assert!(!model_free_bv.try_install_unowned_finite_model_sat_certificate(&roots));
        assert!(model_free_bv.bv_quantifier_full_domain_proof);
        assert!(model_free_bv
            .bv_quantifier_full_domain_query_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(&model_free_bv, &roots)));
        assert!(
            !model_free_bv.has_current_model_bound_quantified_sat_authority(&roots),
            "the generic BV owner is intentionally model-free"
        );

        let mut parked_table = fixture();
        let roots = parked_table.ctx.assertions.clone();
        let package = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &parked_table,
            &roots,
            crate::executor::model::Model::empty(),
            Default::default(),
        )
        .expect("test roots can carry a parked table owner");
        parked_table.finite_table_cert_grant_active = true;
        parked_table.finite_table_cert_witness_state = Some(package);
        assert!(!parked_table.try_install_unowned_finite_model_sat_certificate(&roots));
        assert!(parked_table.finite_table_cert_grant_active);
        assert!(parked_table
            .finite_table_cert_witness_state
            .as_ref()
            .is_some_and(|state| state.is_pending_current_for(&parked_table, &roots)));
        assert!(!parked_table.bv_quantifier_full_domain_proof);
    }
}
