// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Installation of checked model-bound quantified SAT grants.

use ay_core::TermId;

use super::{QuantifiedProjectionBindings, QuantifiedSatAuthorityGrant};
use crate::executor::bv_mbqi::CheckedBvFullDomainSatAuthority;
use crate::executor::mbqi::CheckedMbqiSatAuthority;
use crate::executor::model::{Model, QuantifiedGrantModelEpoch};
use crate::executor::quantifier_loop::result_mapping::{
    CheckedExactArrayNegationSatAuthority, CheckedFiniteExpansionSatAuthority,
};
use crate::executor::Executor;

impl QuantifiedSatAuthorityGrant {
    /// Build a model-bound grant against an uninstalled staged model.
    ///
    /// The ordinary constructor reads `executor.last_model`, which is exactly
    /// the wrong ordering for an atomic replacement: installing the candidate
    /// before every fallible source/root/output check completes would destroy
    /// the predecessor model on a decline. This constructor checks the staged
    /// model's affine seal directly while capturing the same immutable query
    /// scope. The installer below rechecks that scope immediately before the
    /// single commit.
    fn for_checked_staged_model_roots(
        executor: &Executor,
        roots: &[TermId],
        model: &Model,
        model_epoch: QuantifiedGrantModelEpoch,
    ) -> Option<Self> {
        if roots.is_empty()
            || !model.carries_quantified_grant_model(&model_epoch)
            || !model.quantified_certificate_pins_are_current(&executor.ctx.terms)
            || !model.formula_neutral_function_defaults_are_current(&executor.ctx)
            || roots
                .iter()
                .any(|&root| executor.ctx.terms.entry_stamp(root).is_none())
        {
            return None;
        }
        Some(Self {
            epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            projection_bindings: QuantifiedProjectionBindings::None,
            model_epoch: Some(model_epoch),
        })
    }
}

impl Executor {
    /// Atomically install a finite-model SAT witness and its exact model-bound
    /// quantified authority.
    ///
    /// Every fallible operation happens on `staged_model` while the predecessor
    /// model and all of its evidence remain installed:
    ///
    /// 1. consume exact checked root coverage;
    /// 2. add only formula-neutral output defaults for declarations absent from
    ///    those roots (the residual-and-pins witness was already checked by the
    ///    producer; this completion is never a substitute for that check);
    /// 3. seal the staged model and construct/recheck its root grant.
    ///
    /// Only then are predecessor validation, SAT, and quantified-grant artifacts
    /// revoked and the model+grant committed. A false return therefore leaves
    /// the prior public model and evidence exactly untouched. Any later strict
    /// repair uses the ordinary model mutation primitives, revokes the affine
    /// model seal, and makes this grant fail closed at the quantified gate.
    pub(in crate::executor) fn install_finite_model_full_domain_sat_authority(
        &mut self,
        evidence: CheckedBvFullDomainSatAuthority,
        mut staged_model: Model,
    ) -> bool {
        let Some(roots) = evidence.into_current_roots(self) else {
            return false;
        };
        if self.should_abort_theory_loop()
            || !self.complete_quantified_output_model_before_seal(&mut staged_model, &roots)
            || self.should_abort_theory_loop()
        {
            return false;
        }
        let model_epoch = staged_model.seal_quantified_grant_model();
        let Some(grant) = QuantifiedSatAuthorityGrant::for_checked_staged_model_roots(
            self,
            &roots,
            &staged_model,
            model_epoch,
        ) else {
            return false;
        };
        if !grant.scope_is_current_for(self, &roots) {
            return false;
        }

        // The commit boundary. No fallible work may be added below it.
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.last_sat_certificate = None;
        self.model_validation_delegated_assertions.clear();
        self.clear_quantified_sat_authority();
        self.last_model = Some(staged_model);
        crate::executor::model::eval_memo_clear();
        self.bv_quantifier_full_domain_proof = true;
        self.bv_quantifier_full_domain_pending_evidence = None;
        self.bv_quantifier_full_domain_query_grant = Some(grant);
        // Record producer validation only after the exact staged witness and
        // its model-bound grant are installed. The SAT funnel's affine strict
        // gate consumes this bit immediately: it clears it, applies the
        // read-only strict oracle, and restores validation only after the
        // complete gate stack accepts the untouched model.
        self.last_model_validated = true;
        true
    }

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

#[cfg(test)]
mod tests {
    use ay_core::Sort;

    use super::*;
    use crate::executor::model::{EvalValue, ValidationStats};
    use crate::executor_types::SolveResult;

    fn load_assertions(smt: &str) -> Executor {
        let commands = ay_frontend::parse(smt).expect("parse installer fixture");
        let mut executor = Executor::new();
        for command in &commands {
            let output = executor
                .execute(command)
                .expect("execute installer fixture");
            assert!(output.is_none(), "fixture must not contain a query command");
        }
        executor
    }

    fn sentinel_value(executor: &mut Executor, sentinel: TermId) -> EvalValue {
        let model = executor
            .last_model
            .clone()
            .expect("fixture keeps an installed model");
        executor.evaluate_term(&model, sentinel)
    }

    #[test]
    fn stale_finite_model_install_is_exactly_atomic() {
        let mut executor = load_assertions("(set-logic ALL) (assert true)");
        let roots = executor.ctx.assertions.clone();
        let sentinel = executor
            .ctx
            .terms
            .mk_var("finite-install-predecessor", Sort::Bool);
        let mut predecessor = Model::empty();
        assert!(Executor::insert_completed_value(
            &executor.ctx.terms,
            &mut predecessor,
            sentinel,
            &EvalValue::Bool(false),
        ));
        executor.last_model = Some(predecessor);
        executor.last_model_validated = false;
        assert_eq!(
            executor
                .emit_sat_verdict(SolveResult::Sat, &[])
                .expect("predecessor SAT emission"),
            SolveResult::Sat
        );
        assert!(executor.last_sat_certificate.is_some());
        executor.last_validation_stats = Some(ValidationStats {
            checked: 3,
            total: 5,
            ..Default::default()
        });
        executor
            .model_validation_delegated_assertions
            .insert(roots[0]);

        let predecessor_authority = CheckedBvFullDomainSatAuthority::for_test(&executor, &roots);
        assert!(executor.install_bv_full_domain_sat_authority(predecessor_authority));
        let stale = CheckedBvFullDomainSatAuthority::for_test(&executor, &roots);
        executor.advance_query_authority_epoch();

        assert!(!executor.install_finite_model_full_domain_sat_authority(stale, Model::empty(),));
        assert_eq!(
            sentinel_value(&mut executor, sentinel),
            EvalValue::Bool(false),
            "a failed install must retain the exact predecessor model"
        );
        assert!(
            executor.last_model_validated,
            "a failed install must not rewrite predecessor validation state"
        );
        assert!(
            executor.last_sat_certificate.is_some(),
            "a failed install must not consume the predecessor SAT token"
        );
        assert_eq!(
            executor
                .last_validation_stats
                .as_ref()
                .map(|stats| (stats.checked, stats.total)),
            Some((3, 5))
        );
        assert!(executor
            .model_validation_delegated_assertions
            .contains(&roots[0]));
        assert!(executor.bv_quantifier_full_domain_proof);
        assert!(executor.bv_quantifier_full_domain_query_grant.is_some());
    }

    #[test]
    fn successful_finite_model_install_rebinds_every_model_artifact() {
        let mut executor = load_assertions("(set-logic ALL) (assert true)");
        let roots = executor.ctx.assertions.clone();
        let sentinel = executor
            .ctx
            .terms
            .mk_var("finite-install-successor", Sort::Bool);
        executor.last_model = Some(Model::empty());
        let predecessor = CheckedMbqiSatAuthority::for_test(&mut executor, &roots)
            .expect("predecessor model can be sealed");
        assert!(executor.install_mbqi_sat_authority(predecessor));
        executor.last_model_validated = true;
        executor.last_validation_stats = Some(ValidationStats {
            checked: 7,
            total: 11,
            ..Default::default()
        });
        executor
            .model_validation_delegated_assertions
            .insert(roots[0]);

        let mut staged = Model::empty();
        assert!(Executor::insert_completed_value(
            &executor.ctx.terms,
            &mut staged,
            sentinel,
            &EvalValue::Bool(true),
        ));
        let _memo = crate::executor::model::EvalMemoSession::new();
        crate::executor::model::seed_eval_memo_for_test(sentinel, EvalValue::Bool(false));
        let evidence = CheckedBvFullDomainSatAuthority::for_test(&executor, &roots);
        assert!(executor.install_finite_model_full_domain_sat_authority(evidence, staged));

        assert_eq!(
            sentinel_value(&mut executor, sentinel),
            EvalValue::Bool(true),
            "the checked staged model must be the installed model"
        );
        assert!(
            executor.last_model_validated,
            "the affine strict gate must receive producer validation for the exact staged model"
        );
        assert!(executor.last_validation_stats.is_none());
        assert!(executor.model_validation_delegated_assertions.is_empty());
        assert!(!executor.mbqi_sat_cert_grant_active);
        assert!(executor.mbqi_sat_cert_query_grant.is_none());
        assert!(executor.bv_quantifier_full_domain_proof);
        assert!(executor.has_current_model_bound_quantified_sat_authority(&roots));
    }

    #[test]
    fn post_install_model_mutation_revokes_finite_authority() {
        let mut executor = load_assertions(
            r#"
                (set-logic ALL)
                (declare-fun p (Bool) Bool)
                (assert (forall ((x Bool)) (p x)))
            "#,
        );
        let roots = executor.ctx.assertions.clone();
        executor.last_model = Some(Model::empty());
        let evidence = CheckedBvFullDomainSatAuthority::for_test(&executor, &roots);
        assert!(executor.install_finite_model_full_domain_sat_authority(evidence, Model::empty(),));
        assert!(executor.has_current_model_bound_quantified_sat_authority(&roots));

        let sentinel = executor
            .ctx
            .terms
            .mk_var("finite-install-late-mutation", Sort::Bool);
        let mut installed = executor.last_model.take().expect("installed witness");
        assert!(Executor::insert_completed_value(
            &executor.ctx.terms,
            &mut installed,
            sentinel,
            &EvalValue::Bool(true),
        ));
        executor.last_model = Some(installed);

        assert!(
            !executor.has_current_model_bound_quantified_sat_authority(&roots),
            "any semantic write after sealing must revoke the model-bound theorem"
        );
        assert_eq!(
            executor.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Unknown,
            "a stale finite-model grant must not discharge a quantified root"
        );
    }
}
