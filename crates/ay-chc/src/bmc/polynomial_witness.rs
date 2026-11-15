// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed polynomial-model recovery into original-clause ground evidence.
//!
//! The executor already retains finite scalar-UF observations. Keep those
//! observations through the existing ground reshaper and validator instead of
//! treating the legacy scalar trace as the only replay representation. Missing
//! evidence is not a function default or an Unsafe verdict.

use super::{
    AcyclicNames, BmcSolver, ChcEngineResult, ChcExpr, ChcSort, Counterexample, DerivationWitness,
    FxHashMap, GroundDerivation, HornClause, LevelDerivationWitness, SmtValue,
};
use ay_core::time::Instant;

impl BmcSolver {
    /// An explicitly present typed variable value must pass the existing sort
    /// normalizer. Do not retry an incompatible value through the legacy
    /// integer environment, which can erase its source type (for example a BV
    /// observation at an Int-typed local). The normalizer's intentional Int/BV
    /// compatibility remains unchanged; absent keys and non-variable terms
    /// retain the established expression-recovery fallback.
    pub(super) fn polynomial_model_value_for_sort(
        expression: &ChcExpr,
        sort: &ChcSort,
        model: &FxHashMap<String, SmtValue>,
        scalar_env: &FxHashMap<String, i128>,
    ) -> Option<SmtValue> {
        if let ChcExpr::Var(variable) = expression {
            if let Some(value) = model.get(&variable.name) {
                return Self::model_smt_value_for_sort(value, sort);
            }
        }
        Self::model_expr_smt_value_for_sort(expression, sort, model, scalar_env)
    }

    /// Preserve the ordinary original-PDR fallback when ground reconstruction
    /// is incomplete, but never reopen a refused or expired recovery attempt.
    pub(super) fn verified_acyclic_dag_unsafe_from_model(
        &self,
        witness: DerivationWitness,
        model: &FxHashMap<String, SmtValue>,
        queries: &[&HornClause],
        names: &mut AcyclicNames<'_>,
        deadline: Instant,
    ) -> ChcEngineResult {
        let ground = self
            .ground_derivation_from_polynomial_witness(&witness, model, queries, names, deadline);
        if self.polynomial_witness_poll(names, deadline).is_none() {
            return ChcEngineResult::Unknown;
        }
        let result = if let Some(derivation) = ground {
            let steps = self.steps_from_derivation_witness(&witness);
            ChcEngineResult::Unsafe(
                Counterexample::with_witness(steps, witness).with_ground_derivation(derivation),
            )
        } else {
            // This independently re-solves the original clauses, not the
            // rejected ground candidate or a weakened polynomial formula.
            self.verified_unsafe_from_witness(witness, "acyclic polynomial DAG BMC")
        };
        // Both trace construction and the legacy PDR replay have opaque
        // intervals. A successful result still needs the caller's live final
        // admission; this is not a per-operation latency guarantee.
        if self.polynomial_witness_poll(names, deadline).is_none() {
            return ChcEngineResult::Unknown;
        }
        result
    }

    /// Pure reshaping and original-source validation, with no solver fallback.
    ///
    /// Query variables are regenerated from their own ordered query namespace.
    /// They must not be recovered from the root entry's merged instances: a
    /// defining clause can use the same source spelling for a different value.
    pub(super) fn ground_derivation_from_polynomial_witness(
        &self,
        witness: &DerivationWitness,
        model: &FxHashMap<String, SmtValue>,
        queries: &[&HornClause],
        names: &mut AcyclicNames<'_>,
        deadline: Instant,
    ) -> Option<GroundDerivation> {
        self.polynomial_witness_poll(names, deadline)?;
        if !crate::ground_derivation::ground_backtranslation_enabled() {
            return None;
        }
        let witness_budget =
            crate::ground_derivation::witness::ScopedWitnessChainBudget::new_bounded(
                Some(deadline),
                self.config
                    .base
                    .cancellation_token
                    .clone()
                    .unwrap_or_default(),
            );
        let source_query = self.problem.clauses().get(witness.query_clause?)?;
        let mut query_ordinal = None;
        for (ordinal, query) in queries.iter().enumerate() {
            self.polynomial_witness_poll(names, deadline)?;
            if std::ptr::eq(source_query, *query) {
                query_ordinal = Some(ordinal);
                break;
            }
        }
        let query_ordinal = query_ordinal?;
        let scalar_env = Self::model_i128_env(model);
        self.polynomial_witness_poll(names, deadline)?;
        let query_env = self.acyclic_dag_query_instances(
            source_query,
            query_ordinal,
            model,
            &scalar_env,
            names,
        )?;
        self.polynomial_witness_poll(names, deadline)?;
        let level_witness = LevelDerivationWitness {
            witness: witness.clone(),
            query_roots: vec![witness.root],
        };
        self.polynomial_witness_poll(names, deadline)?;
        let mut derivation = self.ground_derivation_from_witness_with(&level_witness, |query| {
            std::ptr::eq(source_query, query).then_some(query_env)
        })?;
        self.polynomial_witness_poll(names, deadline)?;
        // Concrete-argument UF keys survive alpha-renaming. The validator
        // independently checks every original application and derivation-wide
        // congruence; metadata alone grants no theorem or artifact authority.
        Self::copy_uf_application_model_into_derivation(&mut derivation, model);
        self.polynomial_witness_poll(names, deadline)?;
        crate::ground_derivation::validate_ground_derivation(&self.problem, &derivation)
            .inspect_err(|error| {
                crate::ground_derivation::log_ground_translation_detail(format_args!(
                    "polynomial BMC derivation rejected on its own problem: {error}"
                ));
            })
            .ok()?;
        self.polynomial_witness_poll(names, deadline)?;
        drop(level_witness);
        drop(scalar_env);
        drop(witness_budget);
        self.polynomial_witness_poll(names, deadline)?;
        Some(derivation)
    }

    fn polynomial_witness_poll(
        &self,
        names: &mut AcyclicNames<'_>,
        deadline: Instant,
    ) -> Option<()> {
        if self.dag_deadline_expired(deadline) || self.model_extraction_should_stop() {
            self.stats.borrow_mut().budget_exhausted = true;
            return names.refuse();
        }
        names.poll()?;
        // An accepting callback can itself consume the remaining wall time.
        if self.dag_deadline_expired(deadline) || self.model_extraction_should_stop() {
            self.stats.borrow_mut().budget_exhausted = true;
            return names.refuse();
        }
        Some(())
    }
}
