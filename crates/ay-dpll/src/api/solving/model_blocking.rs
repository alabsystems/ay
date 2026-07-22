// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-blocking clause construction for accepted models.

use crate::api::types::{
    ModelBlockingAssignment, ModelBlockingClause, ModelValue, SolverError, Term,
};
use crate::api::Solver;

impl Solver {
    /// Build a Boolean clause that blocks the current accepted model.
    ///
    /// The returned clause is a disjunction of disequalities over `terms`:
    /// `(or (not (= t1 v1)) ... (not (= tn vn)))`, where each `vi` is the
    /// value AY extracted for `ti` from the current SAT model. This method is
    /// intentionally fail-closed: it first checks the same consumer model
    /// boundary as [`try_get_model_for_consumer`](Self::try_get_model_for_consumer),
    /// rejects empty projections, and rejects model values that cannot be
    /// reified as public AY terms.
    ///
    /// Currently reifiable values are Bool, Int, Real, BitVec, and String.
    ///
    /// # Errors
    ///
    /// Returns:
    /// - [`SolverError::NoResult`] when no solve has run.
    /// - [`SolverError::NotSat`] when the last result is not SAT.
    /// - [`SolverError::SatModelNotValidated`] when the SAT model did not pass
    ///   the consumer boundary.
    /// - [`SolverError::ModelBlockingEmptyProjection`] for an empty projection.
    /// - [`SolverError::ModelBlockingUnsupportedValue`] for unsupported model
    ///   value kinds.
    /// - [`SolverError::ModelGenerationFailed`] when value extraction fails.
    /// - [`SolverError::SortMismatch`] when the reified value does not match the
    ///   source term sort.
    #[must_use = "model-blocking construction must fail closed"]
    pub fn try_model_blocking_clause_for_consumer(
        &mut self,
        terms: &[Term],
    ) -> Result<ModelBlockingClause, SolverError> {
        if terms.is_empty() {
            return Err(SolverError::ModelBlockingEmptyProjection);
        }

        self.ensure_last_sat_model_accepted_for_consumer()?;
        let values = self.try_get_values(terms)?;

        let mut assignments = Vec::with_capacity(terms.len());
        let mut disequalities = Vec::with_capacity(terms.len());

        for (&term, value) in terms.iter().zip(values) {
            let value_kind = value.variant_name();
            let value_smtlib = value.to_string();
            let value_term = self.model_value_term_for_blocking(term, &value)?;
            let equality_term = self.try_eq(term, value_term)?;
            let disequality_term = self.try_not(equality_term)?;
            disequalities.push(disequality_term);
            assignments.push(ModelBlockingAssignment {
                term,
                value,
                value_kind,
                value_smtlib,
                value_term,
                equality_term,
                disequality_term,
            });
        }

        let clause = if let [single] = disequalities.as_slice() {
            *single
        } else {
            self.try_or_many(&disequalities)?
        };

        Ok(ModelBlockingClause::accepted(clause, assignments))
    }

    /// Build and assert a Boolean clause that blocks the current accepted model.
    ///
    /// This is a convenience wrapper around
    /// [`try_model_blocking_clause_for_consumer`](Self::try_model_blocking_clause_for_consumer)
    /// followed by [`try_assert_term`](Self::try_assert_term).
    #[must_use = "model-blocking assertion must fail closed"]
    pub fn try_assert_model_blocking_clause_for_consumer(
        &mut self,
        terms: &[Term],
    ) -> Result<ModelBlockingClause, SolverError> {
        let blocking = self.try_model_blocking_clause_for_consumer(terms)?;
        self.try_assert_term(blocking.clause)?;
        Ok(blocking)
    }

    fn model_value_term_for_blocking(
        &mut self,
        source: Term,
        value: &ModelValue,
    ) -> Result<Term, SolverError> {
        match value {
            ModelValue::Bool(value) => Ok(self.bool_const(*value)),
            ModelValue::Int(value) => Ok(self.int_const_bigint(value)),
            ModelValue::Real(value) => Ok(self.rational_const_ratio(value)),
            ModelValue::BitVec { value, width } => self.try_bv_const_bigint(value, *width),
            ModelValue::String(value) => Ok(self.string_const(value)),
            other => Err(SolverError::ModelBlockingUnsupportedValue {
                term: source.to_raw(),
                value_kind: other.variant_name(),
            }),
        }
    }
}
