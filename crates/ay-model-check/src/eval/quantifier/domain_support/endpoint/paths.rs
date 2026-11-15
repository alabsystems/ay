// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Receiver paths require actual typed values, never application commitments.

use super::*;
use std::borrow::Cow;

impl SupportAnalysis<'_, '_> {
    fn endpoint_receiver(
        &self,
        term: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        charge(self.evaluator, 1)?;
        let sort = self.evaluator.terms.sort(term);
        self.endpoint_sort_work(sort, depth)?;
        match self.evaluator.terms.get(term) {
            TermData::Var(name, _) => {
                charge(self.evaluator, name.len().div_ceil(64).max(1))?;
                if !self.endpoint_name_available(name)? {
                    return Ok(None);
                }
                self.endpoint_model_value(term, depth)
            }
            TermData::App(Symbol::Named(operator), args) => {
                charge(self.evaluator, operator.len().div_ceil(64).max(1))?;
                if self.evaluator.terms.is_declared_function(operator) {
                    return Ok(None);
                }
                if self
                    .evaluator
                    .model
                    .projection_argument(term)
                    .map_err(|error| {
                        QuantifierRejection::UnevaluableBody(EvalError::Refused(error.to_string()))
                    })?
                    .is_some()
                {
                    return Ok(None);
                }
                match (operator.as_str(), args.as_slice()) {
                    ("select", [array, index]) => self.endpoint_select(term, *array, *index, depth),
                    (_, [argument]) => self.endpoint_selector(term, operator, *argument, depth),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    pub(super) fn endpoint_selector(
        &self,
        term: TermId,
        selector: &str,
        argument: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        let result_sort = self.evaluator.terms.sort(term);
        self.endpoint_sort_work(result_sort, depth)?;
        let argument_sort = self.evaluator.terms.sort(argument);
        let datatype = match argument_sort {
            Sort::Datatype(datatype) => Cow::Borrowed(datatype),
            Sort::Uninterpreted(name) => {
                charge(self.evaluator, name.len().div_ceil(64).max(1))?;
                let Some(datatype) = self.evaluator.model.datatype_def(name) else {
                    return Ok(None);
                };
                Cow::Owned(datatype)
            }
            _ => return Ok(None),
        };
        self.endpoint_datatype_work(&datatype, depth + 1)?;
        if !datatype.constructors.iter().any(|constructor| {
            constructor
                .fields
                .iter()
                .any(|field| field.name == selector && &field.sort == result_sort)
        }) {
            return Ok(None);
        }
        let Some(value) = self.endpoint_receiver(argument, depth + 1)? else {
            return Ok(None);
        };
        let ModelValue::Datatype { ctor, .. } = value else {
            return Ok(None);
        };
        // The complete value (including unselected siblings) was authenticated.
        // Partial enum selectors do not determine a range bound.
        if !datatype.constructors.iter().any(|constructor| {
            constructor.name == ctor
                && constructor
                    .fields
                    .iter()
                    .any(|field| field.name == selector && &field.sort == result_sort)
        }) {
            return Ok(None);
        }
        // Normal dispatch, not direct projection: built-ins and constructor
        // symbols retain their existing precedence over same-spelled fields.
        self.endpoint_model_value(term, depth)
    }

    pub(super) fn endpoint_select(
        &self,
        term: TermId,
        array: TermId,
        index: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        let array_sort = self.evaluator.terms.sort(array);
        self.endpoint_sort_work(array_sort, depth + 1)?;
        let Sort::Array(array_type) = array_sort else {
            return Ok(None);
        };
        let result_sort = self.evaluator.terms.sort(term);
        self.endpoint_sort_work(result_sort, depth)?;
        if result_sort != &array_type.element_sort {
            return Err(QuantifierRejection::BindingSortMismatch);
        }
        let index_sort = &array_type.index_sort;
        if !matches!(index_sort, Sort::Int)
            && !matches!(index_sort, Sort::BitVec(bitvec)
                if (1..=MAX_GUARDED_BITVEC_WIDTH).contains(&bitvec.width))
        {
            return Ok(None);
        }
        // All recursion, including an index's receiver path, uses the SAME
        // unavailable names and shared evaluator work ledger.
        let index_analysis = SupportAnalysis {
            evaluator: self.evaluator,
            name: self.name,
            sort: index_sort,
            unavailable: self.unavailable,
            eval_depth: self.eval_depth,
            saw_bound_comparison: std::cell::Cell::new(false),
        };
        if index_analysis.endpoint_value(index, depth + 1)?.is_none() {
            return Ok(None);
        }
        if !matches!(
            self.endpoint_receiver(array, depth + 1)?,
            Some(ModelValue::Array(_))
        ) {
            return Ok(None);
        }
        // Only a concrete, fully typed array reaches the built-in read. The
        // evaluator's fallback per-read pin is not authority for this grammar.
        self.endpoint_model_value(term, depth)
    }

    fn endpoint_model_value(
        &self,
        term: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        let Some(value) = self.endpoint_evaluate(term, depth)? else {
            return Ok(None);
        };
        // Model hooks return owned values and the ordinary evaluator has its
        // own memo/clone intervals. Meter the received payload before further
        // path evaluation and typed validation; this is not a global allocator
        // or callback-latency bound.
        self.endpoint_value_work(&value, depth)?;
        self.evaluator
            .ensure_value_inhabits_sort(&value, self.evaluator.terms.sort(term))
            .map_err(QuantifierRejection::UnevaluableBody)?;
        Ok(Some(value))
    }
}
