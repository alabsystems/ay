// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared metadata and received-value work admission for endpoint paths.

use super::*;
use ay_core::DatatypeSort;

impl SupportAnalysis<'_, '_> {
    pub(super) fn endpoint_datatype_work(
        &self,
        datatype: &DatatypeSort,
        depth: usize,
    ) -> Result<(), QuantifierRejection> {
        charge(self.evaluator, datatype.name.len().div_ceil(64).max(1))?;
        if depth > MAX_SUPPORT_DEPTH {
            return Err(QuantifierRejection::NestingLimit);
        }
        for constructor in &datatype.constructors {
            charge(self.evaluator, constructor.name.len().div_ceil(64).max(1))?;
            for field in &constructor.fields {
                charge(self.evaluator, field.name.len().div_ceil(64).max(1))?;
                self.endpoint_sort_work(&field.sort, depth + 1)?;
            }
        }
        Ok(())
    }

    pub(super) fn endpoint_sort_work(
        &self,
        sort: &Sort,
        depth: usize,
    ) -> Result<(), QuantifierRejection> {
        charge(self.evaluator, 1)?;
        if depth > MAX_SUPPORT_DEPTH {
            return Err(QuantifierRejection::NestingLimit);
        }
        match sort {
            Sort::Datatype(datatype) => self.endpoint_datatype_work(datatype, depth),
            Sort::Array(array) => {
                self.endpoint_sort_work(&array.index_sort, depth + 1)?;
                self.endpoint_sort_work(&array.element_sort, depth + 1)
            }
            Sort::Seq(element) => self.endpoint_sort_work(element, depth + 1),
            Sort::Uninterpreted(name) => {
                charge(self.evaluator, name.len().div_ceil(64).max(1))?;
                // Registered field sorts are followed too: recursion cycles
                // conservatively hit the same depth cap before value lookup.
                if let Some(datatype) = self.evaluator.model.datatype_def(name) {
                    self.endpoint_datatype_work(&datatype, depth + 1)?;
                }
                Ok(())
            }
            Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                charge(self.evaluator, name.len().div_ceil(64).max(1))
            }
            _ => Ok(()),
        }
    }

    pub(super) fn endpoint_value_work(
        &self,
        value: &ModelValue,
        depth: usize,
    ) -> Result<(), QuantifierRejection> {
        charge(self.evaluator, 1)?;
        if depth > MAX_SUPPORT_DEPTH {
            return Err(QuantifierRejection::NestingLimit);
        }
        match value {
            ModelValue::Int(value) | ModelValue::BitVec { value, .. } => {
                self.endpoint_number_work(value)?;
            }
            ModelValue::Real(value) => {
                self.endpoint_number_work(value.numer())?;
                self.endpoint_number_work(value.denom())?;
            }
            ModelValue::Str(value) | ModelValue::Uninterpreted(value) => {
                charge(self.evaluator, value.len().div_ceil(64).max(1))?;
            }
            ModelValue::Array(array) => {
                self.endpoint_value_work(&array.default, depth + 1)?;
                for (index, value) in &array.store {
                    self.endpoint_value_work(index, depth + 1)?;
                    self.endpoint_value_work(value, depth + 1)?;
                }
            }
            ModelValue::Datatype { ctor, args } => {
                charge(self.evaluator, ctor.len().div_ceil(64).max(1))?;
                for argument in args {
                    self.endpoint_value_work(argument, depth + 1)?;
                }
            }
            ModelValue::Seq(values) => {
                for value in values {
                    self.endpoint_value_work(value, depth + 1)?;
                }
            }
            ModelValue::Algebraic(value) => {
                let (lower, upper) = value.interval();
                for coefficient in value
                    .minimal_polynomial()
                    .iter()
                    .chain(value.representation())
                    .chain([lower, upper])
                {
                    charge(self.evaluator, 1)?;
                    self.endpoint_number_work(coefficient.numer())?;
                    self.endpoint_number_work(coefficient.denom())?;
                }
            }
            ModelValue::FloatingPointExact { .. } => {
                charge(
                    self.evaluator,
                    crate::fp_exact::bytes(value)
                        .map_err(|_| QuantifierRejection::EvaluationBudget)?,
                )?;
            }
            ModelValue::Bool(_) | ModelValue::FloatingPoint { .. } => {}
        }
        Ok(())
    }
}
