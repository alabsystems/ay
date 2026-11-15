// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assignment scratch owned by one clause-trace conversion, not one row.

use super::*;
use crate::literal::Variable;

#[derive(Debug)]
pub(super) struct CompactionScratch {
    pub(super) assign: Vec<Option<bool>>,
    touched: Vec<Variable>,
}

impl CompactionScratch {
    pub(super) fn planned_bytes(num_vars: usize) -> Result<usize, ResolutionValidationError> {
        Self::bytes(num_vars, num_vars)
    }

    fn bytes(assign: usize, touched: usize) -> Result<usize, ResolutionValidationError> {
        checked_resource_add(
            size_of::<Self>(),
            checked_resource_add(
                checked_resource_mul(
                    assign,
                    size_of::<Option<bool>>(),
                    ResolutionValidationResource::Bytes,
                )?,
                checked_resource_mul(
                    touched,
                    size_of::<Variable>(),
                    ResolutionValidationResource::Bytes,
                )?,
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )
    }

    pub(super) fn new(
        num_vars: usize,
        admitted_bytes: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Self, ResolutionValidationError> {
        meter.check_controls()?;
        enforce_resource(
            ResolutionValidationResource::Bytes,
            Self::planned_bytes(num_vars)?,
            admitted_bytes,
        )?;
        let mut scratch = Self {
            assign: Vec::new(),
            touched: Vec::new(),
        };
        reserve_exact(
            &mut scratch.assign,
            num_vars,
            ResolutionValidationResource::AssignmentScratch,
            meter,
        )?;
        // Check allocator capacities, including the still-pending trail,
        // before allocating the next buffer.
        enforce_resource(
            ResolutionValidationResource::Bytes,
            Self::bytes(scratch.assign.capacity(), num_vars)?,
            admitted_bytes,
        )?;
        reserve_exact(
            &mut scratch.touched,
            num_vars,
            ResolutionValidationResource::AssignmentScratch,
            meter,
        )?;
        enforce_resource(
            ResolutionValidationResource::Bytes,
            Self::bytes(scratch.assign.capacity(), scratch.touched.capacity())?,
            admitted_bytes,
        )?;
        while scratch.assign.len() < num_vars {
            let chunk = (num_vars - scratch.assign.len()).min(CONTROL_POLL_INTERVAL);
            meter.charge(chunk)?;
            scratch.assign.resize(scratch.assign.len() + chunk, None);
            meter.check_controls()?;
        }
        Ok(scratch)
    }

    /// Preserve the original fixed-premise, then negated-target order. Every
    /// first assignment enters the pre-reserved trail exactly once.
    pub(super) fn seed(
        &mut self,
        fixed_unit_premises: &[Literal],
        target_clause: &[Literal],
        meter: &mut ConversionMeter<'_>,
    ) -> Result<bool, ResolutionValidationError> {
        debug_assert!(self.touched.is_empty());
        for (literal, value) in fixed_unit_premises
            .iter()
            .map(|lit| (*lit, lit.is_positive()))
            .chain(target_clause.iter().map(|lit| (*lit, !lit.is_positive())))
        {
            meter.charge(1)?;
            let variable = literal.variable();
            let index = variable.index();
            let Some(assigned) = self.assign.get(index) else {
                return Err(ResolutionDagValidateError::VarOutOfRange {
                    clause: 0,
                    var: index,
                    num_vars: self.assign.len(),
                }
                .into());
            };
            match *assigned {
                None => self.set_unassigned(variable, value, meter)?,
                Some(existing) if existing == value => {}
                Some(_) => return Ok(true),
            }
        }
        Ok(false)
    }

    pub(super) fn set_unassigned(
        &mut self,
        variable: Variable,
        value: bool,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        debug_assert!(self.assign[variable.index()].is_none());
        debug_assert!(self.touched.len() < self.touched.capacity());
        meter.charge(1)?;
        self.touched.push(variable);
        self.assign[variable.index()] = Some(value);
        Ok(())
    }

    pub(super) fn clear(
        &mut self,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        while let Some(&variable) = self.touched.last() {
            meter.charge(1)?;
            self.assign[variable.index()] = None;
            self.touched.pop();
        }
        meter.check_controls()
    }
}

#[cfg(test)]
mod tests;
