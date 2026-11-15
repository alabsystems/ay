// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed native construction of exact Complex expressions.

use super::{Solver, SolverError, Term};
use ay_core::{Sort, TermId, TermStore};

impl Solver {
    /// Construct a Complex from Int/Real components, promoting integers exactly.
    pub fn try_complex(&mut self, real: Term, imaginary: Term) -> Result<Term, SolverError> {
        let real = self.resolve_term("complex.make", real)?;
        let imaginary = self.resolve_term("complex.make", imaginary)?;
        let result = self.terms_mut().mk_complex(real, imaginary);
        self.finish_complex_construction("complex.make", &[real, imaginary], result)
    }

    /// Return the real component, with exact scalar promotion for Int/Real.
    pub fn try_real_part(&mut self, value: Term) -> Result<Term, SolverError> {
        let value = self.resolve_term("complex.real", value)?;
        let result = self.terms_mut().mk_complex_real(value);
        self.finish_complex_construction("complex.real", &[value], result)
    }

    /// Return the imaginary component (zero for an Int/Real scalar).
    pub fn try_imag_part(&mut self, value: Term) -> Result<Term, SolverError> {
        let value = self.resolve_term("complex.imag", value)?;
        let result = self.terms_mut().mk_complex_imaginary(value);
        self.finish_complex_construction("complex.imag", &[value], result)
    }

    pub(super) fn finish_complex_construction(
        &mut self,
        operation: &'static str,
        operands: &[TermId],
        result: Option<TermId>,
    ) -> Result<Term, SolverError> {
        match result {
            Some(value) => Ok(self.wrap_term(value)),
            None => Err(SolverError::SortMismatch {
                operation,
                expected: "valid exact Complex construction operands",
                got: operands
                    .iter()
                    .map(|&id| self.terms().sort(id).clone())
                    .collect(),
            }),
        }
    }

    /// Existing Int/Real contracts stay with their callers. A fold containing
    /// Complex accepts only Int/Real/Complex and uses exact component formulas.
    pub(super) fn try_complex_fold(
        &mut self,
        operation: &'static str,
        operands: &[TermId],
        combine: fn(&mut TermStore, TermId, TermId) -> Option<TermId>,
    ) -> Result<Option<Term>, SolverError> {
        if !operands
            .iter()
            .any(|&id| self.terms().sort(id) == &Sort::Complex)
        {
            return Ok(None);
        }
        let Some((&first, rest)) = operands.split_first() else {
            return Ok(None);
        };
        let mut result = first;
        for &operand in rest {
            let combined = combine(self.terms_mut(), result, operand);
            let wrapped =
                self.finish_complex_construction(operation, &[result, operand], combined)?;
            result = self.resolve_term(operation, wrapped)?;
        }
        Ok(Some(self.wrap_term(result)))
    }
}
