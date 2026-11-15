// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact Complex model values and constructor/projection semantics.

use super::{EvalValue, Executor, Model};
use ay_core::{Sort, TermId};

impl Executor {
    /// Candidate for the existing gate-checked gap completion pass: retain
    /// committed components and choose zero only for an unassigned component.
    /// The caller must validate the entire completed model before publishing it.
    pub(super) fn complex_completion_candidate(
        &self,
        model: &Model,
        variable: TermId,
    ) -> Option<EvalValue> {
        if self.ctx.terms.is_declared_function("complex.real")
            || self.ctx.terms.is_declared_function("complex.imag")
        {
            return None;
        }
        let component = |name| {
            let Some(term) = self.ctx.terms.find_app_named(name, &[variable]) else {
                return EvalValue::Rational(num_rational::BigRational::from_integer(0.into()));
            };
            if self.ctx.terms.sort(term) != &Sort::Real {
                return EvalValue::Unknown;
            }
            match self.committed_complex_component(model, term) {
                EvalValue::Unknown => {
                    EvalValue::Rational(num_rational::BigRational::from_integer(0.into()))
                }
                value => value,
            }
        };
        let value = Self::complex_value(component("complex.real"), component("complex.imag"));
        if matches!(value, EvalValue::Unknown) {
            None
        } else {
            Some(value)
        }
    }

    pub(super) fn evaluate_complex_variable(&self, model: &Model, variable: TermId) -> EvalValue {
        let Some(real) = self.ctx.terms.find_app_named("complex.real", &[variable]) else {
            return EvalValue::Unknown;
        };
        let Some(imaginary) = self.ctx.terms.find_app_named("complex.imag", &[variable]) else {
            return EvalValue::Unknown;
        };
        if self.ctx.terms.sort(real) != &Sort::Real || self.ctx.terms.sort(imaginary) != &Sort::Real
        {
            return EvalValue::Unknown;
        }
        // Read committed scalar assignments directly. Evaluating the projection
        // recursively would re-enter this variable through its receiver.
        let real = self.committed_complex_component(model, real);
        let imaginary = self.committed_complex_component(model, imaginary);
        Self::complex_value(real, imaginary)
    }

    pub(super) fn evaluate_complex_app(
        &self,
        model: &Model,
        term: TermId,
        name: &str,
        args: &[TermId],
    ) -> EvalValue {
        if self.ctx.terms.is_declared_function(name) {
            return EvalValue::Unknown;
        }
        match (name, args) {
            ("complex.make", [real, imaginary]) if self.ctx.terms.sort(term) == &Sort::Complex => {
                Self::complex_value(
                    self.evaluate_term(model, *real),
                    self.evaluate_term(model, *imaginary),
                )
            }
            ("complex.real" | "complex.imag", [value])
                if self.ctx.terms.sort(*value) == &Sort::Complex =>
            {
                match self.evaluate_term(model, *value) {
                    EvalValue::Complex { real, imaginary } => {
                        if name == "complex.real" {
                            *real
                        } else {
                            *imaginary
                        }
                    }
                    EvalValue::Unknown => self.committed_complex_component(model, term),
                    _ => EvalValue::Unknown,
                }
            }
            _ => EvalValue::Unknown,
        }
    }

    fn complex_value(real: EvalValue, imaginary: EvalValue) -> EvalValue {
        if !matches!(real, EvalValue::Rational(_) | EvalValue::Algebraic(_))
            || !matches!(imaginary, EvalValue::Rational(_) | EvalValue::Algebraic(_))
        {
            return EvalValue::Unknown;
        }
        EvalValue::Complex {
            real: Box::new(real),
            imaginary: Box::new(imaginary),
        }
    }

    fn committed_complex_component(&self, model: &Model, term: TermId) -> EvalValue {
        if let Some(value) = self.nra_algebraic_model.get(&term) {
            return EvalValue::Algebraic(value.clone());
        }
        if let Some(value) = model
            .lra_model
            .as_ref()
            .and_then(|lra| lra.values.get(&term))
        {
            return EvalValue::Rational(value.clone());
        }
        if let Some(raw) = model
            .euf_model
            .as_ref()
            .and_then(|euf| euf.term_values.get(&term))
        {
            let value = Self::parse_real_string(raw);
            if matches!(value, EvalValue::Rational(_)) {
                return value;
            }
        }
        match model.completed_values.get(&term) {
            Some(value @ (EvalValue::Rational(_) | EvalValue::Algebraic(_))) => value.clone(),
            _ => EvalValue::Unknown,
        }
    }

    pub(super) fn format_complex_component(value: &EvalValue) -> Result<String, String> {
        use crate::executor_format::format_rational;
        match value {
            EvalValue::Rational(value) => Ok(format_rational(value)),
            EvalValue::Algebraic(value) => match value.to_number_for_output() {
                Some(ay_nra::RealScalar::Rational(value)) => Ok(format_rational(&value)),
                Some(ay_nra::RealScalar::Algebraic(value)) => Ok(value.alpha().to_smtlib()),
                None => Err("Complex component has no exact algebraic value".to_string()),
            },
            _ => Err("Complex component is not an exact Real value".to_string()),
        }
    }
}
