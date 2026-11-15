// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact complex arithmetic lowered to its two Real components.
//! Reference: Z3 5.3.3 src/ast/rewriter/arith_rewriter.cpp, complex arithmetic.

use super::{Symbol, TermData, TermId, TermStore};
use crate::Sort;
use num_rational::BigRational;

enum ComplexOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl TermStore {
    /// Construct a Complex from Real components (Int components promote exactly).
    /// Returns None for a component outside Int/Real.
    pub fn mk_complex(&mut self, real: TermId, imaginary: TermId) -> Option<TermId> {
        if self.is_declared_function("complex.make") {
            return None;
        }
        let real = self.complex_scalar(real)?;
        let imaginary = self.complex_scalar(imaginary)?;
        Some(self.mk_app(
            Symbol::named("complex.make"),
            [real, imaginary],
            Sort::Complex,
        ))
    }

    /// Project a Complex's real component, or promote an Int/Real scalar.
    pub fn mk_complex_real(&mut self, value: TermId) -> Option<TermId> {
        self.complex_components(value).map(|(real, _)| real)
    }

    /// Project a Complex's imaginary component (zero for an Int/Real scalar).
    pub fn mk_complex_imaginary(&mut self, value: TermId) -> Option<TermId> {
        self.complex_components(value)
            .map(|(_, imaginary)| imaginary)
    }

    /// Negate both exact Real components, promoting an Int/Real scalar.
    pub fn mk_complex_negate(&mut self, value: TermId) -> Option<TermId> {
        let (real, imaginary) = self.complex_components(value)?;
        let real = self.mk_neg(real);
        let imaginary = self.mk_neg(imaginary);
        self.mk_complex(real, imaginary)
    }

    /// Complex equality is equality of both Real components, under every
    /// polarity. This introduces neither witnesses nor nonzero assumptions.
    pub(super) fn fold_complex_equality(&mut self, left: TermId, right: TermId) -> Option<TermId> {
        if self.sort(left) != &Sort::Complex || self.sort(right) != &Sort::Complex {
            return None;
        }
        let (real_left, imaginary_left) = self.complex_components(left)?;
        let (real_right, imaginary_right) = self.complex_components(right)?;
        let real_equal = self.mk_eq(real_left, real_right);
        let imaginary_equal = self.mk_eq(imaginary_left, imaginary_right);
        Some(self.mk_and(vec![real_equal, imaginary_equal]))
    }

    /// Add two Complex/Real/Int operands, returning a Complex.
    pub fn mk_complex_add(&mut self, left: TermId, right: TermId) -> Option<TermId> {
        self.complex_binary(left, right, ComplexOperation::Add)
    }

    /// Subtract two Complex/Real/Int operands, returning a Complex.
    pub fn mk_complex_subtract(&mut self, left: TermId, right: TermId) -> Option<TermId> {
        self.complex_binary(left, right, ComplexOperation::Subtract)
    }

    /// Multiply two Complex/Real/Int operands, returning a Complex.
    pub fn mk_complex_multiply(&mut self, left: TermId, right: TermId) -> Option<TermId> {
        self.complex_binary(left, right, ComplexOperation::Multiply)
    }

    /// Divide using Z3's totalized Real-division formula, including at zero.
    /// No nonzero-denominator assumption or floating-point approximation is used.
    pub fn mk_complex_divide(&mut self, left: TermId, right: TermId) -> Option<TermId> {
        self.complex_binary(left, right, ComplexOperation::Divide)
    }

    fn complex_scalar(&mut self, value: TermId) -> Option<TermId> {
        match self.sort(value) {
            Sort::Real => Some(value),
            Sort::Int => Some(self.mk_to_real(value)),
            _ => None,
        }
    }

    fn complex_components(&mut self, value: TermId) -> Option<(TermId, TermId)> {
        if self.sort(value) != &Sort::Complex {
            let real = self.complex_scalar(value)?;
            let zero = self.mk_rational(BigRational::from_integer(0.into()));
            return Some((real, zero));
        }
        if let TermData::App(Symbol::Named(name), fields) = self.get(value) {
            if name == "complex.make" && !self.is_declared_function(name) {
                if let [real, imaginary] = fields.as_slice() {
                    if self.sort(*real) == &Sort::Real && self.sort(*imaginary) == &Sort::Real {
                        return Some((*real, *imaginary));
                    }
                }
            }
        }
        if self.is_declared_function("complex.real") || self.is_declared_function("complex.imag") {
            return None;
        }
        let real = self.mk_app(Symbol::named("complex.real"), [value], Sort::Real);
        let imaginary = self.mk_app(Symbol::named("complex.imag"), [value], Sort::Real);
        Some((real, imaginary))
    }

    fn complex_binary(
        &mut self,
        left: TermId,
        right: TermId,
        operation: ComplexOperation,
    ) -> Option<TermId> {
        let (a, b) = self.complex_components(left)?;
        let (c, d) = self.complex_components(right)?;
        let (real, imaginary) = match operation {
            ComplexOperation::Add => (self.mk_add(vec![a, c]), self.mk_add(vec![b, d])),
            ComplexOperation::Subtract => (self.mk_sub(vec![a, c]), self.mk_sub(vec![b, d])),
            ComplexOperation::Multiply => {
                let ac = self.mk_mul(vec![a, c]);
                let bd = self.mk_mul(vec![b, d]);
                let ad = self.mk_mul(vec![a, d]);
                let bc = self.mk_mul(vec![b, c]);
                (self.mk_sub(vec![ac, bd]), self.mk_add(vec![ad, bc]))
            }
            ComplexOperation::Divide => {
                let cc = self.mk_mul(vec![c, c]);
                let dd = self.mk_mul(vec![d, d]);
                let denominator = self.mk_add(vec![cc, dd]);
                let ac = self.mk_mul(vec![a, c]);
                let bd = self.mk_mul(vec![b, d]);
                let bc = self.mk_mul(vec![b, c]);
                let ad = self.mk_mul(vec![a, d]);
                let real_numerator = self.mk_add(vec![ac, bd]);
                let imaginary_numerator = self.mk_sub(vec![bc, ad]);
                (
                    self.mk_div(real_numerator, denominator),
                    self.mk_div(imaginary_numerator, denominator),
                )
            }
        };
        self.mk_complex(real, imaginary)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parts(terms: &mut TermStore, value: TermId) -> (TermId, TermId) {
        (
            terms.mk_complex_real(value).unwrap(),
            terms.mk_complex_imaginary(value).unwrap(),
        )
    }

    #[test]
    fn complex_ground_arithmetic_is_exact() {
        let mut terms = TermStore::new();
        let one = terms.mk_int(1.into());
        let two = terms.mk_int(2.into());
        let three = terms.mk_int(3.into());
        let minus_four = terms.mk_int((-4).into());
        let left = terms.mk_complex(one, two).unwrap();
        let right = terms.mk_complex(three, minus_four).unwrap();
        let square = terms.mk_complex_multiply(left, left).unwrap();
        let (real, imaginary) = parts(&mut terms, square);
        assert_eq!(
            terms.get_rational(real),
            Some(&BigRational::from_integer((-3).into()))
        );
        assert_eq!(
            terms.get_rational(imaginary),
            Some(&BigRational::from_integer(4.into()))
        );
        let divided = terms.mk_complex_divide(left, right).unwrap();
        let (real, imaginary) = parts(&mut terms, divided);
        assert_eq!(
            terms.get_rational(real),
            Some(&BigRational::new((-1).into(), 5.into()))
        );
        assert_eq!(
            terms.get_rational(imaginary),
            Some(&BigRational::new(2.into(), 5.into()))
        );
        let sum = terms.mk_complex_add(left, right).unwrap();
        let (real, imaginary) = parts(&mut terms, sum);
        assert_eq!(
            terms.get_rational(real),
            Some(&BigRational::from_integer(4.into()))
        );
        assert_eq!(
            terms.get_rational(imaginary),
            Some(&BigRational::from_integer((-2).into()))
        );
        let difference = terms.mk_complex_subtract(left, right).unwrap();
        let (real, imaginary) = parts(&mut terms, difference);
        assert_eq!(
            terms.get_rational(real),
            Some(&BigRational::from_integer((-2).into()))
        );
        assert_eq!(
            terms.get_rational(imaginary),
            Some(&BigRational::from_integer(6.into()))
        );
        let bad = terms.true_term();
        assert!(terms.mk_complex(bad, one).is_none());
    }

    #[test]
    fn complex_zero_division_retains_totalized_real_division() {
        let mut terms = TermStore::new();
        let one = terms.mk_int(1.into());
        let zero = terms.mk_int(0.into());
        let numerator = terms.mk_complex(one, one).unwrap();
        let denominator = terms.mk_complex(zero, zero).unwrap();
        let quotient = terms.mk_complex_divide(numerator, denominator).unwrap();
        let (real, imaginary) = parts(&mut terms, quotient);
        assert_eq!(real, imaginary);
        assert!(terms.get_rational(real).is_none());
        assert!(
            matches!(terms.get(real), TermData::App(name, args) if name.name() == "/" && args.len() == 2)
        );
    }

    #[test]
    fn complex_negation_and_component_equality_are_exact() {
        let mut terms = TermStore::new();
        let two = terms.mk_int(2.into());
        let three = terms.mk_int(3.into());
        let original = terms.mk_complex(two, three).unwrap();
        let negative = terms.mk_complex_negate(original).unwrap();
        let (real, imaginary) = parts(&mut terms, negative);
        assert_eq!(
            terms.get_rational(real),
            Some(&BigRational::from_integer((-2).into()))
        );
        assert_eq!(
            terms.get_rational(imaginary),
            Some(&BigRational::from_integer((-3).into()))
        );
        let equal = terms.mk_eq(original, negative);
        assert_eq!(equal, terms.false_term());
        let restored = terms.mk_complex_negate(negative).unwrap();
        let equal = terms.mk_eq(original, restored);
        assert_eq!(equal, terms.true_term());
        let variable = terms.mk_var("z".to_string(), Sort::Complex);
        let equal = terms.mk_eq(variable, original);
        assert!(
            matches!(terms.get(equal), TermData::App(name, args) if name.name() == "and" && args.len() == 2)
        );
        assert!(terms.mk_complex_negate(terms.true_term()).is_none());
    }

    #[test]
    fn complex_builders_refuse_user_declared_builtin_identities() {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(0.into());
        terms.register_declared_function("complex.make");
        assert!(terms.mk_complex(zero, zero).is_none());
        for selector in ["complex.real", "complex.imag"] {
            let mut terms = TermStore::new();
            let variable = terms.mk_var("z".to_string(), Sort::Complex);
            terms.register_declared_function(selector);
            assert!(terms.mk_complex_real(variable).is_none());
            assert!(terms.mk_complex_imaginary(variable).is_none());
        }
    }
}
