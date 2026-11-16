// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Independently normalize authored univariate quadratic constraints. Common
//! roots are the polynomial gcd; square-free division and gcd with forbidden
//! polynomials remove exactly the disequality roots. Euler's criterion decides
//! whether a residual quadratic has roots. No producer evaluator, coefficients,
//! rank, square-root routine or witness is accepted as evidence.
//! See Shoup, A Computational Introduction to Number Theory and Algebra,
//! chapters 4/17/20, https://shoup.net/ntb/ntb-v2.pdf.

use super::ProofCheckError;
use ay_core::{Constant, FiniteFieldSort, ProofId, Sort, Symbol, TermData, TermId, TermStore};

type Polynomial = [u32; 3];

fn degree(poly: Polynomial) -> Option<usize> {
    (0..3).rev().find(|&index| poly[index] != 0)
}

struct Check<'a, 'p> {
    terms: &'a TermStore,
    field: Option<FiniteFieldSort>,
    variable: Option<TermId>,
    work: usize,
    progress: &'p mut dyn FnMut(usize, usize) -> bool,
}

impl Check<'_, '_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Option<()> {
        self.work = self.work.checked_sub(work)?;
        (self.progress)(work, bytes).then_some(())
    }
    fn modulus(&self) -> Option<u64> {
        Some(u64::from(self.field?.modulus()))
    }
    fn sum(&self, a: u32, b: u32) -> Option<u32> {
        Some(((u64::from(a) + u64::from(b)) % self.modulus()?) as u32)
    }
    fn difference(&self, a: u32, b: u32) -> Option<u32> {
        let p = self.modulus()?;
        Some(((u64::from(a) + p - u64::from(b)) % p) as u32)
    }
    fn product(&mut self, a: u32, b: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some((u64::from(a) * u64::from(b) % self.modulus()?) as u32)
    }
    fn power(&mut self, mut base: u32, mut exponent: u32) -> Option<u32> {
        let mut value = 1;
        while exponent != 0 {
            if exponent & 1 != 0 {
                value = self.product(value, base)?;
            }
            base = self.product(base, base)?;
            exponent >>= 1;
        }
        Some(value)
    }
    fn inverse(&mut self, value: u32) -> Option<u32> {
        if value == 0 {
            return None;
        }
        self.power(value, self.field?.modulus() - 2)
    }

    fn parse(&mut self, id: TermId, depth: usize) -> Option<Polynomial> {
        self.pay(1, 0)?;
        let Sort::FiniteField(field) = self.terms.sort(id) else {
            return None;
        };
        if depth > 128 || field.modulus() == 2 || self.field.is_some_and(|f| f != *field) {
            return None;
        }
        self.field = Some(*field);
        if let TermData::App(Symbol::Named(name), _) = self.terms.get(id) {
            self.pay(name.len(), 0)?;
            if self.terms.is_declared_function(name) {
                return None;
            }
        }
        match self.terms.get(id) {
            TermData::Var(..) => {
                if self.variable.is_some_and(|prior| prior != id) {
                    return None;
                }
                self.variable = Some(id);
                Some([0, 1, 0])
            }
            TermData::Const(Constant::FiniteField {
                value,
                field: actual,
            }) if actual == field && *value < field.modulus() => Some([*value, 0, 0]),
            TermData::App(Symbol::Named(name), args) if args.len() <= 1024 => match name.as_str() {
                "ff.neg" if args.len() == 1 => {
                    let mut result = self.parse(args[0], depth + 1)?;
                    for c in &mut result {
                        *c = self.difference(0, *c)?;
                    }
                    Some(result)
                }
                "ff.add" | "ff.bitsum" if args.len() >= 2 => {
                    let mut result = [0; 3];
                    let mut scale = 1;
                    for &arg in args {
                        let next = self.parse(arg, depth + 1)?;
                        for i in 0..3 {
                            let c = self.product(scale, next[i])?;
                            result[i] = self.sum(result[i], c)?;
                        }
                        if name == "ff.bitsum" {
                            scale = self.sum(scale, scale)?;
                        }
                    }
                    Some(result)
                }
                "ff.mul" if args.len() >= 2 => {
                    let mut result = [1, 0, 0];
                    for &arg in args {
                        let next = self.parse(arg, depth + 1)?;
                        if degree(result)
                            .zip(degree(next))
                            .is_some_and(|(a, b)| a + b > 2)
                        {
                            return None;
                        }
                        let mut product = [0; 3];
                        for k in 0..3 {
                            for i in 0..=k {
                                let c = self.product(result[i], next[k - i])?;
                                product[k] = self.sum(product[k], c)?;
                            }
                        }
                        result = product;
                    }
                    Some(result)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn divide(
        &mut self,
        mut numerator: Polynomial,
        denominator: Polynomial,
    ) -> Option<(Polynomial, Polynomial)> {
        let divisor_degree = degree(denominator)?;
        let inverse = self.inverse(denominator[divisor_degree])?;
        let mut quotient = [0; 3];
        while let Some(top) = degree(numerator).filter(|&d| d >= divisor_degree) {
            self.pay(1, 0)?;
            let position = top - divisor_degree;
            let scale = self.product(numerator[top], inverse)?;
            quotient[position] = scale;
            for i in 0..=divisor_degree {
                let c = self.product(denominator[i], scale)?;
                numerator[position + i] = self.difference(numerator[position + i], c)?;
            }
        }
        Some((quotient, numerator))
    }
    fn gcd(&mut self, mut a: Polynomial, mut b: Polynomial) -> Option<Polynomial> {
        while b != [0; 3] {
            self.pay(1, 0)?;
            let (_, remainder) = self.divide(a, b)?;
            a = b;
            b = remainder;
        }
        if let Some(top) = degree(a) {
            let inverse = self.inverse(a[top])?;
            for coefficient in &mut a {
                *coefficient = self.product(*coefficient, inverse)?;
            }
        }
        Some(a)
    }
    fn exact_quotient(&mut self, a: Polynomial, b: Polynomial) -> Option<Polynomial> {
        let (quotient, remainder) = self.divide(a, b)?;
        (remainder == [0; 3]).then_some(quotient)
    }
    fn reserve<T>(&mut self, vector: &mut Vec<T>, additional: usize) -> Option<()> {
        let required = vector.len().checked_add(additional)?;
        if required > vector.capacity() {
            let capacity = required.max(vector.capacity().max(2).checked_mul(2)?);
            self.pay(vector.len(), capacity.checked_mul(size_of::<T>())?)?;
            vector.try_reserve_exact(capacity - vector.len()).ok()?;
        }
        Some(())
    }
}

pub(in crate::checker) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let valid = (|| -> Option<bool> {
        if clause.is_empty() || u32::try_from(clause.len()).is_err() {
            return None;
        }
        let mut checker = Check {
            terms,
            field: None,
            variable: None,
            work: 4_000_000,
            progress,
        };
        checker.pay(clause.len(), 0)?;
        let mut pending = Vec::new();
        checker.reserve(&mut pending, clause.len())?;
        for &literal in clause {
            if terms.sort(literal) != &Sort::Bool {
                return None;
            }
            let TermData::Not(root) = terms.get(literal) else {
                return None;
            };
            pending.push((*root, false, 0usize));
        }
        let mut equalities = [0; 3];
        let mut forbidden = Vec::new();
        let mut contradiction = false;
        while let Some((term, negative, depth)) = pending.pop() {
            checker.pay(1, 0)?;
            if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
                checker.pay(name.len(), 0)?;
                if terms.is_declared_function(name) {
                    return None;
                }
            }
            if depth > 128 || terms.sort(term) != &Sort::Bool {
                return None;
            }
            match terms.get(term) {
                TermData::Const(Constant::Bool(value)) => contradiction |= *value == negative,
                TermData::Not(child) => pending.push((*child, !negative, depth + 1)),
                TermData::App(Symbol::Named(name), args) if name == "not" && args.len() == 1 => {
                    pending.push((args[0], !negative, depth + 1));
                }
                TermData::App(Symbol::Named(name), args) if name == "and" && !negative => {
                    checker.reserve(&mut pending, args.len())?;
                    pending.extend(args.iter().copied().map(|arg| (arg, false, depth + 1)));
                }
                TermData::App(Symbol::Named(name), args)
                    if matches!(name.as_str(), "=" | "distinct")
                        && args.len() >= 2
                        && args.len() <= 1024 =>
                {
                    let equal = (name == "=") != negative;
                    if negative && args.len() != 2 {
                        return None;
                    }
                    for i in 1..args.len() {
                        let left = checker.parse(args[i], 0)?;
                        for right_term in args.iter().take(if equal { 1 } else { i }) {
                            let right = checker.parse(*right_term, 0)?;
                            let mut poly = [0; 3];
                            for k in 0..3 {
                                poly[k] = checker.difference(left[k], right[k])?;
                            }
                            if equal {
                                equalities = checker.gcd(equalities, poly)?;
                            } else if poly == [0; 3] {
                                contradiction = true;
                            } else if degree(poly) != Some(0) {
                                checker.reserve(&mut forbidden, 1)?;
                                forbidden.push(poly);
                            }
                        }
                    }
                }
                _ => return None,
            }
        }
        let field = checker.field?;
        if contradiction || degree(equalities) == Some(0) {
            return Some(true);
        }
        // gcd(0,...,0) denotes ALL points, not the empty domain. Without an
        // authored nonzero equation this certificate makes no exhaustion claim.
        if equalities == [0; 3] {
            return Some(false);
        }
        let derivative = [equalities[1], checker.sum(equalities[2], equalities[2])?, 0];
        let repeated = checker.gcd(equalities, derivative)?;
        let mut remaining = checker.exact_quotient(equalities, repeated)?;
        for poly in forbidden {
            let excluded = checker.gcd(remaining, poly)?;
            remaining = checker.exact_quotient(remaining, excluded)?;
        }
        match degree(remaining) {
            Some(0) => Some(true),
            Some(1) => Some(false),
            Some(2) => {
                let square = checker.product(remaining[1], remaining[1])?;
                let product = checker.product(remaining[0], remaining[2])?;
                let product = checker.product(4 % field.modulus(), product)?;
                let discriminant = checker.difference(square, product)?;
                Some(
                    discriminant != 0
                        && checker.power(discriminant, (field.modulus() - 1) / 2)?
                            == field.modulus() - 1,
                )
            }
            _ => None,
        }
    })() == Some(true);
    if valid {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step,
            reason:
                "finite-field quadratic root exhaustion is invalid, unsupported, or over budget"
                    .into(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
        terms.mk_app(Symbol::Named(name.into()), args, sort)
    }
    fn equation(terms: &mut TermStore, p: u32, rhs: u32) -> (TermId, TermId) {
        let field = FiniteFieldSort::new(p).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let square = app(terms, "ff.mul", &[x, x], Sort::FiniteField(field));
        let value = terms.mk_finite_field(rhs, field);
        (x, terms.mk_eq(square, value))
    }
    fn literals(terms: &mut TermStore, roots: &[TermId]) -> Vec<TermId> {
        roots.iter().map(|&root| terms.mk_not_raw(root)).collect()
    }
    fn checked(terms: &mut TermStore, roots: &[TermId]) -> bool {
        let clause = literals(terms, roots);
        validate(terms, ProofId(0), &clause, &mut |_, _| true).is_ok()
    }

    #[test]
    fn quadratic_checker_removes_repeated_and_forbidden_roots() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let (x, square) = equation(&mut terms, 65537, 4);
        let two = terms.mk_finite_field(2, field);
        let negative = terms.mk_finite_field(65535, field);
        let first = terms.mk_eq(x, two);
        let first = terms.mk_not_raw(first);
        let second = terms.mk_eq(x, negative);
        let second = terms.mk_not_raw(second);
        assert!(checked(&mut terms, &[square, first, second]));
        assert!(checked(&mut terms, &[second, square, first]));
        assert!(!checked(&mut terms, &[square, first]));

        let minus_two = terms.mk_finite_field(65535, field);
        let shifted = app(
            &mut terms,
            "ff.add",
            &[x, minus_two],
            Sort::FiniteField(field),
        );
        let repeated = app(
            &mut terms,
            "ff.mul",
            &[shifted, shifted],
            Sort::FiniteField(field),
        );
        let zero = terms.mk_finite_field(0, field);
        let repeated = terms.mk_eq(repeated, zero);
        assert!(checked(&mut terms, &[repeated, first]));
        assert!(!checked(&mut terms, &[repeated]));
    }

    #[test]
    fn quadratic_checker_refuses_char_two_zero_and_foreign_sources() {
        let mut binary = TermStore::new();
        let (_, root) = equation(&mut binary, 2, 0);
        assert!(!checked(&mut binary, &[root]), "GF2 x²=0 is satisfiable");

        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let (x, satisfiable) = equation(&mut terms, 65537, 4);
        assert!(!checked(&mut terms, &[satisfiable]));
        let negative = app(&mut terms, "ff.neg", &[x], Sort::FiniteField(field));
        let zero_poly = app(
            &mut terms,
            "ff.add",
            &[x, negative],
            Sort::FiniteField(field),
        );
        let zero = terms.mk_finite_field(0, field);
        let no_constraint = terms.mk_eq(zero_poly, zero);
        assert!(
            !checked(&mut terms, &[no_constraint]),
            "zero polynomial denotes every point"
        );
        let one = terms.mk_finite_field(1, field);
        let impossible_constant = terms.mk_eq(zero_poly, one);
        assert!(checked(&mut terms, &[impossible_constant]));
        let (other, other_eq) = equation(&mut terms, 17, 3);
        assert_ne!(x, other);
        assert!(!checked(&mut terms, &[satisfiable, other_eq]));
        let cubic = app(&mut terms, "ff.mul", &[x, x, x], Sort::FiniteField(field));
        let unsupported = terms.mk_eq(cubic, one);
        assert!(!checked(&mut terms, &[unsupported]));
        let y = terms.mk_var("y", Sort::FiniteField(field));
        let two_vars = app(&mut terms, "ff.mul", &[x, y], Sort::FiniteField(field));
        let two_vars = terms.mk_eq(two_vars, one);
        assert!(!checked(&mut terms, &[two_vars]));
    }

    #[test]
    fn quadratic_checker_retains_original_cumulative_work_and_storage_refusal() {
        let mut terms = TermStore::new();
        let (_, root) = equation(&mut terms, 65537, 3);
        let clause = literals(&mut terms, &[root]);
        let mut cost = 0usize;
        validate(&terms, ProofId(0), &clause, &mut |work, _| {
            cost += work;
            true
        })
        .unwrap();
        assert!(cost > 1);
        let mut remaining = cost;
        let mut original = |work, _| {
            let Some(next) = remaining.checked_sub(work) else {
                return false;
            };
            remaining = next;
            true
        };
        validate(&terms, ProofId(0), &clause, &mut original).unwrap();
        assert!(validate(&terms, ProofId(0), &clause, &mut original).is_err());
        assert!(validate(&terms, ProofId(0), &clause, &mut |_, bytes| bytes == 0).is_err());
        assert!(validate(&terms, ProofId(0), &clause, &mut |_, _| false).is_err());
    }
}
