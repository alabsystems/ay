// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Regular linear fibers over F_p(t): fraction-free Gaussian elimination,
//! rational back substitution, and checked cleared-denominator identities.
//! Only an algebraically certified open family is specialized to a field point.
use super::super::super::univariate;
use super::super::{Polynomial, Ring};

struct Rational {
    numerator: Polynomial,
    denominator: Polynomial,
}

impl Ring<'_, '_> {
    fn polynomial_power(&mut self, value: &Polynomial, mut exponent: u32) -> Option<Polynomial> {
        self.pay(1, 0)?;
        let mut result = self.constant(1)?;
        let mut base = self.duplicate(value)?;
        while exponent != 0 {
            self.pay(1, 0)?;
            if exponent & 1 != 0 {
                result = self.multiply(&result, &base)?;
            }
            exponent >>= 1;
            if exponent != 0 {
                base = self.multiply(&base, &base)?;
            }
        }
        Some(result)
    }
    fn rational_subtract(&mut self, a: Rational, b: Rational) -> Option<Rational> {
        self.pay(1, 0)?;
        let left = self.multiply(&a.numerator, &b.denominator)?;
        let right = self.multiply(&b.numerator, &a.denominator)?;
        Some(Rational {
            numerator: self.subtract(left, &right)?,
            denominator: self.multiply(&a.denominator, &b.denominator)?,
        })
    }
    fn regular_matrix(
        &mut self,
        basis: &[Polynomial],
        values: &[Option<u32>],
        parameter: usize,
    ) -> Option<Option<Vec<Vec<Polynomial>>>> {
        let mut rows = Vec::new();
        let width = values.len().checked_add(1)?;
        for original in basis {
            let row = self.substitute(original, values)?;
            let mut cells = Vec::new();
            self.reserve(&mut cells, width)?;
            self.pay(width, 0)?;
            cells.resize_with(width, Vec::new);
            for term in row {
                self.pay(term.exponents.len(), 0)?;
                let mut column = values.len();
                for (index, &exponent) in term.exponents.iter().enumerate() {
                    if index == parameter || exponent == 0 {
                        continue;
                    }
                    if exponent != 1 || column != values.len() {
                        return Some(None);
                    }
                    column = index;
                }
                let mut powers = self.zero_exponents()?;
                powers[parameter] = term.exponents[parameter];
                self.add_summand(&mut cells[column], &powers, term.coefficient)?;
            }
            self.reserve(&mut rows, 1)?;
            rows.push(cells);
        }
        Some(Some(rows))
    }
    fn regular_functions(
        &mut self,
        mut rows: Vec<Vec<Polynomial>>,
        values: &[Option<u32>],
        parameter: usize,
    ) -> Option<Option<Vec<Rational>>> {
        let n = values.len();
        let mut pivots = Vec::new();
        let mut rank = 0;
        for column in 0..n {
            self.pay(1, 0)?;
            if column == parameter || values[column].is_some() {
                continue;
            }
            let mut selected = None;
            for row in rank..rows.len() {
                self.pay(1, 0)?;
                if !rows[row][column].is_empty() {
                    selected = Some(row);
                    break;
                }
            }
            let Some(selected) = selected else {
                continue;
            };
            rows.swap(rank, selected);
            let pivot = self.duplicate(&rows[rank][column])?;
            for row in rank + 1..rows.len() {
                self.pay(1, 0)?;
                if rows[row][column].is_empty() {
                    continue;
                }
                let factor = self.duplicate(&rows[row][column])?;
                for at in column..=n {
                    self.pay(1, 0)?;
                    let left = self.multiply(&pivot, &rows[row][at])?;
                    let right = self.multiply(&factor, &rows[rank][at])?;
                    rows[row][at] = self.subtract(left, &right)?;
                }
            }
            self.reserve(&mut pivots, 1)?;
            pivots.push((rank, column));
            rank += 1;
        }
        for row in &rows[rank..] {
            self.pay(n, 0)?;
            if row[..n].iter().all(Vec::is_empty) && !row[n].is_empty() {
                return Some(None);
            }
        }
        let mut functions = Vec::new();
        self.reserve(&mut functions, n)?;
        for (index, value) in values.iter().enumerate() {
            let numerator = if index == parameter {
                let mut powers = self.zero_exponents()?;
                powers[parameter] = 1;
                let mut out = Vec::new();
                self.add_summand(&mut out, &powers, 1)?;
                out
            } else {
                self.constant(value.unwrap_or(0))?
            };
            functions.push(Rational {
                numerator,
                denominator: self.constant(1)?,
            });
        }
        // Nonpivot unknown coordinates are algebraically free in this linear
        // system and have value zero; the identities below must still prove
        // that the complete proposed family satisfies EVERY remaining row.
        for &(row, column) in pivots.iter().rev() {
            let numerator = self.subtract(Vec::new(), &rows[row][n])?;
            let mut rhs = Rational {
                numerator,
                denominator: self.constant(1)?,
            };
            for at in column + 1..n {
                self.pay(1, 0)?;
                if rows[row][at].is_empty() {
                    continue;
                }
                let term = Rational {
                    numerator: self.multiply(&rows[row][at], &functions[at].numerator)?,
                    denominator: self.duplicate(&functions[at].denominator)?,
                };
                rhs = self.rational_subtract(rhs, term)?;
            }
            rhs.denominator = self.multiply(&rhs.denominator, &rows[row][column])?;
            functions[column] = rhs;
        }
        Some(Some(functions))
    }
    fn regular_identities(&mut self, basis: &[Polynomial], functions: &[Rational]) -> Option<bool> {
        self.pay(functions.len(), 0)?;
        if functions.len() != self.variables.len()
            || functions
                .iter()
                .any(|function| function.denominator.is_empty())
        {
            return Some(false);
        }
        for row in basis {
            let mut maximum = Vec::new();
            self.reserve(&mut maximum, functions.len())?;
            self.pay(functions.len(), 0)?;
            maximum.resize(functions.len(), 0u32);
            for term in row {
                self.pay(functions.len(), 0)?;
                for (max, &power) in maximum.iter_mut().zip(&term.exponents) {
                    *max = (*max).max(power);
                }
            }
            let mut cleared = Vec::new();
            for term in row {
                let mut product = self.constant(term.coefficient)?;
                for (index, function) in functions.iter().enumerate() {
                    let numerator =
                        self.polynomial_power(&function.numerator, term.exponents[index])?;
                    let denominator = self.polynomial_power(
                        &function.denominator,
                        maximum[index].checked_sub(term.exponents[index])?,
                    )?;
                    product = self.multiply(&product, &numerator)?;
                    product = self.multiply(&product, &denominator)?;
                }
                for term in product {
                    self.add_summand(&mut cleared, &term.exponents, term.coefficient)?;
                }
            }
            if !cleared.is_empty() {
                return Some(false);
            }
        }
        Some(true)
    }
    fn regular_value(
        &mut self,
        polynomial: &Polynomial,
        parameter: usize,
        value: u32,
    ) -> Option<u32> {
        let mut out = 0;
        for term in polynomial {
            self.pay(term.exponents.len(), 0)?;
            if term
                .exponents
                .iter()
                .enumerate()
                .any(|(i, &power)| i != parameter && power != 0)
            {
                return None;
            }
            let power = self.power(value, term.exponents[parameter])?;
            let term = self.product(term.coefficient, power)?;
            out = self.sum(out, term);
        }
        Some(out)
    }
    fn regular_domain(
        &mut self,
        functions: &[Rational],
        parameter: usize,
    ) -> Option<univariate::OutsideRoots> {
        let mut forbidden = self.constant(1)?;
        for function in functions {
            if function.denominator.is_empty() {
                return Some(univariate::OutsideRoots::Unsupported);
            }
            forbidden = self.multiply(&forbidden, &function.denominator)?;
        }
        let mut degree = 0u32;
        for term in &forbidden {
            self.pay(term.exponents.len(), 0)?;
            if term
                .exponents
                .iter()
                .enumerate()
                .any(|(i, &e)| i != parameter && e != 0)
            {
                return None;
            }
            degree = degree.max(term.exponents[parameter]);
        }
        let count = usize::try_from(degree).ok()?.checked_add(1)?;
        self.pay(count, 0)?;
        let mut coefficients = Vec::new();
        self.reserve(&mut coefficients, count)?;
        coefficients.resize(count, 0);
        for term in forbidden {
            self.pay(1, 0)?;
            let at = usize::try_from(term.exponents[parameter]).ok()?;
            coefficients[at] = self.sum(coefficients[at], term.coefficient);
        }
        let control = &mut self.control;
        univariate::outside_roots_with_progress(
            self.terms,
            self.variables[parameter],
            self.field,
            coefficients,
            self.fuel,
            &mut |work, bytes| control(work, bytes),
        )
    }
}

pub(super) fn construct(
    ring: &mut Ring<'_, '_>,
    basis: &[Polynomial],
    values: &[Option<u32>],
) -> Option<Option<Vec<Option<u32>>>> {
    for parameter in (0..values.len()).rev() {
        ring.pay(1, 0)?;
        if values[parameter].is_some() {
            continue;
        }
        let Some(rows) = ring.regular_matrix(basis, values, parameter)? else {
            continue;
        };
        let Some(functions) = ring.regular_functions(rows, values, parameter)? else {
            continue;
        };
        // Check the rational identity BEFORE selecting any point. No lucky
        // constant or Gaussian success flag substitutes for this certificate.
        if !ring.regular_identities(basis, &functions)? {
            continue;
        }
        let univariate::OutsideRoots::Point(point) = ring.regular_domain(&functions, parameter)?
        else {
            continue;
        };
        let mut completed = Vec::new();
        ring.reserve(&mut completed, values.len())?;
        for function in &functions {
            let denominator = ring.regular_value(&function.denominator, parameter, point)?;
            if denominator == 0 {
                return None;
            }
            let numerator = ring.regular_value(&function.numerator, parameter, point)?;
            let inverse = ring.inverse(denominator)?;
            completed.push(Some(ring.product(numerator, inverse)?));
        }
        return Some(Some(completed));
    }
    Some(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{FiniteFieldSort, Sort, TermStore};
    #[test]
    fn parametric_identity_checker_rejects_point_only_luck_and_zero_denominators() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let y = terms.mk_var("y", Sort::FiniteField(field));
        let mut fuel = 100_000;
        let mut control = |_, _| true;
        let mut ring = Ring {
            terms: &terms,
            variables: vec![x, y],
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        let mut row = Vec::new();
        ring.add_summand(&mut row, &[1, 1], 1).unwrap();
        ring.add_summand(&mut row, &[0, 0], 6).unwrap();
        let mut t = Vec::new();
        ring.add_summand(&mut t, &[0, 1], 1).unwrap();
        let wrong = vec![
            Rational {
                numerator: ring.constant(1).unwrap(),
                denominator: ring.constant(1).unwrap(),
            },
            Rational {
                numerator: ring.duplicate(&t).unwrap(),
                denominator: ring.constant(1).unwrap(),
            },
        ];
        let original = ring.duplicate(&row).unwrap();
        assert!(
            !ring.regular_identities(&[original], &wrong).unwrap(),
            "x=1,y=t only works at a lucky point"
        );
        let correct = vec![
            Rational {
                numerator: ring.constant(1).unwrap(),
                denominator: ring.duplicate(&t).unwrap(),
            },
            Rational {
                numerator: t,
                denominator: ring.constant(1).unwrap(),
            },
        ];
        let original = ring.duplicate(&row).unwrap();
        assert!(ring.regular_identities(&[original], &correct).unwrap());
        let malformed = vec![
            Rational {
                numerator: Vec::new(),
                denominator: Vec::new(),
            },
            Rational {
                numerator: ring.constant(1).unwrap(),
                denominator: ring.constant(1).unwrap(),
            },
        ];
        assert!(!ring.regular_identities(&[row], &malformed).unwrap());
    }
    #[test]
    fn parametric_original_refusal_stops_symbolic_work_and_cannot_be_revived() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let y = terms.mk_var("y", Sort::FiniteField(field));
        let run = |fuel: &mut usize, control: &mut dyn FnMut(usize, usize) -> bool| {
            let mut ring = Ring {
                terms: &terms,
                variables: vec![x, y],
                field,
                fuel,
                control,
            };
            let mut row = Vec::new();
            ring.add_summand(&mut row, &[1, 1], 1)?;
            ring.add_summand(&mut row, &[0, 0], 6)?;
            construct(&mut ring, &[row], &[None, None])
        };
        let mut polls = 0;
        let model = run(&mut 500_000, &mut |_, _| {
            polls += 1;
            true
        })
        .unwrap()
        .unwrap();
        assert_eq!(model[0].unwrap() * model[1].unwrap() % 7, 1);
        let cutoff = polls * 3 / 4;
        let mut stopped = 0;
        let mut fuel = 500_000;
        assert!(run(&mut fuel, &mut |_, _| {
            stopped += 1;
            stopped < cutoff
        })
        .is_none());
        assert_eq!(stopped, cutoff);
        assert_eq!(fuel, 0);
        assert!(run(&mut fuel, &mut |_, _| {
            stopped += 1;
            true
        })
        .is_none());
        assert_eq!(stopped, cutoff);
        assert!(run(&mut 500_000, &mut |_, _| true).unwrap().is_some());
    }
}
