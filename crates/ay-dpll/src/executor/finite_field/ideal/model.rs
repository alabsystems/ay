// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Lexicographic elimination / triangular root isolation with substitution.
//! Cox, Little & O'Shea, Ideals, Varieties, and Algorithms, elimination theorem;
//! root isolation reuses the admitted F_p polynomial kernel. No candidate-value
//! trials or field-sized assignment table. A missing triangular equation is
//! unfinished model construction, never an UNSAT certificate.
use super::super::univariate;
use super::{Basis, Polynomial, Ring};
use ay_core::{FiniteFieldSort, TermId};
mod conic;
mod parametric;
mod quadric;

enum Equation {
    Impossible,
    Polynomial {
        variable: usize,
        coefficients: Vec<u32>,
    },
    Free(usize),
    Unsupported,
}
struct Frame {
    variable: usize,
    remaining: Option<Vec<u32>>,
}

impl Ring<'_, '_> {
    fn power(&mut self, mut value: u32, mut exponent: u32) -> Option<u32> {
        let mut out = 1;
        while exponent != 0 {
            if exponent & 1 != 0 {
                out = self.product(out, value)?;
            }
            exponent >>= 1;
            if exponent != 0 {
                value = self.product(value, value)?;
            }
        }
        Some(out)
    }
    fn substitute(&mut self, row: &Polynomial, values: &[Option<u32>]) -> Option<Polynomial> {
        let mut out = Vec::new();
        for term in row {
            let mut exponents = self.exponents(&term.exponents)?;
            let mut coefficient = term.coefficient;
            self.pay(values.len(), 0)?;
            for (power, value) in exponents.iter_mut().zip(values) {
                if let Some(value) = value {
                    let factor = self.power(*value, *power)?;
                    coefficient = self.product(coefficient, factor)?;
                    *power = 0;
                }
            }
            self.add_summand(&mut out, &exponents, coefficient)?;
        }
        Some(out)
    }
    fn equation_once(&mut self, basis: &[Polynomial], values: &[Option<u32>]) -> Option<Equation> {
        let mut present = Vec::new();
        self.reserve(&mut present, values.len())?;
        self.pay(values.len(), 0)?;
        present.resize(values.len(), false);
        let mut best: Option<(usize, Vec<u32>)> = None;
        for row in basis {
            let row = self.substitute(row, values)?;
            if row.is_empty() {
                continue;
            }
            if self.is_constant(&row)? {
                return Some(Equation::Impossible);
            }
            let mut variable = None;
            let mut mixed = false;
            let mut degree = 0u32;
            for term in &row {
                self.pay(term.exponents.len(), 0)?;
                for (index, &power) in term.exponents.iter().enumerate() {
                    if power == 0 {
                        continue;
                    }
                    present[index] = true;
                    if variable.is_some_and(|prior| prior != index) {
                        mixed = true;
                    }
                    variable = Some(index);
                    degree = degree.max(power);
                }
            }
            if mixed {
                continue;
            }
            let variable = variable?;
            let count = usize::try_from(degree).ok()?.checked_add(1)?;
            if best.as_ref().is_some_and(|(old_variable, old)| {
                *old_variable > variable || (*old_variable == variable && old.len() <= count)
            }) {
                continue;
            }
            let mut coefficients = Vec::new();
            self.pay(count, 0)?;
            self.reserve(&mut coefficients, count)?;
            coefficients.resize(count, 0);
            for term in &row {
                self.pay(1, 0)?;
                let at = usize::try_from(term.exponents[variable]).ok()?;
                coefficients[at] = self.sum(coefficients[at], term.coefficient);
            }
            best = Some((variable, coefficients));
        }
        if let Some((variable, coefficients)) = best {
            return Some(Equation::Polynomial {
                variable,
                coefficients,
            });
        }
        // A coordinate is assigned zero ONLY after proving it occurs in no
        // remaining equation. This is algebraic freedom, not a guessed value.
        for index in (0..values.len()).rev() {
            self.pay(1, 0)?;
            if values[index].is_none() && !present[index] {
                return Some(Equation::Free(index));
            }
        }
        Some(Equation::Unsupported)
    }
    fn equation(&mut self, basis: &[Polynomial], values: &[Option<u32>]) -> Option<Equation> {
        let initial = self.equation_once(basis, values)?;
        self.pay(values.len(), 0)?;
        if !matches!(initial, Equation::Unsupported) || values.iter().all(Option::is_none) {
            return Some(initial);
        }
        // Specialization can change leading coefficients. Re-establish the
        // elimination basis inside this branch, under the SAME original
        // budget. A conditional unit only rejects the branch, never licenses
        // a global UNSAT result or a new theorem authority.
        let mut specialized = Vec::new();
        for row in basis {
            let row = self.substitute(row, values)?;
            self.reserve(&mut specialized, 1)?;
            specialized.push(row);
        }
        match self.groebner(specialized)? {
            Basis::Unit => Some(Equation::Impossible),
            Basis::Proper(basis) => self.equation_once(&basis, values),
        }
    }
    pub(super) fn root_choice(
        &mut self,
        variable: usize,
        polynomial: Vec<u32>,
    ) -> Option<Option<univariate::RootChoice>> {
        self.pay(1, 0)?;
        let control = &mut self.control;
        univariate::next_root_with_progress(
            self.terms,
            self.variables[variable],
            self.field,
            polynomial,
            self.fuel,
            &mut |work, bytes| control(work, bytes),
        )
    }
    fn satisfies(&mut self, basis: &[Polynomial], values: &[Option<u32>]) -> Option<bool> {
        for row in basis {
            let mut sum = 0;
            for term in row {
                let mut coefficient = term.coefficient;
                self.pay(values.len(), 0)?;
                for (&power, value) in term.exponents.iter().zip(values) {
                    let value = value.as_ref().copied()?;
                    let factor = self.power(value, power)?;
                    coefficient = self.product(coefficient, factor)?;
                }
                sum = self.sum(sum, coefficient);
            }
            if sum != 0 {
                return Some(false);
            }
        }
        Some(true)
    }
}

fn output(
    ring: &mut Ring<'_, '_>,
    values: &[Option<u32>],
) -> Option<Vec<(TermId, u32, FiniteFieldSort)>> {
    let mut out = Vec::new();
    ring.reserve(&mut out, values.len())?;
    for (index, value) in values.iter().enumerate() {
        ring.pay(1, 0)?;
        out.push((ring.variables[index], (*value)?, ring.field));
    }
    Some(out)
}

pub(super) fn construct(
    ring: &mut Ring<'_, '_>,
    basis: &[Polynomial],
) -> Option<Option<Vec<(TermId, u32, FiniteFieldSort)>>> {
    let mut values = Vec::new();
    ring.reserve(&mut values, ring.variables.len())?;
    ring.pay(ring.variables.len(), 0)?;
    values.resize(ring.variables.len(), None);
    let mut frames: Vec<Frame> = Vec::new();
    let mut assigned = 0usize;
    loop {
        ring.pay(1, 0)?;
        if assigned == values.len() {
            if ring.satisfies(basis, &values)? {
                return output(ring, &values).map(Some);
            }
        } else {
            match ring.equation(basis, &values)? {
                Equation::Free(variable) => {
                    ring.reserve(&mut frames, 1)?;
                    values[variable] = Some(0);
                    frames.push(Frame {
                        variable,
                        remaining: None,
                    });
                    assigned = assigned.checked_add(1)?;
                    continue;
                }
                Equation::Polynomial {
                    variable,
                    coefficients,
                } => {
                    if let Some(choice) = ring.root_choice(variable, coefficients)? {
                        ring.reserve(&mut frames, 1)?;
                        values[variable] = Some(choice.value);
                        frames.push(Frame {
                            variable,
                            remaining: Some(choice.remaining),
                        });
                        assigned = assigned.checked_add(1)?;
                        continue;
                    }
                }
                Equation::Unsupported => {
                    if let Some(completed) = parametric::construct(ring, basis, &values)? {
                        if ring.satisfies(basis, &completed)? {
                            return output(ring, &completed).map(Some);
                        }
                    }
                    if let Some(completed) = conic::construct(ring, basis, &values)? {
                        return output(ring, &completed).map(Some);
                    }
                    if let Some(completed) = quadric::construct(ring, basis, &values)? {
                        return output(ring, &completed).map(Some);
                    }
                }
                Equation::Impossible => {}
            }
        }
        // Iterative backtracking keeps actual root remainders and the SAME
        // original caller budget; no recursive stack or per-branch renewal.
        loop {
            ring.pay(1, 0)?;
            let Some(frame) = frames.pop() else {
                return Some(None);
            };
            values[frame.variable] = None;
            assigned = assigned.checked_sub(1)?;
            if let Some(polynomial) = frame.remaining {
                if let Some(choice) = ring.root_choice(frame.variable, polynomial)? {
                    values[frame.variable] = Some(choice.value);
                    frames.push(Frame {
                        variable: frame.variable,
                        remaining: Some(choice.remaining),
                    });
                    assigned = assigned.checked_add(1)?;
                    break;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, TermStore};

    #[test]
    fn triangular_root_helper_charges_only_monotonic_deltas_and_retains_prior_choices() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let variable = terms.mk_var("x", Sort::FiniteField(field));
        let mut probe_fuel = 100_000;
        let mut first_bytes = 0;
        let first = univariate::next_root(
            &terms,
            variable,
            field,
            vec![65536, 0, 1],
            &mut probe_fuel,
            &mut |total| {
                first_bytes = total;
                true
            },
        )
        .unwrap()
        .unwrap();
        let mut second_bytes = 0;
        let _ = univariate::next_root(
            &terms,
            variable,
            field,
            first.remaining,
            &mut probe_fuel,
            &mut |total| {
                second_bytes = total;
                true
            },
        )
        .unwrap()
        .unwrap();
        let expected = first_bytes + second_bytes;
        let mut fuel = 100_000;
        let mut actual = 0usize;
        {
            let mut control = |_: usize, extra: usize| {
                actual += extra;
                true
            };
            let mut ring = Ring {
                terms: &terms,
                variables: vec![variable],
                field,
                fuel: &mut fuel,
                control: &mut control,
            };
            let first = ring.root_choice(0, vec![65536, 0, 1]).unwrap().unwrap();
            let _ = ring.root_choice(0, first.remaining).unwrap().unwrap();
        }
        assert_eq!(
            actual, expected,
            "no repeated cumulative total, reset, or refund"
        );
        let limit = first_bytes + second_bytes / 2;
        let mut fuel = 100_000;
        let mut used = 0usize;
        let mut polls = 0usize;
        let mut control = |_: usize, extra: usize| {
            polls += 1;
            used += extra;
            used <= limit
        };
        let mut ring = Ring {
            terms: &terms,
            variables: vec![variable],
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        let first = ring.root_choice(0, vec![65536, 0, 1]).unwrap().unwrap();
        assert!(ring.root_choice(0, first.remaining).is_none());
        assert_eq!(*ring.fuel, 0);
        drop(ring);
        let before = polls;
        let mut control = |_: usize, _: usize| {
            polls += 1;
            true
        };
        let mut ring = Ring {
            terms: &terms,
            variables: vec![variable],
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        assert!(ring.root_choice(0, vec![65536, 0, 1]).is_none());
        drop(ring);
        assert_eq!(polls, before);
    }
}
