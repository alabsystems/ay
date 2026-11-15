// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Finite-field Nullstellensatz: adjoining x_i^p-x_i restricts zeros to F_p.
//! See Sicun Gao, "Counting Zeros over Finite Fields with Gröbner Bases"
//! (2009), §3.1, https://my.ece.utah.edu/~kalla/Comp-Algebra/galois-field-grobner-basis.pdf.
//! A unit ideal is a
//! contradiction; a proper ideal alone is never exposed as a SAT answer.

use super::{model, Basis, Candidate, Polynomial, Ring};

pub(super) fn refine(ring: &mut Ring<'_, '_>, basis: &[Polynomial]) -> Option<Candidate> {
    // Before adjoining degree-p rows, exploit an already-derived univariate
    // consequence using modular Frobenius gcd. Inspect ONLY the unconditional
    // original basis: a failed specialized branch is not a global refutation.
    for row in basis {
        let mut variable = None;
        let mut mixed = false;
        let mut degree = 0u32;
        for term in row {
            ring.pay(term.exponents.len(), 0)?;
            for (index, &power) in term.exponents.iter().enumerate() {
                if power != 0 {
                    mixed |= variable.is_some_and(|old| old != index);
                    variable = Some(index);
                    degree = degree.max(1 + (power - 1) % (ring.field.modulus() - 1));
                }
            }
        }
        if mixed || variable.is_none() {
            continue;
        }
        let variable = variable?;
        let count = usize::try_from(degree).ok()?.checked_add(1)?;
        let mut coefficients = Vec::new();
        ring.reserve(&mut coefficients, count)?;
        ring.pay(count, 0)?;
        coefficients.resize(count, 0);
        for term in row {
            ring.pay(1, 0)?;
            let power = term.exponents[variable];
            let reduced = if power == 0 {
                0
            } else {
                1 + (power - 1) % (ring.field.modulus() - 1)
            };
            let at = usize::try_from(reduced).ok()?;
            coefficients[at] = ring.sum(coefficients[at], term.coefficient);
        }
        ring.pay(coefficients.len(), 0)?;
        if coefficients.iter().all(|&coefficient| coefficient == 0) {
            continue;
        }
        if ring.root_choice(variable, coefficients)?.is_none() {
            return Some(Candidate::Contradiction);
        }
    }
    let mut generators = Vec::new();
    for row in basis {
        let row = ring.duplicate(row)?;
        ring.reserve(&mut generators, 1)?;
        generators.push(row);
    }
    for variable in 0..ring.variables.len() {
        let mut powers = ring.zero_exponents()?;
        let mut row = Vec::new();
        powers[variable] = ring.field.modulus();
        ring.add_summand(&mut row, &powers, 1)?;
        powers[variable] = 1;
        ring.add_summand(&mut row, &powers, ring.field.modulus() - 1)?;
        ring.reserve(&mut generators, 1)?;
        generators.push(row);
    }
    // No fresh budget, prime-dependent allowance, or assignment enumeration.
    // Large degrees/quotients can exhaust the original resources and refuse.
    match ring.groebner(generators)? {
        Basis::Unit => Some(Candidate::Contradiction),
        Basis::Proper(basis) => model::construct(ring, &basis)?.map(Candidate::Model),
    }
}
