// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recover signed coefficients from inconsistent integer equality rows.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::{FarkasAnnotation, Sort, Symbol, TermData, TermId, TermStore, TheoryLit};

use super::int_linear_diff;

#[path = "inconsistent_equality_subset/bounds.rs"]
mod bounds;
use bounds::{Control, MAX_CLAUSE, MAX_ROWS};

/// A contradiction from a subset of the original clause's negative equalities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArithInconsistentEqualitySubsetWitness {
    /// Original literal indices, increasing, with no unselected row inserted.
    pub literal_indices: Vec<usize>,
    /// Exact signed multipliers of the native `lhs - rhs` rows in that order.
    pub coefficients: Vec<BigRational>,
}

/// Recover and independently recheck a bounded exact affine contradiction.
/// Only negative, binary, integer equalities participate. Other clause literals
/// are weakened in later checked Boolean steps, never assumed as equalities.
#[must_use]
pub fn arith_inconsistent_equality_subset_witness(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ArithInconsistentEqualitySubsetWitness> {
    arith_inconsistent_equality_subset_witness_with_progress(terms, clause, &mut |_, _| true)
}

/// As [`arith_inconsistent_equality_subset_witness`], with caller cancellation
/// and allocation/work charging before normalization and rational operations.
pub fn arith_inconsistent_equality_subset_witness_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<ArithInconsistentEqualitySubsetWitness> {
    let mut control = Control::new(progress);
    let occurrences = bounds::preflight(terms, clause, &mut control)?;
    let mut candidates = Vec::new();
    for (index, &literal) in clause.iter().enumerate() {
        control.charge(1, 0)?;
        let Some((_, left, right)) = negative_equality(terms, literal) else {
            continue;
        };
        (candidates.len() < MAX_ROWS).then_some(())?;
        control.charge(1, 32)?;
        candidates.push((index, left, right));
    }
    let mut rows = Vec::new();
    let mut atoms = BTreeSet::new();
    for (index, left, right) in candidates {
        control.charge(occurrences, 4_096)?;
        let (mut coefficients, constant) = int_linear_diff(terms, left, right)?;
        coefficients.retain(|_, value| !value.is_zero());
        (coefficients.len() <= 32
            && coefficients
                .values()
                .chain([&constant])
                .all(|value| value.bits() <= 1_024))
        .then_some(())?;
        atoms.extend(coefficients.keys().copied());
        (atoms.len() <= 32).then_some(())?;
        rows.push((index, coefficients, constant));
    }
    (!rows.is_empty()).then_some(())?;
    control.charge(atoms.len(), atoms.len().checked_mul(8)?)?;
    let atoms: Vec<_> = atoms.into_iter().collect();
    let mut basis: Vec<(usize, Row)> = Vec::new();
    for (ordinal, (_, coefficients, constant)) in rows.iter().enumerate() {
        let mut row = Row::new(
            &atoms,
            coefficients,
            constant,
            rows.len(),
            ordinal,
            &mut control,
        )?;
        for (column, pivot) in &basis {
            control.charge(1, 0)?;
            if row.values[*column].is_zero() {
                continue;
            }
            let factor = control.divide(&row.values[*column], &pivot.values[*column])?;
            row.subtract_multiple(pivot, &factor, &mut control)?;
        }
        if let Some(column) = row.values[..atoms.len()]
            .iter()
            .position(|value| !value.is_zero())
        {
            control.charge(1, std::mem::size_of::<Row>())?;
            basis.push((column, row));
            continue;
        }
        if row.values[atoms.len()].is_zero() {
            continue;
        }
        let reverse = row.values[atoms.len()].is_negative();
        let mut witness = ArithInconsistentEqualitySubsetWitness {
            literal_indices: Vec::new(),
            coefficients: Vec::new(),
        };
        for ((index, _, _), weight) in rows.iter().zip(row.weights) {
            control.charge(1, 0)?;
            if weight.is_zero() {
                continue;
            }
            control.rational(&weight)?;
            witness.literal_indices.push(*index);
            witness
                .coefficients
                .push(if reverse { -weight } else { weight });
        }
        recheck(terms, clause, &witness, occurrences, &mut control)?;
        return Some(witness);
    }
    None
}

fn negative_equality(terms: &TermStore, literal: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermData::Not(equality) = terms.get(literal) else {
        return None;
    };
    let TermData::App(Symbol::Named(name), operands) = terms.get(*equality) else {
        return None;
    };
    let [left, right] = operands.as_slice() else {
        return None;
    };
    (name == "="
        && terms.sort(literal) == &Sort::Bool
        && terms.sort(*equality) == &Sort::Bool
        && terms.sort(*left) == &Sort::Int
        && terms.sort(*right) == &Sort::Int)
        .then_some((*equality, *left, *right))
}

struct Row {
    values: Vec<BigRational>,
    weights: Vec<BigRational>,
}

impl Row {
    fn new(
        atoms: &[TermId],
        coefficients: &BTreeMap<TermId, BigInt>,
        constant: &BigInt,
        count: usize,
        ordinal: usize,
        control: &mut Control<'_>,
    ) -> Option<Self> {
        control.charge(
            atoms.len() + count + 1,
            (atoms.len() + count + 1).checked_mul(256)?,
        )?;
        let mut values: Vec<_> = atoms
            .iter()
            .map(|atom| {
                BigRational::from_integer(coefficients.get(atom).cloned().unwrap_or_default())
            })
            .collect();
        values.push(BigRational::from_integer(constant.clone()));
        let mut weights = vec![BigRational::zero(); count];
        weights[ordinal] = BigRational::one();
        Some(Self { values, weights })
    }

    fn subtract_multiple(
        &mut self,
        pivot: &Self,
        factor: &BigRational,
        control: &mut Control<'_>,
    ) -> Option<()> {
        for (target, source) in self
            .values
            .iter_mut()
            .chain(&mut self.weights)
            .zip(pivot.values.iter().chain(&pivot.weights))
        {
            let scaled = control.multiply(source, factor)?;
            let negated = -scaled;
            *target = control.add(target, &negated)?;
        }
        Some(())
    }
}

/// Rebuild from the original rows and check the proposed signed sum directly,
/// then invoke the independent linear Farkas checker. No Gaussian state or
/// producer-provided annotation participates in this final judgment.
fn recheck(
    terms: &TermStore,
    clause: &[TermId],
    witness: &ArithInconsistentEqualitySubsetWitness,
    occurrences: usize,
    control: &mut Control<'_>,
) -> Option<()> {
    (!witness.literal_indices.is_empty()
        && witness.literal_indices.len() <= MAX_ROWS
        && witness.literal_indices.len() == witness.coefficients.len()
        && clause.len() <= MAX_CLAUSE)
        .then_some(())?;
    let mut sum = BTreeMap::<TermId, BigRational>::new();
    let mut total = BigRational::zero();
    let mut previous = None;
    let mut conflict = Vec::new();
    let mut annotation = Vec::new();
    for (&index, weight) in witness.literal_indices.iter().zip(&witness.coefficients) {
        control.charge(occurrences, 4_096)?;
        if previous.is_some_and(|previous| previous >= index) || weight.is_zero() {
            return None;
        }
        previous = Some(index);
        let (equality, left, right) = negative_equality(terms, *clause.get(index)?)?;
        let (coefficients, constant) = int_linear_diff(terms, left, right)?;
        for (atom, coefficient) in coefficients {
            let value = control.multiply(&BigRational::from_integer(coefficient), weight)?;
            let prior = sum.entry(atom).or_insert_with(BigRational::zero);
            *prior = control.add(prior, &value)?;
        }
        let value = control.multiply(&BigRational::from_integer(constant), weight)?;
        total = control.add(&total, &value)?;
        // Existing FarkasAnnotation stores Rational64. Fail closed rather than
        // truncate a correct but unrepresentable exact-rational certificate.
        (weight.numer().bits() <= 62 && weight.denom().bits() <= 62).then_some(())?;
        annotation.push(Rational64::new(
            weight.numer().to_i64()?,
            weight.denom().to_i64()?,
        ));
        conflict.push(TheoryLit {
            term: equality,
            value: true,
        });
    }
    (sum.values().all(Zero::is_zero) && total.is_positive()).then_some(())?;
    control.charge(
        occurrences.checked_mul(1usize.checked_shl(conflict.len() as u32)?)?,
        0,
    )?;
    super::super::verify_farkas_conflict_lits_linear_holds(
        terms,
        &conflict,
        &FarkasAnnotation {
            coefficients: annotation,
        },
    )
    .then_some(())
}

#[cfg(test)]
#[path = "inconsistent_equality_subset/tests.rs"]
mod tests;
