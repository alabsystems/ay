// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer multipliers behind an all-equality lattice clause.
//!
//! [`super::lia_guarded_split`] certifies a clause whose literals are all
//! negated integer equalities `(not (= lhs_i rhs_i))` through its zero-split
//! case: substitute away every equality row that has a `±1` pivot, then apply
//! the attainable-value gap test to the residual rows and to their canonical
//! two-row eliminations. Every row that procedure touches is an INTEGER
//! combination of the clause's own rows: a `±1` pivot substitutes with an
//! integer scale, and an elimination pair has integer multipliers. So when it
//! refutes the clause's negation, one integer vector `λ` exists for which the
//! single derived equality
//!
//! ```text
//! D = Σ λ_i·(lhs_i − rhs_i) = 0
//! ```
//!
//! is refuted on its own: either `D` is a nonzero constant, or the gcd `g` of
//! `D`'s variable coefficients does not divide `D`'s constant `d`, so by
//! Bézout `D` only takes values in `d + gℤ`, which skips zero. Every model of
//! the clause's negation satisfies `D = 0`, hence none exists and the clause
//! is valid. The second case is exactly the unit divisibility theorem that
//! [`super::lia::lia_divisibility_equality_witness`] lowers, stated for a
//! derived equality.
//!
//! [`lia_equality_lattice_witness`] first reads every literal as an all-`Int`
//! negated-equality row (declining the whole clause otherwise), then re-runs
//! the strict checker's own recognizer
//! ([`super::recognize_int_guarded_split_gap`]) on the clause, so a witness
//! exists only for a clause the checker certifies — the binding the
//! unit lowering's [`super::lia::lia_divisibility_equality_witness`] has to
//! `validate_divisibility`. It then replays the elimination while carrying
//! each derived row's multiplier vector over the clause literals, and returns
//! the `λ` of the first refuting row. Finally it recomputes `D` DIRECTLY from
//! the literals and `λ` through the shared `int_linear_diff` normalizer (so
//! the all-`Int` sort guard applies to every variable) and re-runs the test.
//! A bookkeeping mistake can therefore only produce a decline, never a witness
//! whose arithmetic does not hold.
//!
//! The replay mirrors the validator's own order (first row with a `±1`
//! coefficient, first such variable, `swap_remove`), so on an all-equality
//! clause it reaches the same residual rows, and it tests at least every row
//! the validator's gap pool tests: a residual row, each canonical pair of
//! residual rows, and — where two such rows share one form with different
//! constants — their difference, which is a nonzero constant.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::term::{Symbol, TermData};
use crate::{TermId, TermStore};

/// Canonical integer linear form: variable/opaque-atom term → coefficient.
type Coeffs = BTreeMap<TermId, BigInt>;

/// The widest clause this witness search considers, the validator's own row
/// cap. A wider clause is declined outright, never truncated, so the answer
/// cannot depend on literal order.
const MAX_LATTICE_EQUALITIES: usize = 96;

/// An integer combination of a clause's negated equalities that has no
/// integer solution on its own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiaEqualityLatticeWitness {
    /// `(lhs_i, rhs_i)` of each clause literal `(not (= lhs_i rhs_i))`, in
    /// clause order.
    pub equalities: Vec<(TermId, TermId)>,
    /// `lhs_i − rhs_i` of each literal as the shared normalizer reads it:
    /// all-`Int` variable/opaque-atom coefficients and the constant. A
    /// lowering that re-spells a literal compares its printed row to this.
    pub rows: Vec<(BTreeMap<TermId, BigInt>, BigInt)>,
    /// The integer multiplier `λ_i` of `lhs_i − rhs_i` in `D`, in clause
    /// order. Zero for a literal the combination does not use.
    pub multipliers: Vec<BigInt>,
    /// `Some((lower, upper))`: the greatest value of `D` below zero and the
    /// least above it, `upper − lower = g`. `None`: `D` has no variable and is
    /// a nonzero constant.
    pub gap: Option<(BigInt, BigInt)>,
}

/// One row `form = bound` with its multipliers over the clause literals.
#[derive(Debug, Clone)]
struct Row {
    form: Coeffs,
    bound: BigInt,
    multipliers: Vec<BigInt>,
}

impl Row {
    /// `left_scale·self + right_scale·other`.
    fn combine(&self, left_scale: &BigInt, other: &Row, right_scale: &BigInt) -> Row {
        let mut form: Coeffs = self
            .form
            .iter()
            .map(|(term, coeff)| (*term, coeff * left_scale))
            .collect();
        for (term, coeff) in &other.form {
            *form.entry(*term).or_insert_with(BigInt::zero) += coeff * right_scale;
        }
        form.retain(|_, coeff| !coeff.is_zero());
        Row {
            form,
            bound: &self.bound * left_scale + &other.bound * right_scale,
            multipliers: self
                .multipliers
                .iter()
                .zip(&other.multipliers)
                .map(|(left, right)| left * left_scale + right * right_scale)
                .collect(),
        }
    }

    fn negated(&self) -> Row {
        Row {
            form: self
                .form
                .iter()
                .map(|(term, coeff)| (*term, -coeff))
                .collect(),
            bound: -&self.bound,
            multipliers: self.multipliers.iter().map(|m| -m).collect(),
        }
    }

    /// Whether this row alone has no integer solution.
    fn refutes(&self) -> bool {
        let gcd = form_gcd(&self.form);
        if gcd.is_zero() {
            !self.bound.is_zero()
        } else {
            !(&self.bound % &gcd).is_zero()
        }
    }
}

fn form_gcd(form: &Coeffs) -> BigInt {
    form.values()
        .fold(BigInt::zero(), |gcd, coeff| gcd.gcd(&coeff.abs()))
}

/// The validator's gap pool, carrying multipliers: one row per canonical
/// (leading-coefficient-positive) form.
#[derive(Default)]
struct Pool {
    rows: BTreeMap<Coeffs, Row>,
}

impl Pool {
    /// Offer one derived row; the multipliers of a refuting row, if any.
    fn offer(&mut self, row: Row) -> Option<Vec<BigInt>> {
        if row.refutes() {
            return Some(row.multipliers);
        }
        if row.form.is_empty() {
            return None;
        }
        let row = if row.form.values().next().is_some_and(BigInt::is_negative) {
            row.negated()
        } else {
            row
        };
        match self.rows.get(&row.form) {
            // One form pinned to two different values: the difference is a
            // nonzero constant.
            Some(existing) if existing.bound != row.bound => {
                let difference = row.combine(&BigInt::one(), existing, &-BigInt::one());
                difference.refutes().then_some(difference.multipliers)
            }
            Some(_) => None,
            None => {
                let _ = self.rows.insert(row.form.clone(), row);
                None
            }
        }
    }
}

/// Recover the integer combination behind an all-equality lattice clause.
///
/// Every literal must be `(not (= lhs rhs))` over all-`Int` linear operands,
/// and the strict checker's guarded-split recognizer must accept the clause;
/// any other clause, one wider than the validator's row cap, and one whose
/// negation this elimination cannot refute return `None`. See the module docs.
#[must_use]
pub fn lia_equality_lattice_witness(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<LiaEqualityLatticeWitness> {
    if clause.is_empty() || clause.len() > MAX_LATTICE_EQUALITIES {
        return None;
    }
    // The cheap shape test first: every literal an all-`Int` negated equality.
    let mut equalities = Vec::with_capacity(clause.len());
    let mut rows = Vec::with_capacity(clause.len());
    for (index, &literal) in clause.iter().enumerate() {
        let (lhs, rhs) = negated_equality_operands(terms, literal)?;
        let (form, constant) = super::lia::int_linear_diff(terms, lhs, rhs)?;
        let mut multipliers = vec![BigInt::zero(); clause.len()];
        multipliers[index] = BigInt::one();
        equalities.push((lhs, rhs));
        rows.push(Row {
            form,
            bound: -constant,
            multipliers,
        });
    }
    // Bind this carrier to the strict checker: a clause it does not certify
    // has no witness, whatever the replay below would find.
    if !super::recognize_int_guarded_split_gap(terms, clause) {
        return None;
    }
    let multipliers = refuting_combination(rows)?;
    checked_witness(terms, equalities, multipliers)
}

fn negated_equality_operands(terms: &TermStore, literal: TermId) -> Option<(TermId, TermId)> {
    let TermData::Not(inner) = terms.get(literal) else {
        return None;
    };
    match terms.get(*inner) {
        TermData::App(Symbol::Named(name), args) if name == "=" => match args.as_slice() {
            [lhs, rhs] => Some((*lhs, *rhs)),
            _ => None,
        },
        _ => None,
    }
}

/// The validator's equality-only procedure, carrying multipliers.
fn refuting_combination(mut rows: Vec<Row>) -> Option<Vec<BigInt>> {
    // (1) `±1` pivot substitution to fixpoint, in the validator's order.
    for _ in 0..rows.len() {
        let Some((index, pivot, k)) = rows.iter().enumerate().find_map(|(index, row)| {
            row.form
                .iter()
                .find(|(_, coeff)| coeff.abs().is_one())
                .map(|(term, coeff)| (index, *term, coeff.clone()))
        }) else {
            break;
        };
        let pivot_row = rows.swap_remove(index);
        rows = rows
            .into_iter()
            .map(|row| match row.form.get(&pivot) {
                // `row − (m/k)·pivot_row` removes the pivot; exact, `k = ±1`.
                Some(m) => {
                    let scale = -(m / &k);
                    row.combine(&BigInt::one(), &pivot_row, &scale)
                }
                None => row,
            })
            .collect();
    }
    // (2)-(3) Residual rows, then (4) each canonical elimination pair.
    let mut pool = Pool::default();
    for row in &rows {
        if let Some(multipliers) = pool.offer(row.clone()) {
            return Some(multipliers);
        }
    }
    for (index, left) in rows.iter().enumerate() {
        for right in &rows[index + 1..] {
            for (term, left_coeff) in &left.form {
                let Some(right_coeff) = right.form.get(term) else {
                    continue;
                };
                let gcd = left_coeff.abs().gcd(&right_coeff.abs());
                let left_scale = right_coeff.abs() / &gcd;
                let right_scale = if left_coeff.is_negative() == right_coeff.is_negative() {
                    -(left_coeff.abs() / &gcd)
                } else {
                    left_coeff.abs() / &gcd
                };
                if let Some(multipliers) =
                    pool.offer(left.combine(&left_scale, right, &right_scale))
                {
                    return Some(multipliers);
                }
            }
        }
    }
    None
}

/// Recompute `D` from the literals and `λ` alone and re-run the test.
fn checked_witness(
    terms: &TermStore,
    equalities: Vec<(TermId, TermId)>,
    multipliers: Vec<BigInt>,
) -> Option<LiaEqualityLatticeWitness> {
    let mut rows = Vec::with_capacity(equalities.len());
    let mut form = Coeffs::new();
    let mut constant = BigInt::zero();
    for (&(lhs, rhs), multiplier) in equalities.iter().zip(&multipliers) {
        let (row, row_constant) = super::lia::int_linear_diff(terms, lhs, rhs)?;
        for (term, coeff) in &row {
            let entry = form.entry(*term).or_insert_with(BigInt::zero);
            *entry += coeff * multiplier;
            if entry.is_zero() {
                let _ = form.remove(term);
            }
        }
        constant += &row_constant * multiplier;
        rows.push((row, row_constant));
    }
    let gcd = form_gcd(&form);
    let gap = if gcd.is_zero() {
        if constant.is_zero() {
            return None;
        }
        None
    } else {
        if (&constant % &gcd).is_zero() {
            return None;
        }
        // `D ∈ constant + gℤ`, which skips zero: its neighbours around zero.
        let upper = constant.mod_floor(&gcd);
        Some((&upper - &gcd, upper))
    };
    Some(LiaEqualityLatticeWitness {
        equalities,
        rows,
        multipliers,
        gap,
    })
}
