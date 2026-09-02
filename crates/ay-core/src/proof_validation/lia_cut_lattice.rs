// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rank-1 two-row cut validation for WIDE integer clauses.
//!
//! [`super::lia_bound_lattice`] certifies a wide clause when the clause's own
//! literals already squeeze ONE shared linear form into a range holding no
//! attainable value. The empty-clause closer's heads on #4751 are not that
//! shape: their bounds sit on FIVE different linear forms, no form carries
//! both a lower and an upper bound, and that rule correctly declines. The
//! certificate that does work combines TWO rows first and applies the lattice
//! test to the DERIVED form.
//!
//! # The argument
//!
//! Write every parsed literal in one orientation, `F ≥ b` (an upper bound
//! `F ≤ b` is the same constraint as `-F ≥ -b`). For positive integers
//! `λ, μ`, `λ·(F_i − b_i) ≥ 0` and `μ·(F_j − b_j) ≥ 0` add to
//!
//! ```text
//! λ·F_i + μ·F_j  ≥  λ·b_i + μ·b_j
//! ```
//!
//! which is again an integer linear form with an integer bound. Adding these
//! DERIVED rows to the pool and then running the unchanged attainable-value
//! test of [`super::lia_bound_lattice`] on the enlarged pool is therefore
//! sound for exactly the reasons that module states: the derived form is a
//! ℤ-linear combination of all-`Int` forms, so Bézout still pins its values to
//! `g·ℤ` for `g = gcd` of its coefficients, and a range holding no multiple of
//! `g` is unsatisfiable over ℤ.
//!
//! Worked instance — the benchmark's own `cl#7` closer head, whose negation is
//! `D − 4A ≥ −2`, `A ≥ 0`, `C ≥ 0`, `C − A ≥ 0`, `D ≥ 0`, `D − 2A ≤ −1`:
//!
//! ```text
//! D ≥ 0            +  2A − D ≥ 1     ⟹   2A ≥ 1     (eliminate D, λ = μ = 1)
//! −4A + D ≥ −2     +  2A − D ≥ 1     ⟹  −2A ≥ −1    (eliminate D, λ = μ = 1)
//! g = gcd(2) = 2,  2·⌈1/2⌉ = 2 > 1   ⟹  no integer A
//! ```
//!
//! Rationally the same system is satisfiable (`A = 1/2, C = 1/2, D = 9/10`),
//! which is why no Farkas certificate exists for these clauses and why an
//! independent LRA solve over the negation declines.
//!
//! # Why the multiplier search is BOUNDED, and what that costs
//!
//! General cutting-plane multiplier synthesis is an unbounded search — the
//! multipliers are the solution of a linear program over an unbounded cone,
//! and a certificate may need arbitrarily many rows at arbitrary Chvátal rank.
//! This module deliberately does NOT search that space. It enumerates exactly
//! one canonical multiplier pair per (row, row, shared variable) triple: the
//! Fourier–Motzkin/Gomory ELIMINATION pair
//!
//! ```text
//! g = gcd(|c_i|, |c_j|),   λ = |c_j| / g,   μ = |c_i| / g
//! ```
//!
//! for a variable whose coefficients have OPPOSITE signs in the two rows —
//! the unique smallest positive pair that cancels it. That is `O(rows² ·
//! vars)` work with no search and no LP, and it is complete only for rank-1,
//! two-row, variable-eliminating certificates. Everything outside that class
//! is declined, fail-closed: a decline is never evidence that a clause is
//! false.
//!
//! # Why there is no payload
//!
//! The multipliers are re-derived here from the clause, so the strict checker
//! and the producer-side classifier call the SAME function and cannot drift,
//! and there is no annotation for a producer to forge. That is the same
//! discipline [`super::lia_bound_lattice`] adopts, and it is what lets the
//! empty-clause closer offer this kind at all: its standing objection — that a
//! payload-less arithmetic kind converts a rescuable `Generic` rejection into
//! a hard `InvalidTheoryLemma` one — does not apply to a kind whose recognizer
//! IS its validator.

use std::collections::BTreeMap;

use num_bigint::BigInt;

use crate::{TermId, TermStore};

/// Canonical integer linear form: variable/opaque-atom term → coefficient.
/// Zero coefficients are never present, so two spellings of the same form
/// compare equal as map keys.
type Coeffs = BTreeMap<TermId, BigInt>;

/// The most bound rows this rule will consider on one clause.
///
/// The pair enumeration is quadratic, and the strict checker runs under a work
/// envelope this must not exhaust. A clause with more parsed bounds than this
/// is declined OUTRIGHT rather than truncated: truncating would make
/// acceptance depend on literal order, so a producer could hide a rejection by
/// permuting a clause.
const MAX_CUT_ROWS: usize = 48;

/// Which row of the derivation supplied one side of the gap.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CutRow {
    /// A literal of the clause, read directly.
    Literal(usize),
    /// `left_multiplier·left + right_multiplier·right`, both multipliers
    /// positive, both rows taken in their `≥` orientation.
    Combination {
        /// Clause index of the first row.
        left: usize,
        /// Clause index of the second row.
        right: usize,
        /// Positive multiplier applied to `left`.
        left_multiplier: BigInt,
        /// Positive multiplier applied to `right`.
        right_multiplier: BigInt,
    },
}

/// The narrow integer core that makes a wide clause valid under a rank-1
/// two-row cut.
///
/// Returned by [`int_cut_lattice_gap_core`] so tests and diagnostics can
/// re-check an accept independently of the recognizer that produced it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct IntCutLatticeGap {
    /// Row supplying the greatest lower bound on the shared derived form.
    pub lower_row: CutRow,
    /// Row supplying the least upper bound on the shared derived form.
    pub upper_row: CutRow,
    /// The derived form itself, in canonical (leading-coefficient-positive)
    /// orientation.
    pub form: BTreeMap<TermId, BigInt>,
    /// `gcd` of the derived form's coefficients; always `>= 1`.
    pub gcd: BigInt,
    /// Greatest lower bound the clause's negation forces on the form.
    pub lower: BigInt,
    /// Least upper bound the clause's negation forces on the form.
    pub upper: BigInt,
}

/// Recognize a WIDE integer clause made valid by a rank-1 two-row cut and the
/// attainable-value test.
///
/// This is the exact inverse of the strict checker's
/// `validate_int_cut_lattice_gap`, so a classifier that promotes a lemma to
/// [`crate::TheoryLemmaKind::IntCutLatticeGap`] can never drift from the
/// checker that must re-validate it.
///
/// Strictly SUBSUMES [`super::recognize_int_bound_lattice_gap`]: the clause's
/// own rows are in the pool before any combination is added.
#[must_use]
pub fn recognize_int_cut_lattice_gap(terms: &TermStore, clause: &[TermId]) -> bool {
    int_cut_lattice_gap_core(terms, clause).is_some()
}

/// The witnessing core of [`recognize_int_cut_lattice_gap`], or `None` when no
/// row of the clause and no canonical two-row elimination of a pair of them
/// exhibits an attainable-value gap.
#[must_use]
pub fn int_cut_lattice_gap_core(terms: &TermStore, clause: &[TermId]) -> Option<IntCutLatticeGap> {
    let rows = parse_ge_rows(terms, clause)?;
    let mut pool = BoundPool::default();
    for row in &rows {
        pool.insert(row, CutRow::Literal(row.literal));
    }
    if let Some(gap) = pool.find_gap() {
        return Some(gap);
    }
    // Upper-triangle pair walk without index arithmetic: each outer step
    // leaves `pairs` positioned just past `i`, so its clone enumerates exactly
    // the `j > i` suffix with the original indices intact.
    let mut pairs = rows.iter().enumerate();
    while let Some((i, left)) = pairs.next() {
        for (j, right) in pairs.clone() {
            for (derived, multipliers) in eliminating_combinations(left, right) {
                pool.insert(
                    &derived,
                    CutRow::Combination {
                        left: i,
                        right: j,
                        left_multiplier: multipliers.0,
                        right_multiplier: multipliers.1,
                    },
                );
            }
        }
    }
    pool.find_gap()
}

/// One constraint in the single orientation the whole module works in:
/// `form >= bound`, with no zero coefficients in `form`.
#[derive(Debug, Clone)]
struct GeRow {
    /// Index INTO THE CLAUSE of the literal this row was read from, so a
    /// witness names the literal a reader can look up rather than a position
    /// in the filtered row list.
    literal: usize,
    form: Coeffs,
    bound: BigInt,
}

/// Read every literal that parses as an integer bound as a `≥` row.
///
/// `parse_int_bound` returns the constraint that holds when the literal is
/// FALSE — exactly the blocking-clause negation semantics the argument needs.
/// Literals that are not integer bounds (Boolean atoms, `(not true)`,
/// equalities, `Real` arithmetic) are SKIPPED, which is sound because dropping
/// conjuncts only weakens the hypothesis being refuted.
fn parse_ge_rows(terms: &TermStore, clause: &[TermId]) -> Option<Vec<GeRow>> {
    let mut rows = Vec::new();
    for (index, &literal) in clause.iter().enumerate() {
        let Some((coeffs, is_upper, value)) = super::lia::parse_int_bound(terms, literal) else {
            continue;
        };
        // `F <= v` is the same constraint as `-F >= -v`; carrying one
        // orientation removes the direction from every combination rule below.
        let row = if is_upper {
            GeRow {
                literal: index,
                form: coeffs.into_iter().map(|(v, c)| (v, -c)).collect(),
                bound: -value,
            }
        } else {
            GeRow {
                literal: index,
                form: coeffs,
                bound: value,
            }
        };
        // A variable-free "form" is the constant 0, not a lattice. It is NOT
        // filtered here: `BoundPool::find_gap`'s `gcd.is_positive()` is the
        // single live guard for that case, so it stays reachable and therefore
        // mutation-checkable.
        rows.push(row);
        if rows.len() > MAX_CUT_ROWS {
            return None;
        }
    }
    (rows.len() >= 2).then_some(rows)
}

/// Every canonical elimination of one shared variable between two `≥` rows,
/// with the positive multipliers that produced it.
///
/// A variable can be cancelled by a NON-NEGATIVE combination only when its two
/// coefficients have OPPOSITE signs; with equal signs the combination adds
/// them and cancels nothing. For opposite signs the unique smallest positive
/// pair is `(|c_j|/g, |c_i|/g)` with `g = gcd(|c_i|, |c_j|)`.
fn eliminating_combinations(left: &GeRow, right: &GeRow) -> Vec<(GeRow, (BigInt, BigInt))> {
    use num_integer::Integer;
    use num_traits::Signed;
    let mut out = Vec::new();
    for (var, left_coeff) in &left.form {
        let Some(right_coeff) = right.form.get(var) else {
            continue;
        };
        if left_coeff.is_negative() == right_coeff.is_negative() {
            continue;
        }
        let gcd = left_coeff.abs().gcd(&right_coeff.abs());
        let left_multiplier = right_coeff.abs() / &gcd;
        let right_multiplier = left_coeff.abs() / &gcd;
        let mut form: Coeffs = BTreeMap::new();
        for (v, c) in &left.form {
            form.insert(*v, c * &left_multiplier);
        }
        for (v, c) in &right.form {
            let scaled = c * &right_multiplier;
            match form.entry(*v) {
                std::collections::btree_map::Entry::Occupied(mut slot) => {
                    let sum = slot.get() + &scaled;
                    if sum == BigInt::from(0) {
                        slot.remove();
                    } else {
                        slot.insert(sum);
                    }
                }
                std::collections::btree_map::Entry::Vacant(slot) => {
                    slot.insert(scaled);
                }
            }
        }
        // Every variable may have cancelled, leaving a ground `0 >= k`. That
        // is a RATIONAL contradiction when `k > 0`, which the Farkas
        // validators own and the lattice argument does not apply to; it is
        // declined by `find_gap`'s `gcd.is_positive()` rather than filtered
        // here, so that guard stays the single live one.
        let bound = &left.bound * &left_multiplier + &right.bound * &right_multiplier;
        out.push((
            GeRow {
                literal: left.literal,
                form,
                bound,
            },
            (left_multiplier, right_multiplier),
        ));
    }
    out
}

/// The tightest lower and upper bound seen for each canonical linear form,
/// each tagged with the row that supplied it.
/// The tightest bound seen in one direction, with the row that supplied it.
type Extremum = Option<(CutRow, BigInt)>;

#[derive(Default)]
struct BoundPool {
    groups: BTreeMap<Coeffs, (Extremum, Extremum)>,
}

impl BoundPool {
    /// Record `row` under its canonical form.
    ///
    /// Canonicalization multiplies the row by `-1` when its leading
    /// coefficient is negative, which flips the direction and negates the
    /// bound. That is the SAME normalization `parse_int_comparison` applies,
    /// so a derived row and a literal row describing one linear form always
    /// land in one group.
    fn insert(&mut self, row: &GeRow, provenance: CutRow) {
        use num_traits::Signed;
        let leading_negative = row.form.values().next().is_some_and(BigInt::is_negative);
        let (form, is_upper, value) = if leading_negative {
            (
                row.form.iter().map(|(v, c)| (*v, -c)).collect(),
                true,
                -row.bound.clone(),
            )
        } else {
            (row.form.clone(), false, row.bound.clone())
        };
        let (lower_slot, upper_slot) = self.groups.entry(form).or_default();
        let slot = if is_upper { upper_slot } else { lower_slot };
        // Keep the TIGHTEST bound in each direction: the best pair for the
        // lattice test is the greatest lower with the least upper, so a
        // per-group extremum makes the search exhaustive over pairs without
        // enumerating them.
        let tighter = slot.as_ref().is_none_or(|(_, current)| {
            if is_upper {
                &value < current
            } else {
                &value > current
            }
        });
        if tighter {
            *slot = Some((provenance, value));
        }
    }

    /// The first group whose range holds no attainable value.
    fn find_gap(&self) -> Option<IntCutLatticeGap> {
        use num_integer::Integer;
        use num_traits::{Signed, Zero};
        for (form, (lower, upper)) in &self.groups {
            let (Some((lower_row, lower_value)), Some((upper_row, upper_value))) = (lower, upper)
            else {
                continue;
            };
            let mut gcd = BigInt::zero();
            for coeff in form.values() {
                gcd = gcd.gcd(&coeff.abs());
            }
            if !gcd.is_positive() {
                continue;
            }
            // Smallest attainable value `>= lower`; the range holds no
            // attainable value exactly when that overshoots `upper`. This
            // subsumes the plain `lower > upper` bounds gap, for which the
            // smallest attainable value is already `>= lower > upper`.
            if &gcd * lower_value.div_ceil(&gcd) > *upper_value {
                return Some(IntCutLatticeGap {
                    lower_row: lower_row.clone(),
                    upper_row: upper_row.clone(),
                    form: form.clone(),
                    gcd,
                    lower: lower_value.clone(),
                    upper: upper_value.clone(),
                });
            }
        }
        None
    }
}
