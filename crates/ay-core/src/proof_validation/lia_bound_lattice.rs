// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer bound-lattice validation for WIDE arithmetic clauses.
//!
//! The existing integer recognizers in [`super::lia`] are unit- and pair-sized:
//! `recognize_lia_divisibility` takes exactly one negated equality (or exactly
//! two bounds), and `recognize_rounded_integer_bounds_gap` takes exactly two
//! literals over an IDENTICAL coefficient map. A learned CDCL(T) conflict
//! clause is not that shape: it is 7-34 literals wide, and most of those
//! literals are irrelevant to why it is valid.
//!
//! This module certifies such a clause by finding the narrow integer CORE
//! inside it and re-deriving that core's infeasibility from the clause alone.
//!
//! # The argument
//!
//! A clause `C = l_1 ∨ … ∨ l_n` is valid over the integers exactly when the
//! conjunction of the NEGATIONS of its literals has no integer solution.
//! [`super::lia::parse_int_bound`] converts each literal to precisely the
//! constraint asserted by that literal being FALSE — an upper or lower bound on
//! an all-`Int` linear form `L = Σ cᵥ·v`, with strict inequalities already
//! rounded (`L < k` ⟹ `L ≤ k-1`, licensed because every `cᵥ` and every `v` is
//! integral).
//!
//! Group the parsed bounds by their canonical linear form. Within one group,
//! let `lo` be the greatest lower bound and `hi` the least upper bound, and let
//! `g = gcd(cᵥ)`. By Bézout the set `{Σ cᵥ·zᵥ : z ∈ ℤᵏ}` is exactly `g·ℤ`, so
//! `L` can only ever take values that are multiples of `g`. If no multiple of
//! `g` lies in `[lo, hi]` the group's constraints are jointly unsatisfiable
//! over the integers, hence the whole clause is a tautology.
//!
//! Three properties make dropping the rest of the clause sound:
//!
//! * **Dropping conjuncts only weakens the hypothesis.** Showing that a SUBSET
//!   of the negated literals is already infeasible shows the full conjunction
//!   is infeasible. Literals that do not parse as integer bounds — Boolean
//!   atoms, `(not true)`, equalities, `Real` arithmetic — are simply skipped.
//! * **Over-approximating each atom's range is sound in the same direction.**
//!   `parse_linear_expr` normalizes a genuinely nonlinear or uninterpreted
//!   `Int`-sorted subterm to an OPAQUE atom, which this argument then treats as
//!   an unconstrained integer. The reachable set of `L` is therefore a SUBSET
//!   of `g·ℤ`, and a set disjoint from `[lo, hi]` stays disjoint under
//!   restriction.
//! * **Integrality is load-bearing and enforced.** `int_linear_diff` fails
//!   CLOSED on any non-`Int`-sorted variable and on any non-integral
//!   coefficient or constant, so a `Real` form — which can sit strictly between
//!   two lattice points, e.g. `2q ∈ [1,1]` at `q = 1/2` — can never reach here.
//!   That example is also exactly why these clauses have NO rational Farkas
//!   certificate: their negations are satisfiable over ℚ.
//!
//! # Why this is not a generic weakening of the checker
//!
//! The recognizer re-derives the core from the CLAUSE, taking nothing on the
//! producer's word: there is no annotation payload, so there is nothing to
//! forge. A clause it accepts is a genuine integer tautology (proof above);
//! every other clause is rejected fail-closed. It is therefore safe for the
//! strict checker and the producer-side classifier to call the SAME function,
//! which is what keeps the two from drifting.

use std::collections::BTreeMap;

use num_bigint::BigInt;

use crate::{TermId, TermStore};

/// Canonical integer linear form: variable/opaque-atom term → coefficient.
type Coeffs = BTreeMap<TermId, BigInt>;

/// The narrow integer core that makes a wide clause valid.
///
/// Returned by [`int_bound_lattice_gap_core`] so tests and diagnostics can
/// re-check an accept independently of the recognizer that produced it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct IntBoundLatticeGap {
    /// Index into the clause of the literal supplying the greatest lower bound.
    pub lower_literal: usize,
    /// Index into the clause of the literal supplying the least upper bound.
    pub upper_literal: usize,
    /// `gcd` of the shared linear form's coefficients; always `>= 1`.
    pub gcd: BigInt,
    /// Greatest lower bound the clause's negation forces on the linear form.
    pub lower: BigInt,
    /// Least upper bound the clause's negation forces on the linear form.
    pub upper: BigInt,
}

/// Recognize a WIDE integer clause that is valid because some shared linear
/// form inside it is squeezed into a range holding no attainable value.
///
/// This is the exact inverse of the strict checker's
/// `validate_int_bound_lattice_gap`, so a classifier that promotes a lemma to
/// [`crate::TheoryLemmaKind::IntBoundLatticeGap`] can never drift from the
/// checker that must re-validate it.
#[must_use]
pub fn recognize_int_bound_lattice_gap(terms: &TermStore, clause: &[TermId]) -> bool {
    int_bound_lattice_gap_core(terms, clause).is_some() || ite_constant_range_gap(terms, clause)
}

/// Largest number of literals the ITE-range scan reads, and the deepest `not`
/// nesting it will unwrap. Both only ever REJECT.
const MAX_ITE_RANGE_LITERALS: usize = 96;
const MAX_ITE_RANGE_NOT_DEPTH: usize = 8;

/// `[lo, hi]` when `term` is an `ite` whose BOTH branches are integer
/// constants, so the term's value set is `{k1, k2}` in every structure.
///
/// The condition is on the branches alone; the `ite` CONDITION is not read at
/// all, and no case analysis is performed. That is what makes the bound
/// unconditional rather than a claim about which branch is taken.
fn ite_constant_range(terms: &TermStore, term: TermId) -> Option<(BigInt, BigInt)> {
    use crate::term::TermData;
    let TermData::Ite(_, then_branch, else_branch) = terms.get(term) else {
        return None;
    };
    let (then_branch, else_branch) = (*then_branch, *else_branch);
    let value = |branch: TermId| match terms.get(branch) {
        TermData::Const(crate::Constant::Int(n)) => Some(n.clone()),
        _ => None,
    };
    let (a, b) = (value(then_branch)?, value(else_branch)?);
    Some(if a <= b { (a, b) } else { (b, a) })
}

/// Recognize a clause made valid by ONE literal whose bound on an
/// `ite`-of-integer-constants atom is already outside that atom's VALUE RANGE.
///
/// # The argument
///
/// A literal that is a (possibly repeatedly negated) integer comparison
/// contributes, when the literal is FALSE, exactly the row
/// [`super::lia::parse_int_comparison_row`] returns for the atom at the truth
/// value the negation PARITY forces. Take a literal whose row constrains the
/// canonical form `L = 1·A` for an atom `A = (ite c k1 k2)` with `k1, k2`
/// integer constants. `A` denotes `k1` or `k2` in EVERY structure, so
/// `lo <= L <= hi` for `lo = min(k1,k2)`, `hi = max(k1,k2)` — unconditionally,
/// with no case analysis and no reading of `c`. If the row is an UPPER bound
/// below `lo`, or a LOWER bound above `hi`, the clause's negation forces `L`
/// out of its own range and is unsatisfiable, so the clause is a tautology.
///
/// Everything else is fail-closed: `parse_int_comparison_row` already refuses a
/// non-`Int` sort, a non-integral coefficient and a non-comparison atom; a form
/// that is not a SINGLE atom at coefficient exactly `1` is skipped (a scaled or
/// mixed form would need the scaled range, which this rule deliberately does
/// not compute); an `ite` with a non-constant branch is skipped; and both work
/// bounds above only reject.
///
/// The measured population is the `dillig32_000` / `half_true_modif_m_000`
/// CHC family, whose conflicts carry `(not (< (ite (= C 0) 1 0) 0))` and
/// `(not (not (<= 0 (ite (= C 0) 1 0))))`. `parse_linear_expr` normalizes the
/// `ite` to an unconstrained opaque atom — sound, but it loses exactly the fact
/// that makes those clauses valid, which is why the lattice search above finds
/// no group with both bounds.
fn ite_constant_range_gap(terms: &TermStore, clause: &[TermId]) -> bool {
    use crate::term::TermData;
    use num_traits::One;
    if clause.len() > MAX_ITE_RANGE_LITERALS {
        return false;
    }
    for &literal in clause {
        // Negation PARITY, not one wrapper: the literal is FALSE exactly when
        // its atom takes the value the parity forces, which is the same
        // blocking-row contract `parse_int_bound` states for a single `not`.
        let mut atom = literal;
        let mut asserted = false;
        let mut depth = 0usize;
        while let TermData::Not(inner) = terms.get(atom) {
            atom = *inner;
            asserted = !asserted;
            depth += 1;
            if depth > MAX_ITE_RANGE_NOT_DEPTH {
                return false;
            }
        }
        let Some((coeffs, is_upper, value)) =
            super::lia::parse_int_comparison_row(terms, atom, asserted)
        else {
            continue;
        };
        let mut entries = coeffs.iter();
        let (Some((&form_atom, coefficient)), None) = (entries.next(), entries.next()) else {
            continue;
        };
        if !coefficient.is_one() {
            continue;
        }
        let Some((lo, hi)) = ite_constant_range(terms, form_atom) else {
            continue;
        };
        if is_upper {
            if value < lo {
                return true;
            }
        } else if value > hi {
            return true;
        }
    }
    false
}

/// The witnessing core of [`recognize_int_bound_lattice_gap`], or `None` when
/// no group of the clause's literals exhibits one.
///
/// Every rejection is fail-closed: a literal that does not parse as an integer
/// bound is skipped, a group without BOTH a lower and an upper bound is
/// skipped, a variable-free form (`g = 0`, so `L` is the constant `0` and the
/// lattice argument does not apply) is skipped, and a range that does contain
/// an attainable multiple is skipped.
#[must_use]
pub fn int_bound_lattice_gap_core(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<IntBoundLatticeGap> {
    use num_integer::Integer;
    use num_traits::{Signed, Zero};

    type Extremum = Option<(usize, BigInt)>;
    let mut groups: BTreeMap<Coeffs, (Extremum, Extremum)> = BTreeMap::new();
    for (index, &literal) in clause.iter().enumerate() {
        // `parse_int_bound` returns the constraint that holds when THIS literal
        // is false — exactly the blocking-clause negation semantics the
        // argument above needs.
        let Some((coeffs, is_upper, value)) = super::lia::parse_int_bound(terms, literal) else {
            continue;
        };
        let (lower_slot, upper_slot) = groups.entry(coeffs).or_default();
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
            *slot = Some((index, value));
        }
    }

    for (coeffs, (lower, upper)) in groups {
        let (Some((lower_literal, lower)), Some((upper_literal, upper))) = (lower, upper) else {
            continue;
        };
        let mut gcd = BigInt::zero();
        for coeff in coeffs.values() {
            gcd = gcd.gcd(&coeff.abs());
        }
        // `g = 0` means the "linear form" has no variables at all, so it is the
        // constant `0` rather than a lattice; that degenerate clause is left to
        // the ground evaluators (fail-closed here).
        if !gcd.is_positive() {
            continue;
        }
        // Smallest attainable value `>= lower`; the range holds no attainable
        // value exactly when that overshoots `upper`. This subsumes the plain
        // `lower > upper` bounds gap, for which the smallest attainable value
        // is already `>= lower > upper`.
        if &gcd * lower.div_ceil(&gcd) > upper {
            return Some(IntBoundLatticeGap {
                lower_literal,
                upper_literal,
                gcd,
                lower,
                upper,
            });
        }
    }
    None
}
