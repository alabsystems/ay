// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side readings of printed arithmetic, built from the same replay
//! of the pinned checker as the judgements in the parent module. They PLAN a
//! rendering, or refuse one; they never approve one: whatever a producer
//! ships is still judged by [`super::printed_la_generic_holds`] and
//! [`super::printed_poly_simp_holds`].

use super::{key, negate_disequality, read, Budget, LinearComb, Op, Polynomial};
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use std::collections::BTreeMap;

/// The pinned `la_generic` fold over printed literals with NO strengthening:
/// the summed row `atoms rel constant`, with `rel` exactly what the rows
/// entail over the reals — `>` when a strict row has a nonzero multiplier,
/// else `>=` when an inequality row does, else `=`. `None` when a literal
/// cannot be read as a `la_generic` row at all.
fn exact_fold(literals: &[&str], args: &[BigRational]) -> Option<(LinearComb, Op)> {
    if literals.len() != args.len() {
        return None;
    }
    let mut budget = Budget { nodes: 0 };
    let mut acc = LinearComb::default();
    let mut relation = Op::Equals;
    for (literal, a) in literals.iter().zip(args) {
        let literal = read(literal, 0, &mut budget)?;
        let (mut op, left, right) = negate_disequality(&literal)?;
        let mut row = LinearComb::from_term(left, &mut budget)?
            .sub(LinearComb::from_term(right, &mut budget)?);
        row.constant = -row.constant.clone();
        if matches!(op, Op::LessThan | Op::LessEq) {
            row.neg();
            op = if op == Op::LessThan {
                Op::GreaterThan
            } else {
                Op::GreaterEq
            };
        }
        let scale = if op == Op::Equals { a.clone() } else { a.abs() };
        if !scale.is_zero() {
            relation = match (relation, op) {
                (_, Op::GreaterThan) | (Op::GreaterThan, _) => Op::GreaterThan,
                (_, Op::GreaterEq) | (Op::GreaterEq, _) => Op::GreaterEq,
                _ => Op::Equals,
            };
        }
        row.mul(&scale);
        acc = acc.add(row);
    }
    Some((acc, relation))
}

/// The opaque atoms a `la_generic` combination over printed literals leaves
/// uncancelled, keyed exactly as the judgement keys them.
///
/// A PLANNING aid for a producer choosing which `poly_simp` rewrites to add,
/// never a verdict: strengthening only moves a row's constant, so the atom
/// residual is the pinned fold without it. `None` when a literal cannot be
/// read as a `la_generic` row at all.
pub(in crate::alethe_printer) fn printed_la_generic_atom_residual(
    literals: &[&str],
    args: &[BigRational],
) -> Option<BTreeMap<String, BigRational>> {
    exact_fold(literals, args).map(|(acc, _)| acc.atoms)
}

/// Whether a `la_generic` combination over printed literals refutes its
/// hypotheses over the REALS: the atoms cancel and `0 rel constant` is false
/// for the relation the rows really entail (see [`exact_fold`]).
///
/// A producer's REFUSAL test, never an approval. The pinned judgement
/// strengthens every row whose constant is integral with no sort check, so it
/// accepts, over `Real`, steps that are not theorems (`(not (> x 0.0))
/// (not (< x 1.0))` with args `1 1`). A lowering that requires this as well
/// never ships a step whose validity leans on that strengthening.
pub(in crate::alethe_printer) fn printed_la_generic_is_real_contradiction(
    literals: &[&str],
    args: &[BigRational],
) -> bool {
    let Some((acc, relation)) = exact_fold(literals, args) else {
        return false;
    };
    acc.atoms.is_empty()
        && match relation {
            Op::Equals => !acc.constant.is_zero(),
            Op::GreaterEq => acc.constant.is_positive(),
            Op::GreaterThan => !acc.constant.is_negative(),
            Op::LessThan | Op::LessEq => false,
        }
}

/// carcara's `poly_simp` normal form of one printed arithmetic term: its
/// monomials (sorted atom keys, one entry per power) with coefficients, and
/// its constant. `None` exactly where [`super::printed_poly_simp_holds`] has no
/// judgement.
pub(in crate::alethe_printer) fn printed_polynomial(
    text: &str,
) -> Option<(BTreeMap<Vec<String>, BigRational>, BigRational)> {
    let mut budget = Budget { nodes: 0 };
    let polynomial = Polynomial::from_term(&read(text, 0, &mut budget)?, 0, &mut budget)?;
    Some((polynomial.monomials, polynomial.constant))
}

/// The row `left − right` of a printed equality `(= left right)`, read
/// exactly as the pinned `la_generic` reads it: atom key → coefficient, and
/// the constant. A lowering that re-spells an internally certified literal
/// compares this to the row its certificate was computed for. `None` when
/// either side is unreadable or exceeds the replay's node budget.
pub(in crate::alethe_printer) fn printed_linear_difference(
    left: &str,
    right: &str,
) -> Option<(BTreeMap<String, BigRational>, BigRational)> {
    let mut budget = Budget { nodes: 0 };
    let left = LinearComb::from_term(&read(left, 0, &mut budget)?, &mut budget)?;
    let right = LinearComb::from_term(&read(right, 0, &mut budget)?, &mut budget)?;
    let difference = left.sub(right);
    Some((difference.atoms, difference.constant))
}

/// How the pinned `la_generic` reads the hypothesis one printed literal
/// contributes, before any strengthening.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::alethe_printer) enum PrintedRelation {
    /// `atoms = constant`.
    Equal,
    /// `atoms ≥ constant`.
    AtLeast,
    /// `atoms > constant`.
    Above,
}

/// The row `atoms rel constant` the pinned `la_generic` reads off one printed
/// clause literal: its negation, moved to one side, `<`/`≤` flipped to
/// `>`/`≥`. A lowering that re-spells a literal compares this to the row its
/// certificate was computed for. `None` when the literal is not a
/// `la_generic` row at all or exceeds the replay's node budget.
pub(in crate::alethe_printer) fn printed_hypothesis_row(
    literal: &str,
) -> Option<(PrintedRelation, BTreeMap<String, BigRational>, BigRational)> {
    let mut budget = Budget { nodes: 0 };
    let literal = read(literal, 0, &mut budget)?;
    let (op, left, right) = negate_disequality(&literal)?;
    let mut row =
        LinearComb::from_term(left, &mut budget)?.sub(LinearComb::from_term(right, &mut budget)?);
    row.constant = -row.constant.clone();
    if matches!(op, Op::LessThan | Op::LessEq) {
        row.neg();
    }
    let relation = match op {
        Op::Equals => PrintedRelation::Equal,
        Op::LessEq | Op::GreaterEq => PrintedRelation::AtLeast,
        Op::LessThan | Op::GreaterThan => PrintedRelation::Above,
    };
    Some((relation, row.atoms, row.constant))
}

/// The key the pinned `la_generic` files `printed` under as an opaque atom.
pub(in crate::alethe_printer) fn printed_atom_key(printed: &str) -> Option<String> {
    let mut budget = Budget { nodes: 0 };
    let mut out = String::new();
    key(&read(printed, 0, &mut budget)?, &mut out);
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn ints(values: &[i64]) -> Vec<BigRational> {
        values
            .iter()
            .map(|&value| BigRational::from_integer(BigInt::from(value)))
            .collect()
    }

    /// The pinned judgement accepts this over `Real` only through its
    /// sort-blind strengthening (`x > 0` read as `x >= 1`); `x = 0.5`
    /// satisfies both hypotheses, so it is no theorem and the real reading
    /// refuses it.
    #[test]
    fn a_step_only_integer_strengthening_accepts_is_not_a_real_contradiction() {
        let literals = ["(not (> x 0.0))", "(not (< x 1.0))"];
        assert!(super::super::printed_la_generic_holds(
            &literals,
            &["1", "1"]
        ));
        assert!(!printed_la_generic_is_real_contradiction(
            &literals,
            &ints(&[1, 1])
        ));
    }

    /// A strict row keeps the sum strict (`-x² > 0` plus `x² >= 0`), the
    /// sign of an equality row's multiplier is kept, and an inequality
    /// multiplier is read by magnitude, as the pinned fold reads it.
    #[test]
    fn real_contradictions_track_strictness_and_equalities() {
        let square = ["(not (< (* x x) 0.0))", "(not (>= (* x x) 0.0))"];
        assert!(printed_la_generic_is_real_contradiction(
            &square,
            &ints(&[1, 1])
        ));
        let weak = ["(not (<= (* x x) 0.0))", "(not (>= (* x x) 0.0))"];
        assert!(!printed_la_generic_is_real_contradiction(
            &weak,
            &ints(&[1, 1])
        ));
        // `x·y = 7` and `x·y <= 4`: `x·y - 7 = 0` plus `4 - x·y >= 0`.
        let equality = ["(not (= (* x y) 7))", "(not (<= (* x y) 4))"];
        assert!(printed_la_generic_is_real_contradiction(
            &equality,
            &ints(&[1, 1])
        ));
        assert!(printed_la_generic_is_real_contradiction(
            &equality,
            &ints(&[1, -1])
        ));
        assert!(!printed_la_generic_is_real_contradiction(
            &equality,
            &ints(&[-1, 1])
        ));
        assert!(!printed_la_generic_is_real_contradiction(
            &["(not (= x 0))"],
            &ints(&[0])
        ));
        assert!(!printed_la_generic_is_real_contradiction(
            &["(= x y)"],
            &ints(&[1])
        ));
    }
}
