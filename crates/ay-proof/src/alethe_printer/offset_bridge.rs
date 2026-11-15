// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whether an equality between two offset words may be bridged to its shared
//! difference, decided on the PRINTED text.
//!
//! The strict checker validates `(= (bvadd c1 x) (bvadd c2 y))` as
//! `(= (bvsub x y) k)` (`TermStore::bv_offset_equality`). A lowering that
//! blasts the difference instead of the authored atom proves the bridge
//!
//! ```text
//! poly_simp      (= (bvmul 1 (bvsub lhs rhs)) (bvmul f (bvsub left right)))
//! poly_simp_rel  (= (= lhs rhs) (= left right))
//! ```
//!
//! with `f` one or minus one (both odd, as the bit-vector case of
//! `poly_simp_rel` requires). The term store's reading only selects the
//! words; [`printed_factor`] decides the step on what the consumer's
//! `poly_simp` normalizes: both sides read as linear forms over their printed
//! atoms (`bvadd`, binary `bvsub`, `bvneg` and literals of the equality's
//! width; any other printed term is one atom, the way carcara's
//! `Polynomial::from_term` ends at it), compared exactly, modulo `2^w`. An
//! authored spelling that reads differently keeps the ordinary lowering.
//! Users: the circuit lane (`bv_packed/circuit/offset.rs`) and the complete
//! bit-blast (`complete_blast/offset.rs`).

use super::{parse_printed_bitvec_literal, split_application};
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// Longest printed side this lowering reads.
const MAX_PRINTED_SIDE: usize = 8 * 1024;
/// Most printed nodes one linear reading visits.
const MAX_PRINTED_NODES: usize = 64;

/// `(_ bv1 w)` or `(_ bv(2^w - 1) w)`: the factor `f` for which
/// `lhs - rhs = f * (left - right)` holds over the printed atoms, modulo
/// `2^width`, or `None` when neither does.
pub(super) fn printed_factor(
    lhs: &str,
    rhs: &str,
    left: &str,
    right: &str,
    width: u32,
) -> Option<String> {
    if [lhs, rhs, left, right]
        .iter()
        .any(|side| side.len() > MAX_PRINTED_SIDE)
    {
        return None;
    }
    let source = PrintedLinear::difference(lhs, rhs, width)?;
    let target = PrintedLinear::difference(left, right, width)?;
    if source == target {
        return Some(format!("(_ bv1 {width})"));
    }
    let ones = (BigInt::one() << width) - 1;
    (source == target.negated()).then(|| format!("(_ bv{ones} {width})"))
}

/// A printed bit-vector term as `constant + sum(coefficient * atom)`, every
/// number reduced modulo `2^width`. Drop INTEGER-zero monomials before
/// reduction; retain a nonzero integer monomial whose residue is zero, as
/// the consumer's polynomial normalizer does.
#[derive(PartialEq, Eq)]
struct PrintedLinear {
    width: u32,
    constant: BigInt,
    atoms: std::collections::BTreeMap<String, BigInt>,
}

impl PrintedLinear {
    /// `left - right`.
    fn difference(left: &str, right: &str, width: u32) -> Option<Self> {
        let mut form = Self {
            width,
            constant: BigInt::zero(),
            atoms: std::collections::BTreeMap::new(),
        };
        let mut nodes = 0;
        form.add(left, &BigInt::one(), &mut nodes)?;
        form.add(right, &-BigInt::one(), &mut nodes)?;
        Some(form.reduced())
    }

    fn add(&mut self, text: &str, coefficient: &BigInt, nodes: &mut usize) -> Option<()> {
        *nodes += 1;
        if *nodes > MAX_PRINTED_NODES {
            return None;
        }
        if let Some((value, width)) = parse_printed_bitvec_literal(text) {
            if width != self.width {
                return None;
            }
            self.constant += coefficient * BigInt::from(value);
            return Some(());
        }
        if let Some(args) = split_application(text, "bvadd") {
            if args.is_empty() {
                return None;
            }
            return args
                .iter()
                .try_for_each(|arg| self.add(arg, coefficient, nodes));
        }
        if let Some(args) = split_application(text, "bvsub") {
            let [minuend, subtrahend] = args.as_slice() else {
                return None;
            };
            self.add(minuend, coefficient, nodes)?;
            return self.add(subtrahend, &-coefficient, nodes);
        }
        if let Some(args) = split_application(text, "bvneg") {
            let [operand] = args.as_slice() else {
                return None;
            };
            return self.add(operand, &-coefficient, nodes);
        }
        *self.atoms.entry(text.to_string()).or_default() += coefficient;
        Some(())
    }

    fn reduced(mut self) -> Self {
        let modulus = BigInt::one() << self.width;
        let reduce = |value: &BigInt| ((value % &modulus) + &modulus) % &modulus;
        self.constant = reduce(&self.constant);
        self.atoms = std::mem::take(&mut self.atoms)
            .into_iter()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .map(|(atom, coefficient)| (atom, reduce(&coefficient)))
            .collect();
        self
    }

    fn negated(&self) -> Self {
        // A zero residue can still name a retained nonzero monomial. Sign
        // reversal preserves that support; never run integer-zero removal
        // again on coefficients whose integer values have been reduced.
        let modulus = BigInt::one() << self.width;
        let negate = |value: &BigInt| ((-value % &modulus) + &modulus) % &modulus;
        Self {
            width: self.width,
            constant: negate(&self.constant),
            atoms: self
                .atoms
                .iter()
                .map(|(atom, coefficient)| (atom.clone(), negate(coefficient)))
                .collect(),
        }
    }
}

#[cfg(test)]
#[path = "offset_bridge_tests.rs"]
mod tests;

impl super::AlethePrinter<'_> {
    /// A full cancellation removes every authored operator from the lowered
    /// word requests. Retain their existing compositional surface checks,
    /// including variables/atoms that no retained word otherwise visits.
    pub(super) fn full_offset_source_surfaces_agree(
        &self,
        lhs: ay_core::TermId,
        rhs: ay_core::TermId,
        width: u32,
    ) -> Option<()> {
        use ay_core::{Symbol, TermData};
        let mut pending = vec![lhs, rhs];
        let mut visits = 0usize;
        while let Some(term) = pending.pop() {
            self.check_emission_progress(1).ok()?;
            visits += 1;
            if visits > MAX_PRINTED_NODES
                || self.terms.entry_stamp(term).is_none()
                || !matches!(self.terms.sort(term), ay_core::Sort::BitVec(shape) if shape.width == width)
            {
                return None;
            }
            let overridden = self
                .term_overrides
                .is_some_and(|map| map.contains_key(&term))
                || self.skolem_overrides.borrow().contains_key(&term)
                || self.let_bridge_renderings.borrow().contains_key(&term);
            if overridden
                && !super::surface_literal::same_printed_term(
                    &self.format_term(term),
                    &self.format_term_data(self.terms.get(term)),
                )
            {
                return None;
            }
            match self.terms.get(term) {
                TermData::Var(..) | TermData::Const(ay_core::Constant::BitVec { .. }) => (),
                TermData::App(Symbol::Named(head), args)
                    if (head == "bvadd" && args.len() >= 2)
                        || (head == "bvsub" && args.len() == 2)
                        || (head == "bvneg" && args.len() == 1) =>
                {
                    if args.len() > MAX_PRINTED_NODES.saturating_sub(visits) {
                        return None;
                    }
                    pending.extend(args.iter().copied());
                }
                _ => return None,
            }
        }
        Some(())
    }
}
