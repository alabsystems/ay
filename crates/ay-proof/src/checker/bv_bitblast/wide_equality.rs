// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An equality wider than the producer's words, checked slice by slice.
//!
//! Bit-vector equality is bitwise, so `(= l r)` over `w` bits is exactly the
//! conjunction of the equalities of their `[lo, hi]` slices for any cover of
//! `0..w`. A slice of a wide `concat` is taken from its children without
//! ever building the wide word, and a slice of a word the producer can hold
//! by [`ProofProducingLowerer::lower_bv_extract`], which lowers that whole
//! word first. The slices cover every bit, so every child of every wide
//! `concat` is lowered, completely, by some slice: nothing is skipped that
//! the ordinary lowering would have checked. An equality of two 192-bit
//! `concat`s of 64-bit words (a external-codegen gate row, measured 2026-09-30:
//! `BitVec width 192 is outside proof-producing range 1..=128`) lowers to
//! three 64-bit equalities. Wide extensions and add/sub words are planned as
//! narrow limbs with exact carry/borrow; unsupported wide leaves still refuse.
//! Nothing here widens `MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH`.
//!
//! The slices are PLANNED from the source alone ([`planning::plan`]) before any is
//! lowered, so the lowering census (`lowering_share.rs`) counts exactly the
//! requests the lowering then makes: one per narrow piece.

use super::*;

mod comparison;
mod planning;
mod reflexive;

#[derive(Clone, Copy)]
pub(super) enum Partition {
    Fields,
    Limbs,
}

#[derive(Clone, Copy)]
enum Arithmetic {
    Add,
    Sub,
}

impl Arithmetic {
    fn apply(self, lhs: BvExpr, rhs: BvExpr) -> BvExpr {
        match self {
            Self::Add => BvExpr::add(lhs, rhs),
            Self::Sub => BvExpr::sub(lhs, rhs),
        }
    }
}

#[derive(Clone, Copy)]
enum Part {
    Value,
    Carry,
}

/// Bits per slice.
const SLICE: u32 = 64;
/// Widest equality split here. Matching concat fields may select smaller
/// slices; every concat path decreases this width. Other source paths and
/// virtual construction are bounded explicitly by the planner.
const MAX_WIDE_WIDTH: u32 = 1_024;

/// Bits `high..=low` of a wide term, as narrow pieces.
enum Piece {
    /// Bits `high..=low` of a term the producer can hold.
    Narrow {
        term: TermId,
        high: u32,
        low: u32,
    },
    Constant {
        value: u128,
        width: u32,
    },
    Splat {
        bit: Box<Piece>,
        width: u32,
    },
    Extract {
        inner: Box<Piece>,
        high: u32,
        low: u32,
    },
    Arithmetic {
        operation: Arithmetic,
        lhs: Box<Piece>,
        rhs: Box<Piece>,
        carry: Option<Box<Piece>>,
        width: u32,
        part: Part,
    },
    /// A slice across a `concat` boundary: `upper` over `lower`, which is
    /// `lower_width` bits wide.
    Join {
        upper: Box<Piece>,
        lower: Box<Piece>,
        lower_width: u32,
    },
}

#[cfg(test)]
fn plan(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Result<Vec<(Piece, Piece)>, planning::Error> {
    planning::plan(terms, lhs, rhs, Partition::Fields, &mut || Ok(()))
}

fn is_wide(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.sort(term),
        Sort::BitVec(sort) if sort.width > MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH
    )
}

impl Piece {
    /// Collect every narrow request and count this virtual-tree walk.
    fn requests(&self, out: &mut Vec<TermId>) -> usize {
        let children = match self {
            Self::Narrow { term, .. } => {
                out.push(*term);
                0
            }
            Self::Constant { .. } => 0,
            Self::Splat { bit, .. } => bit.requests(out),
            Self::Extract { inner, .. } => inner.requests(out),
            Self::Arithmetic {
                lhs, rhs, carry, ..
            } => {
                let words = lhs.requests(out).saturating_add(rhs.requests(out));
                words.saturating_add(carry.as_ref().map_or(0, |carry| carry.requests(out)))
            }
            Self::Join { upper, lower, .. } => {
                upper.requests(out).saturating_add(lower.requests(out))
            }
        };
        children.saturating_add(1)
    }

    fn width(&self) -> u32 {
        match self {
            Self::Narrow { high, low, .. } => high - low + 1,
            Self::Extract { high, low, .. } => high - low + 1,
            Self::Constant { width, .. } | Self::Splat { width, .. } => *width,
            Self::Arithmetic { width, part, .. } => match part {
                Part::Value => *width,
                Part::Carry => 1,
            },
            Self::Join {
                upper, lower_width, ..
            } => upper.width() + lower_width,
        }
    }
}

impl ProofProducingLowerer<'_, '_> {
    /// Whether `term` is a bit-vector wider than the producer's words.
    pub(super) fn is_wide(&self, term: TermId) -> bool {
        is_wide(self.terms, term)
    }

    /// The requests a wide binary word comparison makes
    /// (`requested_operands`): the narrow pieces of its partition, or, when it
    /// cannot be split, none (the lowering refuses before any request).
    pub(super) fn wide_word_requests(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        partition: Partition,
        out: &mut Vec<TermId>,
    ) -> Result<(), String> {
        match self.planned_slices(lhs, rhs, partition) {
            Ok(slices) => {
                for (left, right) in &slices {
                    let walked = left.requests(out).saturating_add(right.requests(out));
                    self.charge_lowering_walk(walked)?;
                    self.poll_lowering()?;
                }
                Ok(())
            }
            Err(planning::Error::Unsupported(_)) => Ok(()),
            Err(error) => Err(self.planning_error(error)),
        }
    }

    fn planned_slices(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        partition: Partition,
    ) -> Result<Vec<(Piece, Piece)>, planning::Error> {
        let terms = self.terms;
        planning::plan(terms, lhs, rhs, partition, &mut || {
            self.poll_lowering()?;
            self.charge_lowering_walk(1)
        })
    }

    fn planning_error(&mut self, error: planning::Error) -> String {
        if matches!(&error, planning::Error::Resource(_)) {
            self.resource_exhausted = true;
        }
        error.to_string()
    }

    /// `(= lhs rhs)` as the conjunction of its slices' equalities.
    pub(super) fn lower_wide_equality(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<BvExpr, String> {
        let slices = self
            .planned_slices(lhs, rhs, Partition::Fields)
            .map_err(|error| self.planning_error(error))?;
        let mut equalities = Vec::with_capacity(slices.len());
        for (left, right) in &slices {
            let same = reflexive::same(left, right, &mut || {
                self.poll_lowering()?;
                self.charge_lowering_walk(1)
            })?;
            // Both sides are still fully lowered and validated. Only then
            // discard a syntactically reflexive slice, avoiding irrelevant
            // input bits (e.g. common concat padding) in the SAT circuit.
            let left = self.lower_piece(left)?;
            let right = self.lower_piece(right)?;
            self.charge_wide_constructed(1)?;
            equalities.push(if same {
                BvExpr::const_val(1, 1)
            } else {
                BvExpr::eq(left, right)
            });
        }
        balanced_bool_expr_controlled(equalities, true, BvExpr::and, &mut || self.poll_lowering())
            .inspect_err(|_| self.resource_exhausted = true)
    }

    fn lower_piece(&mut self, piece: &Piece) -> Result<BvExpr, String> {
        self.poll_lowering()?;
        match piece {
            Piece::Narrow { term, high, low } => self
                .lower_bv_extract(*term, *high, *low)
                .map(|(slice, _)| slice),
            Piece::Constant { value, width } => {
                self.charge_wide_constructed(1)?;
                Ok(BvExpr::const_val(*value, *width))
            }
            Piece::Splat { bit, width } => {
                let bit = self.lower_piece(bit)?;
                self.charge_wide_constructed(1)?;
                Ok(BvExpr::sign_ext(bit, width - 1))
            }
            Piece::Extract { inner, high, low } => {
                let inner = self.lower_piece(inner)?;
                self.charge_wide_constructed(1)?;
                Ok(BvExpr::extract(inner, *high, *low))
            }
            Piece::Arithmetic {
                operation,
                lhs,
                rhs,
                carry,
                width,
                part,
            } => self.lower_limb(*operation, lhs, rhs, carry.as_deref(), *width, *part),
            Piece::Join {
                upper,
                lower,
                lower_width,
            } => {
                let upper_width = upper.width();
                let upper = self.lower_piece(upper)?;
                let lower = self.lower_piece(lower)?;
                self.charge_wide_constructed(5)?;
                let shifted = BvExpr::shl(
                    BvExpr::zero_ext(upper, *lower_width),
                    BvExpr::const_val(u128::from(*lower_width), upper_width + lower_width),
                );
                Ok(BvExpr::or(shifted, BvExpr::zero_ext(lower, upper_width)))
            }
        }
    }

    /// Charge before allocation and mark these virtual nodes as operands of
    /// the current source lowering, so keep_lowered does not charge them twice.
    fn charge_wide_constructed(&mut self, nodes: usize) -> Result<(), String> {
        self.charge_constructed_expr_nodes(nodes)?;
        if let Some(parent) = self.operand_nodes.last_mut() {
            *parent = parent.saturating_add(nodes);
        }
        Ok(())
    }

    fn lower_limb(
        &mut self,
        operation: Arithmetic,
        lhs: &Piece,
        rhs: &Piece,
        carry: Option<&Piece>,
        width: u32,
        part: Part,
    ) -> Result<BvExpr, String> {
        let zero_operands = matches!(lhs, Piece::Constant { value: 0, .. })
            && matches!(rhs, Piece::Constant { value: 0, .. });
        let lhs = self.lower_piece(lhs)?;
        let rhs = self.lower_piece(rhs)?;
        let carry = carry.map(|piece| self.lower_piece(piece)).transpose()?;
        // Validate every source operand above, even when its value is
        // irrelevant. In a zero limb, 0+0+c is c with no outgoing carry;
        // 0-0-b is the sign extension of b with outgoing borrow b. Keeping
        // those identities explicit avoids a chain of redundant adders in
        // the zero padding that proof export gives wide extensions.
        if zero_operands {
            return self.lower_zero_limb(operation, carry, width, part);
        }
        self.lower_limb_values(operation, lhs, rhs, carry, width, part)
    }

    fn lower_limb_values(
        &mut self,
        operation: Arithmetic,
        lhs: BvExpr,
        rhs: BvExpr,
        carry: Option<BvExpr>,
        width: u32,
        part: Part,
    ) -> Result<BvExpr, String> {
        self.charge_wide_constructed(if carry.is_some() { 6 } else { 4 })?;
        let mut result = operation.apply(BvExpr::zero_ext(lhs, 1), BvExpr::zero_ext(rhs, 1));
        if let Some(carry) = carry {
            result = operation.apply(result, BvExpr::zero_ext(carry, width));
        }
        Ok(match part {
            Part::Value => BvExpr::extract(result, width - 1, 0),
            Part::Carry => BvExpr::extract(result, width, width),
        })
    }

    fn lower_zero_limb(
        &mut self,
        operation: Arithmetic,
        carry: Option<BvExpr>,
        width: u32,
        part: Part,
    ) -> Result<BvExpr, String> {
        match (operation, part, carry) {
            (Arithmetic::Add, Part::Carry, _) | (_, _, None) => {
                self.charge_wide_constructed(1)?;
                let width = match part {
                    Part::Carry => 1,
                    Part::Value => width,
                };
                Ok(BvExpr::const_val(0, width))
            }
            (Arithmetic::Sub, Part::Carry, Some(borrow)) => Ok(borrow),
            (operation, Part::Value, Some(carry)) => {
                self.charge_wide_constructed(1)?;
                Ok(match operation {
                    Arithmetic::Add => BvExpr::zero_ext(carry, width - 1),
                    Arithmetic::Sub => BvExpr::sign_ext(carry, width - 1),
                })
            }
        }
    }
}

#[cfg(test)]
mod overflow_tests;

#[cfg(test)]
mod comparison_tests;

#[cfg(test)]
mod constant_tests;

#[cfg(test)]
mod planning_tests;

#[cfg(test)]
mod tests {
    use super::*;

    /// A 192-bit `concat` equality splits into three 64-bit slices, and a
    /// slice across a boundary joins its two narrow pieces.
    #[test]
    fn a_wide_concat_equality_is_planned_as_narrow_slices() {
        let mut terms = TermStore::new();
        let word = |terms: &mut TermStore, name: &str, width| {
            terms.mk_var(name.to_string(), Sort::bitvec(width))
        };
        let (a, b, c) = (
            word(&mut terms, "a", 64),
            word(&mut terms, "b", 64),
            word(&mut terms, "c", 64),
        );
        let ab = terms.mk_app(Symbol::named("concat"), &[a, b], Sort::bitvec(128));
        let abc = terms.mk_app(Symbol::named("concat"), &[ab, c], Sort::bitvec(192));
        let (x, y) = (word(&mut terms, "x", 96), word(&mut terms, "y", 96));
        let xy = terms.mk_app(Symbol::named("concat"), &[x, y], Sort::bitvec(192));
        let slices = plan(&terms, abc, xy).unwrap();
        assert_eq!(slices.len(), 3);
        let mut requests = Vec::new();
        for (left, right) in &slices {
            assert_eq!(left.width(), 64);
            assert_eq!(right.width(), 64);
            left.requests(&mut requests);
            right.requests(&mut requests);
        }
        // `c`, `b`, `a` on the left; `y`, then `y` and `x` across the
        // boundary at bit 96, then `x` on the right.
        assert_eq!(requests, vec![c, y, ab, x, y, ab, x]);
        // `ab` is narrow (128 bits): its slices are extracts of it.
        assert!(matches!(slices[1].0, Piece::Narrow { term, high: 63, low: 0 } if term == ab));
    }

    #[test]
    fn a_wide_term_that_is_not_a_concat_is_refused() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a".to_string(), Sort::bitvec(192));
        let b = terms.mk_var("b".to_string(), Sort::bitvec(192));
        assert!(plan(&terms, a, b).is_err());
    }
}
