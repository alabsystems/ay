// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! How the proof-producing lowering treats `bvudiv` / `bvurem`.
//!
//! * A divisor that is a power of two — a literal, or a closed term the
//!   bounded evaluator folds — is a shift and a mask.
//! * Any other divisor is, for THEORY-LEMMA validation, one free leaf per
//!   canonical term, minted only once both operands lower and their widths
//!   agree (`BvApplicationLowering::Abstractable`): enough when the same
//!   division occurs on both sides, nothing when the clause needs what the
//!   operator computes.
//! * A lemma that abstracted attempt could not refute, and that mentions a
//!   division, is tried ONCE more with the producer's exact divider
//!   (`bv_blast_solver/divide.rs`; [`clause_mentions_division`],
//!   [`ProofProducingLowerer::new_with_exact_division`]). external-codegen's IDIV
//!   lowerings spelled by `bvsdiv`'s definition need it: `(ite (= b #x..ff)
//!   (bvneg a) (bvsdiv a b))` against `(bvsdiv a b)` holds because
//!   `udiv(|a|, 1) = |a|` when `b = -1`. The first attempt is unchanged, so
//!   no clause it admits is lost to the larger circuit, and the query
//!   authentication lowering never abstracts and never divides exactly: it
//!   keeps declining a reserved operator by name.

use super::*;

impl<'a, 'p> ProofProducingLowerer<'a, 'p> {
    /// The divisor `2^k` (`k` below `width`) of a `bvudiv`/`bvurem`, which is
    /// exactly a shift and a mask: `(bvudiv x 2^k)` is `(bvlshr x k)` and
    /// `(bvurem x 2^k)` is `(bvand x 2^k-1)`. The divisor is a literal or a
    /// CLOSED term the bounded evaluator folds (`bounded_eval::closed_bv_in`);
    /// any other stays outside the exact fragment (`BvApplicationLowering`).
    pub(super) fn power_of_two_divisor(
        &self,
        name: &str,
        divisor: TermId,
        width: u32,
    ) -> Option<u128> {
        if !matches!(name, "bvudiv" | "bvurem") {
            return None;
        }
        let value = match self.terms.get(divisor) {
            TermData::Const(Constant::BitVec { value, .. }) => value.to_u128()?,
            _ => u128::from(bounded_eval::closed_bv_in(
                self.terms,
                divisor,
                &self.constants,
            )?),
        };
        Some(value).filter(|d| d.is_power_of_two() && d.trailing_zeros() < width)
    }

    /// `(bvudiv lhs 2^k)` as `(bvlshr lhs k)` and `(bvurem lhs 2^k)` as
    /// `(bvand lhs 2^k-1)` when [`Self::power_of_two_divisor`] finds the
    /// divisor; otherwise `lhs` is handed back untouched.
    pub(super) fn power_of_two_quotient(
        &self,
        name: &str,
        lhs: BvExpr,
        divisor: TermId,
        width: u32,
    ) -> Result<BvExpr, BvExpr> {
        let Some(divisor) = self.power_of_two_divisor(name, divisor, width) else {
            return Err(lhs);
        };
        Ok(if name == "bvudiv" {
            let shift = u128::from(divisor.trailing_zeros());
            BvExpr::lshr(lhs, BvExpr::const_val(shift, width))
        } else {
            BvExpr::and(lhs, BvExpr::const_val(divisor - 1, width))
        })
    }

    /// [`Self::new_for_lemma_validation`] with exact division.
    pub(super) fn new_with_exact_division(terms: &'a TermStore, deadline: Instant) -> Self {
        Self {
            exact_division: true,
            ..Self::new_for_lemma_validation(terms, deadline)
        }
    }
}

/// Whether `clause` mentions `bvudiv` or `bvurem` (a bounded walk; a clause
/// too large to walk is treated as not mentioning one).
pub(super) fn clause_mentions_division(terms: &TermStore, clause: &[TermId]) -> bool {
    const MAX_VISITS: usize = 1 << 20;
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = clause.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_VISITS {
            return false;
        }
        if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
            if matches!(name.as_str(), "bvudiv" | "bvurem") {
                return true;
            }
        }
        stack.extend(terms.children(term));
    }
    false
}
