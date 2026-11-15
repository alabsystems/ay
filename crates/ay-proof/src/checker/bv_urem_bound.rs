// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The exact unsigned-remainder range theorem, not a bit-blast shortcut.
//!
//! SMT-LIB FixedSizeBitVectors defines `bvurem x d`, for nonzero `d`, as
//! `nat2bv(bv2nat(x) mod bv2nat(d))`; integer remainder lies in `[0,d)` and
//! `bvult` compares these unsigned values. Since `d < 2^n`, conversion back
//! to `n` bits cannot wrap that remainder. At zero the explicit disjunct
//! discharges the theorem (SMT-LIB instead defines `bvurem x 0 = x`).
//! <https://smt-lib.org/theories-FixedSizeBitVectors.shtml>
//!
//! This independently validated theory rule has its own kind. It does not
//! change `BvBitBlast`'s gate/resolution-replay contract, and does not treat
//! successful certificate printing as native evidence.

use super::ProofCheckError;
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};

#[cfg(test)]
mod tests;
mod typing;

/// The existing divider certificate supports at most 128-bit source words.
pub(crate) const MAX_WIDTH: u32 = 128;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Shape {
    pub(crate) width: u32,
    pub(crate) dividend: TermId,
    pub(crate) divisor: TermId,
    pub(crate) theorem: TermId,
}

pub(crate) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Shape, ProofCheckError> {
    let mut meter = Meter {
        progress,
        open: true,
        step,
    };
    meter.admit(1, 0)?;
    // Type the WHOLE input, including dead branches and all operands,
    // before admitting the mathematical schema.
    typing::validate(terms, clause, &mut meter)?;
    let shape = shape(terms, clause).ok_or_else(|| meter.invalid())?;
    meter.admit(0, 0)?;
    Ok(shape)
}

fn shape(terms: &TermStore, clause: &[TermId]) -> Option<Shape> {
    let [theorem] = clause else { return None };
    let [zero_test, bound] = named(terms, *theorem, "or")? else {
        return None;
    };
    let [divisor, zero] = named(terms, *zero_test, "=")? else {
        return None;
    };
    let [remainder, bound_divisor] = named(terms, *bound, "bvult")? else {
        return None;
    };
    let [dividend, remainder_divisor] = named(terms, *remainder, "bvurem")? else {
        return None;
    };
    if divisor != bound_divisor || divisor != remainder_divisor {
        return None;
    }
    let Sort::BitVec(bits) = terms.sort(*divisor) else {
        return None;
    };
    let Constant::BitVec { value, width } = (match terms.get(*zero) {
        TermData::Const(value) => value,
        _ => return None,
    }) else {
        return None;
    };
    if *width != bits.width || value.bits() != 0 {
        return None;
    }
    Some(Shape {
        width: bits.width,
        dividend: *dividend,
        divisor: *divisor,
        theorem: *theorem,
    })
}

fn named<'a>(terms: &'a TermStore, id: TermId, name: &str) -> Option<&'a [TermId]> {
    match terms.get(id) {
        TermData::App(Symbol::Named(head), args) if head.as_str() == name => Some(args),
        _ => None,
    }
}

struct Meter<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    open: bool,
    step: ProofId,
}

impl Meter<'_> {
    fn admit(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if !self.open {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.open = false;
        if !(self.progress)(work, bytes) {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.open = true;
        Ok(())
    }

    fn invalid(&self) -> ProofCheckError {
        ProofCheckError::InvalidTheoryLemma {
            step: self.step,
            reason: "bv_urem_bound requires the exact fully typed guarded unsigned remainder bound"
                .into(),
        }
    }

    fn exhausted(&mut self) -> ProofCheckError {
        self.open = false;
        ProofCheckError::ResourceLimit
    }
}
