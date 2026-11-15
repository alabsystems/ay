// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Constant, Sort, TermData, TermId};
use num_bigint::Sign;
use num_traits::ToPrimitive;

use super::{Reference, ReferenceError, Result};

impl Reference<'_, '_> {
    /// None is the exact all-ones word. The comparison borrows source limbs;
    /// it never constructs a hostile-width mask in the checker.
    pub(super) fn constant(&mut self, id: TermId, width: u32, small: Option<u64>) -> Result<()> {
        let (data, sort) = self.term(id)?;
        if !matches!(sort, Sort::BitVec(actual) if actual.width == width && width > 0) {
            return Err(ReferenceError::Source);
        }
        let TermData::Const(Constant::BitVec {
            value,
            width: stored,
        }) = data
        else {
            return Err(ReferenceError::Source);
        };
        if *stored != width || value.sign() == Sign::Minus || value.bits() > u64::from(width) {
            return Err(ReferenceError::Source);
        }
        if let Some(small) = small {
            self.charge(2, 0)?;
            return if value.to_u64() == Some(small) {
                Ok(())
            } else {
                Err(ReferenceError::Source)
            };
        }
        if value.bits() != u64::from(width) {
            return Err(ReferenceError::Source);
        }
        let mut remaining = width;
        for limb in value.magnitude().iter_u32_digits() {
            self.charge(1, 0)?;
            let bits = remaining.min(32);
            if bits == 0 || limb != u32::MAX >> (32 - bits) {
                return Err(ReferenceError::Source);
            }
            remaining -= bits;
        }
        if remaining == 0 {
            Ok(())
        } else {
            Err(ReferenceError::Source)
        }
    }

    pub(super) fn match_input(&mut self, source: TermId, target: TermId, width: u32) -> Result<()> {
        let (_, sort) = self.term(source)?;
        if matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode") {
            if width != 3 {
                return Err(ReferenceError::Source);
            }
            return self.rm_code(source, target);
        }
        if source != target {
            return Err(ReferenceError::Source);
        }
        Ok(())
    }

    fn rm_code(&mut self, source: TermId, mut target: TermId) -> Result<()> {
        // The code is derived from ACTUAL RM comparisons, not a separate free
        // BV leaf/domain premise. SMT RoundingMode is interpreted as exactly
        // these five values by the enclosing native theory signature contract.
        for (number, name) in ["RNE", "RNA", "RTP", "RTN"].iter().enumerate() {
            let (data, sort) = self.term(target)?;
            if !matches!(sort, Sort::BitVec(actual) if actual.width == 3) {
                return Err(ReferenceError::Source);
            }
            let TermData::Ite(test, code, next) = data else {
                return Err(ReferenceError::Source);
            };
            self.boolean(*test)?;
            let [actual_source, actual_literal] = self.app(*test, "=")?;
            if actual_source != source {
                return Err(ReferenceError::Source);
            }
            let (literal, sort) = self.term(actual_literal)?;
            if !matches!(sort, Sort::Uninterpreted(actual) if actual == "RoundingMode") {
                return Err(ReferenceError::Source);
            }
            let TermData::App(symbol, args) = literal else {
                return Err(ReferenceError::Source);
            };
            if !args.is_empty() || !self.named(symbol, name)? {
                return Err(ReferenceError::Source);
            }
            self.constant(*code, 3, Some(number as u64))?;
            target = *next;
        }
        self.constant(target, 3, Some(4))
    }
}
