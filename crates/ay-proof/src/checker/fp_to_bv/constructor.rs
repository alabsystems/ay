// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These universally quantified schemas follow the SMT-LIB FloatingPoint
//! constructor's sign/exponent/fraction semantics, for every eb,sb >= 2:
//! <https://smt-lib.org/theories-FloatingPoint.shtml>.
//!
//! Inputs are exact live BV variables or canonical constants, not guessed
//! producer leaves. A complete unit equality binds the actual FP constructor
//! and the exact corresponding BV/Bool expression. The seven classifications,
//! negation and absolute value are accepted; no other schema is inferred.
//! This is not a complete arithmetic lowering or CNF import certificate.

use ay_core::{Constant, FpOp, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::Sign;

use super::ProofCheckError;

#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

pub(super) fn recognizes(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    operation: FpOp,
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    let mut reader = Reader {
        terms,
        step,
        progress,
        refused: false,
    };
    reader.charge(0, 0)?;
    let matched = reader.clause(clause, operation);
    // No transient circuit/AST/BigInt allocation is retained by this matcher.
    // Both ordinary nonmatch and success make a final original-owner poll.
    reader.charge(0, 0)?;
    matched
}

#[derive(Clone, Copy)]
enum WordConstant {
    Zero,
    Ones,
}

#[derive(Clone, Copy)]
enum EqualitySense {
    Equal,
    Different,
}

#[derive(Clone, Copy)]
struct Fields {
    sign: TermId,
    exponent: TermId,
    fraction: TermId,
    eb: u32,
    sb: u32,
}

struct Reader<'terms, 'control> {
    terms: &'terms TermStore,
    step: ProofId,
    progress: Progress<'control>,
    refused: bool,
}

impl<'terms> Reader<'terms, '_> {
    fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        // A callback panic cannot clear the local refusal before unwinding.
        self.refused = true;
        if !(self.progress)(work, bytes) {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.refused = false;
        Ok(())
    }

    fn term(&mut self, id: TermId) -> Result<(&'terms TermData, &'terms Sort), ProofCheckError> {
        self.charge(2, 0)?;
        if id.index() >= self.terms.len() {
            let reason = "fp_to_bv schema references a missing live term";
            self.charge(reason.len(), reason.len())?;
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: self.step,
                reason: reason.to_owned(),
            });
        }
        Ok((self.terms.get(id), self.terms.sort(id)))
    }

    fn named(&mut self, symbol: &Symbol, name: &str) -> Result<bool, ProofCheckError> {
        self.charge(2, 0)?;
        let Symbol::Named(actual) = symbol else {
            return Ok(false);
        };
        if actual.len() != name.len() {
            return Ok(false);
        }
        self.charge(name.len(), 0)?;
        Ok(actual.as_str() == name && !self.terms.is_declared_function(actual))
    }

    fn app<const N: usize>(
        &mut self,
        id: TermId,
        name: &str,
    ) -> Result<Option<[TermId; N]>, ProofCheckError> {
        let (data, _) = self.term(id)?;
        self.charge(2, 0)?;
        let TermData::App(symbol, args) = data else {
            return Ok(None);
        };
        if args.len() != N || !self.named(symbol, name)? {
            return Ok(None);
        }
        self.charge(N, 0)?;
        Ok(args.as_slice().try_into().ok())
    }

    fn boolean(&mut self, id: TermId) -> Result<bool, ProofCheckError> {
        let (_, sort) = self.term(id)?;
        Ok(matches!(sort, Sort::Bool))
    }

    fn bv_leaf(&mut self, id: TermId, width: u32) -> Result<bool, ProofCheckError> {
        let (data, sort) = self.term(id)?;
        if !matches!(sort, Sort::BitVec(actual) if actual.width == width && width > 0) {
            return Ok(false);
        }
        Ok(match data {
            TermData::Var(_, _) => true,
            TermData::Const(Constant::BitVec {
                value,
                width: stored,
            }) => {
                *stored == width && value.sign() != Sign::Minus && value.bits() <= u64::from(width)
            }
            _ => false,
        })
    }

    fn fields(&mut self, id: TermId) -> Result<Option<Fields>, ProofCheckError> {
        let (_, sort) = self.term(id)?;
        let Sort::FloatingPoint(eb, sb) = sort else {
            return Ok(None);
        };
        if *eb < 2 || *sb < 2 || eb.checked_add(*sb).is_none() {
            return Ok(None);
        }
        let Some([sign, exponent, fraction]) = self.app(id, "fp")? else {
            return Ok(None);
        };
        if !self.bv_leaf(sign, 1)?
            || !self.bv_leaf(exponent, *eb)?
            || !self.bv_leaf(fraction, *sb - 1)?
        {
            return Ok(None);
        }
        Ok(Some(Fields {
            sign,
            exponent,
            fraction,
            eb: *eb,
            sb: *sb,
        }))
    }

    fn clause(&mut self, clause: &[TermId], operation: FpOp) -> Result<bool, ProofCheckError> {
        self.charge(1, 0)?;
        if clause.len() != 1 || !self.boolean(clause[0])? {
            return Ok(false);
        }
        let Some([left, right]) = self.app(clause[0], "=")? else {
            return Ok(false);
        };
        if self.lowering(left, right, operation)? {
            return Ok(true);
        }
        self.lowering(right, left, operation)
    }

    fn lowering(
        &mut self,
        source: TermId,
        lowered: TermId,
        op: FpOp,
    ) -> Result<bool, ProofCheckError> {
        let name = match op {
            FpOp::Neg => "fp.neg",
            FpOp::Abs => "fp.abs",
            FpOp::IsNaN => "fp.isNaN",
            FpOp::IsInfinite => "fp.isInfinite",
            FpOp::IsZero => "fp.isZero",
            FpOp::IsNormal => "fp.isNormal",
            FpOp::IsSubnormal => "fp.isSubnormal",
            FpOp::IsPositive => "fp.isPositive",
            FpOp::IsNegative => "fp.isNegative",
            _ => return Ok(false),
        };
        let Some([subject]) = self.app(source, name)? else {
            return Ok(false);
        };
        let Some(fields) = self.fields(subject)? else {
            return Ok(false);
        };
        let (_, result_sort) = self.term(source)?;
        if matches!(op, FpOp::Neg | FpOp::Abs) {
            if !matches!(result_sort, Sort::FloatingPoint(eb, sb) if *eb == fields.eb && *sb == fields.sb)
            {
                return Ok(false);
            }
            return self.unary(lowered, fields, op);
        }
        if !matches!(result_sort, Sort::Bool) || !self.boolean(lowered)? {
            return Ok(false);
        }
        self.classification(lowered, fields, op)
    }

    fn unary(&mut self, id: TermId, input: Fields, op: FpOp) -> Result<bool, ProofCheckError> {
        let (_, sort) = self.term(id)?;
        if !matches!(sort, Sort::FloatingPoint(eb, sb) if *eb == input.eb && *sb == input.sb) {
            return Ok(false);
        }
        let Some([sign, exponent, fraction]) = self.app(id, "fp")? else {
            return Ok(false);
        };
        if exponent != input.exponent || fraction != input.fraction {
            return Ok(false);
        }
        match op {
            FpOp::Abs => self.constant(sign, 1, WordConstant::Zero),
            FpOp::Neg => {
                let (_, sort) = self.term(sign)?;
                if !matches!(sort, Sort::BitVec(width) if width.width == 1) {
                    return Ok(false);
                }
                Ok(self.app::<1>(sign, "bvnot")? == Some([input.sign]))
            }
            _ => Ok(false),
        }
    }

    fn classification(&mut self, id: TermId, f: Fields, op: FpOp) -> Result<bool, ProofCheckError> {
        let Some([left, right]) = self.app(id, "and")? else {
            return Ok(false);
        };
        if !self.boolean(left)? || !self.boolean(right)? {
            return Ok(false);
        }
        match op {
            FpOp::IsNaN => Ok(self.field_equal(
                left,
                f.exponent,
                f.eb,
                WordConstant::Ones,
                EqualitySense::Equal,
            )? && self.field_equal(
                right,
                f.fraction,
                f.sb - 1,
                WordConstant::Zero,
                EqualitySense::Different,
            )?),
            FpOp::IsInfinite => Ok(self.field_equal(
                left,
                f.exponent,
                f.eb,
                WordConstant::Ones,
                EqualitySense::Equal,
            )? && self.field_equal(
                right,
                f.fraction,
                f.sb - 1,
                WordConstant::Zero,
                EqualitySense::Equal,
            )?),
            FpOp::IsZero => Ok(self.field_equal(
                left,
                f.exponent,
                f.eb,
                WordConstant::Zero,
                EqualitySense::Equal,
            )? && self.field_equal(
                right,
                f.fraction,
                f.sb - 1,
                WordConstant::Zero,
                EqualitySense::Equal,
            )?),
            FpOp::IsNormal => Ok(self.field_equal(
                left,
                f.exponent,
                f.eb,
                WordConstant::Zero,
                EqualitySense::Different,
            )? && self.field_equal(
                right,
                f.exponent,
                f.eb,
                WordConstant::Ones,
                EqualitySense::Different,
            )?),
            FpOp::IsSubnormal => Ok(self.field_equal(
                left,
                f.exponent,
                f.eb,
                WordConstant::Zero,
                EqualitySense::Equal,
            )? && self.field_equal(
                right,
                f.fraction,
                f.sb - 1,
                WordConstant::Zero,
                EqualitySense::Different,
            )?),
            FpOp::IsPositive | FpOp::IsNegative => self.signed_classification(left, right, f, op),
            _ => Ok(false),
        }
    }

    fn signed_classification(
        &mut self,
        left: TermId,
        right: TermId,
        f: Fields,
        op: FpOp,
    ) -> Result<bool, ProofCheckError> {
        let pattern = if op == FpOp::IsNegative {
            WordConstant::Ones
        } else {
            WordConstant::Zero
        };
        // Both conjuncts remain mandatory. The Boolean constructors may sort
        // the conjunction; a source sign test is never sufficient by itself.
        for (not_nan, sign) in [(left, right), (right, left)] {
            if self.not_nan(not_nan, f)?
                && self.field_equal(sign, f.sign, 1, pattern, EqualitySense::Equal)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn not_nan(&mut self, id: TermId, f: Fields) -> Result<bool, ProofCheckError> {
        let (data, sort) = self.term(id)?;
        if !matches!(sort, Sort::Bool) {
            return Ok(false);
        }
        if let TermData::Not(nan) = data {
            return Ok(self.boolean(*nan)? && self.classification(*nan, f, FpOp::IsNaN)?);
        }
        // mk_not applies De Morgan to the complete NaN test:
        // !(E == ones && F != zero) == (E != ones || F == zero).
        // Match both exact original fields and both polarities. This is a
        // bounded syntax schema, not arbitrary Boolean equivalence search.
        let Some([left, right]) = self.app(id, "or")? else {
            return Ok(false);
        };
        for (exponent, fraction) in [(left, right), (right, left)] {
            if self.field_equal(
                exponent,
                f.exponent,
                f.eb,
                WordConstant::Ones,
                EqualitySense::Different,
            )? && self.field_equal(
                fraction,
                f.fraction,
                f.sb - 1,
                WordConstant::Zero,
                EqualitySense::Equal,
            )? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn field_equal(
        &mut self,
        mut id: TermId,
        field: TermId,
        width: u32,
        pattern: WordConstant,
        sense: EqualitySense,
    ) -> Result<bool, ProofCheckError> {
        if !self.boolean(id)? {
            return Ok(false);
        }
        if matches!(sense, EqualitySense::Different) {
            let (data, _) = self.term(id)?;
            let TermData::Not(inner) = data else {
                return Ok(false);
            };
            id = *inner;
            if !self.boolean(id)? {
                return Ok(false);
            }
        }
        let Some([left, right]) = self.app(id, "=")? else {
            return Ok(false);
        };
        if left == field {
            return self.constant(right, width, pattern);
        }
        if right == field {
            return self.constant(left, width, pattern);
        }
        Ok(false)
    }

    fn constant(
        &mut self,
        id: TermId,
        width: u32,
        pattern: WordConstant,
    ) -> Result<bool, ProofCheckError> {
        let (data, sort) = self.term(id)?;
        if !matches!(sort, Sort::BitVec(actual) if actual.width == width && width > 0) {
            return Ok(false);
        }
        let TermData::Const(Constant::BitVec {
            value,
            width: stored,
        }) = data
        else {
            return Ok(false);
        };
        if *stored != width || value.sign() == Sign::Minus {
            return Ok(false);
        }
        if matches!(pattern, WordConstant::Zero) {
            return Ok(value.sign() == Sign::NoSign);
        }
        if value.bits() != u64::from(width) {
            return Ok(false);
        }
        // Borrowed limb walk: no (1 << width) allocation and no new width cap.
        let mut remaining = width;
        for limb in value.magnitude().iter_u32_digits() {
            self.charge(1, 0)?;
            let bits = remaining.min(32);
            if bits == 0 || limb != (u32::MAX >> (32 - bits)) {
                return Ok(false);
            }
            remaining -= bits;
        }
        Ok(remaining == 0)
    }
}
