// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Narrow COMPLETE source shape: an actual arithmetic operation, RM, and both
//! explicit constructors whose BV fields are canonical constants/free leaves.
//! Unknown/indexed/lookalike/recursive operands decline, not get abstracted.
//! Local live membership is not source-journal or declaration authority.

use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use num_bigint::Sign;

use super::{graph::Binary, graph::RefId, Format, Reference, ReferenceError, Result};

#[derive(Clone, Copy)]
pub(super) struct Fields {
    pub(super) sign: TermId,
    pub(super) exponent: TermId,
    pub(super) fraction: TermId,
}

#[derive(Clone, Copy)]
pub(super) enum RoundingInput {
    Variable(TermId),
    Literal(u64),
}

impl<'terms> Reference<'terms, '_> {
    pub(super) fn term(&mut self, id: TermId) -> Result<(&'terms TermData, &'terms Sort)> {
        self.charge(2, 0)?;
        if id.index() >= self.terms.len() {
            return Err(ReferenceError::Source);
        }
        Ok((self.terms.get(id), self.terms.sort(id)))
    }

    pub(super) fn named(&mut self, symbol: &Symbol, expected: &str) -> Result<bool> {
        self.charge(1, 0)?;
        let Symbol::Named(name) = symbol else {
            return Ok(false);
        };
        if name.len() != expected.len() {
            return Ok(false);
        }
        self.charge(expected.len(), 0)?;
        Ok(name.as_str() == expected && !self.terms.is_declared_function(name))
    }

    pub(super) fn app<const N: usize>(&mut self, id: TermId, name: &str) -> Result<[TermId; N]> {
        let (data, _) = self.term(id)?;
        let TermData::App(symbol, args) = data else {
            return Err(ReferenceError::Source);
        };
        if args.len() != N || !self.named(symbol, name)? {
            return Err(ReferenceError::Source);
        }
        self.charge(N, 0)?;
        args.as_slice()
            .try_into()
            .map_err(|_| ReferenceError::Source)
    }

    fn bv_leaf(&mut self, id: TermId, width: u32) -> Result<()> {
        let (data, sort) = self.term(id)?;
        if !matches!(sort, Sort::BitVec(actual) if actual.width == width && width > 0) {
            return Err(ReferenceError::Source);
        }
        match data {
            TermData::Var(_, _) => Ok(()),
            TermData::Const(Constant::BitVec {
                value,
                width: stored,
            }) if *stored == width
                && value.sign() != Sign::Minus
                && value.bits() <= u64::from(width) =>
            {
                Ok(())
            }
            _ => Err(ReferenceError::Source),
        }
    }

    fn fields(&mut self, id: TermId, format: Format) -> Result<Fields> {
        let (_, sort) = self.term(id)?;
        if !matches!(sort, Sort::FloatingPoint(eb, p) if *eb == format.eb && *p == format.p) {
            return Err(ReferenceError::Source);
        }
        let [sign, exponent, fraction] = self.app(id, "fp")?;
        self.bv_leaf(sign, 1)?;
        self.bv_leaf(exponent, format.eb)?;
        self.bv_leaf(fraction, format.p - 1)?;
        Ok(Fields {
            sign,
            exponent,
            fraction,
        })
    }

    pub(super) fn read_source(&mut self) -> Result<(RoundingInput, Fields, Fields, Format)> {
        let (_, sort) = self.term(self.source)?;
        let Sort::FloatingPoint(eb, p) = sort else {
            return Err(ReferenceError::Source);
        };
        let format = Format::checked_for(self.operation, *eb, *p)?;
        let [rm, x, y] = self.app(self.source, self.operation.name())?;
        // Validate EVERY source operand before precision-scaled owned reserve.
        Ok((
            self.read_rounding(rm)?,
            self.fields(x, format)?,
            self.fields(y, format)?,
            format,
        ))
    }

    fn read_rounding(&mut self, id: TermId) -> Result<RoundingInput> {
        let (data, sort) = self.term(id)?;
        if !matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode") {
            return Err(ReferenceError::Source);
        }
        match data {
            TermData::Var(_, _) => Ok(RoundingInput::Variable(id)),
            TermData::App(symbol, args) if args.is_empty() => {
                let mut found = None;
                for (number, names) in [
                    ["RNE", "roundNearestTiesToEven"],
                    ["RNA", "roundNearestTiesToAway"],
                    ["RTP", "roundTowardPositive"],
                    ["RTN", "roundTowardNegative"],
                    ["RTZ", "roundTowardZero"],
                ]
                .iter()
                .enumerate()
                {
                    if self.named(symbol, names[0])? || self.named(symbol, names[1])? {
                        found = Some(number as u64);
                        break;
                    }
                }
                let number = found.ok_or(ReferenceError::Source)?;
                Ok(RoundingInput::Literal(number))
            }
            _ => Err(ReferenceError::Source),
        }
    }

    pub(super) fn rounding_mode(&mut self, input: RoundingInput) -> Result<(RefId, RefId)> {
        let mode = match input {
            RoundingInput::Variable(id) => self.input(id, 3)?,
            RoundingInput::Literal(number) => self.small(number, 3)?,
        };
        let five = self.small(5, 3)?;
        let domain = self.binary(Binary::Ult, mode, five)?;
        Ok((mode, domain))
    }
}
