// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::graph::{Binary, Bits, RefId};
use super::super::{Arithmetic, Format, ReferenceError};
use super::source::{Builder, Value};
use super::{Error, Result};
use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use num_bigint::Sign;

impl Builder<'_, '_> {
    pub(super) fn lower(&mut self, id: TermId, data: &TermData, sort: &Sort) -> Result<Value> {
        match data {
            TermData::Var(_, _) => self.variable(id, sort),
            TermData::Const(Constant::Bool(value)) => Ok(Value::Bool(
                self.program.reference.small(u64::from(*value), 1)?,
            )),
            TermData::Const(Constant::BitVec { value, width })
                if *width > 0
                    && value.sign() != Sign::Minus
                    && value.bits() <= u64::from(*width) =>
            {
                Ok(Value::Bv(self.program.reference.input(id, *width)?))
            }
            TermData::App(symbol, args) => self.application(symbol, args, sort),
            TermData::Not(child) => {
                let value = self.boolean(*child)?;
                Ok(Value::Bool(self.program.reference.not(value)?))
            }
            TermData::Ite(c, y, n) => self.conditional(*c, *y, *n),
            _ => Err(Error::Source),
        }
    }

    fn variable(&mut self, id: TermId, sort: &Sort) -> Result<Value> {
        match sort {
            Sort::Bool => Ok(Value::Bool(self.program.reference.input(id, 1)?)),
            Sort::BitVec(bv) if bv.width > 0 => {
                Ok(Value::Bv(self.program.reference.input(id, bv.width)?))
            }
            Sort::Uninterpreted(name) if name == "RoundingMode" => {
                let word = self.program.reference.input(id, 3)?;
                self.domain(word)?;
                Ok(Value::Rm(word))
            }
            Sort::FloatingPoint(eb, p) => {
                Format::checked_for(Arithmetic::Mul, *eb, *p)?;
                let width = eb.checked_add(*p).ok_or(ReferenceError::Width)?;
                let word = self.program.reference.input(id, width)?;
                self.interchange(word, *eb, *p)
            }
            _ => Err(Error::Source),
        }
    }

    fn application(&mut self, symbol: &Symbol, args: &[TermId], sort: &Sort) -> Result<Value> {
        // All builtin spellings are short. This refusal avoids unpriced long
        // string comparisons; it does not authenticate declarations by name.
        self.program.reference.charge(1, 0)?;
        match symbol {
            Symbol::Named(name) if name.len() <= 32 => {
                self.program.reference.charge(name.len(), 0)?;
                if self.program.reference.terms.is_declared_function(name) {
                    return Err(Error::Source);
                }
                self.named_application(name.as_str(), args, sort)
            }
            Symbol::Indexed(name, indices) if name.len() <= 32 => {
                self.program
                    .reference
                    .charge(name.len().saturating_add(indices.len()), 0)?;
                if self.program.reference.terms.is_declared_function(name) {
                    return Err(Error::Source);
                }
                self.indexed_application(name.as_str(), indices, args, sort)
            }
            _ => Err(Error::Source),
        }
    }

    fn named_application(&mut self, name: &str, args: &[TermId], sort: &Sort) -> Result<Value> {
        if args.is_empty() {
            let code = match name {
                "RNE" | "roundNearestTiesToEven" => 0,
                "RNA" | "roundNearestTiesToAway" => 1,
                "RTP" | "roundTowardPositive" => 2,
                "RTN" | "roundTowardNegative" => 3,
                "RTZ" | "roundTowardZero" => 4,
                _ => return Err(Error::Source),
            };
            return Ok(Value::Rm(self.program.reference.small(code, 3)?));
        }
        match (name, args) {
            ("not", [a]) => {
                let a = self.boolean(*a)?;
                Ok(Value::Bool(self.program.reference.not(a)?))
            }
            ("and" | "or" | "xor", _) => self.fold_boolean(name, args),
            ("=>", [a, b]) => {
                let a = self.boolean(*a)?;
                let b = self.boolean(*b)?;
                let not_a = self.program.reference.not(a)?;
                Ok(Value::Bool(self.program.reference.binary(
                    Binary::Or,
                    not_a,
                    b,
                )?))
            }
            ("=", [a, b]) => self.equal(*a, *b),
            ("ite", [c, y, n]) => self.conditional(*c, *y, *n),
            ("fp", [s, e, f]) => self.constructor(*s, *e, *f, sort),
            ("fp.add" | "fp.sub" | "fp.mul", [rm, x, y]) => {
                self.arithmetic(name, *rm, *x, *y, sort)
            }
            ("fp.neg" | "fp.abs", [x]) => {
                let (mut bits, eb, p) = self.fp(*x)?;
                bits.sign = if name == "fp.neg" {
                    self.program.reference.not(bits.sign)?
                } else {
                    self.program.reference.small(0, 1)?
                };
                Ok(Value::Fp { bits, eb, p })
            }
            (name, [x]) if name.starts_with("fp.is") => self.classifier(name, *x),
            ("fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq", [x, y]) => {
                self.fp_compare(name, *x, *y)
            }
            _ => self.bv_application(name, args),
        }
    }

    fn fold_boolean(&mut self, name: &str, args: &[TermId]) -> Result<Value> {
        let op = match name {
            "and" => Binary::And,
            "or" => Binary::Or,
            _ => Binary::Xor,
        };
        let mut result = self.program.reference.small(u64::from(name == "and"), 1)?;
        for &arg in args {
            let child = self.boolean(arg)?;
            result = self.program.reference.binary(op, result, child)?;
        }
        Ok(Value::Bool(result))
    }

    fn conditional(&mut self, condition: TermId, yes: TermId, no: TermId) -> Result<Value> {
        let c = self.boolean(condition)?;
        let y = self.value(yes)?;
        let n = self.value(no)?;
        match (y, n) {
            (Value::Bool(y), Value::Bool(n)) => {
                Ok(Value::Bool(self.program.reference.select(c, y, n)?))
            }
            (Value::Bv(y), Value::Bv(n)) => Ok(Value::Bv(self.program.reference.select(c, y, n)?)),
            (Value::Rm(y), Value::Rm(n)) => Ok(Value::Rm(self.program.reference.select(c, y, n)?)),
            (
                Value::Fp { bits: y, eb, p },
                Value::Fp {
                    bits: n,
                    eb: ne,
                    p: np,
                },
            ) if eb == ne && p == np => {
                let sign = self.program.reference.select(c, y.sign, n.sign)?;
                let exponent = self.program.reference.select(c, y.exponent, n.exponent)?;
                let fraction = self.program.reference.select(c, y.fraction, n.fraction)?;
                Ok(Value::Fp {
                    bits: Bits {
                        sign,
                        exponent,
                        fraction,
                    },
                    eb,
                    p,
                })
            }
            _ => Err(Error::Source),
        }
    }

    fn equal(&mut self, a: TermId, b: TermId) -> Result<Value> {
        let a = self.value(a)?;
        let b = self.value(b)?;
        match (a, b) {
            (Value::Bool(a), Value::Bool(b))
            | (Value::Bv(a), Value::Bv(b))
            | (Value::Rm(a), Value::Rm(b)) => Ok(Value::Bool(self.program.reference.binary(
                Binary::Eq,
                a,
                b,
            )?)),
            (
                Value::Fp { bits: a, eb, p },
                Value::Fp {
                    bits: b,
                    eb: be,
                    p: bp,
                },
            ) if eb == be && p == bp => self.structural_equality(a, b),
            _ => Err(Error::Source),
        }
    }

    fn bv_application(&mut self, name: &str, args: &[TermId]) -> Result<Value> {
        match (name, args) {
            ("bvnot", [a]) => {
                let a = self.bv(*a)?;
                Ok(Value::Bv(self.program.reference.not(a)?))
            }
            ("concat", [a, b]) => {
                let a = self.bv(*a)?;
                let b = self.bv(*b)?;
                Ok(Value::Bv(self.concat(a, b)?))
            }
            (_, [a, b]) => {
                let a = self.bv(*a)?;
                let b = self.bv(*b)?;
                let op = match name {
                    "bvadd" => Binary::Add,
                    "bvsub" => Binary::Sub,
                    "bvmul" => Binary::Mul,
                    "bvand" => Binary::And,
                    "bvor" => Binary::Or,
                    "bvxor" => Binary::Xor,
                    "bvshl" => Binary::Shl,
                    "bvlshr" => Binary::Lshr,
                    "bvult" => Binary::Ult,
                    _ => return Err(Error::Source),
                };
                let word = self.program.reference.binary(op, a, b)?;
                Ok(if op == Binary::Ult {
                    Value::Bool(word)
                } else {
                    Value::Bv(word)
                })
            }
            _ => Err(Error::Source),
        }
    }

    pub(super) fn concat(&mut self, high: RefId, low: RefId) -> Result<RefId> {
        let high_width = self.program.reference.width(high)?;
        let low_width = self.program.reference.width(low)?;
        let width = high_width
            .checked_add(low_width)
            .ok_or(ReferenceError::Width)?;
        let high = self.program.reference.resize(high, width)?;
        let count = self.program.reference.small(u64::from(low_width), width)?;
        let high = self.program.reference.binary(Binary::Shl, high, count)?;
        let low = self.program.reference.resize(low, width)?;
        Ok(self.program.reference.binary(Binary::Or, high, low)?)
    }

    fn indexed_application(
        &mut self,
        name: &str,
        indices: &[u32],
        args: &[TermId],
        sort: &Sort,
    ) -> Result<Value> {
        match (name, indices, args) {
            ("extract", [high, low], [word]) => {
                let word = self.bv(*word)?;
                Ok(Value::Bv(
                    self.program.reference.extract(word, *high, *low)?,
                ))
            }
            ("zero_extend", [added], [word]) => {
                let word = self.bv(*word)?;
                let width = self
                    .program
                    .reference
                    .width(word)?
                    .checked_add(*added)
                    .ok_or(ReferenceError::Width)?;
                Ok(Value::Bv(self.program.reference.resize(word, width)?))
            }
            ("to_fp", [eb, p], [word]) => {
                if !matches!(sort, Sort::FloatingPoint(e, s) if e == eb && s == p) {
                    return Err(Error::Source);
                }
                Format::checked_for(Arithmetic::Mul, *eb, *p)?;
                let word = self.bv(*word)?;
                let expected = eb.checked_add(*p).ok_or(ReferenceError::Width)?;
                if self.program.reference.width(word)? != expected {
                    return Err(Error::Source);
                }
                self.interchange(word, *eb, *p)
            }
            ("+zero" | "-zero" | "+oo" | "-oo" | "NaN", [eb, p], []) => {
                self.special_constant(name, *eb, *p)
            }
            _ => Err(Error::Source),
        }
    }

    pub(super) fn interchange(&mut self, word: RefId, eb: u32, p: u32) -> Result<Value> {
        let width = eb.checked_add(p).ok_or(ReferenceError::Width)?;
        let sign = self.program.reference.extract(word, width - 1, width - 1)?;
        let exponent = self.program.reference.extract(word, width - 2, p - 1)?;
        let fraction = self.program.reference.extract(word, p - 2, 0)?;
        Ok(Value::Fp {
            bits: Bits {
                sign,
                exponent,
                fraction,
            },
            eb,
            p,
        })
    }

    fn special_constant(&mut self, name: &str, eb: u32, p: u32) -> Result<Value> {
        Format::checked_for(Arithmetic::Mul, eb, p)?;
        let sign = self
            .program
            .reference
            .small(u64::from(name.starts_with('-')), 1)?;
        let exponent = if name.ends_with("oo") || name == "NaN" {
            self.program.reference.ones(eb)?
        } else {
            self.program.reference.small(0, eb)?
        };
        let fraction = self
            .program
            .reference
            .small(u64::from(name == "NaN"), p - 1)?;
        Ok(Value::Fp {
            bits: Bits {
                sign,
                exponent,
                fraction,
            },
            eb,
            p,
        })
    }
}
