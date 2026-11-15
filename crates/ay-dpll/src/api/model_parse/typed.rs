// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict finite model decoding against recovered declaration sorts.
//!
//! This is separate from the best-effort model printer parser. No missing
//! value becomes a default, and no opaque spelling becomes a concrete value.
//! Input parsing/model printing precede this bounded decoder and remain owned
//! by the caller; these allowances are not a process-memory guarantee.
//! Numeric-library intermediates, allocator bookkeeping and ordered-map
//! comparisons are not an exact allocation or instruction meter.

use ay_core::Sort;
use ay_frontend::SExpr;

use super::super::types::ModelValue;

mod compound;
mod numeric;
mod registry;
mod sorts;

const MAX_DEPTH: usize = 64;
const MAX_WORK: usize = 1_048_576;
const MAX_COPY_BYTES: usize = 16 * 1024 * 1024;

/// One cumulative allowance for every requested value in a get-value batch.
pub(super) struct Decoder<'ctx> {
    context: Option<&'ctx ay_frontend::Context>,
    work: usize,
    bytes: usize,
    stopped: bool,
}

impl<'ctx> Decoder<'ctx> {
    pub(super) fn new() -> Self {
        Self {
            context: None,
            work: MAX_WORK,
            bytes: MAX_COPY_BYTES,
            stopped: false,
        }
    }

    pub(super) fn with_context(context: &'ctx ay_frontend::Context) -> Self {
        Self {
            context: Some(context),
            ..Self::new()
        }
    }

    /// Data-only batch ingress admits every borrowed signature before parsing
    /// the first value. The same ledger later pays for decoding those values.
    pub(super) fn preflight_literal_sort(&mut self, sort: &Sort) -> Option<()> {
        let result = self.sort(sort, 0);
        if result.is_none() {
            self.stopped = true;
        }
        result
    }

    /// Prepay parser/result storage on this decoder's cumulative allowance.
    pub(super) fn reserve_literal_resources(&mut self, work: usize, bytes: usize) -> Option<()> {
        self.charge(work)?;
        self.copy(bytes)
    }

    pub(super) fn refuse_literal_batch(&mut self) {
        self.stopped = true;
    }

    pub(super) fn decode(&mut self, value: &SExpr, sort: &Sort) -> Option<ModelValue> {
        if self.stopped {
            return None;
        }
        let result = self
            .input(value)
            .and_then(|()| self.sort(sort, 0))
            .and_then(|()| self.value(value, sort, 0));
        if result.is_none() {
            self.stopped = true;
        }
        result
    }

    fn charge(&mut self, work: usize) -> Option<()> {
        if self.stopped {
            return None;
        }
        match self.work.checked_sub(work) {
            Some(left) => {
                self.work = left;
                Some(())
            }
            None => {
                self.stopped = true;
                None
            }
        }
    }

    fn copy(&mut self, bytes: usize) -> Option<()> {
        if self.stopped {
            return None;
        }
        match self.bytes.checked_sub(bytes) {
            Some(left) => {
                self.bytes = left;
                Some(())
            }
            None => {
                self.stopped = true;
                None
            }
        }
    }

    fn input(&mut self, root: &SExpr) -> Option<()> {
        self.copy(std::mem::size_of::<&SExpr>())?;
        let mut stack = vec![root];
        while let Some(value) = stack.pop() {
            self.charge(1)?;
            match value {
                SExpr::List(children) => {
                    self.charge(children.len())?;
                    self.copy(children.len().checked_mul(std::mem::size_of::<&SExpr>())?)?;
                    stack.try_reserve_exact(children.len()).ok()?;
                    stack.extend(children);
                }
                SExpr::Symbol(text)
                | SExpr::Numeral(text)
                | SExpr::Decimal(text)
                | SExpr::Hexadecimal(text)
                | SExpr::Binary(text)
                | SExpr::String(text) => {
                    self.charge(text.len())?;
                }
                SExpr::True | SExpr::False => {}
                _ => return None,
            }
        }
        Some(())
    }

    fn value(&mut self, value: &SExpr, sort: &Sort, depth: usize) -> Option<ModelValue> {
        self.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        self.copy(std::mem::size_of::<ModelValue>())?;
        match sort {
            Sort::Bool => match value {
                SExpr::True => Some(ModelValue::Bool(true)),
                SExpr::False => Some(ModelValue::Bool(false)),
                _ => None,
            },
            Sort::FiniteField(field) => {
                let text = if let Some(symbol) = value.as_symbol() {
                    let (n, p) = symbol.strip_prefix("#f")?.split_once('m')?;
                    if p.parse::<u32>().ok()? != field.modulus() {
                        return None;
                    }
                    n
                } else {
                    let [as_kw, numeral, annotation] = value.as_list()? else {
                        return None;
                    };
                    if !as_kw.is_symbol("as") {
                        return None;
                    }
                    self.ascribed(annotation, sort, depth + 1)?;
                    numeral.as_symbol()?.strip_prefix("ff")?
                };
                self.charge(text.len().checked_add(1)?)?;
                self.copy(text.len().checked_mul(4)?.checked_add(64)?)?;
                let n: num_bigint::BigInt = text.parse().ok()?;
                use num_integer::Integer;
                use num_traits::ToPrimitive;
                let n = n
                    .mod_floor(&num_bigint::BigInt::from(field.modulus()))
                    .to_u32()?;
                Some(ModelValue::FiniteField {
                    value: n,
                    field: *field,
                })
            }
            Sort::Int => Some(ModelValue::Int(self.integer(value, depth)?)),
            Sort::Real => Some(ModelValue::Real(self.real(value, depth)?)),
            Sort::BitVec(width) => self.bitvector(value, width.width),
            Sort::String => {
                let SExpr::String(text) = value else {
                    return None;
                };
                self.copy(text.len())?;
                Some(ModelValue::String(text.clone()))
            }
            Sort::Array(array) => self.array(value, array, depth),
            Sort::Datatype(datatype) => self.datatype(value, datatype, depth),
            Sort::Complex => self.datatype(value, sort.datatype_definition()?, depth),
            Sort::Seq(element) => self.sequence(value, element, depth),
            Sort::FloatingPoint(eb, sb) => self.floating_point(value, *eb, *sb),
            Sort::Uninterpreted(carrier) => self.registered(value, carrier, depth),
            _ => None,
        }
    }
}

#[cfg(test)]
pub(crate) fn parse_typed_value(value: &SExpr, sort: &Sort) -> Option<ModelValue> {
    Decoder::new().decode(value, sort)
}

#[cfg(test)]
mod resource_tests;
#[cfg(test)]
mod tests;
