// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact concrete values for the admitted original quantified source fragment.
//! No opaque model aliases, numeric coercions or invented array defaults enter
//! this codec. Store order and every record field are retained verbatim.

use super::SourceControl;
use crate::quantified::records::{sort_bytes, Registry};
use crate::smt::SmtValue;
use crate::ChcSort;
use ay_dpll::api::ModelValue;

mod wide;

const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 128;
const MAX_OUTPUT: usize = 8 * 1024 * 1024;

pub(super) fn decode(
    value: &ModelValue,
    sort: &ChcSort,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<SmtValue> {
    admit_sort(sort, registry, control)?;
    let result = Codec::new(control).decode(value, sort, 0)?;
    control.poll()?;
    Some(result)
}

pub(super) fn literal(
    value: &SmtValue,
    sort: &ChcSort,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<String> {
    admit_sort(sort, registry, control)?;
    let result = {
        let mut codec = Codec::new(control);
        codec.write(value, sort, 0)?;
        codec.text
    };
    // All metadata/formatting scratch has been destroyed before admission.
    control.poll()?;
    Some(result)
}

fn admit_sort(sort: &ChcSort, registry: &Registry, control: &SourceControl<'_>) -> Option<()> {
    control.charge(1)?;
    // The existing borrowed preflight bounds metadata depth, repeated nodes,
    // names and array rank before registry comparison. Its internal scan and
    // the registry validator are bounded opaque intervals, not latency bounds.
    let bytes = sort_bytes(sort)?;
    control.charge(bytes.div_ceil(64))?;
    control.bytes(bytes.checked_mul(2)?)?;
    registry.validate_sort(sort).ok()?;
    control.poll()
}

struct Codec<'a, 'token> {
    control: &'a SourceControl<'token>,
    nodes_left: usize,
    decoded_bytes: usize,
    text: String,
}

impl<'a, 'token> Codec<'a, 'token> {
    fn new(control: &'a SourceControl<'token>) -> Self {
        Self {
            control,
            nodes_left: MAX_NODES,
            decoded_bytes: 0,
            text: String::new(),
        }
    }

    fn step(&mut self, depth: usize) -> Option<()> {
        self.control.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        self.nodes_left = self.nodes_left.checked_sub(1)?;
        Some(())
    }

    fn array_depth(&self, depth: usize, stores: usize) -> Option<usize> {
        // Flat model entries emit nested SMT stores. Count that actual term
        // depth as well as recursive record/array nesting, before allocation.
        let children = stores.checked_mul(2)?.checked_add(1)?;
        if children > self.nodes_left {
            return None;
        }
        self.control.charge(children)?;
        depth
            .checked_add(stores)?
            .checked_add(1)
            .filter(|n| *n <= MAX_DEPTH)
    }

    fn copy(&mut self, bytes: usize) -> Option<()> {
        self.decoded_bytes = self
            .decoded_bytes
            .checked_add(bytes)
            .filter(|n| *n <= MAX_OUTPUT)?;
        self.control.bytes(bytes)
    }

    fn decode(&mut self, value: &ModelValue, sort: &ChcSort, depth: usize) -> Option<SmtValue> {
        self.step(depth)?;
        self.copy(std::mem::size_of::<SmtValue>())?;
        match (value, sort) {
            (ModelValue::Bool(value), ChcSort::Bool) => Some(SmtValue::Bool(*value)),
            (ModelValue::BitVec { value, width }, ChcSort::BitVec(expected)) => {
                self.decode_bitvec(value, *width, *expected)
            }
            (ModelValue::Array { default, stores }, ChcSort::Array(key, cell)) => {
                let child_depth = self.array_depth(depth, stores.len())?;
                self.copy(
                    stores
                        .len()
                        .checked_mul(std::mem::size_of::<(SmtValue, SmtValue)>())?,
                )?;
                let mut entries = Vec::new();
                entries.try_reserve_exact(stores.len()).ok()?;
                let default = Box::new(self.decode(default, cell, child_depth)?);
                for (index, value) in stores {
                    entries.push((
                        self.decode(index, key, child_depth)?,
                        self.decode(value, cell, child_depth)?,
                    ));
                }
                Some(SmtValue::ArrayMap { default, entries })
            }
            (
                ModelValue::Datatype { constructor, args },
                ChcSort::Datatype { constructors, .. },
            ) => {
                let [expected] = constructors.as_slice() else {
                    return None;
                };
                if args.len() != expected.selectors.len() || args.len() > self.nodes_left {
                    return None;
                }
                self.copy(constructor.len().checked_add(expected.name.len())?)?;
                if constructor != &expected.name {
                    return None;
                }
                self.control.charge(args.len())?;
                self.copy(args.len().checked_mul(std::mem::size_of::<SmtValue>())?)?;
                let mut fields = Vec::new();
                fields.try_reserve_exact(args.len()).ok()?;
                for (value, field) in args.iter().zip(&expected.selectors) {
                    fields.push(self.decode(value, &field.sort, depth.checked_add(1)?)?);
                }
                Some(SmtValue::Datatype(expected.name.clone(), fields))
            }
            _ => None,
        }
    }

    fn push(&mut self, text: &str) -> Option<()> {
        self.control.charge(1)?;
        self.text
            .len()
            .checked_add(text.len())
            .filter(|n| *n <= MAX_OUTPUT)?;
        self.control.bytes(text.len().checked_mul(2)?)?;
        self.text.try_reserve(text.len()).ok()?;
        self.text.push_str(text);
        Some(())
    }

    fn symbol(&mut self, name: &str) -> Option<()> {
        // Source metadata was completely authenticated before reaching here.
        self.control
            .bytes(name.len().checked_mul(2)?.checked_add(4)?)?;
        self.push(&ay_core::quote_symbol(name))
    }

    fn sort(&mut self, sort: &ChcSort) -> Option<()> {
        self.control.charge(1)?;
        match sort {
            ChcSort::Bool => self.push("Bool"),
            ChcSort::BitVec(width) => {
                self.control.bytes(32)?;
                self.push(&format!("(_ BitVec {width})"))
            }
            ChcSort::Array(key, cell) => {
                self.push("(Array ")?;
                self.sort(key)?;
                self.push(" ")?;
                self.sort(cell)?;
                self.push(")")
            }
            ChcSort::Datatype { name, .. } => self.symbol(name),
            _ => None,
        }
    }

    fn write(&mut self, value: &SmtValue, sort: &ChcSort, depth: usize) -> Option<()> {
        self.step(depth)?;
        match (value, sort) {
            (SmtValue::Bool(value), ChcSort::Bool) => {
                self.push(if *value { "true" } else { "false" })
            }
            (SmtValue::BitVec(value, width), ChcSort::BitVec(expected)) => {
                self.write_small_bitvec(*value, *width, *expected)
            }
            (SmtValue::BigBitVec(value, width), ChcSort::BitVec(expected)) => {
                self.write_big_bitvec(value, *width, *expected)
            }
            (SmtValue::ConstArray(default), ChcSort::Array(_, cell)) => {
                let depth = self.array_depth(depth, 0)?;
                self.constant(default, sort, cell, depth)
            }
            (SmtValue::ArrayMap { default, entries }, ChcSort::Array(key, cell)) => {
                let depth = self.array_depth(depth, entries.len())?;
                for _ in entries {
                    self.push("(store ")?;
                }
                self.constant(default, sort, cell, depth)?;
                for (index, value) in entries {
                    self.push(" ")?;
                    self.write(index, key, depth)?;
                    self.push(" ")?;
                    self.write(value, cell, depth)?;
                    self.push(")")?;
                }
                Some(())
            }
            (SmtValue::Datatype(constructor, args), ChcSort::Datatype { name, constructors }) => {
                let [expected] = constructors.as_slice() else {
                    return None;
                };
                if args.len() != expected.selectors.len() || args.len() > self.nodes_left {
                    return None;
                }
                self.control
                    .bytes(constructor.len().checked_add(expected.name.len())?)?;
                if constructor != &expected.name {
                    return None;
                }
                self.control.charge(args.len())?;
                self.push("((as ")?;
                self.symbol(constructor)?;
                self.push(" ")?;
                self.symbol(name)?;
                self.push(")")?;
                for (value, field) in args.iter().zip(&expected.selectors) {
                    self.push(" ")?;
                    self.write(value, &field.sort, depth.checked_add(1)?)?;
                }
                self.push(")")
            }
            _ => None,
        }
    }

    fn constant(
        &mut self,
        value: &SmtValue,
        array: &ChcSort,
        cell: &ChcSort,
        depth: usize,
    ) -> Option<()> {
        self.push("((as const ")?;
        self.sort(array)?;
        self.push(") ")?;
        self.write(value, cell, depth)?;
        self.push(")")
    }
}

#[cfg(test)]
mod tests;
