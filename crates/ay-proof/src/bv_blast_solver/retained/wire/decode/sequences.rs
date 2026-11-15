// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::marker::PhantomData;

pub(super) struct Rows<'a, 'b, 'p>(pub(super) Shared<'a, 'b, 'p>);

impl<'de> DeserializeSeed<'de> for Rows<'_, '_, '_> {
    type Value = Vec<RetainedRupRow>;
    fn deserialize<D: serde::Deserializer<'de>>(self, de: D) -> Result<Self::Value, D::Error> {
        de.deserialize_seq(self)
    }
}

impl<'de> Visitor<'de> for Rows<'_, '_, '_> {
    type Value = Vec<RetainedRupRow>;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an array of retained rows")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut rows = Vec::new();
        while let Some(()) = seq.next_element_seed(RowEntry {
            control: self.0,
            output: &mut rows,
        })? {}
        Ok(rows)
    }
}

struct RowEntry<'o, 'a, 'b, 'p> {
    control: Shared<'a, 'b, 'p>,
    output: &'o mut Vec<RetainedRupRow>,
}

impl<'de> DeserializeSeed<'de> for RowEntry<'_, '_, '_, '_> {
    type Value = ();
    fn deserialize<D: serde::Deserializer<'de>>(self, de: D) -> Result<(), D::Error> {
        let limit = de_result(self.control.borrow_mut().item(Item::Row))?;
        de_result(self.control.borrow_mut().slot(self.output, limit))?;
        // Reserve the parent slot BEFORE any of the row's child allocations.
        let row = de.deserialize_map(visitors::Row(self.control))?;
        self.output.push(row);
        Ok(())
    }
}

pub(super) trait WireNumber: Sized {
    const ITEM: Item;
    fn from_u64(value: u64) -> Option<Self>;
}

impl WireNumber for u32 {
    const ITEM: Item = Item::Literal;
    fn from_u64(value: u64) -> Option<Self> {
        u32::try_from(value).ok()
    }
}

impl WireNumber for u64 {
    const ITEM: Item = Item::Hint;
    fn from_u64(value: u64) -> Option<Self> {
        Some(value)
    }
}

pub(super) struct Numbers<'a, 'b, 'p, T>(Shared<'a, 'b, 'p>, PhantomData<T>);

pub(super) fn numbers<'a, 'b, 'p, T>(control: Shared<'a, 'b, 'p>) -> Numbers<'a, 'b, 'p, T> {
    Numbers(control, PhantomData)
}

impl<'de, T: WireNumber> DeserializeSeed<'de> for Numbers<'_, '_, '_, T> {
    type Value = Vec<T>;
    fn deserialize<D: serde::Deserializer<'de>>(self, de: D) -> Result<Vec<T>, D::Error> {
        de.deserialize_seq(self)
    }
}

impl<'de, T: WireNumber> Visitor<'de> for Numbers<'_, '_, '_, T> {
    type Value = Vec<T>;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an array of unsigned integers")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Vec<T>, A::Error> {
        let mut values = Vec::new();
        while let Some(()) = seq.next_element_seed(NumberEntry {
            control: self.0,
            output: &mut values,
        })? {}
        Ok(values)
    }
}

struct NumberEntry<'o, 'a, 'b, 'p, T> {
    control: Shared<'a, 'b, 'p>,
    output: &'o mut Vec<T>,
}

impl<'de, T: WireNumber> DeserializeSeed<'de> for NumberEntry<'_, '_, '_, '_, T> {
    type Value = ();
    fn deserialize<D: serde::Deserializer<'de>>(self, de: D) -> Result<(), D::Error> {
        let limit = de_result(self.control.borrow_mut().item(T::ITEM))?;
        de_result(self.control.borrow_mut().slot(self.output, limit))?;
        let value = Number(self.control).deserialize(de)?;
        let value = T::from_u64(value).ok_or_else(|| invalid(self.control, "integer range"))?;
        self.output.push(value);
        Ok(())
    }
}
