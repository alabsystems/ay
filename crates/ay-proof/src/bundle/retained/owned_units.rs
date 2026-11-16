// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed unit-enum routes using the owning type's existing variant registry.
//!
//! Only the four explicit wrappers are exposed. No arbitrary owning serde
//! decoder, JSON parser or diagnostic allocation is hidden here. The enum's
//! Deserialize supplies its static names; variant seeds receive a known static
//! name. Every nonunit request refuses BEFORE invoking its payload seed, even
//! if a future enum revision adds an owning variant. Payload routes must be
//! selected before this bridge, never retried after its sticky refusal.

use super::owned_values::{null, tagged, RawSlice};
use super::{Control, TransportError};
use ay_core::{AletheRule, BvGateType, FpOp, TheoryLemmaKind};
use serde::{de, Deserialize, Deserializer};
use std::fmt;

pub(super) fn bv_gate(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<BvGateType, TransportError> {
    decode(raw, control)
}

pub(super) fn fp_operation(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<FpOp, TransportError> {
    decode(raw, control)
}

pub(super) fn theory_unit(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<TheoryLemmaKind, TransportError> {
    decode(raw, control)
}

pub(super) fn alethe_unit(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<AletheRule, TransportError> {
    decode(raw, control)
}

fn decode<T: for<'de> Deserialize<'de>>(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<T, TransportError> {
    control.charge(0, 0)?;
    // The concrete wrappers above are the complete admitted type set. This
    // private generic is not an entry point for arbitrary owning ADTs.
    let result = T::deserialize(UnitDeserializer { raw, control });
    let value = match result {
        Ok(value) => value,
        Err(error) => return control.fail(error.0),
    };
    control.charge(0, 0)?;
    Ok(value)
}

#[derive(Clone, Copy, Debug)]
struct Error(TransportError);

impl Error {
    fn unsupported() -> Self {
        Self(TransportError::InvalidShape("expected a unit enum variant"))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("invalid controlled unit enum")
    }
}
impl std::error::Error for Error {}
impl de::Error for Error {
    fn custom<T: fmt::Display>(_: T) -> Self {
        Self::unsupported()
    }
}

struct UnitDeserializer<'raw, 'scope, 'progress> {
    raw: RawSlice<'raw>,
    control: &'scope mut Control<'progress>,
}

impl<'de> Deserializer<'de> for UnitDeserializer<'_, '_, '_> {
    type Error = Error;

    fn deserialize_any<V: de::Visitor<'de>>(self, _: V) -> Result<V::Value, Error> {
        Err(Error::unsupported())
    }

    fn deserialize_enum<V: de::Visitor<'de>>(
        self,
        _: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Error> {
        let tag = tagged(self.raw, variants, self.control).map_err(Error)?;
        // The existing enum visitor dispatches over the known static names
        // once more. Price that bounded second pass rather than hiding it in
        // the metadata comparison already charged by tagged().
        self.control.charge(variants.len(), 0).map_err(Error)?;
        for name in variants {
            self.control.charge(name.len(), 0).map_err(Error)?;
        }
        let name = variants
            .get(tag.index)
            .copied()
            .ok_or_else(Error::unsupported)?;
        visitor.visit_enum(UnitAccess {
            name,
            payload: tag.payload,
            control: self.control,
        })
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct identifier ignored_any
    }
}

struct UnitAccess<'raw, 'scope, 'progress> {
    name: &'static str,
    payload: Option<RawSlice<'raw>>,
    control: &'scope mut Control<'progress>,
}

impl<'de> de::EnumAccess<'de> for UnitAccess<'_, '_, '_> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V: de::DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, Self), Error> {
        let value =
            seed.deserialize(de::value::BorrowedStrDeserializer::<Error>::new(self.name))?;
        Ok((value, self))
    }
}

impl<'de> de::VariantAccess<'de> for UnitAccess<'_, '_, '_> {
    type Error = Error;

    fn unit_variant(self) -> Result<(), Error> {
        match self.payload {
            Some(raw) => null(raw, self.control).map_err(Error),
            None => self.control.charge(0, 0).map_err(Error),
        }
    }

    fn newtype_variant_seed<T: de::DeserializeSeed<'de>>(self, _: T) -> Result<T::Value, Error> {
        Err(Error::unsupported())
    }

    fn tuple_variant<V: de::Visitor<'de>>(self, _: usize, _: V) -> Result<V::Value, Error> {
        Err(Error::unsupported())
    }

    fn struct_variant<V: de::Visitor<'de>>(
        self,
        _: &'static [&'static str],
        _: V,
    ) -> Result<V::Value, Error> {
        Err(Error::unsupported())
    }
}

#[cfg(test)]
mod tests;
