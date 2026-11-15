// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Streaming bounds for the new payload, independent of untrusted size hints.

use super::{NraSosCertificate, NraSosRational, NraSosTerm};
use crate::term::TermId;
use serde::de::{Error, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{fmt, marker::PhantomData};

struct Bounded<T, const N: usize>(Vec<T>);

/// A sequence's first excess element is refused before its payload is decoded.
/// In particular a 46th Gram row cannot allocate its own coefficient vectors.
struct ExcessEntry;

impl<'de> Deserialize<'de> for ExcessEntry {
    fn deserialize<D: Deserializer<'de>>(_: D) -> Result<Self, D::Error> {
        Err(D::Error::custom("SOS sequence exceeds its fixed bound"))
    }
}

pub(in crate::proof) fn deserialize_clause<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<TermId>, D::Error> {
    Ok(Bounded::<TermId, { NraSosCertificate::MAX_CLAUSE_SLOTS }>::deserialize(deserializer)?.0)
}

impl<'de, T: Deserialize<'de>, const N: usize> Deserialize<'de> for Bounded<T, N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct BoundedVisitor<T, const N: usize>(PhantomData<T>);
        impl<'de, T: Deserialize<'de>, const N: usize> Visitor<'de> for BoundedVisitor<T, N> {
            type Value = Bounded<T, N>;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "at most {N} SOS entries")
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                let mut values = Vec::new();
                loop {
                    if values.len() == N {
                        let _ = seq.next_element::<ExcessEntry>()?;
                        break;
                    }
                    let Some(value) = seq.next_element::<T>()? else {
                        break;
                    };
                    values.try_reserve(1).map_err(A::Error::custom)?;
                    values.push(value);
                }
                Ok(Bounded(values))
            }
        }
        deserializer.deserialize_seq(BoundedVisitor::<T, N>(PhantomData))
    }
}

pub(super) mod integer {
    use super::*;
    use num_bigint::{BigInt, Sign};

    pub(crate) fn serialize<S: Serializer>(
        value: &BigInt,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        crate::serde_bignum::bigint::serialize(value, serializer)
    }

    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<BigInt, D::Error> {
        let (sign, limbs) = <(i8, Bounded<u32, 32>)>::deserialize(deserializer)?;
        let sign = match sign {
            -1 => Sign::Minus,
            0 => Sign::NoSign,
            1 => Sign::Plus,
            _ => return Err(D::Error::custom("invalid SOS integer sign")),
        };
        if limbs.0.last() == Some(&0) || ((sign == Sign::NoSign) != limbs.0.is_empty()) {
            return Err(D::Error::custom("noncanonical SOS integer limbs"));
        }
        Ok(BigInt::new(sign, limbs.0))
    }
}

pub(super) mod basis {
    use super::*;
    pub(crate) fn serialize<S: Serializer>(
        value: &[Vec<TermId>],
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        value.serialize(serializer)
    }
    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<Vec<TermId>>, D::Error> {
        let rows = Bounded::<Bounded<TermId, 2>, { NraSosCertificate::MAX_BASIS }>::deserialize(
            deserializer,
        )?;
        Ok(rows.0.into_iter().map(|row| row.0).collect())
    }
}

pub(super) mod gram {
    use super::*;
    pub(crate) fn serialize<S: Serializer>(
        value: &[Vec<NraSosRational>],
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        value.serialize(serializer)
    }
    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<Vec<NraSosRational>>, D::Error> {
        let rows = Bounded::<
            Bounded<NraSosRational, { NraSosCertificate::MAX_BASIS }>,
            { NraSosCertificate::MAX_BASIS },
        >::deserialize(deserializer)?;
        Ok(rows.0.into_iter().map(|row| row.0).collect())
    }
}

pub(super) mod terms {
    use super::*;
    pub(crate) fn serialize<S: Serializer>(
        value: &[NraSosTerm],
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        value.serialize(serializer)
    }
    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<NraSosTerm>, D::Error> {
        Ok(Bounded::<NraSosTerm, { NraSosCertificate::MAX_TERMS }>::deserialize(deserializer)?.0)
    }
}
