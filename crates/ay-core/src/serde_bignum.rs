// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Local serde codecs for the bignum-bearing proof artifacts.
//!
//! # Why this module exists
//!
//! `num-bigint` and `num-rational` were third-party serde blockers for the
//! whole workspace for one reason only: `Cargo.toml` enabled their `serde`
//! features. Dropping those two features severs the edge — but three
//! definitions in this crate are `#[derive(Serialize, Deserialize)]` and
//! carry bignum members, so they need their impls back from somewhere:
//!
//! * [`crate::term::Constant`] — `Int(BigInt)` and `BitVec { value: BigInt }`
//! * [`crate::term::RationalWrapper`] — `BigRational`
//! * [`crate::proof::FarkasAnnotation`] — `Vec<Rational64>`
//!
//! `Rational64 = Ratio<i64>` is the one that hides: it contains no `BigInt`
//! and not even the substring "Big", so a scan for bignum-typed members is
//! structurally blind to it. It needs its own `Ratio<i64>` codec
//! ([`rational64`] / [`rational64_vec`]); the `BigInt` codec does not apply.
//!
//! # Byte-identity is the whole gate
//!
//! These are PROOF ARTIFACTS: they are written to disk and read back. A codec
//! that encodes even one case differently makes previously-written evidence
//! unreadable or — far worse — silently reinterpreted. So these functions do
//! not invent a nicer format. They reproduce, byte for byte, what
//! `num-bigint 0.4.6` and `num-rational 0.4.2` produced with their `serde`
//! features on, as captured in
//! `crates/ay-core/tests/fixtures/serde_bignum_golden.json` and enforced by
//! `crates/ay-core/tests/serde_bignum_golden.rs`. **Any change here that the
//! golden fixture does not already record is a format break.**
//!
//! (This is deliberately unlike the decimal-string codecs in
//! `ay-milp::hybrid_pb_lp` and `ay-pb-core::optimize::farkas_cert`. Those
//! chose a portable encoding for a NEW artifact; this one is bound to an
//! encoding that already exists on disk.)
//!
//! # The format, observed rather than assumed
//!
//! * `BigInt` is the 2-tuple `[sign, limbs]`. `sign` is a bare `i8` in
//!   `{-1, 0, 1}` — **sign-magnitude, not two's complement**. `limbs` is a
//!   sequence of **base-2^32** digits, least significant first.
//! * The limb array is exactly `magnitude().to_u32_digits()`. That is not a
//!   convenience: on a 64-bit host `num-bigint` stores 64-bit limbs and
//!   splits each into `(lo, hi)` u32 words on the way out **but omits the
//!   final limb's high word when it is zero**, so the word count can be odd.
//!   `to_u32_digits()` is defined in base 2^32 regardless of the host's
//!   `BigDigit` width, so a codec written against it also produces identical
//!   bytes on a 32-bit host.
//! * Decoding mirrors `BigInt::from_biguint`, which NORMALIZES: sign `0`
//!   clears the limbs, an empty limb vector demotes the sign to `0`, and
//!   trailing zero limbs are trimmed. Non-canonical input is therefore
//!   accepted and silently canonicalized, exactly as before.
//! * `Ratio<T>` is the 2-tuple `[numer, denom]`, and **neither direction
//!   normalizes**. Decoding uses `Ratio::new_raw`, so `[2,4]` really decodes
//!   to 2/4 and a negative denominator survives. A codec that reduced would
//!   rewrite stored evidence — and `Ratio`'s `PartialEq` compares by VALUE,
//!   so a round-trip equality assertion cannot see it.
//! * A zero denominator is REJECTED, in both the `BigInt` and the `i64` ratio.

use num_bigint::{BigInt, BigUint, Sign};
use num_rational::Rational64;
use serde::de::{Error as DeError, SeqAccess, Unexpected, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

/// Wording of the sign rejection, kept identical to `num-bigint`'s.
const SIGN_EXPECTED: &str = "a sign of -1, 0, or 1";

/// Wording of the limb-sequence type error, kept identical to the
/// `expecting` string on `num-bigint`'s own `U32Visitor`. A plain
/// `Vec<u32>` would say "a sequence" instead, which is a different message
/// for the same malformed artifact.
const LIMBS_EXPECTED: &str = "a sequence of unsigned 32-bit numbers";

/// Wording of the zero-denominator rejection, kept identical to
/// `num-rational`'s.
const NONZERO_DENOM_EXPECTED: &str = "a ratio with non-zero denominator";

/// `Sign` -> the bare `i8` that goes on the wire.
fn sign_to_i8(sign: Sign) -> i8 {
    match sign {
        Sign::Minus => -1,
        Sign::NoSign => 0,
        Sign::Plus => 1,
    }
}

/// The wire `i8` -> `Sign`, as its OWN deserialize step.
///
/// This is a named type, not an `i8` field validated after the fact, because
/// the incumbent's `Sign` is itself a `Deserialize` impl sitting at element 0
/// of the tuple. That placement is observable in two ways, and a codec that
/// reads `(i8, Vec<u32>)` and *then* checks the sign gets both wrong:
///
/// * **Which fault is reported.** For `[2, [-1]]` — a bad sign AND a bad limb
///   — the incumbent reports the SIGN, because it never reaches the limbs.
///   Validating afterwards reports the limb instead.
/// * **The position suffix.** An error raised inside element 0's deserialize
///   is decorated by `serde_json` with `at line 1 column N`; one raised after
///   the whole tuple has been read carries no position at all.
///
/// Anything outside `{-1, 0, 1}` is rejected, not clamped: a clamp would
/// silently reinterpret a corrupted artifact.
struct WireSign(Sign);

impl<'de> Deserialize<'de> for WireSign {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match i8::deserialize(deserializer)? {
            -1 => Ok(Self(Sign::Minus)),
            0 => Ok(Self(Sign::NoSign)),
            1 => Ok(Self(Sign::Plus)),
            other => Err(D::Error::invalid_value(
                Unexpected::Signed(other.into()),
                &SIGN_EXPECTED,
            )),
        }
    }
}

/// The wire limb sequence, mirroring `num-bigint`'s own `U32Visitor` rather
/// than deferring to `Vec<u32>`.
///
/// The visitor is what supplies the `expecting` string in a type-error
/// message, so `Vec<u32>` would report `expected a sequence` where the
/// incumbent reports `expected a sequence of unsigned 32-bit numbers`.
/// Elements are still read one at a time and in order, so a malformed limb
/// is reported at exactly the position the incumbent reports it.
struct WireLimbs(Vec<u32>);

/// Cap the pre-allocation a hostile `size_hint` can request, as `num-bigint`
/// does. Inert for JSON (which cannot hint a sequence length) but this codec
/// must not become the one place a self-describing format can force a large
/// allocation from a small document. Applied with `.min` directly at the
/// allocation site so the bound is checkable there.
const MAX_PREALLOC_BYTES: usize = 1024 * 1024;
const MAX_PREALLOC_LIMBS: usize = MAX_PREALLOC_BYTES / size_of::<u32>();

struct LimbVisitor;

impl<'de> Visitor<'de> for LimbVisitor {
    type Value = WireLimbs;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(LIMBS_EXPECTED)
    }

    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<Self::Value, S::Error> {
        let mut data = Vec::with_capacity(seq.size_hint().unwrap_or(0).min(MAX_PREALLOC_LIMBS));
        while let Some(value) = seq.next_element::<u32>()? {
            data.push(value);
        }
        Ok(WireLimbs(data))
    }
}

impl<'de> Deserialize<'de> for WireLimbs {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(LimbVisitor)
    }
}

/// Owning decode half of the `BigInt` wire form.
///
/// A named type rather than an inline `(i8, Vec<u32>)` so that nesting it in
/// a ratio preserves the incumbent's *streaming* error order: a malformed
/// numerator is reported while the numerator is being read, before the
/// denominator is looked at.
struct WireBigInt(BigInt);

/// Borrowing encode half of the `BigInt` wire form.
struct WireBigIntRef<'a>(&'a BigInt);

impl Serialize for WireBigIntRef<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // `to_u32_digits()` IS the recipe — see the module docs on trailing
        // high-word suppression. Do not open-code a limb split here.
        (
            sign_to_i8(self.0.sign()),
            self.0.magnitude().to_u32_digits(),
        )
            .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for WireBigInt {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Element order matters: the sign validates itself at element 0, so a
        // malformed sign is reported before the limbs are read. See `WireSign`.
        let (sign, limbs) = <(WireSign, WireLimbs)>::deserialize(deserializer)?;
        // `from_biguint` + `from_slice` together reproduce the incumbent's
        // normalization: NoSign clears the limbs, an empty magnitude demotes
        // the sign, and trailing zero limbs are trimmed.
        Ok(Self(BigInt::from_biguint(
            sign.0,
            BigUint::from_slice(&limbs.0),
        )))
    }
}

/// Owning decode half of the `Ratio<i64>` wire form.
struct WireRational64(Rational64);

/// Borrowing encode half of the `Ratio<i64>` wire form.
struct WireRational64Ref<'a>(&'a Rational64);

impl Serialize for WireRational64Ref<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (*self.0.numer(), *self.0.denom()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for WireRational64 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (numer, denom) = <(i64, i64)>::deserialize(deserializer)?;
        if denom == 0 {
            return Err(D::Error::invalid_value(
                Unexpected::Signed(0),
                &NONZERO_DENOM_EXPECTED,
            ));
        }
        // `new_raw`, NOT `new`: the incumbent does not reduce, and reducing
        // would rewrite stored evidence invisibly to a value-based `==`.
        Ok(Self(Rational64::new_raw(numer, denom)))
    }
}

/// `#[serde(with = "…")]` codec for [`num_bigint::BigInt`].
///
/// Wire form: `[sign, limbs]` — see the module docs.
pub mod bigint {
    use super::{WireBigInt, WireBigIntRef};
    use num_bigint::BigInt;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Encode a `BigInt` as `[sign, base-2^32 limbs]`.
    pub fn serialize<S: Serializer>(value: &BigInt, serializer: S) -> Result<S::Ok, S::Error> {
        WireBigIntRef(value).serialize(serializer)
    }

    /// Decode a `BigInt` from `[sign, base-2^32 limbs]`, normalizing
    /// non-canonical input exactly as `BigInt::from_biguint` does.
    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<BigInt, D::Error> {
        WireBigInt::deserialize(deserializer).map(|wire| wire.0)
    }
}

/// `#[serde(with = "…")]` codec for [`num_rational::BigRational`].
///
/// Wire form: `[numer, denom]`, each a [`bigint`] pair. Neither direction
/// normalizes; a zero denominator is rejected.
pub mod bigrational {
    use super::{DeError, WireBigInt, WireBigIntRef, NONZERO_DENOM_EXPECTED};
    use num_rational::BigRational;
    use num_traits::Zero;
    use serde::de::Unexpected;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Encode a `BigRational` as `[numer, denom]`.
    pub fn serialize<S: Serializer>(value: &BigRational, serializer: S) -> Result<S::Ok, S::Error> {
        (WireBigIntRef(value.numer()), WireBigIntRef(value.denom())).serialize(serializer)
    }

    /// Decode a `BigRational` from `[numer, denom]` without reducing.
    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<BigRational, D::Error> {
        let (numer, denom) = <(WireBigInt, WireBigInt)>::deserialize(deserializer)?;
        let (numer, denom) = (numer.0, denom.0);
        if denom.is_zero() {
            return Err(D::Error::invalid_value(
                Unexpected::Signed(0),
                &NONZERO_DENOM_EXPECTED,
            ));
        }
        // `new_raw`, NOT `new` — see the note in `WireRational64`.
        Ok(BigRational::new_raw(numer, denom))
    }
}

/// `#[serde(with = "…")]` codec for a single [`num_rational::Rational64`].
///
/// Wire form: `[numer, denom]` as plain `i64`s. This is a genuinely separate
/// codec from [`bigint`] — `Ratio<i64>` holds no bignum at all.
pub mod rational64 {
    use super::{WireRational64, WireRational64Ref};
    use num_rational::Rational64;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Encode a `Rational64` as `[numer, denom]`.
    pub fn serialize<S: Serializer>(value: &Rational64, serializer: S) -> Result<S::Ok, S::Error> {
        WireRational64Ref(value).serialize(serializer)
    }

    /// Decode a `Rational64` from `[numer, denom]` without reducing.
    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Rational64, D::Error> {
        WireRational64::deserialize(deserializer).map(|wire| wire.0)
    }
}

/// `#[serde(with = "…")]` codec for a `Vec<Rational64>`.
///
/// The sequence adapter over [`rational64`]. `#[serde(with)]` binds to a
/// FIELD, and the field this exists for is
/// [`crate::proof::FarkasAnnotation::coefficients`], whose element type loses
/// its own `Serialize` when the `num-rational/serde` feature is dropped.
pub mod rational64_vec {
    use super::{WireRational64, WireRational64Ref};
    use num_rational::Rational64;
    use serde::ser::SerializeSeq;
    use serde::{Deserialize, Deserializer, Serializer};

    /// Encode as a sequence of `[numer, denom]` pairs.
    pub fn serialize<S: Serializer>(
        value: &[Rational64],
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        // `collect_seq` expanded by hand: a slice iterator's length hint is
        // exact, so this emits the same bytes with a locally provable bound.
        let mut seq = serializer.serialize_seq(Some(value.len()))?;
        for item in value {
            seq.serialize_element(&WireRational64Ref(item))?;
        }
        seq.end()
    }

    /// Decode a sequence of `[numer, denom]` pairs without reducing any of
    /// them.
    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<Rational64>, D::Error> {
        Vec::<WireRational64>::deserialize(deserializer)
            .map(|wires| wires.into_iter().map(|wire| wire.0).collect())
    }
}
