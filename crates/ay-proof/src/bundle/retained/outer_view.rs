// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed envelope only: no legacy term, sort, step or declaration is decoded.
//! The caller retains the input and owns its admission. `read` uses the existing
//! control, never a renewed grant or deadline. Its borrowed serde parse is an
//! opaque span bounded by the admitted input length, not hard stop latency.
//! The operation owner must run the existing post-cleanup `Control::finish`.
//! Nothing here authenticates a proof or establishes nested legacy validity.

use super::*;

mod admission;

/// Keep the actual wire schema and retained inventory together. In particular,
/// this is never a v6 document normalized into a payload-free legacy snapshot.
#[derive(Debug)]
pub(in crate::bundle) struct OuterView<'a> {
    pub(in crate::bundle) encoding: BundleEncoding,
    pub(in crate::bundle) fields: RawFields<'a>,
}

/// Legacy Option<TermId> fields accept omission as well as explicit null.
/// Preserve that distinction without allocating or inventing a raw null value.
#[derive(Clone, Copy, Debug, Default)]
pub(in crate::bundle) enum NullableTerm<'a> {
    #[default]
    Absent,
    Present(&'a RawValue),
}

impl<'de: 'a, 'a> Deserialize<'de> for NullableTerm<'a> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        <&'de RawValue>::deserialize(deserializer).map(Self::Present)
    }
}

/// These references point into the admitted input; escaped keys need only the
/// bounded parser scratch, not owning legacy values. Do not use unconstrained
/// serde on this type instead of the controlled `read` entry point.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in crate::bundle) struct RawFields<'a> {
    #[serde(borrow)]
    pub(in crate::bundle) schema: &'a RawValue,
    #[serde(borrow)]
    pub(in crate::bundle) steps: &'a RawValue,
    #[serde(borrow)]
    pub(in crate::bundle) term_entries: &'a RawValue,
    #[serde(default, borrow)]
    pub(in crate::bundle) true_term: NullableTerm<'a>,
    #[serde(default, borrow)]
    pub(in crate::bundle) false_term: NullableTerm<'a>,
    #[serde(borrow)]
    pub(in crate::bundle) var_counter: &'a RawValue,
    #[serde(borrow)]
    pub(in crate::bundle) obligation_assertions: &'a RawValue,
    #[serde(borrow)]
    pub(in crate::bundle) datatype_declarations: &'a RawValue,
    #[serde(borrow)]
    pub(in crate::bundle) constructor_selectors: &'a RawValue,
    #[serde(borrow)]
    pub(in crate::bundle) datatype_member_signatures: &'a RawValue,
    #[serde(borrow)]
    pub(in crate::bundle) declared_function_identities: &'a RawValue,
    #[serde(default, borrow)]
    pub(in crate::bundle) retained: BorrowedField<'a>,
}

pub(super) fn read<'a>(
    bytes: &'a [u8],
    maximum_bytes: usize,
    control: &mut Control<'_>,
) -> Result<OuterView<'a>, TransportError> {
    control.charge(0, 0)?;
    control.cap("outer JSON bytes", bytes.len(), maximum_bytes)?;
    // Depth-only admission precedes serde, but cannot itself bound the scratch
    // used to unescape top-level keys. The second pass admits those tokens too.
    lexical::outer(bytes, control)?;
    admission::metadata(bytes, control)?;
    control.charge(0, 0)?;
    let fields = match serde_json::from_slice::<RawFields<'a>>(bytes) {
        Ok(fields) => fields,
        Err(error) => {
            drop(error); // Never format attacker-controlled serde diagnostics.
            return control.fail(TransportError::InvalidJson);
        }
    };
    // The slice deserializer and its scratch have already been dropped.
    control.charge(0, 0)?;
    envelope_types(&fields, control)?;
    let encoding = schema(fields.schema, control)?;
    let schema_name = match encoding {
        BundleEncoding::SnapshotV5 => SNAPSHOT_SCHEMA,
        BundleEncoding::RetainedV6 => RETAINED_SCHEMA,
    };
    presence(schema_name, !fields.retained.is_absent())
        .map_err(TransportError::from)
        .or_else(|error| control.fail(error))?;
    control.charge(0, 0)?;
    Ok(OuterView { encoding, fields })
}

fn envelope_types(fields: &RawFields<'_>, control: &mut Control<'_>) -> Result<(), TransportError> {
    for array in [
        fields.steps,
        fields.term_entries,
        fields.obligation_assertions,
        fields.datatype_declarations,
        fields.constructor_selectors,
        fields.datatype_member_signatures,
        fields.declared_function_identities,
    ] {
        control.charge(1, 0)?;
        if !array.get().starts_with('[') {
            return control.fail(TransportError::InvalidShape(
                "legacy field must be an array",
            ));
        }
    }
    // Pinned serde's missing_field<Option<_>> accepts omission as None. These
    // two optional fields therefore admit both omission and null; all eight
    // other legacy keys remain required. Do not collapse their raw presence.
    for term in [fields.true_term, fields.false_term] {
        match term {
            NullableTerm::Present(raw) if raw.get() != "null" => unsigned(raw, control)?,
            NullableTerm::Absent | NullableTerm::Present(_) => control.charge(1, 0)?,
        }
    }
    unsigned(fields.var_counter, control)
}

fn unsigned(raw: &RawValue, control: &mut Control<'_>) -> Result<(), TransportError> {
    let bytes = raw.get().as_bytes();
    control.charge(1, 0)?;
    if bytes.is_empty() || bytes.len() > 10 {
        return control.fail(TransportError::InvalidShape("legacy field must be u32"));
    }
    let mut value = 0_u32;
    for &byte in bytes {
        control.charge(1, 0)?;
        if !byte.is_ascii_digit() {
            return control.fail(TransportError::InvalidShape("legacy field must be u32"));
        }
        value = value
            .checked_mul(10)
            .and_then(|value| value.checked_add(u32::from(byte - b'0')))
            .ok_or(TransportError::InvalidShape("legacy field must be u32"))
            .or_else(|error| control.fail(error))?;
    }
    Ok(())
}

struct Schema(BundleEncoding);

impl<'de> Deserialize<'de> for Schema {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Name;
        impl de::Visitor<'_> for Name {
            type Value = Schema;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a supported proof bundle schema")
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<Schema, E> {
                match value {
                    SNAPSHOT_SCHEMA => Ok(Schema(BundleEncoding::SnapshotV5)),
                    RETAINED_SCHEMA => Ok(Schema(BundleEncoding::RetainedV6)),
                    _ => Err(E::custom("unsupported proof bundle schema")),
                }
            }
        }
        deserializer.deserialize_str(Name)
    }
}

fn schema(raw: &RawValue, control: &mut Control<'_>) -> Result<BundleEncoding, TransportError> {
    control.charge(1, 0)?;
    if !raw.get().starts_with('"') {
        return control.fail(TransportError::InvalidShape("schema must be a string"));
    }
    let encoding = match serde_json::from_str::<Schema>(raw.get()) {
        Ok(Schema(encoding)) => encoding,
        Err(error) => {
            drop(error);
            return control.fail(TransportError::Presence(PresenceError::UnsupportedSchema));
        }
    };
    control.charge(0, 0)?;
    Ok(encoding)
}

#[cfg(test)]
mod tests;
