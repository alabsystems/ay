// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Borrow-only field for an outer DTO AFTER admit_outer_json. Missing and
/// present-empty differ; null is refused. Borrowing confers no admission token.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(in crate::bundle) enum BorrowedField<'a> {
    #[default]
    Absent,
    Present(&'a [u8]),
}

impl BorrowedField<'_> {
    pub(super) fn is_absent(&self) -> bool {
        matches!(self, Self::Absent)
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for BorrowedField<'a> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let raw = <&'de RawValue>::deserialize(deserializer)?;
        if !raw.get().starts_with('[') {
            return Err(de::Error::custom("retained field must be an array"));
        }
        Ok(Self::Present(raw.get().as_bytes()))
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Entry<'a> {
    pub(super) step: u32,
    #[serde(borrow)]
    pub(super) payload: &'a RawValue,
}

pub(super) struct Inventory<'a> {
    pub(super) entries: [Option<Entry<'a>>; MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF],
    pub(super) len: usize,
}

impl Inventory<'_> {
    pub(super) fn empty() -> Self {
        Self {
            entries: [None; MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF],
            len: 0,
        }
    }
}

impl Serialize for Inventory<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        let mut seq = serializer.serialize_seq(Some(self.len))?;
        for entry in self.entries.iter().take(self.len) {
            let entry = entry
                .as_ref()
                .ok_or_else(|| serde::ser::Error::custom("missing retained entry"))?;
            seq.serialize_element(entry)?;
        }
        seq.end()
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for Inventory<'a> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Entries;
        impl<'de> de::Visitor<'de> for Entries {
            type Value = Inventory<'de>;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("at most eight retained entries")
            }
            fn visit_seq<A: de::SeqAccess<'de>>(
                self,
                mut sequence: A,
            ) -> Result<Self::Value, A::Error> {
                let mut out = Inventory::empty();
                for index in 0..MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
                    match sequence.next_element()? {
                        Some(entry) => {
                            out.entries[index] = Some(entry);
                            out.len += 1;
                        }
                        None => return Ok(out),
                    }
                }
                if sequence.next_element_seed(RefuseExtra)?.is_some() {
                    return Err(de::Error::custom("too many retained entries"));
                }
                Ok(out)
            }
        }
        deserializer.deserialize_seq(Entries)
    }
}

struct RefuseExtra;
impl<'de> de::DeserializeSeed<'de> for RefuseExtra {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, _deserializer: D) -> Result<(), D::Error> {
        Err(de::Error::custom("too many retained entries"))
    }
}
