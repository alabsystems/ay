// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use fields::{Field, Key};

pub(super) struct Root<'a, 'b, 'p>(pub(super) Shared<'a, 'b, 'p>);

impl<'de> DeserializeSeed<'de> for Root<'_, '_, '_> {
    type Value = RetainedBvRefutation;
    fn deserialize<D: serde::Deserializer<'de>>(self, de: D) -> Result<Self::Value, D::Error> {
        de.deserialize_map(self)
    }
}

impl<'de> Visitor<'de> for Root<'_, '_, '_> {
    type Value = RetainedBvRefutation;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a retained refutation object")
    }
    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let (mut version, mut rows, mut terminal) = (None, None, None);
        while let Some(field) = map.next_key_seed(Key(self.0))? {
            match field {
                Field::Version if version.is_none() => {
                    let value = map.next_value_seed(Number(self.0))?;
                    if value != u64::from(VERSION) {
                        return Err(invalid(self.0, "version"));
                    }
                    version = Some(VERSION);
                }
                Field::Rows if rows.is_none() => {
                    rows = Some(map.next_value_seed(sequences::Rows(self.0))?)
                }
                Field::Terminal if terminal.is_none() => {
                    terminal = Some(map.next_value_seed(Number(self.0))?)
                }
                _ => return Err(invalid(self.0, "unknown or duplicate root field")),
            }
        }
        match (version, rows, terminal) {
            (Some(version), Some(rows), Some(empty_clause_id)) => Ok(RetainedBvRefutation {
                version,
                rows,
                empty_clause_id,
            }),
            _ => Err(invalid(self.0, "missing root field")),
        }
    }
}

pub(super) struct Row<'a, 'b, 'p>(pub(super) Shared<'a, 'b, 'p>);

impl<'de> Visitor<'de> for Row<'_, '_, '_> {
    type Value = RetainedRupRow;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a retained RUP row object")
    }
    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let (mut id, mut literals, mut hints) = (None, None, None);
        while let Some(field) = map.next_key_seed(Key(self.0))? {
            match field {
                Field::Id if id.is_none() => id = Some(map.next_value_seed(Number(self.0))?),
                Field::Literals if literals.is_none() => {
                    literals = Some(map.next_value_seed(sequences::numbers::<u32>(self.0))?)
                }
                Field::Hints if hints.is_none() => {
                    hints = Some(map.next_value_seed(sequences::numbers::<u64>(self.0))?)
                }
                _ => return Err(invalid(self.0, "unknown or duplicate row field")),
            }
        }
        match (id, literals, hints) {
            (Some(id), Some(literals), Some(hints)) => Ok(RetainedRupRow {
                id,
                literals,
                hints,
            }),
            _ => Err(invalid(self.0, "missing row field")),
        }
    }
}
