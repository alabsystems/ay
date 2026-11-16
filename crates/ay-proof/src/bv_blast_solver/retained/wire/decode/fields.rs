// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Field {
    Version,
    Rows,
    Terminal,
    Id,
    Literals,
    Hints,
}

pub(super) struct Key<'a, 'b, 'p>(pub(super) Shared<'a, 'b, 'p>);

impl<'de> DeserializeSeed<'de> for Key<'_, '_, '_> {
    type Value = Field;
    fn deserialize<D: serde::Deserializer<'de>>(self, de: D) -> Result<Field, D::Error> {
        de_result(self.0.borrow_mut().charge(1))?;
        de.deserialize_identifier(self)
    }
}

impl Visitor<'_> for Key<'_, '_, '_> {
    type Value = Field;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a retained row field")
    }
    fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Field, E> {
        match value {
            "version" => Ok(Field::Version),
            "rows" => Ok(Field::Rows),
            "empty_clause_id" => Ok(Field::Terminal),
            "id" => Ok(Field::Id),
            "literals" => Ok(Field::Literals),
            "hints" => Ok(Field::Hints),
            _ => Err(invalid(self.0, "unknown field")),
        }
    }
}
