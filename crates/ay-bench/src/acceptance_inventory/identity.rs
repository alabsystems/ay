// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! v4-v8 are frozen source contracts, not open-ended execution-report formats.
//!
//! Their complete canonical document identities bind every historical field,
//! source hash, unavailable input, archived grant, oracle and unqualified route.
//! These are independently derived from the Python-validated v4/v5 projections
//! and v6-v8 manifests, not from data claiming its own expected hash. A new source
//! contract needs a reviewed schema/identity update, not an in-place retagging.
//! Object order/whitespace do not matter; array order and every value do.
//! This stricter admission is metadata validation, never solver qualification.

use std::collections::BTreeMap;

use serde::ser::{SerializeMap as _, SerializeSeq as _};
use serde::{Serialize, Serializer};
use serde_json::Value;
use sha2::{Digest as _, Sha256};

use super::{
    INVENTORY_SCHEMA_V4, INVENTORY_SCHEMA_V5, INVENTORY_SCHEMA_V6, INVENTORY_SCHEMA_V7,
    INVENTORY_SCHEMA_V8,
};
use crate::{BenchError, Result};

pub(super) fn validate(value: &Value) -> Result<()> {
    let expected = match value.get("schema").and_then(Value::as_str) {
        Some(INVENTORY_SCHEMA_V4) => {
            "de2c4071a0e02ef55a1a9964d579fc9beb55a24caa5669e75dfbc151419c1c21"
        }
        Some(INVENTORY_SCHEMA_V5) => {
            "42049b4d54f2d107af3e961f9088432a77d6af33f30f29e21261bbc5c6e93269"
        }
        Some(INVENTORY_SCHEMA_V6) => {
            "34469b1c9a1663bb120f21214f7fe4367ac822d68e10b1a65192193e0689bb89"
        }
        Some(INVENTORY_SCHEMA_V7) => {
            "6e975fb0ddf2c34dbbc4482971a6a05fa84f854788d9affaef9be37b89005fe5"
        }
        Some(INVENTORY_SCHEMA_V8) => {
            "ee382ac6ea8d10bf8a20123b66a5d4c2675ed18c5ae29a26871ddcd3cc5b144f"
        }
        // Historical v1-v3 retain their existing structural admission.
        _ => return Ok(()),
    };
    let bytes = serde_json::to_vec(&Canonical(value))?;
    if format!("{:x}", Sha256::digest(&bytes)) != expected {
        return Err(BenchError::msg(
            "frozen inventory source identity changed: historical values, original obligations and unresolved evidence must be preserved",
        ));
    }
    Ok(())
}

// Explicit ordering avoids dependence on serde_json's preserve_order feature.
// Strings use UTF-8 JSON encoding; all currently frozen source text is ASCII.
struct Canonical<'a>(&'a Value);

impl Serialize for Canonical<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        match self.0 {
            Value::Object(fields) => {
                let ordered: BTreeMap<_, _> = fields.iter().collect();
                let mut map = serializer.serialize_map(Some(ordered.len()))?;
                for (key, value) in ordered {
                    map.serialize_entry(key, &Canonical(value))?;
                }
                map.end()
            }
            Value::Array(values) => {
                let mut sequence = serializer.serialize_seq(Some(values.len()))?;
                for value in values {
                    sequence.serialize_element(&Canonical(value))?;
                }
                sequence.end()
            }
            scalar => scalar.serialize(serializer),
        }
    }
}
