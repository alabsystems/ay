// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unconditional aggregate bounds for datatype field-row scans.

use super::{
    OpaqueDtConstructionBudget, MAX_BOUNDED_NODE_WORK, MAX_OPAQUE_DT_COLLECTION_RAW_ARGS,
    MAX_OPAQUE_DT_WORK, MAX_ROUNDTRIP_SCHEMA_NODES,
};

pub(in crate::executor::model) const MAX_DT_FIELD_SCAN_FIELDS: usize = MAX_ROUNDTRIP_SCHEMA_NODES;
pub(in crate::executor::model) const MAX_DT_FIELD_SCAN_ROWS: usize =
    MAX_OPAQUE_DT_COLLECTION_RAW_ARGS;
pub(in crate::executor::model) const MAX_DT_FIELD_SCAN_COMPARISONS: usize =
    MAX_OPAQUE_DT_WORK / MAX_BOUNDED_NODE_WORK;

impl OpaqueDtConstructionBudget {
    /// Precharge a schema-field scan over retained selector applications and
    /// constructor argument rows before any nested loops or name comparisons.
    /// The comparison envelope applies even when no opaque term is present;
    /// only the additional per-node charge is conditional on that lane.
    pub(in crate::executor::model) fn charge_field_scans(
        &mut self,
        fields: usize,
        selectors: usize,
        constructor_rows: usize,
    ) -> bool {
        let Some(rows) = selectors.checked_add(constructor_rows) else {
            return self.fail();
        };
        if fields > MAX_DT_FIELD_SCAN_FIELDS || rows > MAX_DT_FIELD_SCAN_ROWS {
            return self.fail();
        }
        let Some(comparisons) = rows.checked_mul(fields) else {
            return self.fail();
        };
        let Some(remaining) = self.field_scan_remaining.checked_sub(comparisons) else {
            return self.fail();
        };
        let Some(scans) = comparisons.checked_mul(MAX_BOUNDED_NODE_WORK) else {
            return self.fail();
        };
        self.field_scan_remaining = remaining;
        self.charge(scans)
    }
}
