// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Wire shape only. Original IDs, literal namespace and proof truth can ONLY
/// be established by source reconstruction and independent DAG replay.
pub(super) fn validate(
    payload: &RetainedBvRefutation,
    control: &mut Control<'_>,
) -> Result<(), WireError> {
    control.charge(1)?;
    if payload.version != VERSION || payload.rows.is_empty() {
        return control.fail(WireError::InvalidPayload("version or empty rows"));
    }
    let mut previous = 0;
    for row in &payload.rows {
        control.charge(1)?;
        if row.id <= previous {
            return control.fail(WireError::InvalidPayload("row order"));
        }
        previous = row.id;
        for &hint in &row.hints {
            control.charge(1)?;
            if hint == 0 || hint >= row.id {
                return control.fail(WireError::InvalidPayload("zero or forward hint"));
            }
        }
    }
    match payload.rows.last() {
        Some(row) if row.id == payload.empty_clause_id && row.literals.is_empty() => Ok(()),
        _ => control.fail(WireError::InvalidPayload("terminal row")),
    }
}
