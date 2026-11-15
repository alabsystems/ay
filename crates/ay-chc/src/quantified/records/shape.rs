// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= MAX_NAME_BYTES
        && !super::super::source::theory_symbol(name)
        && !crate::parser::is_builtin_term_symbol(name)
        && !matches!(name, "!" | "match" | "par" | "lambda")
        && !name
            .bytes()
            .any(|byte| byte.is_ascii_control() || matches!(byte, b'|' | b'\\'))
}

fn scalar(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
    )
}

/// Bounded scalar/rank-one scalar-array fragment, checked without traversal.
/// Larger admitted sorts require a complete metadata-copy allowance.
pub(crate) fn field_sort(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Array(key, value) => {
            matches!(
                key.as_ref(),
                ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
            ) && scalar(value)
        }
        _ => scalar(sort),
    }
}

/// Old per-node copy allowances cover only this narrow shape. Admission of a
/// wide scalar/key does not make its limb-sized allowance disappear.
pub(crate) fn small_copy_sort(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Bool | ChcSort::BitVec(1..=64) => true,
        ChcSort::Array(key, value) => {
            matches!(key.as_ref(), ChcSort::BitVec(1..=64))
                && matches!(value.as_ref(), ChcSort::Bool | ChcSort::BitVec(1..=64))
        }
        _ => false,
    }
}

/// Bounded structural support, not an assertion that this record was declared.
#[cfg(test)]
pub(crate) fn supported_sort(sort: &ChcSort) -> bool {
    sort_bytes(sort).is_some()
}

/// Conservative complete metadata/name-copy and formatting allowance. Repeated
/// Arc DAG occurrences are charged independently; this is not unique-node cost.
/// Depth, occurrences, names, leaves and bytes are bounded before comparisons.
/// Callers aggregate this per use; it confers no registry/application authority.
pub(crate) fn sort_bytes(sort: &ChcSort) -> Option<usize> {
    let mut meter = super::scan::Meter::default();
    meter.sort(sort, 0).ok()?;
    Some(meter.bytes())
}
