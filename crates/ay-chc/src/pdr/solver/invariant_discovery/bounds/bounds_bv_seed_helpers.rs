// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;

pub(super) const MAX_BLOCKED_STATE_BV_CONSTANTS_PER_VAR: usize = 4;

pub(super) fn collect_bv_constants(expr: &ChcExpr, constants: &mut FxHashSet<(u128, u32)>) {
    match expr {
        ChcExpr::BitVec(value, width) => {
            constants.insert((*value, *width));
        }
        ChcExpr::Op(_, args) => {
            for arg in args {
                collect_bv_constants(arg, constants);
            }
        }
        _ => {}
    }
}

pub(super) fn bitvec_bits_from_seed_value(value: i128, width: u32) -> u128 {
    let mask = if width >= 128 {
        u128::MAX
    } else if width == 0 {
        0
    } else {
        (1u128 << width) - 1
    };
    (value as u128) & mask
}

pub(super) fn push_bv_lower_bound_candidate(
    candidates: &mut Vec<ChcExpr>,
    seen: &mut FxHashSet<String>,
    var: &ChcVar,
    value: u128,
) {
    let ChcSort::BitVec(width) = var.sort else {
        return;
    };
    let lower_bound = ChcExpr::Op(
        ChcOp::BvSLe,
        vec![
            Arc::new(ChcExpr::BitVec(value, width)),
            Arc::new(ChcExpr::var(var.clone())),
        ],
    );
    let key = format!("{lower_bound}");
    if seen.insert(key) {
        candidates.push(lower_bound);
    }
}
