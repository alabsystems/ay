// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::transform::array_ghost_pairs::GhostPredSpec;
use crate::{ChcExpr, ChcSort, ChcVar};

fn byte_array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn two_array_spec() -> GhostPredSpec {
    GhostPredSpec {
        original_arity: 2,
        index_sorts: vec![ChcSort::BitVec(64); 2],
        array_positions: vec![0, 1],
    }
}

#[test]
fn partial_alignment_preserves_distinct_fresh_slots() {
    let array = byte_array();
    let body_spec = two_array_spec();
    let head_spec = two_array_spec();
    let shared = var("shared", array.clone());
    let body_args = vec![shared.clone(), var("body_only", array.clone())];
    let head_args = vec![var("head_only", array), shared];
    let fresh = vec![
        var("fresh_0", ChcSort::BitVec(64)),
        var("fresh_1", ChcSort::BitVec(64)),
    ];

    let tuple = super::aligned_body_ghost_indices(
        &body_spec,
        &body_args,
        &head_spec,
        &head_args,
        1,
        &fresh,
        &[],
    )
    .expect("one exact array and one fallback array remain alignable");
    assert_eq!(
        tuple,
        vec![fresh[1].clone(), fresh[0].clone()],
        "the exact permutation must reserve fresh_1 for the shared array"
    );
}

#[test]
fn renamed_shifted_store_array_retains_legacy_fresh_index() {
    let array = byte_array();
    let body_spec = GhostPredSpec {
        original_arity: 2,
        array_positions: vec![1],
        index_sorts: vec![ChcSort::BitVec(64)],
    };
    let head_spec = GhostPredSpec {
        original_arity: 2,
        array_positions: vec![0],
        index_sorts: vec![ChcSort::BitVec(64)],
    };
    let old_memory = var("old_memory", array.clone());
    let body_args = vec![var("count", ChcSort::BitVec(32)), old_memory.clone()];
    let head_args = vec![
        ChcExpr::store(old_memory, ChcExpr::BitVec(1, 64), ChcExpr::BitVec(0xff, 8)),
        var("count", ChcSort::BitVec(32)),
    ];
    let fresh = vec![var("fresh", ChcSort::BitVec(64))];

    assert_eq!(
        super::aligned_body_ghost_indices(
            &body_spec,
            &body_args,
            &head_spec,
            &head_args,
            1,
            &fresh,
            &[],
        ),
        Some(fresh),
    );
}
