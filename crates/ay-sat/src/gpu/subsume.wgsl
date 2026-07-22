// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// GPU pairwise subsumption checking for SAT inprocessing.
// Reference: ParaFROST GPU SAT solver (Osama & Wijs, SAT 2021).
//
// Each thread checks one (i, j) clause pair for subsumption:
// clause_i subsumes clause_j iff every literal in clause_i also appears
// in clause_j (subset relationship).
//
// Literal encoding: u32 where positive = var*2, negative = var*2+1.

@group(0) @binding(0) var<storage, read> literals_buf: array<u32>;
@group(0) @binding(1) var<storage, read> offsets_buf: array<u32>;
@group(0) @binding(2) var<storage, read> params_buf: array<u32>;
@group(0) @binding(3) var<storage, read_write> results_buf: array<atomic<u32>>;

@compute @workgroup_size(256)
fn subsume_check(@builtin(global_invocation_id) gid: vec3<u32>) {
    let num_clauses = params_buf[0];
    let workgroups_x = params_buf[1];
    let pair_idx = gid.x + gid.y * workgroups_x * 256u;
    let total_pairs = num_clauses * num_clauses;

    // Out-of-bounds guard.
    if pair_idx >= total_pairs {
        return;
    }

    let i = pair_idx / num_clauses;
    let j = pair_idx % num_clauses;

    // Self-subsumption is trivial and not useful.
    if i == j {
        return;
    }

    // Clause i boundaries.
    let i_start = offsets_buf[i];
    let i_end = offsets_buf[i + 1u];
    let i_len = i_end - i_start;

    // Clause j boundaries.
    let j_start = offsets_buf[j];
    let j_end = offsets_buf[j + 1u];
    let j_len = j_end - j_start;

    // Clause i can only subsume clause j if |i| <= |j|.
    if i_len > j_len {
        return;
    }

    // Check if every literal in clause i appears in clause j.
    var all_found: bool = true;
    for (var ki = i_start; ki < i_end; ki = ki + 1u) {
        let lit_i = literals_buf[ki];
        var found: bool = false;
        for (var kj = j_start; kj < j_end; kj = kj + 1u) {
            if literals_buf[kj] == lit_i {
                found = true;
                break;
            }
        }
        if !found {
            all_found = false;
            break;
        }
    }

    if all_found {
        let word_idx = pair_idx / 32u;
        let bit_idx = pair_idx % 32u;
        let mask = 1u << bit_idx;
        atomicOr(&results_buf[word_idx], mask);
    }
}
