// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// GPU compute shader for BVE batch resolvent generation.
//
// Each thread handles one (pos_clause, neg_clause) pair. Resolution merges
// literals from both clauses, excludes the pivot variable, skips root-level
// assigned literals, and detects tautologies (both L and ~L present).
//
// Literal encoding: positive = 2*var, negative = 2*var + 1.
// Variable extraction: var = lit >> 1.
// Polarity: sign = lit & 1 (0 = positive, 1 = negative).

// Parameters buffer layout:
// [0] = pivot_var (the variable being eliminated)
// [1] = num_pos (number of positive-polarity clauses)
// [2] = num_neg (number of negative-polarity clauses)
// [3] = max_resolvent_len (max literals per resolvent slot in output)
// [4] = num_vars (total number of variables, for mark array bounds)

@group(0) @binding(0) var<storage, read> clause_data: array<u32>;
// clause_meta: interleaved (start, len) pairs. clause_meta[2*id] = start,
// clause_meta[2*id + 1] = len.
@group(0) @binding(1) var<storage, read> clause_meta: array<u32>;
@group(0) @binding(2) var<storage, read> pos_indices: array<u32>;
@group(0) @binding(3) var<storage, read> neg_indices: array<u32>;
@group(0) @binding(4) var<storage, read> params: array<u32>;
@group(0) @binding(5) var<storage, read> vals: array<u32>;
// results: each pair gets a stride of (max_resolvent_len + 2) u32s.
// results[pair_id * stride + 0] = resolvent length (0 if tautological/satisfied)
// results[pair_id * stride + 1] = tautology flag (1 = skip, 0 = valid)
// results[pair_id * stride + 2..] = literal values
@group(0) @binding(6) var<storage, read_write> results: array<u32>;

// 7 bindings total, well within the 8-binding default limit.

@compute @workgroup_size(64, 1, 1)
fn resolve_pairs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let pair_id = gid.x;
    let pivot_var = params[0];
    let num_pos = params[1];
    let num_neg = params[2];
    let max_res_len = params[3];
    let num_pairs = num_pos * num_neg;

    // Out-of-bounds thread: nothing to do
    if pair_id >= num_pairs {
        return;
    }

    let pos_idx = pair_id / num_neg;
    let neg_idx = pair_id % num_neg;

    let pos_clause_id = pos_indices[pos_idx];
    let neg_clause_id = neg_indices[neg_idx];

    let pos_start = clause_meta[pos_clause_id * 2u];
    let pos_len = clause_meta[pos_clause_id * 2u + 1u];
    let neg_start = clause_meta[neg_clause_id * 2u];
    let neg_len = clause_meta[neg_clause_id * 2u + 1u];

    // Output stride: 2 (length + tautology flag) + max_resolvent_len (literals)
    let stride = max_res_len + 2u;
    let out_base = pair_id * stride;

    // Phase 1: Collect literals from positive clause (excluding pivot)
    // We use the output buffer itself as scratch, writing literals starting
    // at out_base + 2. We'll write the count and flag at the end.
    var res_count: u32 = 0u;
    var is_tautology: u32 = 0u;
    var parent_satisfied: u32 = 0u;

    // Process positive clause: add all non-pivot, unassigned literals
    for (var i: u32 = 0u; i < pos_len; i = i + 1u) {
        let lit = clause_data[pos_start + i];
        let var_id = lit >> 1u;

        // Skip pivot variable
        if var_id == pivot_var {
            continue;
        }

        // Check root-level assignment via vals array
        // vals uses literal-indexed encoding: vals[lit] where
        // positive lit = 2*var, negative lit = 2*var + 1
        let val = vals[lit];
        if val == 1u {
            // Literal is true at root level: parent clause is satisfied
            parent_satisfied = 1u;
            break;
        }
        if val == 255u {
            // Literal is false at root level: skip (pruned)
            continue;
        }

        // Add literal to resolvent if we have room
        if res_count < max_res_len {
            results[out_base + 2u + res_count] = lit;
            res_count = res_count + 1u;
        }
    }

    if parent_satisfied == 0u {
        // Phase 2: Process negative clause literals
        // For tautology detection, we need to check each neg literal against
        // the positive literals already in the resolvent.
        for (var j: u32 = 0u; j < neg_len; j = j + 1u) {
            let lit = clause_data[neg_start + j];
            let var_id = lit >> 1u;

            // Skip pivot variable
            if var_id == pivot_var {
                continue;
            }

            // Check root-level assignment
            let val = vals[lit];
            if val == 1u {
                parent_satisfied = 1u;
                break;
            }
            if val == 255u {
                continue;
            }

            // Check for tautology and duplicates against existing resolvent
            var duplicate = false;
            for (var k: u32 = 0u; k < res_count; k = k + 1u) {
                let existing = results[out_base + 2u + k];
                let existing_var = existing >> 1u;
                if existing_var == var_id {
                    // Same variable: check if same or opposite polarity
                    if existing == lit {
                        // Duplicate literal: skip
                        duplicate = true;
                        break;
                    } else {
                        // Opposite polarity: tautology
                        is_tautology = 1u;
                        break;
                    }
                }
            }

            if is_tautology == 1u {
                break;
            }

            if !duplicate && res_count < max_res_len {
                results[out_base + 2u + res_count] = lit;
                res_count = res_count + 1u;
            }
        }
    }

    // Write output header
    if parent_satisfied == 1u || is_tautology == 1u {
        results[out_base] = 0u;
        results[out_base + 1u] = 1u; // tautology/satisfied flag
    } else {
        results[out_base] = res_count;
        results[out_base + 1u] = 0u; // valid resolvent
    }
}
