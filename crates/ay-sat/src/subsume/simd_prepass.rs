// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SIMD-accelerated batch subsumption prepass.
//!
//! Packs the active clause database into a cache-friendly flat arena,
//! generates candidate subsumption pairs (shorter-or-equal vs longer),
//! and uses NEON/SSE2 SIMD instructions for parallel literal matching.
//!
//! This runs as a bulk pre-pass before the fine-grained CaDiCaL-style
//! one-watch forward subsumption, analogous to the GPU prepass (#8096).
//! The SIMD pass handles the embarrassingly-parallel pairwise case;
//! the CPU pass then handles incremental dirty-variable-guided checking.
//!
//! Only active when the `jit` feature is enabled.

use ay_jit::simd_inprocess::SimdClauseScanner;

use crate::clause_arena::ClauseArena;

/// Minimum clause count before SIMD prepass is worthwhile.
/// Below this threshold, the arena packing overhead exceeds the SIMD benefit.
const SIMD_SUBSUME_THRESHOLD: usize = 500;

/// Maximum clause length for SIMD prepass candidates.
/// Longer clauses are unlikely to participate in subsumption.
const SIMD_SUBSUME_MAX_LEN: usize = 20;

/// Maximum number of pairs to check in one SIMD prepass.
/// Caps the quadratic blowup for large clause databases.
const SIMD_SUBSUME_MAX_PAIRS: usize = 200_000;

/// Result of the SIMD subsumption prepass.
pub(crate) struct SimdSubsumeResult {
    /// (subsumed_arena_idx, subsumer_arena_idx) pairs.
    pub pairs: Vec<(usize, usize)>,
    /// Number of clauses packed into the SIMD arena.
    pub clauses_packed: usize,
    /// Number of pairs checked.
    pub pairs_checked: usize,
}

/// Run SIMD-accelerated batch subsumption prepass.
///
/// Collects active clauses from the arena, packs them into a
/// `SimdClauseScanner`, generates candidate pairs (sorted by size),
/// and returns detected subsumption pairs.
///
/// `vals`: literal value array. Non-zero = fixed at level 0 (skip clause).
pub(crate) fn simd_subsume_prepass(clauses: &ClauseArena, vals: &[i8]) -> SimdSubsumeResult {
    // Collect active clauses suitable for SIMD subsumption.
    let mut clause_data: Vec<(usize, usize)> = Vec::new(); // (arena_idx, len)

    for idx in clauses.indices() {
        if clauses.is_dead(idx) || clauses.is_empty_clause(idx) {
            continue;
        }
        let lits = clauses.literals(idx);
        if lits.len() < 2 || lits.len() > SIMD_SUBSUME_MAX_LEN {
            continue;
        }
        // Skip clauses with level-0 fixed literals.
        let has_fixed = lits.iter().any(|lit| {
            let li = lit.index();
            li < vals.len() && vals[li] != 0
        });
        if has_fixed {
            continue;
        }
        clause_data.push((idx, lits.len()));
    }

    if clause_data.len() < SIMD_SUBSUME_THRESHOLD {
        return SimdSubsumeResult {
            pairs: Vec::new(),
            clauses_packed: clause_data.len(),
            pairs_checked: 0,
        };
    }

    // Sort by clause length ascending for pair generation.
    clause_data.sort_unstable_by_key(|&(_, len)| len);

    // Pack clauses into SIMD scanner.
    let total_lits: usize = clause_data.iter().map(|&(_, len)| len).sum();
    let mut scanner = SimdClauseScanner::with_capacity(clause_data.len(), total_lits);
    let mut arena_indices: Vec<usize> = Vec::with_capacity(clause_data.len());

    for &(idx, _) in &clause_data {
        let lits = clauses.literals(idx);
        let raw_lits: Vec<i32> = lits.iter().map(|lit| lit.0 as i32).collect();
        scanner.push(&raw_lits);
        arena_indices.push(idx);
    }

    // Generate candidate pairs: for each clause A, check it against
    // larger-or-equal clauses B. A can subsume B only if |A| <= |B|.
    // Use a sliding window to limit quadratic blowup.
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let n = scanner.len();

    // Group clauses by length for efficient pair generation.
    // For each size group, check against all larger groups.
    let mut size_groups: Vec<(usize, usize, usize)> = Vec::new(); // (len, start, end)
    let mut group_start = 0;
    while group_start < n {
        let group_len = clause_data[group_start].1;
        let mut group_end = group_start + 1;
        while group_end < n && clause_data[group_end].1 == group_len {
            group_end += 1;
        }
        size_groups.push((group_len, group_start, group_end));
        group_start = group_end;
    }

    // Generate pairs: each clause in a smaller group against each clause
    // in a larger-or-equal group. Cap at SIMD_SUBSUME_MAX_PAIRS.
    'pair_gen: for (gi, &(_, a_start, a_end)) in size_groups.iter().enumerate() {
        for &(_, b_start, b_end) in &size_groups[gi..] {
            for a in a_start..a_end {
                for b in b_start..b_end {
                    if a == b {
                        continue;
                    }
                    pairs.push((a, b));
                    if pairs.len() >= SIMD_SUBSUME_MAX_PAIRS {
                        break 'pair_gen;
                    }
                }
            }
        }
    }

    let pairs_checked = pairs.len();

    // Run SIMD batch subsumption check.
    let results = scanner.batch_subsumption_check(&pairs);

    // Collect detected subsumptions, mapping scanner indices back to arena indices.
    let subsumed_pairs: Vec<(usize, usize)> = results
        .into_iter()
        .filter(|&(_, _, is_subsumed)| is_subsumed)
        .map(|(a, b, _)| {
            // a subsumes b: subsumed=b, subsumer=a
            (arena_indices[b], arena_indices[a])
        })
        .collect();

    SimdSubsumeResult {
        pairs: subsumed_pairs,
        clauses_packed: clause_data.len(),
        pairs_checked,
    }
}
