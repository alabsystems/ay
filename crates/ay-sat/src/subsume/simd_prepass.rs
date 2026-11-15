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
use crate::kani_compat::DetHashMap;

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

    // Pack clauses into SIMD scanner, building a literal-occurrence index
    // (literal -> packed clause indices containing it) alongside.
    let total_lits: usize = clause_data.iter().map(|&(_, len)| len).sum();
    let mut scanner = SimdClauseScanner::with_capacity(clause_data.len(), total_lits);
    let mut arena_indices: Vec<usize> = Vec::with_capacity(clause_data.len());
    let mut occ: DetHashMap<i32, Vec<u32>> = DetHashMap::default();

    for (a, &(idx, _)) in clause_data.iter().enumerate() {
        let lits = clauses.literals(idx);
        let raw_lits: Vec<i32> = lits.iter().map(|lit| lit.0 as i32).collect();
        scanner.push(&raw_lits);
        arena_indices.push(idx);
        for &raw in &raw_lits {
            let list = occ.entry(raw).or_default();
            // A clause never repeats a literal; guard anyway so a repeat
            // cannot emit duplicate candidate pairs below.
            if list.last() != Some(&(a as u32)) {
                list.push(a as u32);
            }
        }
    }

    // Length groups over the packed order, as in the legacy candidate
    // generation this replaces: groups are (start, end) ranges of equal
    // clause length, and `group_id` maps each packed index to its group.
    let n = clause_data.len();
    let mut groups: Vec<(usize, usize)> = Vec::new();
    let mut group_id: Vec<usize> = vec![0; n];
    let mut group_start = 0;
    while group_start < n {
        let group_len = clause_data[group_start].1;
        let mut group_end = group_start + 1;
        while group_end < n && clause_data[group_end].1 == group_len {
            group_end += 1;
        }
        let gi = groups.len();
        for slot in &mut group_id[group_start..group_end] {
            *slot = gi;
        }
        groups.push((group_start, group_end));
        group_start = group_end;
    }
    // Rank at which each (gi, gj) block starts in the legacy enumeration
    // (gi ascending, gj from gi ascending; a-major within a block).
    let mut block_start: Vec<Vec<u64>> = vec![vec![0; groups.len()]; groups.len()];
    let mut next_rank: u64 = 0;
    for gi in 0..groups.len() {
        for gj in gi..groups.len() {
            block_start[gi][gj] = next_rank;
            let (a_lo, a_hi) = groups[gi];
            let (b_lo, b_hi) = groups[gj];
            let block_pairs = if gi == gj {
                let g = (a_hi - a_lo) as u64;
                g * (g - 1)
            } else {
                (a_hi - a_lo) as u64 * (b_hi - b_lo) as u64
            };
            next_rank += block_pairs;
        }
    }

    // Generate candidate pairs through the occurrence index, keeping the
    // legacy generation's detections exactly: A can subsume B only if
    // |A| <= |B| and B contains every literal of A, in particular A's
    // rarest literal (CaDiCaL subsume.cpp candidate generation), so any
    // legacy pair outside the rarest literal's occurrence list cannot
    // subsume and checking it is pure waste. Each surviving candidate is
    // ranked by its position in the legacy length-group enumeration and
    // admitted only under the same SIMD_SUBSUME_MAX_PAIRS cap, then
    // sorted by rank — so the batch checks the same subsumption-capable
    // pairs, in the same order, as the legacy Cartesian generation,
    // while skipping the (often ~200k) pairs that cannot subsume.
    // (Widening the cap to the filtered candidates instead was measured
    // to lose decided files: the extra deletions perturb sat search
    // trajectories more than the saved checks repay.)
    let mut ranked: Vec<(u64, usize, usize)> = Vec::new();
    for (a, &(_, a_len)) in clause_data.iter().enumerate() {
        let a_lits = clauses.literals(arena_indices[a]);
        let Some(rarest) = a_lits
            .iter()
            .map(|lit| lit.0 as i32)
            .min_by_key(|raw| occ.get(raw).map_or(usize::MAX, Vec::len))
        else {
            continue;
        };
        let Some(candidates) = occ.get(&rarest) else {
            continue;
        };
        for &b in candidates {
            let b = b as usize;
            if b == a || clause_data[b].1 < a_len {
                continue;
            }
            let rank = legacy_pair_rank(&groups, &block_start, &group_id, a, b);
            if rank < SIMD_SUBSUME_MAX_PAIRS as u64 {
                ranked.push((rank, a, b));
            }
        }
    }
    ranked.sort_unstable();
    let pairs: Vec<(usize, usize)> = ranked.into_iter().map(|(_, a, b)| (a, b)).collect();

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

/// Position of pair `(a, b)` (`a != b`, `len(b) >= len(a)`) in the legacy
/// length-group pair enumeration: blocks ordered by (a-group, b-group)
/// with b-group >= a-group, a-major within a block, diagonal pairs
/// skipped inside a same-length block.
fn legacy_pair_rank(
    groups: &[(usize, usize)],
    block_start: &[Vec<u64>],
    group_id: &[usize],
    a: usize,
    b: usize,
) -> u64 {
    let ga = group_id[a];
    let gb = group_id[b];
    let (a_lo, _) = groups[ga];
    let (b_lo, b_hi) = groups[gb];
    let within = (a - a_lo) as u64 * (b_hi - b_lo) as u64 + (b - b_lo) as u64;
    // Same-length block: the skipped diagonals (x, x) for x before a, and
    // (a, a) itself when a < b, precede (a, b) in the raw product but are
    // never emitted, so subtract them from the raw offset.
    let skipped = if ga == gb {
        (a - a_lo) as u64 + u64::from(a < b)
    } else {
        0
    };
    block_start[ga][gb] + within - skipped
}
