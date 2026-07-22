// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU-accelerated pairwise subsumption checking via wgpu compute shaders.
//!
//! Subsumption checking is O(n^2) over clause pairs — embarrassingly parallel.
//! ParaFROST (Osama & Wijs, SAT 2021) demonstrated 2-10x speedups for GPU
//! subsumption on large clause databases.
//!
//! Architecture:
//! - Pack clause literals into a flat u32 buffer with an offset table
//! - Dispatch one thread per (clause_i, clause_j) pair
//! - Each thread checks if clause_i's literals are a subset of clause_j's
//! - Read back a bounded bitset of subsumed pair flags
//!
//! Threshold: GPU path for >10K clauses, CPU fallback for smaller sets.

use super::{BufferBinding, GpuContext, GpuError, StorageBinding};
use std::mem::size_of;

/// Minimum clause count to use the GPU subsumption path.
/// Below this threshold, CPU subsumption is faster due to GPU dispatch overhead.
const GPU_SUBSUME_THRESHOLD: usize = 10_000;

/// WGSL compute shader source for pairwise subsumption.
const SUBSUME_SHADER: &str = include_str!("subsume.wgsl");

/// Workgroup size matching the shader's @workgroup_size(256).
const WORKGROUP_SIZE: u32 = 256;

/// Conservative WebGPU per-dimension dispatch limit.
const MAX_WORKGROUPS_PER_DIMENSION: usize = 65_535;

/// One result bit per ordered clause pair.
const RESULT_BITS_PER_WORD: usize = u32::BITS as usize;

/// Maximum result bitset allocated for a single GPU subsumption dispatch.
///
/// This keeps the 10K threshold practical (10K clauses need 12.5 MB) while
/// preventing larger instances from allocating unbounded O(n^2) readback buffers.
const GPU_SUBSUME_MAX_RESULT_BYTES: usize = 128 * 1024 * 1024;

/// A subsumed clause pair: clause at index `subsumer` subsumes clause at index `subsumed`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SubsumedPair {
    /// Index of the subsuming clause (smaller or equal size).
    pub subsumer: usize,
    /// Index of the subsumed clause (larger or equal size).
    pub subsumed: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SubsumptionDispatchPlan {
    total_pairs: usize,
    result_words: usize,
    result_bytes: usize,
    total_workgroups: usize,
    workgroups_x: u32,
    workgroups_y: u32,
}

/// Pack clause data into flat buffers suitable for GPU upload.
///
/// Returns `(literals_flat, offsets)` where:
/// - `literals_flat[offsets[i]..offsets[i+1]]` contains the literals of clause `i`
/// - Literals are raw `u32` values (var*2 + polarity encoding)
/// - `offsets` has length `clauses.len() + 1`
pub(crate) fn pack_clauses(clauses: &[&[u32]]) -> (Vec<u32>, Vec<u32>) {
    let total_lits: usize = clauses.iter().map(|c| c.len()).sum();
    let mut literals_flat = Vec::with_capacity(total_lits);
    let mut offsets = Vec::with_capacity(clauses.len() + 1);

    for clause in clauses {
        offsets.push(literals_flat.len() as u32);
        literals_flat.extend_from_slice(clause);
    }
    offsets.push(literals_flat.len() as u32);

    (literals_flat, offsets)
}

/// Check whether the GPU subsumption path should be used based on clause count.
#[must_use]
pub(crate) fn should_use_gpu(num_clauses: usize) -> bool {
    num_clauses >= GPU_SUBSUME_THRESHOLD && subsumption_dispatch_plan(num_clauses).is_ok()
}

fn subsumption_dispatch_plan(num_clauses: usize) -> Result<SubsumptionDispatchPlan, GpuError> {
    let total_pairs = num_clauses
        .checked_mul(num_clauses)
        .ok_or(GpuError::OutputSizeOverflow { len: num_clauses })?;
    let result_words = total_pairs.div_ceil(RESULT_BITS_PER_WORD);
    let result_bytes = result_words
        .checked_mul(size_of::<u32>())
        .ok_or(GpuError::OutputSizeOverflow { len: result_words })?;
    if result_bytes > GPU_SUBSUME_MAX_RESULT_BYTES {
        return Err(GpuError::SubsumptionResultBufferTooLarge {
            num_clauses,
            result_bytes,
            max_result_bytes: GPU_SUBSUME_MAX_RESULT_BYTES,
        });
    }
    let total_workgroups = total_pairs.div_ceil(WORKGROUP_SIZE as usize);
    let workgroups_x = total_workgroups.min(MAX_WORKGROUPS_PER_DIMENSION);
    let workgroups_y = total_workgroups.div_ceil(workgroups_x);
    if workgroups_y > MAX_WORKGROUPS_PER_DIMENSION {
        return Err(GpuError::OutputSizeOverflow {
            len: total_workgroups,
        });
    }

    Ok(SubsumptionDispatchPlan {
        total_pairs,
        result_words,
        result_bytes,
        total_workgroups,
        workgroups_x: workgroups_x as u32,
        workgroups_y: workgroups_y as u32,
    })
}

/// Run pairwise subsumption checking on the GPU.
///
/// Each clause is represented as a slice of raw literal `u32` values.
/// Returns a list of `SubsumedPair` indicating which clauses are subsumed.
///
/// # Errors
///
/// Returns `GpuError` if GPU initialization, buffer creation, or readback fails.
pub(crate) fn gpu_subsume_check(
    ctx: &GpuContext,
    clauses: &[&[u32]],
) -> Result<Vec<SubsumedPair>, GpuError> {
    let num_clauses = clauses.len();
    if num_clauses == 0 {
        return Ok(Vec::new());
    }

    let plan = subsumption_dispatch_plan(num_clauses)?;
    debug_assert!(plan.result_bytes <= GPU_SUBSUME_MAX_RESULT_BYTES);
    debug_assert!(plan.total_workgroups > 0);

    // Pack clause data into flat GPU-friendly buffers.
    let (literals_flat, offsets) = pack_clauses(clauses);

    // Ensure we have at least one literal to avoid zero-size buffer issues.
    let literals_buf = if literals_flat.is_empty() {
        ctx.create_storage_buffer_from_u32("subsume-literals", &[0_u32])?
    } else {
        ctx.create_storage_buffer_from_u32("subsume-literals", &literals_flat)?
    };
    let offsets_buf = ctx.create_storage_buffer_from_u32("subsume-offsets", &offsets)?;
    let params_buf = ctx.create_storage_buffer_from_u32(
        "subsume-params",
        &[num_clauses as u32, plan.workgroups_x],
    )?;

    // Output buffer: one bit per ordered pair, initialized to 0.
    let results_zeros = vec![0_u32; plan.result_words];
    let results_buf = ctx.create_storage_buffer_from_u32("subsume-results", &results_zeros)?;

    // Create bind group layout and bind group.
    let layout = ctx.create_storage_bind_group_layout(
        "subsume-layout",
        &[
            StorageBinding {
                binding: 0,
                read_only: true,
            },
            StorageBinding {
                binding: 1,
                read_only: true,
            },
            StorageBinding {
                binding: 2,
                read_only: true,
            },
            StorageBinding {
                binding: 3,
                read_only: false,
            },
        ],
    );

    let bind_group = ctx.create_bind_group(
        "subsume-bind-group",
        &layout,
        &[
            BufferBinding {
                binding: 0,
                buffer: &literals_buf,
            },
            BufferBinding {
                binding: 1,
                buffer: &offsets_buf,
            },
            BufferBinding {
                binding: 2,
                buffer: &params_buf,
            },
            BufferBinding {
                binding: 3,
                buffer: &results_buf,
            },
        ],
    );

    // Compile shader and create pipeline.
    let shader = ctx.create_shader_module("subsume-shader", SUBSUME_SHADER);
    let pipeline =
        ctx.create_compute_pipeline("subsume-pipeline", &shader, "subsume_check", &[&layout]);

    ctx.dispatch_compute(
        "subsume-dispatch",
        &pipeline,
        &bind_group,
        (plan.workgroups_x, plan.workgroups_y, 1),
    );

    // Read back results.
    let results = ctx.read_u32_buffer(&results_buf, plan.result_words)?;

    // Collect subsumed pairs.
    let mut pairs = Vec::new();
    for (word_idx, &word) in results.iter().enumerate() {
        let mut bits = word;
        while bits != 0 {
            let bit = bits.trailing_zeros() as usize;
            let pair_idx = word_idx * RESULT_BITS_PER_WORD + bit;
            bits &= bits - 1;
            if pair_idx >= plan.total_pairs {
                continue;
            }
            let i = pair_idx / num_clauses;
            let j = pair_idx % num_clauses;
            pairs.push(SubsumedPair {
                subsumer: i,
                subsumed: j,
            });
        }
    }

    Ok(pairs)
}

/// CPU reference implementation for pairwise subsumption checking.
///
/// Used as fallback below the GPU threshold and as a test oracle.
/// Each clause is a slice of raw literal `u32` values.
#[cfg(test)]
pub(crate) fn cpu_subsume_check(clauses: &[&[u32]]) -> Vec<SubsumedPair> {
    let num_clauses = clauses.len();
    let mut pairs = Vec::new();
    let normalized: Vec<Vec<u32>> = clauses
        .iter()
        .map(|clause| {
            let mut lits = clause.to_vec();
            lits.sort_unstable();
            lits.dedup();
            lits
        })
        .collect();
    let signatures: Vec<u64> = normalized
        .iter()
        .map(|clause| {
            let mut signature = 0_u64;
            for &lit in clause {
                let bit = lit.wrapping_mul(0x9E37_79B1) & 63;
                signature |= 1_u64 << bit;
            }
            signature
        })
        .collect();

    for i in 0..num_clauses {
        for j in 0..num_clauses {
            if i == j {
                continue;
            }
            // clause_i can only subsume clause_j if |i| <= |j|.
            if clauses[i].len() > clauses[j].len() {
                continue;
            }
            if signatures[i] & !signatures[j] != 0 {
                continue;
            }
            // Check if every literal in clause_i appears in clause_j.
            let mut j_lit = 0;
            let mut is_subset = true;
            for &lit in &normalized[i] {
                while j_lit < normalized[j].len() && normalized[j][j_lit] < lit {
                    j_lit += 1;
                }
                if j_lit == normalized[j].len() || normalized[j][j_lit] != lit {
                    is_subset = false;
                    break;
                }
            }
            if is_subset {
                pairs.push(SubsumedPair {
                    subsumer: i,
                    subsumed: j,
                });
            }
        }
    }

    pairs
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// Helper: encode a positive literal for variable v.
    fn pos(v: u32) -> u32 {
        v * 2
    }

    /// Helper: encode a negative literal for variable v.
    fn neg(v: u32) -> u32 {
        v * 2 + 1
    }

    #[test]
    fn test_pack_clauses_empty() {
        let clauses: Vec<&[u32]> = vec![];
        let (lits, offsets) = pack_clauses(&clauses);
        assert!(lits.is_empty());
        assert_eq!(offsets, vec![0]);
    }

    #[test]
    fn test_pack_clauses_basic() {
        let c0 = vec![pos(0), neg(1)];
        let c1 = vec![pos(0), neg(1), pos(2)];
        let clauses: Vec<&[u32]> = vec![&c0, &c1];
        let (lits, offsets) = pack_clauses(&clauses);
        assert_eq!(lits, vec![pos(0), neg(1), pos(0), neg(1), pos(2)]);
        assert_eq!(offsets, vec![0, 2, 5]);
    }

    #[test]
    fn test_cpu_subsume_basic() {
        // c0 = {x0, ~x1} subsumes c1 = {x0, ~x1, x2}
        let c0 = vec![pos(0), neg(1)];
        let c1 = vec![pos(0), neg(1), pos(2)];
        let clauses: Vec<&[u32]> = vec![&c0, &c1];
        let pairs = cpu_subsume_check(&clauses);
        assert_eq!(pairs.len(), 1);
        assert_eq!(
            pairs[0],
            SubsumedPair {
                subsumer: 0,
                subsumed: 1
            }
        );
    }

    #[test]
    fn test_cpu_subsume_no_match() {
        // c0 = {x0, x1}, c1 = {x0, ~x1} — different polarities, no subsumption
        let c0 = vec![pos(0), pos(1)];
        let c1 = vec![pos(0), neg(1)];
        let clauses: Vec<&[u32]> = vec![&c0, &c1];
        let pairs = cpu_subsume_check(&clauses);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_cpu_subsume_mutual() {
        // c0 = {x0, x1}, c1 = {x0, x1} — identical clauses: mutual subsumption
        let c0 = vec![pos(0), pos(1)];
        let c1 = vec![pos(0), pos(1)];
        let clauses: Vec<&[u32]> = vec![&c0, &c1];
        let pairs = cpu_subsume_check(&clauses);
        assert_eq!(pairs.len(), 2);
    }

    #[test]
    fn test_cpu_subsume_unit_subsumes_all_containing() {
        // Unit clause {x0} subsumes any clause containing x0.
        let c0 = vec![pos(0)];
        let c1 = vec![pos(0), pos(1)];
        let c2 = vec![pos(0), neg(2), pos(3)];
        let c3 = vec![neg(0)]; // different polarity, no subsumption
        let clauses: Vec<&[u32]> = vec![&c0, &c1, &c2, &c3];
        let pairs = cpu_subsume_check(&clauses);
        // c0 subsumes c1 and c2 only.
        let expected = vec![
            SubsumedPair {
                subsumer: 0,
                subsumed: 1,
            },
            SubsumedPair {
                subsumer: 0,
                subsumed: 2,
            },
        ];
        assert_eq!(pairs, expected);
    }

    #[test]
    fn test_dispatch_plan_uses_bounded_bitset_at_10k() {
        let plan = subsumption_dispatch_plan(10_000).expect("10K dispatch must fit bound");
        assert_eq!(plan.total_pairs, 100_000_000);
        assert_eq!(plan.result_words, 3_125_000);
        assert_eq!(plan.result_bytes, 12_500_000);
        assert_eq!(plan.total_workgroups, 390_625);
        assert_eq!(plan.workgroups_x as usize, MAX_WORKGROUPS_PER_DIMENSION);
        assert_eq!(plan.workgroups_y, 6);
        assert!(plan.result_bytes < plan.total_pairs * size_of::<u32>());
    }

    #[test]
    fn test_dispatch_plan_accepts_medium_25k_bitset() {
        let plan = subsumption_dispatch_plan(25_000).expect("25K bitset should fit bound");
        assert_eq!(plan.total_pairs, 625_000_000);
        assert_eq!(plan.result_bytes, 78_125_000);
        assert!(plan.result_bytes <= GPU_SUBSUME_MAX_RESULT_BYTES);
    }

    #[test]
    fn test_dispatch_plan_rejects_oversized_result_bitset() {
        let err = subsumption_dispatch_plan(50_000).expect_err("50K must exceed result cap");
        assert!(matches!(
            err,
            GpuError::SubsumptionResultBufferTooLarge {
                num_clauses: 50_000,
                ..
            }
        ));
    }

    #[test]
    fn test_gpu_subsume_matches_cpu() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        // Build a test clause set with known subsumption relationships.
        let c0 = vec![pos(0), neg(1)];
        let c1 = vec![pos(0), neg(1), pos(2)]; // subsumed by c0
        let c2 = vec![pos(3), pos(4)];
        let c3 = vec![pos(3), pos(4), neg(5)]; // subsumed by c2
        let c4 = vec![neg(0), pos(1)]; // no subsumption relationship with others
        let clauses: Vec<&[u32]> = vec![&c0, &c1, &c2, &c3, &c4];

        let cpu_pairs = cpu_subsume_check(&clauses);
        let gpu_pairs =
            gpu_subsume_check(&ctx, &clauses).expect("GPU subsumption check must succeed");

        // Sort both for comparison.
        let mut cpu_sorted = cpu_pairs;
        cpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));
        let mut gpu_sorted = gpu_pairs;
        gpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));

        assert_eq!(
            cpu_sorted, gpu_sorted,
            "GPU and CPU subsumption results must match"
        );
    }

    #[test]
    fn test_gpu_subsume_empty_clauses() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let clauses: Vec<&[u32]> = vec![];
        let pairs = gpu_subsume_check(&ctx, &clauses).expect("GPU subsumption check must succeed");
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_gpu_subsume_single_clause() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let c0 = vec![pos(0), pos(1)];
        let clauses: Vec<&[u32]> = vec![&c0];
        let pairs = gpu_subsume_check(&ctx, &clauses).expect("GPU subsumption check must succeed");
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_gpu_subsume_unit_clauses() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let c0 = vec![pos(0)];
        let c1 = vec![pos(0), pos(1)];
        let c2 = vec![pos(0), neg(2), pos(3)];
        let c3 = vec![neg(0)];
        let clauses: Vec<&[u32]> = vec![&c0, &c1, &c2, &c3];

        let cpu_pairs = cpu_subsume_check(&clauses);
        let gpu_pairs =
            gpu_subsume_check(&ctx, &clauses).expect("GPU subsumption check must succeed");

        let mut cpu_sorted = cpu_pairs;
        cpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));
        let mut gpu_sorted = gpu_pairs;
        gpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));

        assert_eq!(cpu_sorted, gpu_sorted);
    }

    #[test]
    fn test_gpu_subsume_identical_clauses() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        // Identical clauses subsume each other.
        let c0 = vec![pos(0), pos(1)];
        let c1 = vec![pos(0), pos(1)];
        let clauses: Vec<&[u32]> = vec![&c0, &c1];

        let cpu_pairs = cpu_subsume_check(&clauses);
        let gpu_pairs =
            gpu_subsume_check(&ctx, &clauses).expect("GPU subsumption check must succeed");

        let mut cpu_sorted = cpu_pairs;
        cpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));
        let mut gpu_sorted = gpu_pairs;
        gpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));

        assert_eq!(cpu_sorted, gpu_sorted);
        assert_eq!(gpu_sorted.len(), 2); // mutual subsumption
    }

    #[test]
    fn test_gpu_subsume_satcomp_stable300_10k_real_clause_differential() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => {
                eprintln!("SKIP: no GPU adapter for real-clause subsumption differential");
                return;
            }
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../benchmarks/sat/satcomp2024-sample")
            .join("8b31606e10656ff7eb2936262b647443-stable-300-0.1-20-98765432130020.cnf");
        let contents = match std::fs::read_to_string(&path) {
            Ok(contents) => contents,
            Err(error) => {
                eprintln!(
                    "SKIP: {} unavailable for real-clause subsumption differential: {error}",
                    path.display()
                );
                return;
            }
        };
        let formula = crate::parse_dimacs(&contents).expect("parse stable-300 SATCOMP sample");
        let raw_clauses: Vec<Vec<u32>> = formula
            .clauses
            .iter()
            .take(GPU_SUBSUME_THRESHOLD)
            .map(|clause| clause.iter().map(|lit| lit.raw()).collect())
            .collect();
        assert_eq!(
            raw_clauses.len(),
            GPU_SUBSUME_THRESHOLD,
            "stable-300 sample must provide a 10K real-clause GPU dispatch set"
        );
        assert!(should_use_gpu(raw_clauses.len()));

        let plan =
            subsumption_dispatch_plan(raw_clauses.len()).expect("10K real-clause dispatch fits");
        assert_eq!(plan.result_bytes, 12_500_000);

        let clause_refs: Vec<&[u32]> = raw_clauses.iter().map(Vec::as_slice).collect();
        let mut gpu_pairs =
            gpu_subsume_check(&ctx, &clause_refs).expect("GPU real-clause subsumption succeeds");
        let mut cpu_pairs = cpu_subsume_check(&clause_refs);
        gpu_pairs.sort_by_key(|p| (p.subsumer, p.subsumed));
        cpu_pairs.sort_by_key(|p| (p.subsumer, p.subsumed));

        eprintln!(
            "gpu_subsume_real_clause_differential clauses={} result_bytes={} pairs={}",
            raw_clauses.len(),
            plan.result_bytes,
            cpu_pairs.len()
        );
        assert_eq!(
            cpu_pairs, gpu_pairs,
            "GPU and CPU subsumption must match on stable-300 10K real clauses"
        );
    }

    #[test]
    fn test_should_use_gpu_threshold() {
        assert!(!should_use_gpu(0));
        assert!(!should_use_gpu(100));
        assert!(!should_use_gpu(9_999));
        assert!(should_use_gpu(10_000));
        assert!(should_use_gpu(25_000));
        assert!(!should_use_gpu(50_000));
    }
}
