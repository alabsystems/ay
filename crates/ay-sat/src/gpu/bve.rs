// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU-accelerated BVE resolvent generation.
//!
//! Dispatches batch resolution of (positive_clause, negative_clause) pairs
//! on the GPU when the pair count exceeds `GPU_BVE_PAIR_THRESHOLD`. Each
//! pair is independent (embarrassingly parallel), making this a good fit
//! for compute shaders.
//!
//! The GPU path computes resolvents and tautology flags in a single dispatch.
//! The CPU then filters non-tautological results back into the standard BVE
//! elimination pipeline.
//!
//! Reference: ParaFROST (Osama & Wijs, SAT 2021) — GPU-accelerated variable
//! elimination via CUDA. AY uses wgpu/WGSL for cross-platform portability.

use super::{byte_len_u32, BufferBinding, GpuContext, GpuError, StorageBinding};
use crate::bve::ELIM_CLAUSE_SIZE_LIMIT;
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

/// Minimum number of resolution pairs to justify GPU dispatch overhead.
/// Below this threshold, CPU resolution is faster due to GPU launch latency.
/// ParaFROST uses ~1000 as the crossover; we use a conservative 2048.
const GPU_BVE_PAIR_THRESHOLD: usize = 2048;

/// Maximum resolvent length supported by the GPU shader. Resolvents longer
/// than this are rejected by the CPU path (ELIM_CLAUSE_SIZE_LIMIT=100).
/// Using 128 provides headroom for the shader output buffer stride.
const GPU_MAX_RESOLVENT_LEN: u32 = 128;

// SOUNDNESS INVARIANT: the shader silently truncates a resolvent at
// GPU_MAX_RESOLVENT_LEN literals, saturating the reported length there.
// Truncated resolvents are only rejected because the CPU post-processing
// rejects any resolvent longer than ELIM_CLAUSE_SIZE_LIMIT. That rejection
// path is sound only while the saturation point stays strictly above the
// CPU limit; otherwise a truncated (stronger-than-justified) resolvent
// could be accepted, which is unsound.
const _: () = assert!(GPU_MAX_RESOLVENT_LEN as usize > ELIM_CLAUSE_SIZE_LIMIT);

/// WGSL shader source, embedded at compile time.
const BVE_RESOLVE_SHADER: &str = include_str!("bve_resolve.wgsl");

/// Workgroup size matching the shader's @workgroup_size(64, 1, 1).
const WORKGROUP_SIZE: u32 = 64;

/// Per-pair output stride: 2 (length + tautology_flag) + max_resolvent_len.
const OUTPUT_STRIDE: u32 = GPU_MAX_RESOLVENT_LEN + 2;

/// Result from GPU resolvent generation for a single (pos, neg) pair.
#[derive(Debug, Clone)]
pub(crate) struct GpuResolvent {
    /// The resolvent literals (empty if tautological or parent-satisfied).
    pub literals: Vec<Literal>,
    /// Index into the positive occurrence list.
    pub pos_idx: usize,
    /// Index into the negative occurrence list.
    pub neg_idx: usize,
    /// Whether this pair was tautological/satisfied (should be skipped).
    pub is_tautology: bool,
}

/// Cached GPU pipeline for BVE resolvent generation.
///
/// Holds the compiled shader module and pipeline layout so they can be
/// reused across multiple BVE dispatch calls within a single solve. The
/// pipeline is compiled against a caller-owned [`GpuContext`]; every
/// dispatch must pass the same context the pipeline was created from.
pub(crate) struct GpuBvePipeline {
    #[allow(dead_code)] // Retained: wgpu requires ShaderModule to outlive ComputePipeline
    shader: wgpu::ShaderModule,
    layout: wgpu::BindGroupLayout,
    pipeline: wgpu::ComputePipeline,
}

impl GpuBvePipeline {
    /// Compile the GPU BVE pipeline against an existing GPU context.
    ///
    /// Shares the caller's device/queue instead of probing a second wgpu
    /// adapter, so the solver holds a single GPU device across all
    /// GPU-accelerated passes.
    pub(crate) fn try_new(context: &GpuContext) -> Option<Self> {
        let shader = context.create_shader_module("ay-bve-resolve", BVE_RESOLVE_SHADER);

        // 7 bindings: clause_data, clause_meta, pos_indices, neg_indices,
        // params, vals, results. All within the 8-binding default limit.
        let bindings = [
            StorageBinding {
                binding: 0,
                read_only: true,
            }, // clause_data
            StorageBinding {
                binding: 1,
                read_only: true,
            }, // clause_meta (interleaved start, len)
            StorageBinding {
                binding: 2,
                read_only: true,
            }, // pos_indices
            StorageBinding {
                binding: 3,
                read_only: true,
            }, // neg_indices
            StorageBinding {
                binding: 4,
                read_only: true,
            }, // params
            StorageBinding {
                binding: 5,
                read_only: true,
            }, // vals
            StorageBinding {
                binding: 6,
                read_only: false,
            }, // results (includes tautology flags)
        ];

        let layout = context.create_storage_bind_group_layout("ay-bve-layout", &bindings);
        let pipeline = context.create_compute_pipeline(
            "ay-bve-pipeline",
            &shader,
            "resolve_pairs",
            &[&layout],
        );

        Some(Self {
            shader,
            layout,
            pipeline,
        })
    }

    /// Returns true if the pair count justifies GPU dispatch.
    #[inline]
    pub(crate) fn should_use_gpu(num_pos: usize, num_neg: usize) -> bool {
        num_pos
            .checked_mul(num_neg)
            .is_some_and(|pairs| pairs >= GPU_BVE_PAIR_THRESHOLD)
    }

    /// Dispatch GPU resolvent generation for all (pos, neg) pairs.
    ///
    /// `pos_clause_indices` and `neg_clause_indices` are arena offsets for
    /// clauses containing the positive and negative pivot literal respectively.
    /// Every index MUST reference a live (in-range, non-dead) clause; the
    /// caller is responsible for filtering stale occurrence-list entries
    /// (CPU parity: `check_bounded_elimination_with_marks`).
    /// `arena` provides clause data. `vals` is the literal-indexed value array.
    /// `pivot_var` is the variable being eliminated.
    ///
    /// `context` must be the same [`GpuContext`] the pipeline was compiled
    /// against.
    ///
    /// Returns a vector of `GpuResolvent` results, one per pair. Returns
    /// `GpuError::BveDispatchTooLarge` (callers fall back to CPU) when the
    /// dispatch would exceed a device limit; without this guard an oversized
    /// buffer or workgroup count raises a wgpu validation error, which
    /// panics the process via the default uncaptured-error handler.
    pub(crate) fn dispatch_resolve(
        &self,
        context: &GpuContext,
        pivot_var: Variable,
        pos_clause_indices: &[usize],
        neg_clause_indices: &[usize],
        arena: &ClauseArena,
        vals: &[i8],
    ) -> Result<Vec<GpuResolvent>, GpuError> {
        let num_pos = pos_clause_indices.len();
        let num_neg = neg_clause_indices.len();
        let num_pairs = num_pos * num_neg;

        if num_pairs == 0 {
            return Ok(Vec::new());
        }

        debug_assert!(
            pos_clause_indices
                .iter()
                .chain(neg_clause_indices.iter())
                .all(|&idx| idx < arena.len() && !arena.is_dead(idx)),
            "BUG: GPU BVE dispatch received a dead or out-of-range clause index",
        );

        // Device-limit pre-flight. The results buffer dominates
        // (OUTPUT_STRIDE u32 words per pair); the vals buffer can also grow
        // large on huge formulas (2 vars-worth of u32 per variable).
        let limits = context.limits();
        let max_binding_bytes = u64::from(limits.max_storage_buffer_binding_size);
        let results_len = num_pairs
            .checked_mul(OUTPUT_STRIDE as usize)
            .ok_or(GpuError::OutputSizeOverflow { len: num_pairs })?;
        let results_bytes = byte_len_u32(results_len)?;
        let vals_bytes = byte_len_u32(vals.len())?;
        let required_bytes = results_bytes.max(vals_bytes);
        if required_bytes > max_binding_bytes {
            return Err(GpuError::BveDispatchTooLarge {
                num_pairs,
                required_bytes,
                max_binding_bytes,
            });
        }
        let workgroups_x = (num_pairs as u64).div_ceil(u64::from(WORKGROUP_SIZE));
        if workgroups_x > u64::from(limits.max_compute_workgroups_per_dimension) {
            return Err(GpuError::BveDispatchTooLarge {
                num_pairs,
                required_bytes: results_bytes,
                max_binding_bytes,
            });
        }
        let workgroups_x = workgroups_x as u32;

        // Build clause data: flatten all referenced clauses into a contiguous
        // u32 array with interleaved (start, len) metadata for the shader.
        let mut clause_id_map = std::collections::HashMap::new();
        let mut clause_data_flat: Vec<u32> = Vec::new();
        let mut clause_meta: Vec<u32> = Vec::new(); // interleaved (start, len)

        let all_clause_indices: Vec<usize> = pos_clause_indices
            .iter()
            .chain(neg_clause_indices.iter())
            .copied()
            .collect();

        for &arena_idx in &all_clause_indices {
            if clause_id_map.contains_key(&arena_idx) {
                continue;
            }
            let id = clause_meta.len() / 2; // each clause has 2 entries
            clause_id_map.insert(arena_idx, id as u32);
            let lits = arena.literals(arena_idx);
            let start = clause_data_flat.len() as u32;
            for &lit in lits {
                clause_data_flat.push(lit.0);
            }
            clause_meta.push(start);
            clause_meta.push(lits.len() as u32);
        }

        // Build pos_indices and neg_indices as clause IDs (not arena offsets)
        let pos_ids: Vec<u32> = pos_clause_indices
            .iter()
            .map(|idx| clause_id_map[idx])
            .collect();
        let neg_ids: Vec<u32> = neg_clause_indices
            .iter()
            .map(|idx| clause_id_map[idx])
            .collect();

        // Build vals buffer: convert i8 vals to u32 for shader
        // vals[lit_index]: 0=unassigned, 1=true, 255=false
        let vals_u32: Vec<u32> = vals
            .iter()
            .map(|&v| {
                if v > 0 {
                    1u32
                } else if v < 0 {
                    255u32
                } else {
                    0u32
                }
            })
            .collect();

        // Params buffer: [pivot_var, num_pos, num_neg, max_resolvent_len, num_vars]
        let num_vars = vals.len() / 2;
        let params: Vec<u32> = vec![
            pivot_var.0,
            num_pos as u32,
            num_neg as u32,
            GPU_MAX_RESOLVENT_LEN,
            num_vars as u32,
        ];

        // Clause data can exceed the binding limit on formulas with very
        // long clauses; pre-check like the results/vals buffers above.
        if byte_len_u32(clause_data_flat.len())? > max_binding_bytes {
            return Err(GpuError::BveDispatchTooLarge {
                num_pairs,
                required_bytes: byte_len_u32(clause_data_flat.len())?,
                max_binding_bytes,
            });
        }

        // Create GPU buffers
        let clause_data_buf =
            context.create_storage_buffer_from_u32("bve-clause-data", &clause_data_flat)?;
        let clause_meta_buf =
            context.create_storage_buffer_from_u32("bve-clause-meta", &clause_meta)?;
        let pos_ids_buf = context.create_storage_buffer_from_u32("bve-pos-ids", &pos_ids)?;
        let neg_ids_buf = context.create_storage_buffer_from_u32("bve-neg-ids", &neg_ids)?;
        let params_buf = context.create_storage_buffer_from_u32("bve-params", &params)?;
        let vals_buf = context.create_storage_buffer_from_u32("bve-vals", &vals_u32)?;
        let results_buf =
            context.create_storage_buffer_from_u32("bve-results", &vec![0u32; results_len])?;

        // Create bind group
        let bind_group = context.create_bind_group(
            "bve-bind-group",
            &self.layout,
            &[
                BufferBinding {
                    binding: 0,
                    buffer: &clause_data_buf,
                },
                BufferBinding {
                    binding: 1,
                    buffer: &clause_meta_buf,
                },
                BufferBinding {
                    binding: 2,
                    buffer: &pos_ids_buf,
                },
                BufferBinding {
                    binding: 3,
                    buffer: &neg_ids_buf,
                },
                BufferBinding {
                    binding: 4,
                    buffer: &params_buf,
                },
                BufferBinding {
                    binding: 5,
                    buffer: &vals_buf,
                },
                BufferBinding {
                    binding: 6,
                    buffer: &results_buf,
                },
            ],
        );

        // Dispatch compute shader
        context.dispatch_compute(
            "bve-resolve-dispatch",
            &self.pipeline,
            &bind_group,
            (workgroups_x, 1, 1),
        );

        // Read back results
        let result_data = context.read_u32_buffer(&results_buf, results_len)?;

        // Parse GPU output into GpuResolvent results
        let stride = OUTPUT_STRIDE as usize;
        let mut resolvents = Vec::with_capacity(num_pairs);
        for pair_id in 0..num_pairs {
            let pos_list_idx = pair_id / num_neg;
            let neg_list_idx = pair_id % num_neg;

            let base = pair_id * stride;
            let res_len = result_data[base] as usize;
            let is_tautology = result_data[base + 1] != 0;

            let literals = if is_tautology || res_len == 0 {
                Vec::new()
            } else {
                let mut lits = Vec::with_capacity(res_len);
                for i in 0..res_len {
                    lits.push(Literal(result_data[base + 2 + i]));
                }
                lits
            };

            resolvents.push(GpuResolvent {
                literals,
                pos_idx: pos_list_idx,
                neg_idx: neg_list_idx,
                is_tautology,
            });
        }

        Ok(resolvents)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a minimal arena with specific clauses for testing.
    /// Returns (arena, clause_indices).
    fn build_test_arena(clauses: &[Vec<Literal>]) -> (ClauseArena, Vec<usize>) {
        let mut arena = ClauseArena::new();
        let mut indices = Vec::new();
        for clause in clauses {
            let idx = arena.add(clause, false);
            indices.push(idx);
        }
        (arena, indices)
    }

    fn lit(var: u32, positive: bool) -> Literal {
        if positive {
            Literal::positive(Variable(var))
        } else {
            Literal::negative(Variable(var))
        }
    }

    /// Initialize a GPU context + BVE pipeline, or `None` when no adapter
    /// is available (tests skip in that case).
    fn init_gpu() -> Option<(GpuContext, GpuBvePipeline)> {
        let context = GpuContext::initialize().ok()?;
        let pipeline = GpuBvePipeline::try_new(&context)?;
        Some((context, pipeline))
    }

    #[test]
    fn test_gpu_bve_pipeline_initialization() {
        // When a GPU context exists, pipeline compilation must succeed;
        // without an adapter the test skips.
        let Ok(context) = GpuContext::initialize() else {
            return;
        };
        assert!(
            GpuBvePipeline::try_new(&context).is_some(),
            "BVE pipeline must compile on an available GPU context"
        );
    }

    #[test]
    fn test_dispatch_too_large_returns_error_not_panic() {
        let Some((context, pipeline)) = init_gpu() else {
            return;
        };

        // 600 x 600 = 360,000 pairs -> results buffer of 360K * 130 * 4
        // bytes (~187 MB) exceeds the default 128 MiB storage binding limit.
        // The dispatch must fail with BveDispatchTooLarge (CPU fallback),
        // not a wgpu validation panic.
        let pivot = Variable(0);
        let pos_clause = vec![lit(0, true), lit(1, true)];
        let neg_clause = vec![lit(0, false), lit(2, true)];
        let (arena, indices) = build_test_arena(&[pos_clause, neg_clause]);
        let vals: Vec<i8> = vec![0; 3 * 2];

        let pos_list = vec![indices[0]; 600];
        let neg_list = vec![indices[1]; 600];
        let result =
            pipeline.dispatch_resolve(&context, pivot, &pos_list, &neg_list, &arena, &vals);
        assert!(
            matches!(result, Err(GpuError::BveDispatchTooLarge { .. })),
            "oversized dispatch must be rejected via Err, got {result:?}",
        );
    }

    #[test]
    fn test_should_use_gpu_threshold() {
        assert!(!GpuBvePipeline::should_use_gpu(10, 10)); // 100 < 2048
        assert!(!GpuBvePipeline::should_use_gpu(45, 45)); // 2025 < 2048
        assert!(GpuBvePipeline::should_use_gpu(46, 46)); // 2116 >= 2048
        assert!(GpuBvePipeline::should_use_gpu(100, 100)); // 10000 >= 2048
        assert!(!GpuBvePipeline::should_use_gpu(0, 100)); // 0 pairs
    }

    #[test]
    fn test_gpu_resolve_simple_non_tautological() {
        let Some((context, pipeline)) = init_gpu() else {
            return; // No GPU
        };

        // Variable 1 is the pivot (var index 1)
        // Positive clause: {x1, x2} = {Literal(2), Literal(4)}
        // Negative clause: {~x1, x3} = {Literal(3), Literal(6)}
        // Expected resolvent: {x2, x3} = {Literal(4), Literal(6)}
        let pivot = Variable(1);
        let pos_clause = vec![lit(1, true), lit(2, true)]; // x1, x2
        let neg_clause = vec![lit(1, false), lit(3, true)]; // ~x1, x3

        let (arena, indices) = build_test_arena(&[pos_clause, neg_clause]);

        // vals: all unassigned (0)
        let num_vars = 4;
        let vals: Vec<i8> = vec![0; num_vars * 2];

        let results = pipeline
            .dispatch_resolve(&context, pivot, &[indices[0]], &[indices[1]], &arena, &vals)
            .expect("GPU dispatch must succeed");

        assert_eq!(results.len(), 1);
        assert!(!results[0].is_tautology);
        assert_eq!(results[0].literals.len(), 2);
        // Should contain x2 and x3 (Literal(4) and Literal(6))
        let mut result_lits: Vec<u32> = results[0].literals.iter().map(|l| l.0).collect();
        result_lits.sort();
        assert_eq!(result_lits, vec![4, 6]);
    }

    #[test]
    fn test_gpu_resolve_tautological_pair() {
        let Some((context, pipeline)) = init_gpu() else {
            return; // No GPU
        };

        // Pivot: variable 0
        // Positive clause: {x0, x1} = {Literal(0), Literal(2)}
        // Negative clause: {~x0, ~x1} = {Literal(1), Literal(3)}
        // Resolvent: {x1, ~x1} = tautology
        let pivot = Variable(0);
        let pos_clause = vec![lit(0, true), lit(1, true)];
        let neg_clause = vec![lit(0, false), lit(1, false)];

        let (arena, indices) = build_test_arena(&[pos_clause, neg_clause]);
        let vals: Vec<i8> = vec![0; 4 * 2];

        let results = pipeline
            .dispatch_resolve(&context, pivot, &[indices[0]], &[indices[1]], &arena, &vals)
            .expect("GPU dispatch must succeed");

        assert_eq!(results.len(), 1);
        assert!(results[0].is_tautology);
    }

    #[test]
    fn test_gpu_resolve_root_assigned_literal_pruning() {
        let Some((context, pipeline)) = init_gpu() else {
            return; // No GPU
        };

        // Pivot: variable 0
        // Positive clause: {x0, x1, x2} = {Lit(0), Lit(2), Lit(4)}
        // Negative clause: {~x0, x3} = {Lit(1), Lit(6)}
        // x1 is false at root level -> pruned from resolvent
        // Expected: {x2, x3}
        let pivot = Variable(0);
        let pos_clause = vec![lit(0, true), lit(1, true), lit(2, true)];
        let neg_clause = vec![lit(0, false), lit(3, true)];

        let (arena, indices) = build_test_arena(&[pos_clause, neg_clause]);

        let mut vals: Vec<i8> = vec![0; 4 * 2];
        // x1 positive literal = Literal(2), index = 2. Set to false.
        vals[2] = -1;

        let results = pipeline
            .dispatch_resolve(&context, pivot, &[indices[0]], &[indices[1]], &arena, &vals)
            .expect("GPU dispatch must succeed");

        assert_eq!(results.len(), 1);
        assert!(!results[0].is_tautology);
        // x1 should be pruned, leaving {x2, x3}
        assert_eq!(results[0].literals.len(), 2);
        let mut result_lits: Vec<u32> = results[0].literals.iter().map(|l| l.0).collect();
        result_lits.sort();
        assert_eq!(result_lits, vec![4, 6]); // x2=Lit(4), x3=Lit(6)
    }

    #[test]
    fn test_gpu_resolve_parent_satisfied_at_root() {
        let Some((context, pipeline)) = init_gpu() else {
            return; // No GPU
        };

        // Pivot: variable 0
        // Positive clause: {x0, x1}
        // Negative clause: {~x0, x2}
        // x1 is true at root level -> positive parent is satisfied
        let pivot = Variable(0);
        let pos_clause = vec![lit(0, true), lit(1, true)];
        let neg_clause = vec![lit(0, false), lit(2, true)];

        let (arena, indices) = build_test_arena(&[pos_clause, neg_clause]);

        let mut vals: Vec<i8> = vec![0; 4 * 2];
        vals[2] = 1; // x1 positive literal is true

        let results = pipeline
            .dispatch_resolve(&context, pivot, &[indices[0]], &[indices[1]], &arena, &vals)
            .expect("GPU dispatch must succeed");

        assert_eq!(results.len(), 1);
        // Parent satisfied is treated as tautology (skip) by the shader
        assert!(results[0].is_tautology);
    }

    #[test]
    fn test_gpu_resolve_multiple_pairs() {
        let Some((context, pipeline)) = init_gpu() else {
            return; // No GPU
        };

        // Pivot: variable 0
        // Pos clauses: {x0, x1}, {x0, x2}
        // Neg clauses: {~x0, x3}, {~x0, x4}
        // 4 pairs: (p0,n0), (p0,n1), (p1,n0), (p1,n1)
        let pivot = Variable(0);
        let clauses = vec![
            vec![lit(0, true), lit(1, true)],  // pos0
            vec![lit(0, true), lit(2, true)],  // pos1
            vec![lit(0, false), lit(3, true)], // neg0
            vec![lit(0, false), lit(4, true)], // neg1
        ];

        let (arena, indices) = build_test_arena(&clauses);
        let vals: Vec<i8> = vec![0; 5 * 2];

        let results = pipeline
            .dispatch_resolve(
                &context,
                pivot,
                &[indices[0], indices[1]],
                &[indices[2], indices[3]],
                &arena,
                &vals,
            )
            .expect("GPU dispatch must succeed");

        assert_eq!(results.len(), 4);

        // All should be non-tautological
        for r in &results {
            assert!(!r.is_tautology);
            assert_eq!(r.literals.len(), 2);
        }

        // Pair (0,0): {x1, x3}
        let mut lits: Vec<u32> = results[0].literals.iter().map(|l| l.0).collect();
        lits.sort();
        assert_eq!(lits, vec![2, 6]); // x1=Lit(2), x3=Lit(6)

        // Pair (0,1): {x1, x4}
        let mut lits: Vec<u32> = results[1].literals.iter().map(|l| l.0).collect();
        lits.sort();
        assert_eq!(lits, vec![2, 8]); // x1=Lit(2), x4=Lit(8)
    }

    #[test]
    fn test_gpu_resolve_empty_resolvent() {
        let Some((context, pipeline)) = init_gpu() else {
            return; // No GPU
        };

        // Pivot: variable 0
        // Unit positive clause: {x0}
        // Unit negative clause: {~x0}
        // Resolvent: empty (UNSAT)
        let pivot = Variable(0);
        let pos_clause = vec![lit(0, true)];
        let neg_clause = vec![lit(0, false)];

        let (arena, indices) = build_test_arena(&[pos_clause, neg_clause]);
        let vals: Vec<i8> = vec![0; 2 * 2];

        let results = pipeline
            .dispatch_resolve(&context, pivot, &[indices[0]], &[indices[1]], &arena, &vals)
            .expect("GPU dispatch must succeed");

        assert_eq!(results.len(), 1);
        // Empty resolvent: length=0, tautology_flag=0 -> not tautological
        assert!(!results[0].is_tautology);
        assert!(results[0].literals.is_empty());
    }

    #[test]
    fn test_gpu_resolve_duplicate_literal_dedup() {
        let Some((context, pipeline)) = init_gpu() else {
            return; // No GPU
        };

        // Pivot: variable 0
        // Positive clause: {x0, x1}
        // Negative clause: {~x0, x1} (x1 appears in both)
        // Resolvent: {x1} (deduplicated)
        let pivot = Variable(0);
        let pos_clause = vec![lit(0, true), lit(1, true)];
        let neg_clause = vec![lit(0, false), lit(1, true)];

        let (arena, indices) = build_test_arena(&[pos_clause, neg_clause]);
        let vals: Vec<i8> = vec![0; 2 * 2];

        let results = pipeline
            .dispatch_resolve(&context, pivot, &[indices[0]], &[indices[1]], &arena, &vals)
            .expect("GPU dispatch must succeed");

        assert_eq!(results.len(), 1);
        assert!(!results[0].is_tautology);
        assert_eq!(results[0].literals.len(), 1);
        assert_eq!(results[0].literals[0].0, 2); // x1 = Literal(2)
    }
}
