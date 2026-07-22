// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU-accelerated PDR lemma push pre-filter via wgpu compute shaders.
//!
//! PDR/IC3 frame propagation checks whether each lemma in frame F_i can be
//! pushed to F_{i+1}. A lemma is pushable if it is inductive relative to F_i.
//! The full inductiveness check requires SAT queries (F_i /\ T |= clause').
//!
//! This module provides a conservative GPU pre-filter: a lemma is definitely
//! pushable if some frame clause already subsumes it (every literal of the
//! frame clause appears in the lemma). Lemmas that pass this filter can skip
//! the expensive SAT call.
//!
//! Architecture:
//! - Pack lemma and frame-clause literals into flat u32 buffers with offset tables
//! - Dispatch one thread per lemma
//! - Each thread checks whether any frame clause subsumes that lemma
//! - Read back the indices of definitely pushable lemmas
//!
//! Threshold: GPU path for >=100 lemma*frame comparisons, CPU fallback otherwise.

use super::subsume::pack_clauses;
use super::{BufferBinding, GpuContext, GpuError, StorageBinding};

/// Minimum total comparison count (lemmas * frame_clauses) to use the GPU path.
/// Below this threshold, CPU scanning is faster due to GPU dispatch overhead.
const GPU_PDR_PUSH_THRESHOLD: usize = 100;

/// WGSL compute shader source for PDR lemma push pre-filter.
const PDR_PUSH_SHADER: &str = include_str!("pdr_push.wgsl");

/// Workgroup size matching the shader's @workgroup_size(256).
const WORKGROUP_SIZE: u32 = 256;

/// Check whether the GPU PDR push path should be used based on total work.
#[must_use]
pub(crate) fn should_use_gpu_pdr_push(num_lemmas: usize, num_frame_clauses: usize) -> bool {
    num_lemmas > 0
        && num_frame_clauses > 0
        && num_lemmas.saturating_mul(num_frame_clauses) >= GPU_PDR_PUSH_THRESHOLD
}

/// Run the PDR lemma push pre-filter on the GPU.
///
/// Each lemma and frame clause is represented as a slice of raw literal `u32` values.
/// Returns the indices of lemmas that are definitely pushable because some frame
/// clause already subsumes them.
///
/// # Errors
///
/// Returns `GpuError` if GPU initialization, buffer creation, or readback fails.
pub(crate) fn gpu_pdr_push_check(
    ctx: &GpuContext,
    lemmas: &[&[u32]],
    frame_clauses: &[&[u32]],
) -> Result<Vec<usize>, GpuError> {
    let num_lemmas = lemmas.len();
    let num_frame_clauses = frame_clauses.len();
    if num_lemmas == 0 {
        return Ok(Vec::new());
    }

    // Pack clause data into flat GPU-friendly buffers.
    let (lemma_literals_flat, lemma_offsets) = pack_clauses(lemmas);
    let (frame_literals_flat, frame_offsets) = pack_clauses(frame_clauses);

    // Ensure we have at least one literal to avoid zero-size buffer issues.
    let lemma_literals_buf = if lemma_literals_flat.is_empty() {
        ctx.create_storage_buffer_from_u32("pdr-push-lemma-literals", &[0_u32])?
    } else {
        ctx.create_storage_buffer_from_u32("pdr-push-lemma-literals", &lemma_literals_flat)?
    };
    let lemma_offsets_buf =
        ctx.create_storage_buffer_from_u32("pdr-push-lemma-offsets", &lemma_offsets)?;

    let frame_literals_buf = if frame_literals_flat.is_empty() {
        ctx.create_storage_buffer_from_u32("pdr-push-frame-literals", &[0_u32])?
    } else {
        ctx.create_storage_buffer_from_u32("pdr-push-frame-literals", &frame_literals_flat)?
    };
    let frame_offsets_buf =
        ctx.create_storage_buffer_from_u32("pdr-push-frame-offsets", &frame_offsets)?;

    let params_buf = ctx.create_storage_buffer_from_u32(
        "pdr-push-params",
        &[num_lemmas as u32, num_frame_clauses as u32],
    )?;

    // Output buffer: one u32 per lemma, initialized to 0.
    let results_zeros = vec![0_u32; num_lemmas];
    let results_buf = ctx.create_storage_buffer_from_u32("pdr-push-results", &results_zeros)?;

    // Create bind group layout and bind group.
    let layout = ctx.create_storage_bind_group_layout(
        "pdr-push-layout",
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
                read_only: true,
            },
            StorageBinding {
                binding: 4,
                read_only: true,
            },
            StorageBinding {
                binding: 5,
                read_only: false,
            },
        ],
    );

    let bind_group = ctx.create_bind_group(
        "pdr-push-bind-group",
        &layout,
        &[
            BufferBinding {
                binding: 0,
                buffer: &lemma_literals_buf,
            },
            BufferBinding {
                binding: 1,
                buffer: &lemma_offsets_buf,
            },
            BufferBinding {
                binding: 2,
                buffer: &frame_literals_buf,
            },
            BufferBinding {
                binding: 3,
                buffer: &frame_offsets_buf,
            },
            BufferBinding {
                binding: 4,
                buffer: &params_buf,
            },
            BufferBinding {
                binding: 5,
                buffer: &results_buf,
            },
        ],
    );

    // Compile shader and create pipeline.
    let shader = ctx.create_shader_module("pdr-push-shader", PDR_PUSH_SHADER);
    let pipeline =
        ctx.create_compute_pipeline("pdr-push-pipeline", &shader, "pdr_push_check", &[&layout]);

    // Dispatch: ceil(num_lemmas / WORKGROUP_SIZE) workgroups.
    let num_workgroups = (num_lemmas as u32 + WORKGROUP_SIZE - 1) / WORKGROUP_SIZE;
    ctx.dispatch_compute(
        "pdr-push-dispatch",
        &pipeline,
        &bind_group,
        (num_workgroups, 1, 1),
    );

    // Read back results.
    let results = ctx.read_u32_buffer(&results_buf, num_lemmas)?;

    // Collect pushable lemma indices.
    let mut pushable = Vec::new();
    for (lemma_idx, &val) in results.iter().enumerate() {
        if val != 0 {
            pushable.push(lemma_idx);
        }
    }

    Ok(pushable)
}

/// CPU reference implementation for the PDR lemma push pre-filter.
///
/// Used as fallback below the GPU threshold and as a test oracle.
/// Each lemma and frame clause is a slice of raw literal `u32` values.
pub(crate) fn cpu_pdr_push_check(lemmas: &[&[u32]], frame_clauses: &[&[u32]]) -> Vec<usize> {
    let mut pushable = Vec::new();

    for (lemma_idx, lemma) in lemmas.iter().enumerate() {
        for frame_clause in frame_clauses {
            // frame_clause can only subsume lemma if |frame| <= |lemma|.
            if frame_clause.len() > lemma.len() {
                continue;
            }

            // Check if every literal in frame_clause appears in lemma.
            let all_found = frame_clause
                .iter()
                .all(|frame_lit| lemma.iter().any(|lemma_lit| lemma_lit == frame_lit));

            if all_found {
                pushable.push(lemma_idx);
                break;
            }
        }
    }

    pushable
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: encode a positive literal for variable v.
    fn pos(v: u32) -> u32 {
        v * 2
    }

    /// Helper: encode a negative literal for variable v.
    fn neg(v: u32) -> u32 {
        v * 2 + 1
    }

    #[test]
    fn test_cpu_pdr_push_basic() {
        // l0 = {x0, ~x1, x2} is subsumed by f0 = {x0, ~x1}
        // l1 = {~x0, x1} is not subsumed by any frame clause
        let l0 = vec![pos(0), neg(1), pos(2)];
        let l1 = vec![neg(0), pos(1)];
        let f0 = vec![pos(0), neg(1)];
        let f1 = vec![pos(3)];
        let lemmas: Vec<&[u32]> = vec![&l0, &l1];
        let frame_clauses: Vec<&[u32]> = vec![&f0, &f1];

        let pushable = cpu_pdr_push_check(&lemmas, &frame_clauses);
        assert_eq!(pushable, vec![0]);
    }

    #[test]
    fn test_cpu_pdr_push_no_match() {
        // No frame clause subsumes any lemma (polarity mismatch).
        let l0 = vec![pos(0), neg(1)];
        let l1 = vec![neg(2), pos(3)];
        let f0 = vec![pos(0), pos(1)]; // pos(1) not in l0 (l0 has neg(1))
        let f1 = vec![neg(3), pos(4)]; // neg(3) not in l1, pos(4) not in l1
        let lemmas: Vec<&[u32]> = vec![&l0, &l1];
        let frame_clauses: Vec<&[u32]> = vec![&f0, &f1];

        let pushable = cpu_pdr_push_check(&lemmas, &frame_clauses);
        assert!(pushable.is_empty());
    }

    #[test]
    fn test_cpu_pdr_push_unit_subsumes() {
        // Unit frame clause {x0} subsumes any lemma containing x0.
        let l0 = vec![pos(0), pos(1)];
        let l1 = vec![pos(0), neg(2), pos(3)];
        let l2 = vec![neg(0), pos(4)]; // does NOT contain pos(0)
        let f0 = vec![pos(0)];
        let lemmas: Vec<&[u32]> = vec![&l0, &l1, &l2];
        let frame_clauses: Vec<&[u32]> = vec![&f0];

        let pushable = cpu_pdr_push_check(&lemmas, &frame_clauses);
        assert_eq!(pushable, vec![0, 1]);
    }

    #[test]
    fn test_cpu_pdr_push_empty_lemmas() {
        let f0 = vec![pos(0)];
        let lemmas: Vec<&[u32]> = vec![];
        let frame_clauses: Vec<&[u32]> = vec![&f0];

        let pushable = cpu_pdr_push_check(&lemmas, &frame_clauses);
        assert!(pushable.is_empty());
    }

    #[test]
    fn test_cpu_pdr_push_empty_frame() {
        let l0 = vec![pos(0), pos(1)];
        let lemmas: Vec<&[u32]> = vec![&l0];
        let frame_clauses: Vec<&[u32]> = vec![];

        let pushable = cpu_pdr_push_check(&lemmas, &frame_clauses);
        assert!(pushable.is_empty());
    }

    #[test]
    fn test_cpu_pdr_push_all_pushable() {
        // Frame clause is identical to each lemma — trivial subsumption.
        let l0 = vec![pos(0), neg(1)];
        let l1 = vec![pos(0), neg(1), pos(2)];
        let f0 = vec![pos(0), neg(1)];
        let lemmas: Vec<&[u32]> = vec![&l0, &l1];
        let frame_clauses: Vec<&[u32]> = vec![&f0];

        let pushable = cpu_pdr_push_check(&lemmas, &frame_clauses);
        assert_eq!(pushable, vec![0, 1]);
    }

    #[test]
    fn test_gpu_pdr_push_matches_cpu() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let l0 = vec![pos(0), neg(1), pos(2)];
        let l1 = vec![pos(3), neg(6)];
        let l2 = vec![neg(4), pos(5), pos(7)];
        let l3 = vec![pos(8), neg(9)];
        let f0 = vec![pos(0), neg(1)]; // subsumes l0
        let f1 = vec![pos(3)]; // subsumes l1
        let f2 = vec![neg(4), pos(5)]; // subsumes l2

        let lemmas: Vec<&[u32]> = vec![&l0, &l1, &l2, &l3];
        let frame_clauses: Vec<&[u32]> = vec![&f0, &f1, &f2];

        let cpu_pushable = cpu_pdr_push_check(&lemmas, &frame_clauses);
        let gpu_pushable = gpu_pdr_push_check(&ctx, &lemmas, &frame_clauses)
            .expect("GPU PDR push check must succeed");

        assert_eq!(
            cpu_pushable, gpu_pushable,
            "GPU and CPU PDR push results must match"
        );
    }

    #[test]
    fn test_gpu_pdr_push_empty() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let lemmas: Vec<&[u32]> = vec![];
        let f0 = vec![pos(0)];
        let frame_clauses: Vec<&[u32]> = vec![&f0];

        let pushable = gpu_pdr_push_check(&ctx, &lemmas, &frame_clauses)
            .expect("GPU PDR push check must succeed");
        assert!(pushable.is_empty());
    }

    #[test]
    fn test_gpu_pdr_push_single_lemma() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let l0 = vec![pos(0), pos(1)];
        let f0 = vec![pos(0)]; // unit clause subsumes l0
        let lemmas: Vec<&[u32]> = vec![&l0];
        let frame_clauses: Vec<&[u32]> = vec![&f0];

        let pushable = gpu_pdr_push_check(&ctx, &lemmas, &frame_clauses)
            .expect("GPU PDR push check must succeed");
        assert_eq!(pushable, vec![0]);
    }

    #[test]
    fn test_gpu_pdr_push_no_subsumption() {
        let ctx = match GpuContext::initialize() {
            Ok(ctx) => ctx,
            Err(GpuError::AdapterUnavailable { .. }) => return,
            Err(error) => panic!("GPU initialization failed: {error}"),
        };

        let l0 = vec![pos(0), neg(1)];
        let l1 = vec![pos(2), pos(3)];
        let f0 = vec![pos(0), pos(1)]; // pos(1) not in l0
        let f1 = vec![neg(2), pos(3)]; // neg(2) not in l1
        let lemmas: Vec<&[u32]> = vec![&l0, &l1];
        let frame_clauses: Vec<&[u32]> = vec![&f0, &f1];

        let pushable = gpu_pdr_push_check(&ctx, &lemmas, &frame_clauses)
            .expect("GPU PDR push check must succeed");
        assert!(pushable.is_empty());
    }

    #[test]
    fn test_should_use_gpu_pdr_push_threshold() {
        assert!(!should_use_gpu_pdr_push(0, 0));
        assert!(!should_use_gpu_pdr_push(100, 0));
        assert!(!should_use_gpu_pdr_push(0, 100));
        assert!(!should_use_gpu_pdr_push(1, 99));
        assert!(!should_use_gpu_pdr_push(9, 11));
        assert!(should_use_gpu_pdr_push(10, 10));
        assert!(should_use_gpu_pdr_push(1, 100));
        assert!(should_use_gpu_pdr_push(100, 1));
        assert!(should_use_gpu_pdr_push(50, 50));
    }
}
