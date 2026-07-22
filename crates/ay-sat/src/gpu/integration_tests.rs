// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for GPU-accelerated inprocessing passes.
//!
//! Tests verify that:
//! 1. GpuContext lazy initialization works (initializes once, caches result)
//! 2. GPU subsumption pre-pass produces correct results consistent with CPU
//! 3. GPU BVE dispatch threshold gating works correctly
//! 4. Fallback to CPU path when GPU unavailable is silent and correct
//! 5. Feature gating: all GPU code compiles cleanly behind #[cfg(feature = "gpu")]

use super::GpuContext;
use crate::solver::inproc_engines::InprocessingEngines;

#[test]
fn test_inproc_engines_gpu_lazy_init() {
    let mut engines = InprocessingEngines::new(10);

    // Before first access, no GPU context should exist.
    assert!(!engines.gpu_init_attempted);
    assert!(engines.gpu_context.is_none());

    // First access triggers initialization.
    let first = engines.gpu_context().is_some();

    // After first access, init was attempted (regardless of success).
    assert!(engines.gpu_init_attempted);

    // On a machine with a GPU adapter, the context must actually exist.
    if GpuContext::initialize().is_ok() {
        assert!(first, "GPU adapter available but lazy init returned None");
    }

    // Second access should not re-initialize (cached result).
    let attempted_before = engines.gpu_init_attempted;
    assert_eq!(engines.gpu_context().is_some(), first);
    assert_eq!(engines.gpu_init_attempted, attempted_before);
}

#[test]
fn test_inproc_engines_gpu_bve_pipeline_lazy_init() {
    let mut engines = InprocessingEngines::new(10);

    // BVE pipeline should be None initially.
    assert!(engines.gpu_bve_pipeline.is_none());

    // Accessing the pipeline triggers GPU context init + pipeline compilation.
    let available = engines.gpu_bve().is_some();

    // After access, both init steps were attempted.
    assert!(engines.gpu_init_attempted);
    assert!(engines.gpu_bve_pipeline_attempted);

    // On a machine with a GPU adapter, the pipeline must compile.
    if GpuContext::initialize().is_ok() {
        assert!(
            available,
            "GPU adapter available but BVE pipeline failed to initialize"
        );
    }
}

#[test]
fn test_gpu_subsume_threshold_gating() {
    use super::subsume::should_use_gpu;

    // Below threshold: should not use GPU.
    assert!(!should_use_gpu(0));
    assert!(!should_use_gpu(100));
    assert!(!should_use_gpu(9_999));

    // At threshold and within the bounded result bitset: should use GPU.
    assert!(should_use_gpu(10_000));
    assert!(should_use_gpu(25_000));

    // Above the result bitset cap: should stay on CPU without GPU init.
    assert!(!should_use_gpu(50_000));
}

#[test]
fn test_gpu_bve_threshold_gating() {
    use super::bve::GpuBvePipeline;

    // Below threshold: should not use GPU.
    assert!(!GpuBvePipeline::should_use_gpu(10, 10)); // 100 < 2048
    assert!(!GpuBvePipeline::should_use_gpu(45, 45)); // 2025 < 2048
    assert!(!GpuBvePipeline::should_use_gpu(0, 100)); // 0 pairs

    // At or above threshold: should use GPU.
    assert!(GpuBvePipeline::should_use_gpu(46, 46)); // 2116 >= 2048
    assert!(GpuBvePipeline::should_use_gpu(100, 100)); // 10000 >= 2048
}

#[test]
fn test_gpu_subsume_cpu_fallback_correctness() {
    use super::subsume::{cpu_subsume_check, gpu_subsume_check, SubsumedPair};

    // Create a clause set with known subsumption relationships.
    let c0 = vec![0u32, 3]; // {x0, ~x1}
    let c1 = vec![0u32, 3, 4]; // {x0, ~x1, x2} — subsumed by c0
    let c2 = vec![6u32, 8]; // {x3, x4}
    let c3 = vec![6u32, 8, 11]; // {x3, x4, ~x5} — subsumed by c2
    let c4 = vec![1u32, 2]; // {~x0, x1} — no subsumption
    let clauses: Vec<&[u32]> = vec![&c0, &c1, &c2, &c3, &c4];

    let cpu_pairs = cpu_subsume_check(&clauses);

    // Verify CPU finds the expected subsumptions.
    let mut cpu_sorted = cpu_pairs;
    cpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));
    assert!(cpu_sorted.contains(&SubsumedPair {
        subsumer: 0,
        subsumed: 1
    }));
    assert!(cpu_sorted.contains(&SubsumedPair {
        subsumer: 2,
        subsumed: 3
    }));

    // If GPU is available, verify it matches CPU. Skip only when no
    // adapter exists; any other init failure is a real bug.
    let ctx = match GpuContext::initialize() {
        Ok(ctx) => ctx,
        Err(super::GpuError::AdapterUnavailable { .. }) => return,
        Err(error) => panic!("GPU initialization failed: {error}"),
    };

    let gpu_pairs = gpu_subsume_check(&ctx, &clauses).expect("GPU check must succeed");
    let mut gpu_sorted = gpu_pairs;
    gpu_sorted.sort_by_key(|p| (p.subsumer, p.subsumed));
    assert_eq!(cpu_sorted, gpu_sorted, "GPU and CPU subsumption must match");
}

#[test]
fn test_gpu_pdr_push_cpu_fallback_correctness() {
    use super::pdr_push::{cpu_pdr_push_check, gpu_pdr_push_check};

    let l0 = vec![0u32, 3, 4]; // lemma: {x0, ~x1, x2}
    let l1 = vec![6u32, 2]; // lemma: {x3, x1}
    let f0 = vec![0u32, 3]; // frame: {x0, ~x1} — subsumes l0
    let f1 = vec![10u32]; // frame: {x5}

    let lemmas: Vec<&[u32]> = vec![&l0, &l1];
    let frame_clauses: Vec<&[u32]> = vec![&f0, &f1];

    let cpu_result = cpu_pdr_push_check(&lemmas, &frame_clauses);
    assert_eq!(cpu_result, vec![0]); // Only l0 is pushable

    // If GPU available, verify match. Skip only when no adapter exists.
    let ctx = match GpuContext::initialize() {
        Ok(ctx) => ctx,
        Err(super::GpuError::AdapterUnavailable { .. }) => return,
        Err(error) => panic!("GPU initialization failed: {error}"),
    };

    let gpu_result =
        gpu_pdr_push_check(&ctx, &lemmas, &frame_clauses).expect("GPU check must succeed");
    assert_eq!(cpu_result, gpu_result, "GPU and CPU PDR push must match");
}

/// Verify that the solver correctly falls back to CPU subsumption when
/// the clause count is below the GPU threshold.
#[test]
fn test_solver_subsume_small_formula_uses_cpu() {
    use crate::literal::{Literal, Variable};
    use crate::Solver;

    // Create a small formula (well below 10K clause threshold).
    let mut solver = Solver::new(10);
    for i in 0..5 {
        let v = Variable(i);
        solver.add_clause(vec![Literal::positive(v)]);
    }
    // Subsumption should work (CPU path) without panicking.
    // We can't directly call subsume() from outside the crate, but
    // we can verify solve() works, which exercises inprocessing.
    let result = solver.solve();
    assert!(
        matches!(result.into_inner(), crate::SatResult::Sat(_)),
        "small formula should be satisfiable"
    );
}
