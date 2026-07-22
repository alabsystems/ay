// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TRL Kani verification harnesses.
//!
//! Previous harnesses were deleted in P1 formal_proofs audit:
//! - proof_learned_relations_monotonic: tested Vec::push semantics, not TRL logic
//! - proof_loop_detection_correct: assumed start<=end, then asserted it
//! - proof_trace_id_bounds: asserted id < len inside for id in 0..len
//! - proof_blocking_clause_depth_valid: asserted end+1 > end (trivially true)
//! - proof_backtrack_preserves_invariant: followed directly from assume constraints
//!
//! Replacement invariant tests that exercise real AY Trace/DependencyGraph code
//! live in trl/tests.rs (test_loop_detection_*, test_trace_clear_*, test_graph_intern_*).
//!
//! Real TRL Kani harnesses require either:
//! 1. A CBMC-tractable abstraction of DependencyGraph (FxHashSet blocks unwinding)
//! 2. Targeted harnesses for individual pure functions extracted from TRL
