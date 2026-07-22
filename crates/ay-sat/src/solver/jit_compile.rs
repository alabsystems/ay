// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-BCP JIT compilation for the SAT solver.
//!
//! BCP JIT compilation (CompiledFormula, per-variable propagation functions)
//! was removed in #8517. This file retains:
//! - The conflict analysis JIT processor (non-BCP, used by conflict_analysis.rs)
//! - No-op stubs for methods still referenced from non-cfg-gated call sites
//!   (inprocessing_schedule, arena_gc, etc.)

use super::*;

impl Solver {
    /// Compile the JIT conflict analysis processor.
    ///
    /// The conflict processor JIT-compiles the hot inner loop of 1UIP
    /// conflict analysis (seen-flag read/modify/write + level classification)
    /// into native code, reducing overhead in the most latency-sensitive path.
    pub(super) fn compile_conflict_processor(&mut self) {
        if self.cold.jit_disabled {
            return;
        }
        let num_vars = self.var_data.len();
        // Recompile if capacity is insufficient for current var count.
        if let Some(ref proc) = self.jit_conflict_processor {
            if proc.capacity() >= num_vars {
                return;
            }
            // Capacity too small — drop and recompile below.
        }
        match ay_jit::conflict_jit::compile_conflict_processor(num_vars) {
            Ok(processor) => {
                tracing::debug!(
                    "JIT: conflict analysis processor compiled (capacity={})",
                    num_vars,
                );
                self.jit_conflict_output.resize(num_vars);
                self.jit_conflict_processor = Some(processor);
                // Register with code cache for memory tracking.
                if let Some(ref proc) = self.jit_conflict_processor {
                    let bytes = proc.allocated_bytes();
                    self.cold
                        .code_cache
                        .register_allocation(ay_jit::CacheSlot::ConflictProcessor, bytes);
                }
            }
            Err(e) => {
                tracing::debug!("JIT: conflict processor compilation failed: {e}");
            }
        }
    }

    /// Install current-mode SAT native helpers after preprocessing.
    ///
    /// This keeps scalar CDCL authoritative: if the native helper is not
    /// requested, profile metadata is missing, compilation is disabled, or
    /// compilation fails, the solver simply continues on the scalar path.
    pub(super) fn install_sat_native_helpers_for_current_mode_at_solver_start(&mut self) {
        if !sat_native_helpers_current_mode_requested() || self.cold.jit_disabled {
            return;
        }
        if !sat_native_helper_competition_metadata_present() {
            tracing::debug!("SAT native helpers skipped: missing SAT competition profile metadata");
            return;
        }

        self.compile_conflict_processor();
    }

    // ══════════════════════════════════════════════════════════════════════
    // No-op stubs for BCP JIT methods (#8517).
    //
    // These methods were part of the BCP JIT infrastructure. Their call
    // sites in inprocessing_schedule.rs, arena_gc.rs, etc. are not behind
    // #[cfg(feature = "jit")] gates. Rather than cfg-gating dozens of
    // call sites, we provide no-op stubs so the code compiles cleanly.
    // These stubs have zero runtime cost.
    // ══════════════════════════════════════════════════════════════════════

    /// No-op: BCP JIT formula compilation removed (#8517).
    #[inline]
    pub(crate) fn has_compiled_formula(&self) -> bool {
        false
    }

    /// No-op: BCP JIT structural invalidation removed (#8517).
    #[inline]
    pub(crate) fn jit_invalidate_for_structural_pass(&mut self) {}

    /// No-op: BCP JIT recompilation after inprocessing removed (#8517).
    #[inline]
    pub(crate) fn jit_recompile_after_inprocessing(&mut self, _had_compiled_formula: bool) {}

    /// No-op: BCP JIT watch reattachment removed (#8517).
    #[inline]
    pub(crate) fn reattach_jit_watches(&mut self) -> usize {
        0
    }
}

fn sat_native_helpers_current_mode_requested() -> bool {
    std::env::var("AY_COMPETITION_JIT_MODE")
        .ok()
        .is_some_and(|value| value.trim().eq_ignore_ascii_case("current"))
}

fn sat_native_helper_competition_metadata_present() -> bool {
    trimmed_env_value("AY_SAT_COMPETITION_PROFILE").is_some()
        && trimmed_env_value("AY_SAT_PROFILE_ID").is_some()
}

fn trimmed_env_value(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}
