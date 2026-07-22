// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! No-JIT counterparts for legacy BCP-JIT lifecycle hooks.
//!
//! BCP formula compilation was removed, but structural passes still call these
//! zero-cost hooks without feature gates. Keeping the stubs available in a
//! no-JIT build makes `default-features = false` a real, supported build mode.

use super::Solver;

impl Solver {
    #[inline]
    pub(crate) fn has_compiled_formula(&self) -> bool {
        false
    }

    #[inline]
    pub(crate) fn jit_invalidate_for_structural_pass(&mut self) {}

    #[inline]
    pub(crate) fn jit_recompile_after_inprocessing(&mut self, _had_compiled_formula: bool) {}

    #[inline]
    pub(crate) fn reattach_jit_watches(&mut self) -> usize {
        0
    }
}
