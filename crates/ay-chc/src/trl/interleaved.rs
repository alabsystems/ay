// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interleaved forward/backward TRL scheduler.
//!
//! Alternates single steps between forward and backward TRL solvers.
//! When one side produces a definitive Safe/Unsafe, the scheduler returns
//! immediately. When one side returns Unknown (exhausted), the other side
//! runs to completion alone.
//!
//! Semantics aligned with LoAT's interleaved scheduler:
//! - `reference/loat/src/interleaved/stepwise.hpp:7-14`
//! - `reference/loat/src/interleaved/interleaved.cpp:8-51`
//!
//! Part of #7327

use crate::engine_result::ChcEngineResult;

/// Trait for stepwise TRL analysis. Each call to `do_step()` performs one
/// unit of work and returns `None` when more work remains, or `Some(result)`
/// when a definitive answer is reached.
pub(crate) trait StepwiseTrl {
    fn do_step(&mut self) -> Option<ChcEngineResult>;
}

/// Interleaved forward/backward TRL scheduler.
///
/// Alternates one step at a time between forward and backward solvers.
/// Matches LoAT semantics: if one side returns Unknown, the other side
/// runs solo to completion. No cross-direction clause sharing.
pub(crate) struct InterleavedTrl<F, B> {
    forward: F,
    backward: B,
    active_is_forward: bool,
}

impl<F: StepwiseTrl, B: StepwiseTrl> InterleavedTrl<F, B> {
    pub(crate) fn new(forward: F, backward: B) -> Self {
        Self {
            forward,
            backward,
            active_is_forward: true, // forward goes first (LoAT convention)
        }
    }

    /// Run the interleaved scheduler to completion.
    ///
    /// Phase 1 (alternating): Alternate single steps between forward and
    /// backward. If the active side returns Safe/Unsafe, return immediately.
    /// If it returns Unknown, fall through to Phase 2.
    ///
    /// Phase 2 (solo): Run the passive side to completion. Return whatever
    /// it produces (including Unknown if it also exhausts).
    pub(crate) fn solve(&mut self) -> ChcEngineResult {
        // Phase 1: alternating round-robin
        loop {
            let result = if self.active_is_forward {
                self.forward.do_step()
            } else {
                self.backward.do_step()
            };

            match result {
                None => {
                    // Active made progress but no conclusion yet. Swap sides.
                    self.active_is_forward = !self.active_is_forward;
                }
                Some(ChcEngineResult::Unknown) => {
                    // Active side is exhausted. Run the passive side solo.
                    break;
                }
                Some(definitive) => {
                    // Safe or Unsafe — return immediately.
                    return definitive;
                }
            }
        }

        // Phase 2: run the passive side (opposite of current active) to completion.
        // The active side returned Unknown, so switch to the other one.
        self.active_is_forward = !self.active_is_forward;
        loop {
            let result = if self.active_is_forward {
                self.forward.do_step()
            } else {
                self.backward.do_step()
            };

            match result {
                None => continue, // more work remains
                Some(final_result) => return final_result,
            }
        }
    }
}

#[cfg(test)]
#[path = "interleaved_tests.rs"]
mod tests;
