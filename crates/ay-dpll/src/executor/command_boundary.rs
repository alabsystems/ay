// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed command-publication boundaries and native continuation adapters.

use super::*;

/// Complete authority/publication contract for one command execution.
/// Combining origin and publication prevents authored-but-unpublished states.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CommandExecutionBoundary {
    GenericText,
    AuthoredText,
    NativeMaxSmtTextContinuation,
    NativeOptimization,
}

impl Executor {
    /// Run generic check-sat routing without consuming its linear result at a
    /// text boundary; the native optimization wrapper consumes it instead.
    pub(crate) fn execute_native_optimization_check_sat(&mut self) -> Result<SolveResult> {
        stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            self.execute_stack_guarded(
                &Command::CheckSat,
                CommandExecutionBoundary::NativeOptimization,
            )?;
            Ok(self.last_result.clone().unwrap_or(SolveResult::Unknown))
        })
    }

    /// Continue an already-started native MaxSMT query through generic text
    /// admission without replenishing its outer resource envelopes.
    pub(crate) fn execute_native_maxsmt_check_sat(&mut self) -> Result<Option<String>> {
        stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            self.execute_stack_guarded(
                &Command::CheckSat,
                CommandExecutionBoundary::NativeMaxSmtTextContinuation,
            )
        })
    }
}
