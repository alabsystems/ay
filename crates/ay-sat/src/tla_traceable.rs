// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared trait for solvers that emit TLA2-format JSONL traces.
//!
//! Eliminates duplicated enable/env-check boilerplate across Solver, PdrSolver,
//! and KindSolver.  Each implementor provides its TLA module name and variable
//! list; the trait supplies the common `maybe_enable_tla_trace_from_env` logic.

/// Trait for solver types that support TLA2 JSONL trace emission.
///
/// Implementors store an `Option<TlaTraceWriter>` and provide the TLA+ module
/// name and variable list that match their corresponding TLA+ spec.
pub trait TlaTraceable {
    /// TLA+ module name (e.g. `"cdcl_test"`, `"pdr_test"`, `"kind_test"`).
    fn tla_module() -> &'static str;

    /// TLA+ variable names that appear in every trace step.
    fn tla_variables() -> &'static [&'static str];

    /// TLA+ transition operators that may appear in trace action metadata.
    ///
    /// Solvers without action metadata may keep the empty default.
    fn tla_actions() -> &'static [&'static str] {
        &[]
    }

    /// Enable TLA2 JSONL trace emission, writing to `path`.
    ///
    /// Must be called before `solve()`.  Implementations typically store the
    /// writer and may emit an initial step (index 0).
    fn enable_tla_trace(&mut self, path: &str, module: &str, variables: &[&str]);

    /// Enable trace output when `AY_TRACE_FILE` is set.
    ///
    /// This default implementation reads the environment variable and delegates
    /// to [`enable_tla_trace`](Self::enable_tla_trace) with the implementor's
    /// module and variables.
    fn maybe_enable_tla_trace_from_env(&mut self) {
        if !ay_core::trace_file_available() {
            return;
        }
        let Some(path) = &ay_core::trace_config().trace_file_path else {
            return;
        };
        self.enable_tla_trace(path, Self::tla_module(), Self::tla_variables());
    }
}
