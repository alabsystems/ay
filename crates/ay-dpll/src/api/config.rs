// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Configuration for constructing a [`Solver`] with pre-set options.
///
/// Use this to configure timeout, memory limits, and other solver parameters
/// at construction time rather than calling individual setter methods.
///
/// # Example
///
/// ```
/// use std::time::Duration;
/// use ay_dpll::api::{Logic, Solver, SolverConfig};
///
/// let config = SolverConfig::default()
///     .with_timeout(Duration::from_millis(5000))
///     .with_memory_limit(1024 * 1024 * 1024);
/// let mut solver = Solver::try_new_with_config(Logic::QfBv, config).unwrap();
/// // All check_sat calls will respect the 5s timeout
/// ```
#[derive(Debug, Clone, Default)]
#[must_use]
pub struct SolverConfig {
    /// Per-query timeout for check_sat calls.
    pub timeout: Option<Duration>,
    /// Process RSS memory limit in bytes.
    pub memory_limit: Option<usize>,
    /// Per-instance term memory limit in bytes.
    pub term_memory_limit: Option<usize>,
    /// Maximum learned clauses for SAT solver.
    pub learned_clause_limit: Option<usize>,
    /// Maximum clause DB size (bytes) for SAT solver.
    pub clause_db_bytes_limit: Option<usize>,
}

impl SolverConfig {
    /// Set the per-query timeout for check_sat calls.
    ///
    /// Each `check_sat` call computes a deadline from `Instant::now() + timeout`
    /// and returns `Unknown` with reason `Timeout` if the deadline expires.
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Set the process RSS memory limit in bytes.
    pub fn with_memory_limit(mut self, limit: usize) -> Self {
        self.memory_limit = Some(limit);
        self
    }

    /// Set the per-instance term memory limit in bytes.
    pub fn with_term_memory_limit(mut self, limit: usize) -> Self {
        self.term_memory_limit = Some(limit);
        self
    }

    /// Set the maximum learned clauses for the SAT solver.
    pub fn with_learned_clause_limit(mut self, limit: usize) -> Self {
        self.learned_clause_limit = Some(limit);
        self
    }

    /// Set the maximum clause DB size in bytes.
    pub fn with_clause_db_bytes_limit(mut self, limit: usize) -> Self {
        self.clause_db_bytes_limit = Some(limit);
        self
    }
}
