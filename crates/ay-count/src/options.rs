// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fmt;
use std::time::{Duration, Instant};

use crate::engine::EngineConfig;

/// Options for a solve run.
pub struct SolveOptions {
    /// Component-cache budget in bytes.
    pub cache_budget_bytes: usize,
    /// Attach engine statistics to the outcome.
    pub stats: bool,
    /// Tree-decomposition time budget in seconds (0 disables TD scoring).
    /// Must be finite, non-negative, and representable as a [`Duration`].
    pub td_budget_secs: f64,
    /// Phase-1 budget: solve WITHOUT TD scores for this long first; only on
    /// expiry compute the tree decomposition and re-solve (easy instances
    /// never pay the TD cost). 0 = single-phase. Must be finite, non-negative,
    /// and representable as a deadline.
    pub phase1_secs: f64,
    /// TD score weight (`decow`; competition value 100). Must be finite and
    /// non-negative.
    pub decow: f64,
    /// Explicit FlowCutter binary path (else `AY_FLOWCUTTER` env / exe dir /
    /// PATH).
    pub flow_cutter: Option<std::path::PathBuf>,
}

impl SolveOptions {
    /// Validate numeric options before starting a solve.
    ///
    /// # Errors
    ///
    /// Returns the first field that is non-finite, negative, cannot be
    /// represented as a duration, or cannot form an [`Instant`] deadline.
    pub fn validate(&self) -> Result<(), SolveOptionsError> {
        let td_budget = duration(self.td_budget_secs, "td_budget_secs")?;
        let phase1 = duration(self.phase1_secs, "phase1_secs")?;
        let now = Instant::now();
        if now.checked_add(td_budget).is_none() {
            return Err(SolveOptionsError::new("td_budget_secs"));
        }
        if now.checked_add(phase1).is_none() {
            return Err(SolveOptionsError::new("phase1_secs"));
        }
        if !self.decow.is_finite() || self.decow < 0.0 {
            return Err(SolveOptionsError::new("decow"));
        }
        Ok(())
    }
}

fn duration(value: f64, field: &'static str) -> Result<Duration, SolveOptionsError> {
    Duration::try_from_secs_f64(value).map_err(|_| SolveOptionsError::new(field))
}

impl Default for SolveOptions {
    fn default() -> Self {
        Self {
            cache_budget_bytes: EngineConfig::default().cache_budget_bytes,
            stats: false,
            td_budget_secs: 0.0,
            phase1_secs: 10.0,
            decow: 100.0,
            flow_cutter: None,
        }
    }
}

/// Invalid numeric field in [`SolveOptions`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolveOptionsError {
    field: &'static str,
}

impl SolveOptionsError {
    const fn new(field: &'static str) -> Self {
        Self { field }
    }

    /// Name of the invalid [`SolveOptions`] field.
    pub const fn field(self) -> &'static str {
        self.field
    }
}

impl fmt::Display for SolveOptionsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid solve option `{}`: expected a finite, non-negative supported value",
            self.field
        )
    }
}

impl std::error::Error for SolveOptionsError {}
