// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::io;
use thiserror::Error;

/// Errors from the solver driver.
#[derive(Debug, Error)]
pub enum SolverError {
    #[error("I/O error: {0}")]
    IoError(#[source] io::Error),
    #[error("solver error: {0}")]
    SolverError(String),
    #[error("solver produced no output")]
    EmptyOutput,
    #[error("unexpected solver output: {0}")]
    UnexpectedOutput(String),
    #[error("objective '{0}' not in model")]
    MissingObjective(String),
    #[error("cannot parse integer: {0}")]
    ParseIntError(String),
}

impl From<io::Error> for SolverError {
    fn from(e: io::Error) -> Self {
        Self::IoError(e)
    }
}
