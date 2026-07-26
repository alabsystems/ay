// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! ay-bench library — competition-standard benchmarking for AY.
//!
//! This crate provides the benchmarking runner and scoring engines.
//! The binary entry point has moved to the unified ay CLI (`ay bench`).

pub mod campaign;
pub mod chc_gate;
pub mod cross_verify;
pub mod db;
pub mod diff;
pub mod diff_markdown;
pub mod environment;
pub mod error;
pub mod features;
pub mod harvest;
pub mod native;
mod resource;
pub mod runner;
pub mod sat_delta;
pub mod sat_mirror_manifest;
pub mod scoring;

pub use error::{BenchError, Result, WithContext};
pub use resource::{
    effective_execution_envelope, GuardedCapturedOutput, GuardedTranscriptOutput, PlannedResources,
    ResourcePlan, ENFORCEMENT_AY_MEMORY_RSS_V1, ENFORCEMENT_RSS_WATCHDOG_V1,
    GUARDED_TRANSCRIPT_INPUT_LIMIT, GUARDED_TRANSCRIPT_STREAM_LIMIT,
};
