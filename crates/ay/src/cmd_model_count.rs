// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model Counting Competition command surface (`ay model-count`).
//!
//! Covers every MC-2026 track with exact arbitrary-precision counting via the
//! `ay-count` component-caching engine: `mc`/`pmc` (natural counts), `wmc`/
//! `pwmc` (exact rationals, zero/negative weights supported), and
//! `amc-complex` (complex rationals). Output follows the competition format
//! spec v1.2 (mandatory `s`, `c s type`, `c s [neg]log10-estimate`, and
//! `c s exact arb ...` lines).

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use ay_count::output::render;
use ay_count::parse::parse_instance;
use ay_count::{solve_instance_big_stack, SolveOptions};
use clap::Args;

/// Arguments for `ay model-count FILE`.
#[derive(Args, Clone)]
pub(crate) struct ModelCountArgs {
    /// Input file in the Model Counting Competition DIMACS-like format.
    #[arg(value_name = "FILE")]
    pub(crate) file: PathBuf,

    /// Component-cache budget in MiB.
    #[arg(long, value_name = "MIB", default_value_t = 4096)]
    pub(crate) cache_mb: usize,

    /// Print engine statistics as `c o` comment lines.
    #[arg(long)]
    pub(crate) stats: bool,

    /// Tree-decomposition time budget in seconds (0 disables TD branching
    /// scores; competition configs use 60-120).
    #[arg(long, value_name = "SECS", default_value_t = 0.0)]
    pub(crate) decot: f64,

    /// Phase-1 budget in seconds: solve without TD first; only on expiry
    /// compute the tree decomposition and re-solve. 0 = single phase.
    #[arg(long, value_name = "SECS", default_value_t = 10.0)]
    pub(crate) phase1: f64,

    /// Tree-decomposition score weight.
    #[arg(long, value_name = "W", default_value_t = 100.0)]
    pub(crate) decow: f64,

    /// Path to the FlowCutter binary (else AY_FLOWCUTTER env, the executable
    /// directory, or PATH).
    #[arg(long, value_name = "PATH")]
    pub(crate) flow_cutter: Option<PathBuf>,
}

/// Entry point dispatched from `main.rs`.
pub(crate) fn run(args: &ModelCountArgs) -> Result<()> {
    let content = fs::read_to_string(&args.file)
        .with_context(|| format!("failed to read {}", args.file.display()))?;
    let instance = match parse_instance(&content) {
        Ok(instance) => instance,
        Err(e) => {
            // Competition spec: parse/format errors must be reported; do not
            // emit a solution line.
            println!("c o PARSE ERROR: {e}");
            anyhow::bail!("parse error: {e}");
        }
    };
    let options = SolveOptions {
        cache_budget_bytes: args.cache_mb << 20,
        stats: args.stats,
        td_budget_secs: args.decot,
        phase1_secs: args.phase1,
        decow: args.decow,
        flow_cutter: args.flow_cutter.clone(),
    };
    let outcome = solve_instance_big_stack(instance, options);
    print!("{}", render(&outcome));
    Ok(())
}
