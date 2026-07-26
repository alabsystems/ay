// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Role-based tutorial tracks and solver-backed games.

use anyhow::Result;
use clap::{Subcommand, ValueEnum};

mod atlas;
mod engineers;
mod experts;
mod sudoku;

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
#[clap(rename_all = "kebab-case")]
pub(super) enum FeatureSection {
    Solving,
    Proofs,
    Optimization,
    Exploration,
    Integration,
    Tooling,
}

impl FeatureSection {
    const ALL: [Self; 6] = [
        Self::Solving,
        Self::Proofs,
        Self::Optimization,
        Self::Exploration,
        Self::Integration,
        Self::Tooling,
    ];

    const fn title(self) -> &'static str {
        match self {
            Self::Solving => "Solving",
            Self::Proofs => "Proofs",
            Self::Optimization => "Optimization",
            Self::Exploration => "Exploration",
            Self::Integration => "Integration",
            Self::Tooling => "Tooling",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
#[clap(rename_all = "kebab-case")]
pub(super) enum EngineerChapter {
    Build,
    Automation,
    Rust,
    Migration,
    Production,
}

impl EngineerChapter {
    const ALL: [Self; 5] = [
        Self::Build,
        Self::Automation,
        Self::Rust,
        Self::Migration,
        Self::Production,
    ];

    const fn title(self) -> &'static str {
        match self {
            Self::Build => "Build search programs, not search algorithms",
            Self::Automation => "Process automation and result contracts",
            Self::Rust => "Native Rust embedding",
            Self::Migration => "Migrate from Z3 one boundary at a time",
            Self::Production => "Budgets, evidence, and production rollout",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
#[clap(rename_all = "kebab-case")]
pub(super) enum ExpertChapter {
    Proofs,
    Incremental,
    Optimization,
    Theories,
    Research,
}

impl ExpertChapter {
    const ALL: [Self; 5] = [
        Self::Proofs,
        Self::Incremental,
        Self::Optimization,
        Self::Theories,
        Self::Research,
    ];

    const fn title(self) -> &'static str {
        match self {
            Self::Proofs => "Proof objects, checking, and trust boundaries",
            Self::Incremental => "Scopes, assumptions, cores, and warm sessions",
            Self::Optimization => "OMT, exact bounds, PB, MaxSAT, and MILP",
            Self::Theories => "Theory combinations, interpolation, and CHC",
            Self::Research => "Experiments, ablations, traces, and benchmarks",
        }
    }
}

#[derive(Subcommand)]
pub(super) enum PlayCommand {
    /// Check moves, ask for hints, and inspect a live 4x4 Sudoku encoding
    Sudoku,
}

pub(super) fn run_feature_atlas(selected: Option<FeatureSection>, interactive: bool) -> Result<()> {
    atlas::run(selected, interactive)
}

pub(super) fn run_engineer_course(
    selected: Option<EngineerChapter>,
    interactive: bool,
) -> Result<()> {
    engineers::run(selected, interactive)
}

pub(super) fn run_expert_course(selected: Option<ExpertChapter>, interactive: bool) -> Result<()> {
    experts::run(selected, interactive)
}

pub(super) fn run_game(command: &PlayCommand) -> Result<()> {
    match command {
        PlayCommand::Sudoku => sudoku::run(),
    }
}
