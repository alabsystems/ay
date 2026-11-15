// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded original-SMT CLI execution. In-tree self-check is recorded distinctly
//! from independent proof replay. Every remaining inventory obligation survives;
//! this adapter never grants ask closure or authenticates a consumer tuple.

mod assess;
mod execution;
mod selection;
mod snapshot;
#[cfg(test)]
mod tests;
mod types;

pub use execution::run_smt_cli;
pub use types::{
    DefaultObservation, SmtCliArgs, SmtCliBlocker, SmtCliCase, SmtCliRecord, SmtCliReport,
    SmtCliTerminal, SmtMemoryVariant,
};
