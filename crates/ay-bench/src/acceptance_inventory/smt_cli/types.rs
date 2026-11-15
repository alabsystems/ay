// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{AcceptancePlan, CliStatus};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::PathBuf;

/// Fixed original request profiles. MachineDefault never supplies --memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SmtMemoryVariant {
    #[serde(rename = "serial-enforced-tree-4g")]
    Serial4GiB,
    #[serde(rename = "store-historical-2g")]
    Historical2GiB,
    #[serde(rename = "store-machine-default")]
    MachineDefault,
}
impl SmtMemoryVariant {
    pub(super) const fn policy(self) -> &'static str {
        match self {
            Self::Serial4GiB => "serial-enforced-tree-4g",
            Self::Historical2GiB => "store-historical-2g",
            Self::MachineDefault => "store-machine-default",
        }
    }
    pub(super) const fn explicit_mib(self) -> Option<usize> {
        match self {
            Self::Serial4GiB => Some(4096),
            Self::Historical2GiB => Some(2048),
            Self::MachineDefault => None,
        }
    }
}

/// One invocation owns this total timeout, including admission and all variants.
pub struct SmtCliArgs {
    pub selection: PathBuf,
    pub ay: PathBuf,
    pub out_dir: PathBuf,
    pub timeout_sec: f64,
}

#[derive(Debug, Clone, Serialize)]
pub struct SmtCliCase {
    pub input_id: String,
    pub request_ids: Vec<String>,
    pub repository: String,
    pub revision: String,
    pub original_path: String,
    pub path: PathBuf,
    pub sha256: String,
    pub size_bytes: u64,
    pub expected: CliStatus,
    pub timeout_ms: u64,
    pub variant: SmtMemoryVariant,
}

/// Unmet obligations remain explicit, including on a self-checked SAT/UNSAT.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SmtCliBlocker {
    IncompleteRequiredRoutes,
    UnfinishedRoute,
    TreePeakUnavailable,
    ConsumerTupleUnqualified,
    IndependentReplayNotRun,
    PerformanceComparisonNotRun,
    BinaryStampUnqualified,
    OriginalSourceRevisionUnqualified,
    Deadline,
    MemoryLimit,
    OutputIncomplete,
    ChildFailure,
    Unknown,
    WrongAnswer,
    StatsBindingMismatch,
    DefaultMemoryUnavailable,
    DefaultMemoryExceedsTreeEnvelope,
    DefaultMemoryChanged,
}

#[derive(Debug, Clone, Serialize)]
pub struct SmtCliRecord {
    pub case: SmtCliCase,
    pub binary: serde_json::Value,
    pub terminal: Option<SmtCliTerminal>,
    pub argv: Vec<String>,
    pub environment: BTreeMap<String, String>,
    pub observed_status: String,
    /// Only the pinned binary's fail-closed --self-check contract; not external replay.
    pub in_tree_self_check_passed: bool,
    pub independent_replay_passed: bool,
    pub observed_solver_memory_bytes: Option<u64>,
    pub default_observation: Option<DefaultObservation>,
    pub tree_memory_bytes: u64,
    pub execution_envelope: String,
    pub elapsed_ns: u64,
    /// Exact monotonic deadline offset within this invocation, never a renewed duration.
    pub deadline_from_run_start_ns: u64,
    pub stdout_sha256: String,
    pub stderr_sha256: String,
    pub blockers: Vec<SmtCliBlocker>,
    pub promotable_for_ask_closure: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct DefaultObservation {
    pub argv: Vec<String>,
    pub input_sha256: String,
    pub input_size_bytes: u64,
    pub solver_memory_bytes: Option<u64>,
    pub terminal: SmtCliTerminal,
    pub blockers: Vec<SmtCliBlocker>,
    pub stdout_sha256: String,
    pub stderr_sha256: String,
}

#[derive(Debug, Serialize)]
pub struct SmtCliReport {
    pub schema: &'static str,
    pub selection_sha256: String,
    pub owner_budget_ns: u64,
    pub observed_tree_peak_bytes: Option<u64>,
    pub inventory_sha256: String,
    pub plan: AcceptancePlan,
    pub binary: serde_json::Value,
    pub resources: serde_json::Value,
    pub records: Vec<SmtCliRecord>,
    pub blockers: Vec<SmtCliBlocker>,
    pub promotable_for_ask_closure: bool,
}

/// Reaped-child/capture observations. A missing exit or incomplete stream is a
/// refusal, never inferred successful cleanup or an accepted solver answer.
#[derive(Debug, Clone, Serialize)]
pub struct SmtCliTerminal {
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    pub memory_limit_exceeded: bool,
    pub original_deadline_expired: bool,
    pub stdout_complete: bool,
    pub stderr_complete: bool,
    pub errors: Vec<String>,
}
