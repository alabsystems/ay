// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{SmtCliBlocker as Blocker, SmtCliCase};
use crate::environment::SolverProvenance;
use serde_json::Value;

pub(super) struct Assessment {
    pub status: String,
    pub checked: bool,
    pub memory: Option<u64>,
    pub blockers: Vec<Blocker>,
}

/// Parse exact original-run telemetry, never recover a success from a partial
/// transcript, contradictory verdict, foreign binary stamp or wrong dialect.
pub(super) fn assess(
    case: &SmtCliCase,
    binary: &SolverProvenance,
    stdout: &str,
    stderr: &str,
    exit: Option<i32>,
    timed_out: bool,
    memout: bool,
    default_memory: Option<u64>,
) -> Assessment {
    let mut blockers = Vec::new();
    if timed_out {
        blockers.push(Blocker::Deadline);
    }
    if memout {
        blockers.push(Blocker::MemoryLimit);
    }
    let verdicts = stdout
        .lines()
        .chain(stderr.lines())
        .filter_map(crate::resource::solver_verdict_line)
        .count();
    let stdout_verdicts = stdout
        .lines()
        .map(str::trim)
        .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
        .count();
    let status = crate::resource::strict_solver_verdict(stdout, stderr, exit).to_owned();
    if verdicts != 1 || stdout_verdicts != 1 || exit != Some(0) {
        blockers.push(Blocker::ChildFailure);
    }
    if status == "unknown" {
        blockers.push(Blocker::Unknown);
    } else if status != case.expected.as_str() {
        blockers.push(Blocker::WrongAnswer);
    }
    let stats = stats(stdout, stderr);
    let memory = stats
        .as_ref()
        .and_then(|stats| stats.get("resource.memory_limit_bytes"))
        .and_then(Value::as_u64)
        .filter(|n| *n > 0);
    let same_stats = stats.as_ref().is_some_and(|stats| {
        stats.get("mode").and_then(Value::as_str) == Some("smt")
            && stats.get("result").and_then(Value::as_str) == Some(status.as_str())
            && stats.pointer("/ay_build/commit").and_then(Value::as_str)
                == Some(binary.build_commit.as_str())
            && stats.pointer("/ay_build/stamp").and_then(Value::as_str)
                == Some(binary.build_stamp.as_str())
            && stats.pointer("/ay_build/version").and_then(Value::as_str)
                == Some(binary.build_version.as_str())
            && stats
                .pointer("/ay_build/datetime_utc")
                .and_then(Value::as_str)
                == Some(binary.build_datetime_utc.as_str())
    });
    if !same_stats {
        blockers.push(Blocker::StatsBindingMismatch);
    }
    match case.variant.explicit_mib() {
        Some(mib) if memory != Some(mib as u64 * 1024 * 1024) => {
            blockers.push(Blocker::StatsBindingMismatch)
        }
        None if default_memory.is_none() || memory.is_none() => {
            blockers.push(Blocker::DefaultMemoryUnavailable)
        }
        None if memory != default_memory => blockers.push(Blocker::DefaultMemoryChanged),
        _ => {}
    }
    let stamp_known = binary.build_commit.len() == 40
        && binary.build_commit.bytes().all(|b| b.is_ascii_hexdigit())
        && !binary.build_stamp.is_empty()
        && !binary.build_stamp.contains("unknown")
        && binary.build_datetime_utc != "unknown"
        && binary.build_version != "unknown";
    if !stamp_known {
        blockers.push(Blocker::BinaryStampUnqualified);
    }
    Assessment {
        status,
        checked: blockers.is_empty(),
        memory,
        blockers,
    }
}

fn stats(stdout: &str, stderr: &str) -> Option<Value> {
    let mut result = None;
    for line in stdout.lines().chain(stderr.lines()) {
        let line = line.trim();
        if !line.starts_with('{') {
            continue;
        }
        let value: Value = serde_json::from_str(line).ok()?;
        if value.get("mode").is_none() {
            continue;
        }
        if result.is_some() {
            return None;
        }
        result = Some(value);
    }
    result
}
