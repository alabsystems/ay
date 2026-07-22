// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared resource admission for benchmark subprocesses.
//!
//! `scripts/_oom_guard.py` is the repository's single source of truth for RAM
//! headroom, job caps, and RSS-backstop behavior.  Native Rust harnesses use
//! its machine-readable `plan` output and attach its `rss_watchdog` to external
//! solver process groups through the `watch` sidecar.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt as _;

use crate::error::{BenchError, Result, WithContext as _};

const WATCHDOG_BREACH_EXIT: i32 = 86;

/// Persistable resource envelope returned by `_oom_guard.py plan`.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub(crate) struct ResourcePlan {
    pub requested_jobs: usize,
    pub jobs: usize,
    pub memlimit_mb_per_child: usize,
    pub nbcore_per_child: usize,
    pub headroom_mb: usize,
    pub planner: String,
}

impl ResourcePlan {
    /// Canonical execution envelope used when deciding whether two benchmark
    /// rows may be compared. Requested parallelism and planner location are
    /// provenance, while these four values are the admitted/enforced limits.
    pub(crate) fn execution_envelope(&self) -> String {
        format!(
            "oom-guard-v1:jobs={};memlimit_mb={};nbcore={};headroom_mb={}",
            self.jobs, self.memlimit_mb_per_child, self.nbcore_per_child, self.headroom_mb
        )
    }

    pub(crate) fn same_execution_envelope(&self, other: &Self) -> bool {
        self.jobs == other.jobs
            && self.memlimit_mb_per_child == other.memlimit_mb_per_child
            && self.nbcore_per_child == other.nbcore_per_child
            && self.headroom_mb == other.headroom_mb
    }
}

/// A planned envelope plus the executable planner used to enforce it.
#[derive(Debug, Clone)]
pub(crate) struct PlannedResources {
    pub plan: ResourcePlan,
    guard_script: PathBuf,
}

impl PlannedResources {
    /// Ask the repository OOM guard to cap `requested_jobs` and split RAM/CPU.
    pub fn plan(repo_root: &Path, requested_jobs: usize, label: &str) -> Result<Self> {
        let requested_jobs = requested_jobs.max(1);
        let guard_script = repo_root.join("scripts").join("_oom_guard.py");
        if !guard_script.is_file() {
            return Err(BenchError::msg(format!(
                "required resource planner is missing: {}",
                guard_script.display()
            )));
        }

        let mut command = Command::new("python3");
        command
            .arg(&guard_script)
            .arg("plan")
            .arg("--jobs")
            .arg(requested_jobs.to_string())
            .arg("--label")
            .arg(label);
        // Unit tests invoke focused fake-solver harnesses from a live
        // `cargo test` parent. Production binaries retain the strict build
        // exclusion; tests exercise that policy directly in _oom_guard.py.
        #[cfg(not(test))]
        command.arg("--warn-concurrent-build");
        let output = command.output().with_bench_context(|| {
            format!(
                "running resource planner {} for {label}",
                guard_script.display()
            )
        })?;

        if !output.stderr.is_empty() {
            eprint!("{}", String::from_utf8_lossy(&output.stderr));
        }
        if !output.status.success() {
            return Err(BenchError::msg(format!(
                "resource planner {} exited with {}",
                guard_script.display(),
                output.status
            )));
        }

        let plan_output = String::from_utf8_lossy(&output.stdout);
        let values = parse_plan_output(&plan_output)?;
        let jobs = plan_value(&values, "PLAN_JOBS")?;
        let memlimit_mb_per_child = plan_value(&values, "PLAN_MEMLIMIT_MB")?;
        let nbcore_per_child = plan_value(&values, "PLAN_NBCORE")?;
        let headroom_mb = plan_value(&values, "PLAN_HEADROOM_MB")?;
        if jobs == 0 || jobs > requested_jobs {
            return Err(BenchError::msg(format!(
                "resource planner returned invalid job count {jobs} for request {requested_jobs}"
            )));
        }
        if memlimit_mb_per_child == 0 {
            return Err(BenchError::msg(
                "resource planner returned PLAN_MEMLIMIT_MB=0; refusing to spawn an unenveloped child",
            ));
        }
        if nbcore_per_child == 0 {
            return Err(BenchError::msg("resource planner returned PLAN_NBCORE=0"));
        }

        Ok(Self {
            plan: ResourcePlan {
                requested_jobs,
                jobs,
                memlimit_mb_per_child,
                nbcore_per_child,
                headroom_mb,
                planner: guard_script.display().to_string(),
            },
            guard_script,
        })
    }

    /// Attach `_oom_guard.rss_watchdog` to an already isolated child group.
    pub fn watch_external_child(&self, child: &Child, label: &str) -> Result<RssWatchdog> {
        let sidecar = Command::new("python3")
            .arg(&self.guard_script)
            .arg("watch")
            .arg("--pid")
            .arg(child.id().to_string())
            .arg("--limit-mb")
            .arg(self.plan.memlimit_mb_per_child.to_string())
            .arg("--grace-mb")
            .arg("0")
            .arg("--label")
            .arg(label)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .spawn()
            .with_bench_context(|| {
                format!(
                    "starting RSS watchdog {} for child {}",
                    self.guard_script.display(),
                    child.id()
                )
            })?;
        Ok(RssWatchdog {
            sidecar: Some(sidecar),
        })
    }

    #[cfg(test)]
    pub(crate) fn for_test(repo_root: &Path, memlimit_mb_per_child: usize) -> Self {
        Self {
            plan: ResourcePlan {
                requested_jobs: 1,
                jobs: 1,
                memlimit_mb_per_child,
                nbcore_per_child: 1,
                headroom_mb: 0,
                planner: "test".to_string(),
            },
            guard_script: repo_root.join("scripts").join("_oom_guard.py"),
        }
    }
}

/// Handle for one `_oom_guard.py watch` sidecar.
pub(crate) struct RssWatchdog {
    sidecar: Option<Child>,
}

impl RssWatchdog {
    /// Reap the sidecar and report whether it killed the solver for memory.
    pub fn finish(mut self) -> Result<bool> {
        let Some(mut sidecar) = self.sidecar.take() else {
            return Ok(false);
        };
        let status = match sidecar.wait_timeout(Duration::from_secs(12))? {
            Some(status) => status,
            None => {
                let _ = sidecar.kill();
                let _ = sidecar.wait();
                return Err(BenchError::msg(
                    "RSS watchdog did not exit after the solver was reaped",
                ));
            }
        };
        match status.code() {
            Some(0) => Ok(false),
            Some(WATCHDOG_BREACH_EXIT) => Ok(true),
            _ => Err(BenchError::msg(format!(
                "RSS watchdog exited unexpectedly with {status}"
            ))),
        }
    }
}

impl Drop for RssWatchdog {
    fn drop(&mut self) {
        if let Some(sidecar) = self.sidecar.as_mut() {
            let _ = sidecar.kill();
            let _ = sidecar.wait();
        }
    }
}

/// Put a solver and all descendants in a dedicated process group so timeout
/// and RSS enforcement cover the complete tree.
#[cfg(unix)]
pub(crate) fn isolate_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    command.process_group(0);
}

#[cfg(not(unix))]
pub(crate) fn isolate_process_group(_command: &mut Command) {}

/// Kill and reap an isolated solver process group.
pub(crate) fn terminate_process_group(child: &mut Child) {
    #[cfg(unix)]
    {
        if let Ok(pid) = i32::try_from(child.id()) {
            let pgid = nix::unistd::Pid::from_raw(pid);
            let _ = nix::sys::signal::killpg(pgid, nix::sys::signal::Signal::SIGKILL);
        }
    }
    #[cfg(not(unix))]
    {
        let _ = child.kill();
    }
    let _ = child.wait();
}

fn parse_plan_output(output: &str) -> Result<BTreeMap<&str, usize>> {
    let mut values = BTreeMap::new();
    for line in output.lines() {
        let Some((key, value)) = line.trim().split_once('=') else {
            continue;
        };
        if !key.starts_with("PLAN_") {
            continue;
        }
        let value = value.parse::<usize>().map_err(|_| {
            BenchError::msg(format!("resource planner returned invalid {key}={value:?}"))
        })?;
        values.insert(key, value);
    }
    Ok(values)
}

fn plan_value(values: &BTreeMap<&str, usize>, key: &'static str) -> Result<usize> {
    values
        .get(key)
        .copied()
        .ok_or_else(|| BenchError::msg(format!("resource planner omitted {key}")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_complete_plan_without_shell_evaluation() {
        let parsed = parse_plan_output(
            "PLAN_JOBS=3\nPLAN_MEMLIMIT_MB=2048\nPLAN_NBCORE=2\nPLAN_HEADROOM_MB=16000\n",
        )
        .expect("parse plan");
        assert_eq!(plan_value(&parsed, "PLAN_JOBS").unwrap(), 3);
        assert_eq!(plan_value(&parsed, "PLAN_MEMLIMIT_MB").unwrap(), 2048);
    }

    #[test]
    fn rejects_non_numeric_plan_values() {
        let err = parse_plan_output("PLAN_JOBS=$(bad)\n").expect_err("must reject");
        assert!(err.to_string().contains("invalid PLAN_JOBS"));
    }
}
