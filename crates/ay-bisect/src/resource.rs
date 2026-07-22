// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `_oom_guard.py` admission planning for parallel bisect trials.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::{BisectError, Result};

const EMBEDDED_OOM_GUARD: &str = include_str!("../../../scripts/_oom_guard.py");

#[derive(Debug, Clone, PartialEq, Eq)]
enum PlannerSource {
    Checkout(PathBuf),
    Embedded,
}

impl PlannerSource {
    fn provenance(&self) -> String {
        match self {
            Self::Checkout(path) => path.display().to_string(),
            Self::Embedded => "embedded:scripts/_oom_guard.py".to_string(),
        }
    }

    fn command(&self) -> Command {
        let mut command = Command::new("python3");
        match self {
            Self::Checkout(path) => {
                command.arg(path);
            }
            // Execute the build-time copy of the repository's authoritative
            // planner. This keeps standalone installed binaries usable without
            // creating a second Rust implementation whose policy could drift.
            Self::Embedded => {
                command.arg("-c").arg(EMBEDDED_OOM_GUARD);
            }
        }
        command
    }
}

/// Persistable resource envelope applied to every concrete AY trial.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourcePlan {
    pub requested_jobs: usize,
    pub jobs: usize,
    pub memlimit_mb_per_child: usize,
    pub nbcore_per_child: usize,
    pub headroom_mb: usize,
    pub planner: String,
}

pub(crate) fn plan(requested_jobs: usize, ay_binary: &Path) -> Result<ResourcePlan> {
    let requested_jobs = requested_jobs.max(1);
    let planner =
        locate_planner(ay_binary).map_or(PlannerSource::Embedded, PlannerSource::Checkout);
    let output = planner
        .command()
        .arg("plan")
        .arg("--jobs")
        .arg(requested_jobs.to_string())
        .arg("--label")
        .arg("ay-bisect")
        .arg("--warn-concurrent-build")
        .output()
        .map_err(|source| BisectError::SpawnFailed {
            binary: "python3".to_string(),
            source,
        })?;
    if !output.stderr.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
    }
    if !output.status.success() {
        return Err(BisectError::ResourcePlan {
            message: format!("{} exited with {}", planner.provenance(), output.status),
        });
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let values = parse_plan(&stdout)?;
    let jobs = value(&values, "PLAN_JOBS")?;
    let memlimit_mb_per_child = value(&values, "PLAN_MEMLIMIT_MB")?;
    let nbcore_per_child = value(&values, "PLAN_NBCORE")?;
    let headroom_mb = value(&values, "PLAN_HEADROOM_MB")?;
    if jobs == 0 || jobs > requested_jobs || memlimit_mb_per_child == 0 || nbcore_per_child == 0 {
        return Err(BisectError::ResourcePlan {
            message: format!(
                "invalid plan: requested_jobs={requested_jobs} jobs={jobs} memory={memlimit_mb_per_child}MiB NBCORE={nbcore_per_child}"
            ),
        });
    }
    Ok(ResourcePlan {
        requested_jobs,
        jobs,
        memlimit_mb_per_child,
        nbcore_per_child,
        headroom_mb,
        planner: planner.provenance(),
    })
}

fn locate_planner(ay_binary: &Path) -> Option<PathBuf> {
    let mut starts = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        starts.push(cwd);
    }
    let binary = ay_binary
        .canonicalize()
        .unwrap_or_else(|_| ay_binary.to_path_buf());
    if let Some(parent) = binary.parent() {
        starts.push(parent.to_path_buf());
    }
    starts.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")));
    for start in starts {
        for ancestor in start.ancestors() {
            let candidate = ancestor.join("scripts").join("_oom_guard.py");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

fn parse_plan(output: &str) -> Result<BTreeMap<&str, usize>> {
    let mut values = BTreeMap::new();
    for line in output.lines() {
        let Some((key, raw)) = line.trim().split_once('=') else {
            continue;
        };
        if !key.starts_with("PLAN_") {
            continue;
        }
        let parsed = raw
            .parse::<usize>()
            .map_err(|_| BisectError::ResourcePlan {
                message: format!("invalid {key}={raw:?}"),
            })?;
        values.insert(key, parsed);
    }
    Ok(values)
}

fn value(values: &BTreeMap<&str, usize>, key: &'static str) -> Result<usize> {
    values
        .get(key)
        .copied()
        .ok_or_else(|| BisectError::ResourcePlan {
            message: format!("planner omitted {key}"),
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_parser_is_strict_and_does_not_evaluate_shell() {
        let err = parse_plan("PLAN_JOBS=$(oops)\n").expect_err("reject shell text");
        assert!(err.to_string().contains("invalid PLAN_JOBS"));
    }

    #[test]
    fn locates_repository_planner() {
        let planner = locate_planner(Path::new("target/debug/ay")).expect("planner");
        assert!(planner.ends_with("scripts/_oom_guard.py"));
    }

    #[test]
    fn embedded_planner_is_the_authoritative_script_and_reports_provenance() {
        let source = PlannerSource::Embedded;
        assert_eq!(source.provenance(), "embedded:scripts/_oom_guard.py");
        let output = source
            .command()
            .args(["plan", "--jobs", "1", "--label", "ay-bisect-test"])
            .output()
            .expect("run embedded planner");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        let values = parse_plan(&stdout).expect("parse plan");
        assert_eq!(value(&values, "PLAN_JOBS").unwrap(), 1);
        assert!(value(&values, "PLAN_MEMLIMIT_MB").unwrap() > 0);
    }
}
