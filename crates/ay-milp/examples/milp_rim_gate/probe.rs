// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Instant, SystemTime};

use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::baseline::Row;
use crate::cli::BusyPolicy;
use crate::{GateError, GateResult};

const WATCHDOG_TIMEOUT_EXIT: i32 = 124;
const WATCHDOG_BREACH_EXIT: i32 = 86;

pub(crate) struct Resources {
    memlimit_mb: usize,
    nbcore: usize,
    headroom_mb: usize,
}

impl Resources {
    pub(crate) fn report(&self) {
        println!(
            "resource envelope: jobs=1 memlimit_mb={} nbcore={} headroom_mb={} enforcement=scripts/_oom_guard.py:run(grace=0)",
            self.memlimit_mb, self.nbcore, self.headroom_mb
        );
    }
}

pub(crate) struct Measurements {
    pub(crate) rows: Vec<Row>,
    pub(crate) missing: Vec<String>,
}

fn output_text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn tail(text: &str, limit: usize) -> String {
    let start = text
        .char_indices()
        .rev()
        .nth(limit.saturating_sub(1))
        .map_or(0, |(index, _)| index);
    text[start..].trim().to_owned()
}

fn parse_plan(text: &str) -> GateResult<Resources> {
    let fields: BTreeMap<&str, &str> = text
        .lines()
        .filter_map(|line| line.split_once('='))
        .collect();
    let number = |key: &str| {
        fields
            .get(key)
            .ok_or_else(|| GateError::setup(format!("OOM planner omitted {key}")))?
            .parse::<usize>()
            .map_err(|error| GateError::setup(format!("OOM planner returned bad {key}: {error}")))
    };
    if number("PLAN_JOBS")? != 1 {
        return Err(GateError::setup(
            "OOM planner did not preserve the serial jobs=1 run",
        ));
    }
    Ok(Resources {
        memlimit_mb: number("PLAN_MEMLIMIT_MB")?,
        nbcore: number("PLAN_NBCORE")?,
        headroom_mb: number("PLAN_HEADROOM_MB")?,
    })
}

pub(crate) fn plan_resources(repo: &Path) -> GateResult<Resources> {
    let output = Command::new("python3")
        .arg(repo.join("scripts/_oom_guard.py"))
        .args([
            "plan",
            "--jobs",
            "1",
            "--label",
            "milp-rim-gate",
            "--warn-concurrent-build",
        ])
        .current_dir(repo)
        .output()
        .map_err(|error| GateError::setup(format!("cannot run the OOM planner: {error}")))?;
    if !output.status.success() {
        return Err(GateError::setup(format!(
            "OOM resource planning failed: {}",
            tail(&output_text(&output.stderr), 2_000)
        )));
    }
    parse_plan(&output_text(&output.stdout))
}

fn load_average() -> Option<f64> {
    let text = fs::read_to_string("/proc/loadavg").ok()?;
    text.split_whitespace().next()?.parse().ok()
}

pub(crate) fn require_quiet_host(policy: BusyPolicy) -> GateResult<()> {
    if policy == BusyPolicy::AllowBusy {
        return Ok(());
    }
    let Some(load) = load_average() else {
        return Ok(());
    };
    let cpus = std::thread::available_parallelism().map_or(1, usize::from);
    if load > 0.35 * cpus as f64 {
        return Err(GateError::setup(format!(
            "load average {load:.1} on {cpus} cpus -- the rim pins are only deadline-free\n\
             while every instance finishes inside --limit. Wait, or pass --allow-busy."
        )));
    }
    Ok(())
}

fn cargo_probe(repo: &Path) -> GateResult<PathBuf> {
    let output = Command::new("cargo")
        .args([
            "test",
            "-p",
            "ay-milp",
            "--release",
            "--lib",
            "--no-run",
            "--message-format=json",
        ])
        .current_dir(repo)
        .output()
        .map_err(|error| GateError::setup(format!("cannot run Cargo: {error}")))?;
    if !output.status.success() {
        return Err(GateError::setup(format!(
            "cargo test --no-run failed:\n{}",
            tail(&output_text(&output.stderr), 2_000)
        )));
    }
    let mut executable = None;
    for line in output_text(&output.stdout).lines() {
        let Ok(message) = serde_json::from_str::<Value>(line) else {
            continue;
        };
        let is_library = message["target"]["kind"]
            .as_array()
            .is_some_and(|kinds| kinds.len() == 1 && kinds[0].as_str() == Some("lib"));
        if message["reason"].as_str() == Some("compiler-artifact")
            && message["target"]["name"].as_str() == Some("ay_milp")
            && is_library
        {
            executable = message["executable"].as_str().map(PathBuf::from);
        }
    }
    executable
        .filter(|path| path.is_file())
        .ok_or_else(|| GateError::setup("Cargo did not report an ay-milp lib test executable"))
}

fn report_provenance(path: &Path) -> GateResult<()> {
    let bytes = fs::read(path)?;
    let digest = format!("{:x}", Sha256::digest(bytes));
    let modified = path
        .metadata()?
        .modified()?
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_err(|error| {
            GateError::setup(format!("probe mtime predates the Unix epoch: {error}"))
        })?;
    println!("probe binary: {}", path.display());
    println!(
        "              sha256 {}  mtime_unix_s {}",
        &digest[..16],
        modified.as_secs()
    );
    Ok(())
}

pub(crate) fn resolve(requested: Option<&Path>, repo: &Path) -> GateResult<PathBuf> {
    let path = match requested {
        Some(path) if path.is_file() => path.to_owned(),
        Some(path) => {
            return Err(GateError::setup(format!(
                "probe binary not found at {}",
                path.display()
            )));
        }
        None => cargo_probe(repo)?,
    };
    report_provenance(&path)?;
    Ok(path)
}

fn find_model(name: &str, corpora: &[PathBuf]) -> Option<PathBuf> {
    for corpus in corpora {
        for extension in ["mps", "mps.gz"] {
            let path = corpus.join(format!("{name}.{extension}"));
            if path.is_file() {
                return Some(path);
            }
        }
    }
    None
}

fn parse_result(text: &str) -> Option<BTreeMap<&str, &str>> {
    let line = text
        .lines()
        .rev()
        .find(|line| line.starts_with("RIMRESULT "))?;
    Some(
        line.split_whitespace()
            .skip(1)
            .filter_map(|token| token.split_once('='))
            .collect(),
    )
}

fn failed_row(pin: &Row, status: String, raw: String, wall_s: f64) -> Row {
    Row {
        name: pin.name.clone(),
        class: pin.class.clone(),
        status,
        form: String::new(),
        switch_at: 0,
        p1_pivots: 0,
        pivots: 0,
        value: String::new(),
        tier: pin.tier.clone(),
        wall_s,
        raw: Some(raw),
    }
}

fn measured_row(pin: &Row, fields: &BTreeMap<&str, &str>, wall_s: f64) -> GateResult<Row> {
    let field = |key: &str| {
        fields
            .get(key)
            .copied()
            .ok_or_else(|| GateError::setup(format!("probe output omitted `{key}`")))
    };
    let integer = |key: &str| {
        field(key)?.parse::<i64>().map_err(|error| {
            GateError::setup(format!(
                "probe returned invalid `{key}` for {}: {error}",
                pin.name
            ))
        })
    };
    Ok(Row {
        name: pin.name.clone(),
        class: pin.class.clone(),
        status: field("status")?.to_owned(),
        form: field("form")?.to_owned(),
        switch_at: integer("switch_at")?,
        p1_pivots: integer("p1_pivots")?,
        pivots: integer("pivots")?,
        value: fields.get("value").copied().unwrap_or_default().to_owned(),
        tier: pin.tier.clone(),
        wall_s,
        raw: None,
    })
}

fn run_one(
    pin: &Row,
    model: &Path,
    probe: &Path,
    limit_secs: f64,
    resources: &Resources,
    repo: &Path,
) -> GateResult<Row> {
    let timeout = limit_secs * 2.0 + 120.0;
    let started = Instant::now();
    let output = Command::new("python3")
        .arg(repo.join("scripts/_oom_guard.py"))
        .args(["run", "--limit-mb"])
        .arg(resources.memlimit_mb.to_string())
        .args(["--timeout-s"])
        .arg(format!("{timeout:.3}"))
        .args(["--label"])
        .arg(format!("milp-rim:{}", pin.name))
        .arg("--")
        .arg(probe)
        .args([
            "exact::probe::rim",
            "--exact",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("RIM_INST", model)
        .env("RIM_SECS", (limit_secs.floor() as u64).to_string())
        .env("MEMLIMIT", resources.memlimit_mb.to_string())
        .env("NBCORE", resources.nbcore.to_string())
        .env_remove("RIM_FORCE")
        .env_remove("RIM_PARAMS")
        .env_remove("RIM_TRACE")
        .env_remove("RIM_ITERS")
        .current_dir(repo)
        .output()
        .map_err(|error| GateError::setup(format!("cannot run {}: {error}", pin.name)))?;
    let wall_s = (started.elapsed().as_secs_f64() * 1_000.0).round() / 1_000.0;
    let stdout = output_text(&output.stdout);
    let stderr = output_text(&output.stderr);
    if !output.status.success() {
        let code = output.status.code().unwrap_or(-1);
        let status = match code {
            WATCHDOG_TIMEOUT_EXIT => "HARNESS_TIMEOUT".to_owned(),
            WATCHDOG_BREACH_EXIT => "HARNESS_MEMOUT".to_owned(),
            other => format!("EXIT_{other}"),
        };
        return Ok(failed_row(
            pin,
            status,
            tail(&(stdout + &stderr), 600),
            wall_s,
        ));
    }
    let combined = stderr + &stdout;
    let Some(fields) = parse_result(&combined) else {
        return Ok(failed_row(
            pin,
            "NO_OUTPUT".to_owned(),
            tail(&combined, 600),
            wall_s,
        ));
    };
    match measured_row(pin, &fields, wall_s) {
        Ok(row) => Ok(row),
        Err(error) => Ok(failed_row(
            pin,
            "PARSE_ERROR".to_owned(),
            error.to_string(),
            wall_s,
        )),
    }
}

pub(crate) fn measure(
    pins: &[Row],
    probe: &Path,
    corpora: &[PathBuf],
    limit_secs: f64,
    resources: &Resources,
    repo: &Path,
) -> GateResult<Measurements> {
    let mut rows = Vec::with_capacity(pins.len());
    let mut missing = Vec::new();
    for pin in pins {
        let Some(model) = find_model(&pin.name, corpora) else {
            missing.push(pin.name.clone());
            continue;
        };
        rows.push(run_one(pin, &model, probe, limit_secs, resources, repo)?);
    }
    Ok(Measurements { rows, missing })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn result_parser_keeps_the_exact_rational() {
        let fields = parse_result(
            "noise\nRIMRESULT status=OPTIMAL form=reduced switch_at=0 p1_pivots=1 pivots=2 value=-123/47\n",
        );
        assert_eq!(
            fields.and_then(|row| row.get("value").copied()),
            Some("-123/47")
        );
    }
}
