// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native Rust benchmark runner — executes AY directly without Python.
//!
//! Discovers benchmarks from eval spec YAML, runs them with timeout,
//! and produces results.json compatible with scoring.rs.

use serde::Serialize;
use std::collections::VecDeque;
use std::ffi::OsString;
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use crate::error::{BenchError, Result, WithContext};
use std::collections::BTreeMap;

// ===================================================================
// Temp file cleanup guard
// ===================================================================

/// RAII guard that deletes a temporary file when dropped.
struct TempFileGuard(Option<PathBuf>);

impl Drop for TempFileGuard {
    fn drop(&mut self) {
        if let Some(ref path) = self.0 {
            let _ = std::fs::remove_file(path);
        }
    }
}

// ===================================================================
// Result types (JSON-compatible with scoring.rs)
// ===================================================================

#[derive(Debug, Serialize)]
pub(crate) struct NativeResultItem {
    /// Display name retained for existing scoring/report consumers.
    pub file: String,
    /// Original benchmark path before any ay-bench decompression.
    pub benchmark_path: String,
    /// Stable hash of the original benchmark bytes. Comparisons fail closed
    /// when this is missing or differs from the baseline/result being compared.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub benchmark_content_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver_input_path: Option<String>,
    pub expected: Option<String>,
    pub result: String,
    pub time_sec: f64,
    pub cpu_time_sec: f64,
    pub exit_code: Option<i32>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub solver_argv: Vec<String>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub solver_env: BTreeMap<String, String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifacts: Option<SolverArtifactMetadata>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sat_run: Option<SatAppliedRunMetadata>,
}

#[derive(Debug, Serialize)]
pub(crate) struct ComparisonItem {
    pub file: String,
    pub ay_result: String,
    pub ay_time_sec: f64,
    pub ref_result: String,
    pub ref_time_sec: f64,
    pub agreement: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ComparisonSummary {
    pub reference_solver: String,
    pub reference_solver_path: String,
    pub reference_solver_version: String,
    pub reference_solver_build_version: String,
    pub reference_solver_build_commit: String,
    pub reference_solver_build_datetime_utc: String,
    pub reference_solver_build_stamp: String,
    pub agree: u32,
    pub disagree: u32,
    pub ay_only: u32,
    pub ref_only: u32,
    pub both_solved: u32,
    pub ay_faster: u32,
    pub ref_faster: u32,
    pub ay_total_time: f64,
    pub ref_total_time: f64,
}

/// Host fingerprint recorded beside a stamped `run_class` so a stamped
/// results.json carries the hardware it was produced on. Recording only —
/// verification against cited official specs is `bench compare check`'s job.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct HostFingerprint {
    /// Hardware model identifier (e.g. "MacBookPro18,3"), "unknown" if
    /// unavailable.
    pub hw_model: String,
    pub cpu_model: String,
    pub cpu_count: u32,
    pub memory_bytes: u64,
}

impl HostFingerprint {
    fn capture(env: &crate::environment::Environment) -> Self {
        Self {
            hw_model: crate::environment::hw_model(),
            cpu_model: env.cpu_model.clone(),
            cpu_count: env.cpu_count,
            memory_bytes: env.memory_bytes,
        }
    }
}

#[derive(Debug, Serialize)]
pub(crate) struct NativeResults {
    pub environment: crate::environment::Environment,
    pub items: Vec<NativeResultItem>,
    pub settings: NativeSettings,
    /// Legacy single-reference summary, kept populated with the first entry
    /// of `references` for one release (dropped in a schema bump).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparison: Option<ComparisonSummary>,
    /// Per-benchmark agreement rows for the first reference solver.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparisons: Option<Vec<ComparisonItem>>,
    /// Comparison run class stamp ("replay" | "laptop"). Stamped, never
    /// verified, by `bench run --run-class`; unstamped runs omit the field
    /// and must not be quoted as any class.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub run_class: Option<String>,
    /// True only when the class was set and verified by `bench compare run`;
    /// a class stamped via `bench run --run-class` is always false.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub run_class_verified: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub host_fingerprint: Option<HostFingerprint>,
    /// One summary per `--reference-solver`, in flag order.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub references: Option<Vec<ComparisonSummary>>,
}

#[derive(Debug, Serialize)]
pub(crate) struct NativeSettings {
    pub benchmarks_dir: String,
    pub timeout_sec: f64,
    pub domain: String,
    pub benchmark_count: usize,
    pub runs: u32,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub solver_args: Vec<String>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub solver_env: BTreeMap<String, String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_output_dir: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sat_track: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sat_ai_class: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sat_variant: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sat_competition_profile: Option<SatCompetitionProfileMetadata>,
    /// RAM/CPU envelope applied to every solver child in this run.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resource_plan: Option<crate::resource::ResourcePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resource_enforcement: Option<String>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub(crate) struct SolverArtifactMetadata {
    pub output_dir: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_format: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_exists: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_bytes: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_hash: Option<String>,
}

#[derive(Debug, Clone, Serialize, Default, PartialEq, Eq)]
pub(crate) struct SatAppliedRunMetadata {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub policy: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub policy_source: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub route_profile: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub route_fail_closed: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub guidance_loaded: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_active: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_format: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_origin: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verify_proof: Option<String>,
}

impl SatAppliedRunMetadata {
    fn is_empty(&self) -> bool {
        self.policy.is_none()
            && self.policy_source.is_none()
            && self.route_profile.is_none()
            && self.route_fail_closed.is_none()
            && self.guidance_loaded.is_none()
            && self.proof_active.is_none()
            && self.proof_format.is_none()
            && self.proof_origin.is_none()
            && self.verify_proof.is_none()
    }
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub(crate) struct SatCompetitionProfileMetadata {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub track: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ai_class: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub variant: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalized_track: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalized_ai_class: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub profile_id: Option<String>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub env: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
struct SolverArtifactPlan {
    output_dir: PathBuf,
    proof_path: Option<PathBuf>,
    proof_format: Option<&'static str>,
}

// ===================================================================
// Verdict parsing
// ===================================================================

fn parse_verdict(stdout: &str, exit_code: Option<i32>) -> &'static str {
    for line in stdout.lines() {
        let trimmed = line.trim();
        let lower = trimmed.to_ascii_lowercase();
        match lower.as_str() {
            "sat" | "s satisfiable" | "satisfiable" => return "sat",
            "unsat" | "s unsatisfiable" | "unsatisfiable" => return "unsat",
            "unknown" | "s unknown" => return "unknown",
            _ => {}
        }
    }
    match exit_code {
        Some(10) => "sat",
        Some(20) => "unsat",
        _ => "error",
    }
}

fn parse_reference_verdict(stdout: &str, exit_code: Option<i32>) -> &'static str {
    if exit_code.is_none() && stdout.trim().is_empty() {
        return "unknown";
    }
    parse_verdict(stdout, exit_code)
}

fn guess_expected_from_path(path: &Path) -> Option<String> {
    let name = path.file_name()?.to_str()?.to_ascii_lowercase();
    let parts: Vec<String> = path
        .iter()
        .map(|p| p.to_string_lossy().to_ascii_lowercase())
        .collect();

    if parts.iter().any(|p| p == "unsat") {
        return Some("unsat".to_string());
    }
    if parts.iter().any(|p| p == "sat") {
        return Some("sat".to_string());
    }
    // SATLIB naming: uufN = unsatisfiable uniform random, ufN = satisfiable
    // Only match when followed by a digit to avoid false positives on
    // UFLRA/UFLIA/etc. SMT-LIB logic names.
    if name.starts_with("uuf") && name.as_bytes().get(3).is_some_and(|b| b.is_ascii_digit()) {
        return Some("unsat".to_string());
    }
    if name.starts_with("uf") && name.as_bytes().get(2).is_some_and(|b| b.is_ascii_digit()) {
        return Some("sat".to_string());
    }
    None
}

// ===================================================================
// Benchmark discovery
// ===================================================================

fn is_benchmark_file(path: &Path, domain: &str) -> bool {
    let name = match path.file_name().and_then(|n| n.to_str()) {
        Some(n) => n,
        None => return false,
    };
    match domain {
        "sat" => {
            name.ends_with(".cnf")
                || name.ends_with(".cnf.xz")
                || name.ends_with(".cnf.gz")
                || name.ends_with(".cnf.bz2")
                || name.ends_with(".dimacs")
                || name.ends_with(".icnf")
        }
        "chc" | "smt" => name.ends_with(".smt2"),
        "hwmcc" => name.ends_with(".btor2"),
        // Security benchmark domains
        "sygus" => name.ends_with(".sl"),
        "maxsat" => {
            name.ends_with(".wcnf") || name.ends_with(".wcnf.xz") || name.ends_with(".wcnf.gz")
        }
        "qbf" => name.ends_with(".qdimacs") || name.ends_with(".qdimacs.gz"),
        "allsat" => {
            name.ends_with(".cnf")
                || name.ends_with(".smt2")
                || name.ends_with(".aig")
                || name.ends_with(".aag")
        }
        "counting" => {
            name.ends_with(".cnf") || name.ends_with(".cnf.gz") || name.ends_with(".smt2")
        }
        "omt" => name.ends_with(".smt2"),
        _ => {
            name.ends_with(".smt2")
                || name.ends_with(".cnf")
                || name.ends_with(".cnf.xz")
                || name.ends_with(".btor2")
                || name.ends_with(".sl")
                || name.ends_with(".wcnf")
                || name.ends_with(".qdimacs")
                || name.ends_with(".aig")
                || name.ends_with(".aag")
        }
    }
}

/// Returns true if the benchmark path needs decompression before solving.
fn needs_decompression(path: &Path) -> bool {
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
    name.ends_with(".xz") || name.ends_with(".gz") || name.ends_with(".bz2")
}

/// Decompress a compressed benchmark to a temporary file.
/// Returns the path to the decompressed temp file. Caller must delete it.
fn decompress_to_temp(path: &Path) -> Result<PathBuf> {
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("bench");
    let (decompressed_name, decompress_cmd) = if name.ends_with(".xz") {
        (name.strip_suffix(".xz").unwrap_or(name), "xz")
    } else if name.ends_with(".gz") {
        (name.strip_suffix(".gz").unwrap_or(name), "gzip")
    } else if name.ends_with(".bz2") {
        (name.strip_suffix(".bz2").unwrap_or(name), "bzip2")
    } else {
        return Err(BenchError::UnsupportedFormat {
            path: path.to_path_buf(),
        });
    };

    let temp_dir = std::env::temp_dir().join("ay-bench-decompress");
    std::fs::create_dir_all(&temp_dir)?;
    let temp_path = temp_dir.join(decompressed_name);

    let output = Command::new(decompress_cmd)
        .args(["-d", "-k", "-c"])
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .with_bench_context(|| {
            format!(
                "failed to run {decompress_cmd} — is it installed? (needed for {})",
                path.display()
            )
        })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(BenchError::msg(format!(
            "{decompress_cmd} failed on {}: {}",
            path.display(),
            stderr.trim()
        )));
    }

    std::fs::write(&temp_path, &output.stdout)
        .with_bench_context(|| format!("writing decompressed file to {}", temp_path.display()))?;

    Ok(temp_path)
}

pub(crate) fn discover_benchmarks(dir: &Path, domain: &str) -> Result<Vec<PathBuf>> {
    if !dir.exists() {
        return Err(BenchError::BenchmarksDirMissing {
            path: dir.to_path_buf(),
        });
    }
    let mut files = Vec::new();
    collect_benchmarks_recursive(dir, domain, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_benchmarks_recursive(dir: &Path, domain: &str, out: &mut Vec<PathBuf>) -> Result<()> {
    for entry in
        std::fs::read_dir(dir).with_bench_context(|| format!("reading {}", dir.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_benchmarks_recursive(&path, domain, out)?;
        } else if is_benchmark_file(&path, domain) {
            out.push(path);
        }
    }
    Ok(())
}

// ===================================================================
// CPU time measurement via /usr/bin/time
// ===================================================================

/// Check whether `/usr/bin/time` is available (cached after first call).
fn has_usr_bin_time() -> bool {
    use std::sync::OnceLock;
    static AVAILABLE: OnceLock<bool> = OnceLock::new();
    *AVAILABLE.get_or_init(|| Path::new("/usr/bin/time").exists())
}

/// Parse POSIX-format time output (`-p` flag) to extract user+sys CPU seconds.
///
/// Format (macOS and Linux):
/// ```text
/// real 1.23
/// user 0.80
/// sys 0.05
/// ```
///
/// Returns `Some(user + sys)` on success, `None` if parsing fails.
fn parse_posix_time_output(stderr: &str) -> Option<f64> {
    let mut user: Option<f64> = None;
    let mut sys: Option<f64> = None;

    // Scan from the end of stderr since /usr/bin/time appends its output
    // after any solver stderr output.
    for line in stderr.lines().rev() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("user") {
            if user.is_none() {
                user = rest.trim().parse::<f64>().ok();
            }
        } else if let Some(rest) = trimmed.strip_prefix("sys") {
            if sys.is_none() {
                sys = rest.trim().parse::<f64>().ok();
            }
        }
        // Stop scanning once we have both values
        if user.is_some() && sys.is_some() {
            break;
        }
    }

    match (user, sys) {
        (Some(u), Some(s)) => Some(u + s),
        _ => None,
    }
}

// ===================================================================
// Solver execution with timeout
// ===================================================================

#[cfg(unix)]
fn isolate_process_group(cmd: &mut Command) {
    use std::os::unix::process::CommandExt as _;

    // Keep wrapper processes like /usr/bin/time and any solver descendants in
    // a dedicated process group so timeout handling can reap the whole tree.
    cmd.process_group(0);
}

#[cfg(not(unix))]
fn isolate_process_group(_cmd: &mut Command) {}

fn terminate_timed_out_child(child: &mut Child) {
    #[cfg(unix)]
    {
        terminate_process_group(child);
    }
    #[cfg(not(unix))]
    {
        let _ = child.kill();
        let _ = child.wait();
    }
}

fn terminate_exited_child_process_group(child: &mut Child) {
    #[cfg(unix)]
    {
        terminate_process_group(child);
    }
    #[cfg(not(unix))]
    {
        let _ = child.kill();
    }
}

#[cfg(unix)]
fn terminate_process_group(child: &mut Child) {
    use nix::sys::signal::Signal;
    use nix::unistd::Pid;

    let pgid = match i32::try_from(child.id()) {
        Ok(pid) if pid > 0 => pid,
        _ => {
            let _ = child.kill();
            let _ = child.wait();
            return;
        }
    };
    let pgid = Pid::from_raw(pgid);

    signal_process_group(pgid, Signal::SIGTERM);
    let graceful_deadline = Instant::now() + Duration::from_millis(200);
    let mut child_exited = false;
    while Instant::now() < graceful_deadline {
        match child.try_wait() {
            Ok(Some(_)) => {
                child_exited = true;
                break;
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(10)),
            Err(_) => break,
        }
    }

    signal_process_group(pgid, Signal::SIGKILL);
    if !child_exited {
        let _ = child.kill();
        let _ = child.wait();
    }
}

#[cfg(unix)]
fn signal_process_group(pgid: nix::unistd::Pid, signal: nix::sys::signal::Signal) {
    let _ = nix::sys::signal::killpg(pgid, signal);
}

const CAPTURE_HEAD_BYTES: usize = 512 * 1024;
const CAPTURE_TAIL_BYTES: usize = 512 * 1024;

struct PipeCapture {
    receiver: std::sync::mpsc::Receiver<String>,
}

impl PipeCapture {
    /// Drain from process start so a verbose solver cannot fill a pipe and
    /// deadlock before `try_wait` observes its exit. Retain bounded head+tail
    /// diagnostics so verdicts/stats at either end remain parseable.
    fn start<R>(mut reader: R) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let mut head = Vec::new();
            let mut tail: VecDeque<Vec<u8>> = VecDeque::new();
            let mut tail_len = 0usize;
            let mut total_len = 0usize;
            let mut chunk = [0u8; 8192];
            loop {
                let read = match reader.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(read) => read,
                };
                total_len = total_len.saturating_add(read);
                let head_read = read.min(CAPTURE_HEAD_BYTES.saturating_sub(head.len()));
                head.extend_from_slice(&chunk[..head_read]);
                if head_read < read {
                    let trailing = chunk[head_read..read].to_vec();
                    tail_len += trailing.len();
                    tail.push_back(trailing);
                    while tail_len > CAPTURE_TAIL_BYTES {
                        let excess = tail_len - CAPTURE_TAIL_BYTES;
                        let Some(front) = tail.front_mut() else {
                            break;
                        };
                        let remove = excess.min(front.len());
                        front.drain(..remove);
                        tail_len -= remove;
                        if front.is_empty() {
                            tail.pop_front();
                        }
                    }
                }
            }
            if !tail.is_empty() {
                if total_len > CAPTURE_HEAD_BYTES + CAPTURE_TAIL_BYTES {
                    head.extend_from_slice(b"\n[... output truncated ...]\n");
                }
                for bytes in tail {
                    head.extend_from_slice(&bytes);
                }
            }
            let _ = sender.send(String::from_utf8_lossy(&head).into_owned());
        });
        Self { receiver }
    }

    fn finish(self) -> String {
        self.receiver
            .recv_timeout(Duration::from_secs(2))
            .unwrap_or_default()
    }
}

fn discard_captures(stdout: Option<PipeCapture>, stderr: Option<PipeCapture>) {
    if let Some(stdout) = stdout {
        let _ = stdout.finish();
    }
    if let Some(stderr) = stderr {
        let _ = stderr.finish();
    }
}

fn run_solver(
    ay_path: &Path,
    benchmark: &Path,
    timeout_sec: f64,
    domain: &str,
    solver_args: &[String],
    solver_env: &BTreeMap<String, String>,
    artifact_plan: Option<&SolverArtifactPlan>,
) -> NativeResultItem {
    let benchmark_content_hash = content_hash_file(benchmark).ok();
    let file_name = benchmark
        .file_name()
        .map(|n| n.to_string_lossy().to_string())
        .unwrap_or_else(|| benchmark.display().to_string());
    let benchmark_path = benchmark.display().to_string();
    let expected = guess_expected_from_path(benchmark);
    let mut command_args = solver_command_args(domain, solver_args);
    if let Some(proof_path) = artifact_plan.and_then(|plan| plan.proof_path.as_ref()) {
        command_args.push("--proof".to_string());
        command_args.push(proof_path.display().to_string());
    }

    // Decompress if needed, using the decompressed path for solving
    let (actual_path, _temp_guard) = if needs_decompression(benchmark) {
        match decompress_to_temp(benchmark) {
            Ok(p) => {
                let guard = TempFileGuard(Some(p.clone()));
                (p, Some(guard))
            }
            Err(e) => {
                return NativeResultItem {
                    file: file_name,
                    benchmark_path,
                    benchmark_content_hash,
                    solver_input_path: None,
                    expected,
                    result: format!("error: decompression failed: {e}"),
                    time_sec: 0.0,
                    cpu_time_sec: 0.0,
                    exit_code: None,
                    solver_argv: solver_argv(ay_path, &command_args, benchmark),
                    solver_env: solver_env.clone(),
                    artifacts: artifact_metadata(artifact_plan),
                    sat_run: None,
                };
            }
        }
    } else {
        (benchmark.to_path_buf(), None)
    };

    let start = Instant::now();
    let timeout = Duration::from_secs_f64(timeout_sec);

    // When /usr/bin/time is available, wrap the solver command to get true
    // child-process CPU time (user + sys). This avoids unsafe code while
    // providing accurate CPU time for competition scoring (PAR-2, SMT-COMP).
    let use_time_wrapper = has_usr_bin_time();

    let mut cmd = if use_time_wrapper {
        let mut c = Command::new("/usr/bin/time");
        c.arg("-p"); // POSIX output format
        c.arg(ay_path);
        c
    } else {
        Command::new(ay_path)
    };

    cmd.args(&command_args);
    cmd.envs(solver_env);
    cmd.arg("--");
    cmd.arg(&actual_path);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());
    isolate_process_group(&mut cmd);
    let solver_argv = solver_argv(ay_path, &command_args, &actual_path);
    let solver_input_path = if actual_path == benchmark {
        None
    } else {
        Some(actual_path.display().to_string())
    };

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return NativeResultItem {
                file: file_name,
                benchmark_path,
                benchmark_content_hash,
                solver_input_path,
                expected,
                result: format!("error: {e}"),
                time_sec: 0.0,
                cpu_time_sec: 0.0,
                exit_code: None,
                solver_argv,
                solver_env: solver_env.clone(),
                artifacts: artifact_metadata(artifact_plan),
                sat_run: None,
            };
        }
    };
    let stdout_capture = child.stdout.take().map(PipeCapture::start);
    let stderr_capture = child.stderr.take().map(PipeCapture::start);

    // Poll for completion with timeout
    let poll_interval = Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed = start.elapsed().as_secs_f64();
                terminate_exited_child_process_group(&mut child);
                let stdout = stdout_capture.map(PipeCapture::finish).unwrap_or_default();
                let stderr_output = stderr_capture.map(PipeCapture::finish).unwrap_or_default();
                let verdict = parse_verdict(&stdout, status.code());

                // Extract CPU time from /usr/bin/time output, fall back to wall time.
                let cpu_time = if use_time_wrapper {
                    parse_posix_time_output(&stderr_output).unwrap_or(elapsed)
                } else {
                    elapsed
                };

                return NativeResultItem {
                    file: file_name,
                    benchmark_path,
                    benchmark_content_hash,
                    solver_input_path,
                    expected,
                    result: verdict.to_string(),
                    time_sec: round6(elapsed),
                    cpu_time_sec: round6(cpu_time),
                    exit_code: status.code(),
                    solver_argv,
                    solver_env: solver_env.clone(),
                    artifacts: artifact_metadata(artifact_plan),
                    sat_run: parse_sat_applied_run_metadata(&stderr_output),
                };
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    terminate_timed_out_child(&mut child);
                    discard_captures(stdout_capture, stderr_capture);
                    return NativeResultItem {
                        file: file_name,
                        benchmark_path,
                        benchmark_content_hash,
                        solver_input_path,
                        expected,
                        result: "timeout".to_string(),
                        time_sec: round6(timeout_sec),
                        cpu_time_sec: round6(timeout_sec),
                        exit_code: None,
                        solver_argv,
                        solver_env: solver_env.clone(),
                        artifacts: artifact_metadata(artifact_plan),
                        sat_run: None,
                    };
                }
                std::thread::sleep(poll_interval);
            }
            Err(_) => {
                let elapsed = start.elapsed().as_secs_f64();
                terminate_timed_out_child(&mut child);
                discard_captures(stdout_capture, stderr_capture);
                return NativeResultItem {
                    file: file_name,
                    benchmark_path,
                    benchmark_content_hash,
                    solver_input_path,
                    expected,
                    result: "error".to_string(),
                    time_sec: round6(elapsed),
                    cpu_time_sec: round6(elapsed),
                    exit_code: None,
                    solver_argv,
                    solver_env: solver_env.clone(),
                    artifacts: artifact_metadata(artifact_plan),
                    sat_run: None,
                };
            }
        }
    }
}

fn solver_command_args(domain: &str, solver_args: &[String]) -> Vec<String> {
    let mut args = Vec::new();
    // Only pass --chc for CHC domain. Other domains use standard file
    // formats that AY auto-detects from the file extension. Future AY
    // capabilities (--sygus, --maxsat, --qbf, --allsat, --count,
    // --optimize) will be added here as those features are implemented.
    if domain == "chc" {
        args.push("--chc".to_string());
    }
    args.extend(solver_args.iter().cloned());
    args
}

fn solver_argv(ay_path: &Path, solver_args: &[String], benchmark: &Path) -> Vec<String> {
    let mut argv = Vec::with_capacity(3 + solver_args.len());
    argv.push(ay_path.display().to_string());
    argv.extend(solver_args.iter().cloned());
    argv.push("--".to_string());
    argv.push(benchmark.display().to_string());
    argv
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeReferenceKind {
    Golem,
    Other,
}

impl NativeReferenceKind {
    fn detect(path: &Path) -> Self {
        let file_name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("");
        if file_name.eq_ignore_ascii_case("golem") {
            Self::Golem
        } else {
            Self::Other
        }
    }
}

fn external_solver_args(solver_path: &Path, benchmark: &Path, _timeout_sec: f64) -> Vec<OsString> {
    let mut args = Vec::new();
    match NativeReferenceKind::detect(solver_path) {
        NativeReferenceKind::Golem => {
            args.push(OsString::from("-l"));
            args.push(OsString::from("QF_LIA"));
            args.push(OsString::from("-e"));
            args.push(OsString::from("spacer"));
            args.push(benchmark.as_os_str().to_os_string());
        }
        NativeReferenceKind::Other => {
            args.push(OsString::from("--"));
            args.push(benchmark.as_os_str().to_os_string());
        }
    }
    args
}

fn watchdog_breached(watchdog: Option<crate::resource::RssWatchdog>) -> Result<bool> {
    watchdog.map_or(Ok(false), crate::resource::RssWatchdog::finish)
}

/// Run an external solver (e.g., z3) on a benchmark and return (verdict, time_sec).
fn run_external_solver(
    solver_path: &Path,
    benchmark: &Path,
    timeout_sec: f64,
    resources: Option<&crate::resource::PlannedResources>,
) -> (String, f64) {
    // Decompress if needed
    let (actual_path, _temp_guard) = if needs_decompression(benchmark) {
        match decompress_to_temp(benchmark) {
            Ok(p) => {
                let guard = TempFileGuard(Some(p.clone()));
                (p, Some(guard))
            }
            Err(_) => return ("error".to_string(), 0.0),
        }
    } else {
        (benchmark.to_path_buf(), None)
    };

    let start = Instant::now();
    let timeout = Duration::from_secs_f64(timeout_sec);

    let mut cmd = Command::new(solver_path);
    cmd.args(external_solver_args(solver_path, &actual_path, timeout_sec));
    if let Some(plan) = resources.map(|resources| &resources.plan) {
        // ay-pb consumes these directly; other reference solvers remain under
        // the exact zero-grace RSS watchdog while receiving the planned CPU
        // budget as advisory environment provenance.
        cmd.env("MEMLIMIT", plan.memlimit_mb_per_child.to_string());
        cmd.env("NBCORE", plan.nbcore_per_child.to_string());
    }
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());
    isolate_process_group(&mut cmd);

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(_) => return ("error".to_string(), 0.0),
    };
    let stdout_capture = child.stdout.take().map(PipeCapture::start);
    let stderr_capture = child.stderr.take().map(PipeCapture::start);
    let watchdog = match resources
        .map(|resources| resources.watch_external_child(&child, "ay bench run reference"))
        .transpose()
    {
        Ok(watchdog) => watchdog,
        Err(_) => {
            terminate_timed_out_child(&mut child);
            discard_captures(stdout_capture, stderr_capture);
            return ("error".to_string(), round6(start.elapsed().as_secs_f64()));
        }
    };

    let poll_interval = Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed = start.elapsed().as_secs_f64();
                terminate_exited_child_process_group(&mut child);
                let stdout = stdout_capture.map(PipeCapture::finish).unwrap_or_default();
                if let Some(stderr) = stderr_capture {
                    let _ = stderr.finish();
                }
                match watchdog_breached(watchdog) {
                    Ok(true) => return ("memout".to_string(), round6(elapsed)),
                    Ok(false) => {}
                    Err(error) => {
                        eprintln!("[resource] RSS watchdog failure: {error}");
                        return ("error".to_string(), round6(elapsed));
                    }
                }
                let verdict = parse_reference_verdict(&stdout, status.code());
                return (verdict.to_string(), round6(elapsed));
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    terminate_timed_out_child(&mut child);
                    discard_captures(stdout_capture, stderr_capture);
                    let elapsed = round6(start.elapsed().as_secs_f64());
                    match watchdog_breached(watchdog) {
                        Ok(true) => return ("memout".to_string(), elapsed),
                        Ok(false) => {}
                        Err(error) => {
                            eprintln!("[resource] RSS watchdog failure: {error}");
                            return ("error".to_string(), elapsed);
                        }
                    }
                    return ("timeout".to_string(), round6(timeout_sec));
                }
                std::thread::sleep(poll_interval);
            }
            Err(_) => {
                terminate_timed_out_child(&mut child);
                discard_captures(stdout_capture, stderr_capture);
                if let Some(watchdog) = watchdog {
                    let _ = watchdog.finish();
                }
                return ("error".to_string(), round6(start.elapsed().as_secs_f64()));
            }
        }
    }
}

fn progress_every_from_env() -> usize {
    std::env::var("AY_BENCH_PROGRESS_EVERY")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|value| *value > 0)
        .unwrap_or(10)
}

fn should_log_progress(index: usize, total: usize, every: usize) -> bool {
    index == 0 || index + 1 == total || (index + 1).is_multiple_of(every)
}

fn round6(x: f64) -> f64 {
    (x * 1_000_000.0).round() / 1_000_000.0
}

fn classify_agreement(ay: &str, reference: &str) -> &'static str {
    let definitive = |s: &str| s == "sat" || s == "unsat";
    match (definitive(ay), definitive(reference)) {
        (true, true) => {
            if ay == reference {
                "agree"
            } else {
                "disagree"
            }
        }
        (true, false) => "ay_only",
        (false, true) => "ref_only",
        (false, false) => "both_unknown",
    }
}

fn nonempty_trimmed(value: &str) -> Option<String> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.to_string())
    }
}

fn canonical_sat_track(track: &str) -> String {
    let trimmed = track.trim();
    let lower = trimmed.to_ascii_lowercase();
    match lower.as_str() {
        "main" | "main track" | "main-track" | "main_track" => "main".to_string(),
        _ => trimmed.to_string(),
    }
}

fn canonical_sat_ai_class(ai_class: &str) -> String {
    ai_class
        .trim()
        .to_ascii_lowercase()
        .replace([' ', '_'], "-")
}

fn sat_competition_profile_metadata(
    domain: &str,
    sat_track: Option<&String>,
    sat_ai_class: Option<&String>,
    sat_variant: Option<&String>,
) -> Option<SatCompetitionProfileMetadata> {
    if domain != "sat" {
        return None;
    }

    let track = sat_track.and_then(|v| nonempty_trimmed(v));
    let ai_class = sat_ai_class.and_then(|v| nonempty_trimmed(v));
    let variant = sat_variant.and_then(|v| nonempty_trimmed(v));
    if track.is_none() && ai_class.is_none() && variant.is_none() {
        return None;
    }

    let normalized_track = track.as_deref().map(canonical_sat_track);
    let normalized_ai_class = ai_class
        .as_deref()
        .map(canonical_sat_ai_class)
        .or_else(|| normalized_track.as_ref().map(|_| "regular".to_string()));
    let mut env = BTreeMap::new();

    if let Some(track) = normalized_track.as_deref() {
        env.insert("AY_SAT_TRACK".to_string(), track.to_string());
    }
    if let Some(ai_class) = normalized_ai_class.as_deref() {
        env.insert("AY_SAT_AI_CLASS".to_string(), ai_class.to_string());
    }

    let profile_id = normalized_track.as_ref().map(|track| {
        let ai = normalized_ai_class.as_deref().unwrap_or("regular");
        format!("ay-sat-{ai}-{track}")
    });
    if let Some(profile_id) = profile_id.as_deref() {
        env.insert("AY_SAT_PROFILE_ID".to_string(), profile_id.to_string());
    }
    if normalized_track.is_some() || normalized_ai_class.is_some() {
        let profile = normalized_ai_class.as_deref().unwrap_or("regular");
        env.insert(
            "AY_SAT_COMPETITION_PROFILE".to_string(),
            profile.to_string(),
        );
    }

    Some(SatCompetitionProfileMetadata {
        track,
        ai_class,
        variant,
        normalized_track,
        normalized_ai_class,
        profile_id,
        env,
    })
}

fn sat_proof_format_for_profile(profile: Option<&SatCompetitionProfileMetadata>) -> &'static str {
    if profile
        .and_then(|p| p.normalized_track.as_deref())
        .is_some_and(|track| track.eq_ignore_ascii_case("main"))
    {
        "lrat"
    } else {
        "drat"
    }
}

fn artifact_file_name(index: usize, benchmark: &Path, proof_format: &str) -> String {
    let raw = benchmark
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("benchmark");
    let sanitized: String = raw
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_') {
                c
            } else {
                '_'
            }
        })
        .collect();
    format!("{:06}-{sanitized}.{proof_format}", index + 1)
}

fn artifact_plan_for_benchmark(
    domain: &str,
    profile: Option<&SatCompetitionProfileMetadata>,
    output_dir: Option<&Path>,
    index: usize,
    benchmark: &Path,
) -> Option<SolverArtifactPlan> {
    if domain != "sat" {
        return None;
    }
    let output_dir = output_dir?;
    let proof_format = sat_proof_format_for_profile(profile);
    let proof_path = output_dir.join(artifact_file_name(index, benchmark, proof_format));
    Some(SolverArtifactPlan {
        output_dir: output_dir.to_path_buf(),
        proof_path: Some(proof_path),
        proof_format: Some(proof_format),
    })
}

fn artifact_metadata(plan: Option<&SolverArtifactPlan>) -> Option<SolverArtifactMetadata> {
    let plan = plan?;
    let proof_exists = plan.proof_path.as_ref().map(|path| path.exists());
    let proof_bytes = plan
        .proof_path
        .as_ref()
        .and_then(|path| std::fs::metadata(path).ok())
        .map(|m| m.len());
    let proof_hash = plan
        .proof_path
        .as_ref()
        .filter(|path| path.is_file())
        .and_then(|path| content_hash_file(path).ok());
    Some(SolverArtifactMetadata {
        output_dir: plan.output_dir.display().to_string(),
        proof_path: plan.proof_path.as_ref().map(|p| p.display().to_string()),
        proof_format: plan.proof_format.map(str::to_string),
        proof_exists,
        proof_bytes,
        proof_hash,
    })
}

fn content_hash_file(path: &Path) -> Result<String> {
    use std::hash::Hasher as _;

    let mut file = std::fs::File::open(path)
        .with_bench_context(|| format!("opening proof artifact {}", path.display()))?;
    let mut h1 = std::collections::hash_map::DefaultHasher::new();
    let mut h2 = std::collections::hash_map::DefaultHasher::new();
    h2.write_u64(0x9E37_79B9_7F4A_7C15);
    let mut buf = [0u8; 8192];
    loop {
        let n = file
            .read(&mut buf)
            .with_bench_context(|| format!("reading proof artifact {}", path.display()))?;
        if n == 0 {
            break;
        }
        h1.write(&buf[..n]);
        h2.write(&buf[..n]);
    }
    Ok(format!("fh128:{:016x}{:016x}", h1.finish(), h2.finish()))
}

fn parse_sat_applied_run_metadata(stderr: &str) -> Option<SatAppliedRunMetadata> {
    let mut metadata = SatAppliedRunMetadata::default();
    for line in stderr.lines() {
        let Some(rest) = line.trim().strip_prefix("c sat.") else {
            continue;
        };
        let Some((key, value)) = rest.split_once(':') else {
            continue;
        };
        let value = value.trim().to_string();
        match key.trim() {
            "policy" => metadata.policy = Some(value),
            "policy_source" => metadata.policy_source = Some(value),
            "route_profile" => metadata.route_profile = Some(value),
            "route_fail_closed" => metadata.route_fail_closed = Some(value),
            "guidance_loaded" => metadata.guidance_loaded = Some(value),
            "proof_active" => metadata.proof_active = Some(value),
            "proof_format" => metadata.proof_format = Some(value),
            "proof_origin" => metadata.proof_origin = Some(value),
            "verify_proof" => metadata.verify_proof = Some(value),
            _ => {}
        }
    }

    if metadata.is_empty() {
        None
    } else {
        Some(metadata)
    }
}

// ===================================================================
// Public entry point
// ===================================================================

pub(crate) struct NativeRunArgs<'a> {
    pub ay: &'a Path,
    pub benchmarks_dir: &'a Path,
    pub timeout_sec: f64,
    pub domain: &'a str,
    pub quiet: bool,
    /// Pre-built file list. If set, skips directory discovery.
    pub file_list: Option<Vec<PathBuf>>,
    /// Number of runs per benchmark. The median-time run is selected.
    pub runs: u32,
    /// Reference solvers for comparison as (name, path) pairs, run in order.
    pub reference_solvers: Vec<(String, PathBuf)>,
    /// Comparison run class ("replay" | "laptop") stamped, never verified,
    /// into the results together with a host fingerprint.
    pub run_class: Option<String>,
    /// Additional arguments passed to ay before the benchmark path.
    pub solver_args: Vec<String>,
    /// SAT-COMP track metadata for result auditing.
    pub sat_track: Option<String>,
    /// SAT-COMP AI-class metadata for result auditing.
    pub sat_ai_class: Option<String>,
    /// SAT solver variant metadata for result auditing.
    pub sat_variant: Option<String>,
    /// Environment captured by the caller when it needs the run timestamp
    /// before invoking native execution.
    pub environment: Option<crate::environment::Environment>,
    /// Directory where ay-bench should place per-benchmark artifacts.
    pub artifact_output_dir: Option<PathBuf>,
    /// Resource admission and enforcement produced by `scripts/_oom_guard.py`.
    /// `None` is reserved for focused unit tests.
    pub resources: Option<crate::resource::PlannedResources>,
}

/// Legacy display name for a reference solver path (file name, falling back
/// to the full path) — the naming the single `--reference-solver PATH` flag
/// has always recorded into results.json.
pub(crate) fn reference_display_name(path: &Path) -> String {
    path.file_name()
        .map(|n| n.to_string_lossy().to_string())
        .unwrap_or_else(|| path.display().to_string())
}

/// Select the representative run from multiple results for the same benchmark.
/// Picks the run with median wall time. For even counts, picks the lower median.
pub(crate) fn select_representative(mut results: Vec<NativeResultItem>) -> NativeResultItem {
    if results.len() == 1 {
        return results.remove(0);
    }
    results.sort_by(|a, b| a.time_sec.partial_cmp(&b.time_sec).unwrap());
    let mid = (results.len() - 1) / 2;
    results.remove(mid)
}

pub(crate) fn run_native(args: &NativeRunArgs<'_>) -> Result<NativeResults> {
    let env = args
        .environment
        .clone()
        .unwrap_or_else(|| crate::environment::Environment::capture(args.ay));

    let benchmarks = if let Some(ref list) = args.file_list {
        list.clone()
    } else {
        discover_benchmarks(args.benchmarks_dir, args.domain)?
    };
    if benchmarks.is_empty() {
        return Err(BenchError::msg(format!(
            "no {} benchmarks found in {}",
            args.domain,
            args.benchmarks_dir.display()
        )));
    }

    let total = benchmarks.len();
    let runs = args.runs.max(1);
    let sat_profile = sat_competition_profile_metadata(
        args.domain,
        args.sat_track.as_ref(),
        args.sat_ai_class.as_ref(),
        args.sat_variant.as_ref(),
    );
    let mut solver_env = sat_profile
        .as_ref()
        .map(|profile| profile.env.clone())
        .unwrap_or_default();
    if let Some(plan) = args.resources.as_ref().map(|resources| &resources.plan) {
        solver_env.insert("NBCORE".to_string(), plan.nbcore_per_child.to_string());
    }
    if let Some(output_dir) = args.artifact_output_dir.as_ref() {
        std::fs::create_dir_all(output_dir)?;
    }
    let artifact_output_dir = args
        .artifact_output_dir
        .as_ref()
        .map(|path| path.display().to_string());

    if !args.quiet {
        eprintln!("[env] {env}");
        if runs > 1 {
            eprintln!(
                "[native] running {} {} benchmarks x {} runs, timeout={:.0}s",
                total, args.domain, runs, args.timeout_sec,
            );
        } else {
            eprintln!(
                "[native] running {} {} benchmarks, timeout={:.0}s",
                total, args.domain, args.timeout_sec,
            );
        }
    }

    let progress_every = progress_every_from_env();
    let mut items = Vec::with_capacity(total);
    for (idx, benchmark) in benchmarks.iter().enumerate() {
        if !args.quiet && should_log_progress(idx, total, progress_every) {
            eprintln!(
                "[native] {}/{}: {}",
                idx + 1,
                total,
                benchmark.file_name().unwrap_or_default().to_string_lossy(),
            );
        }
        if runs == 1 {
            let artifact_plan = artifact_plan_for_benchmark(
                args.domain,
                sat_profile.as_ref(),
                args.artifact_output_dir.as_deref(),
                idx,
                benchmark,
            );
            let item = run_solver(
                args.ay,
                benchmark,
                args.timeout_sec,
                args.domain,
                &args.solver_args,
                &solver_env,
                artifact_plan.as_ref(),
            );
            items.push(item);
        } else {
            let mut run_results = Vec::with_capacity(runs as usize);
            for _ in 0..runs {
                let artifact_plan = artifact_plan_for_benchmark(
                    args.domain,
                    sat_profile.as_ref(),
                    args.artifact_output_dir.as_deref(),
                    idx,
                    benchmark,
                );
                run_results.push(run_solver(
                    args.ay,
                    benchmark,
                    args.timeout_sec,
                    args.domain,
                    &args.solver_args,
                    &solver_env,
                    artifact_plan.as_ref(),
                ));
            }
            items.push(select_representative(run_results));
        }
    }

    // Run each reference solver, in flag order. The first reference also
    // populates the legacy single-reference `comparison`/`comparisons`
    // fields, byte-compatible with the old single --reference-solver flag.
    let mut reference_summaries: Vec<ComparisonSummary> = Vec::new();
    let mut first_comparison_items: Option<Vec<ComparisonItem>> = None;
    for (ref_name, ref_solver) in &args.reference_solvers {
        let (summary, comp_items) = run_reference_comparison(
            ref_name,
            ref_solver,
            &benchmarks,
            &items,
            args.timeout_sec,
            args.quiet,
            progress_every,
            args.resources.as_ref(),
        );
        if first_comparison_items.is_none() {
            first_comparison_items = Some(comp_items);
        }
        reference_summaries.push(summary);
    }
    let references = if reference_summaries.is_empty() {
        None
    } else {
        Some(reference_summaries)
    };
    let comparison = references.as_ref().and_then(|refs| refs.first().cloned());

    // Stamp — never verify — the requested run class with a host fingerprint.
    let run_class = args.run_class.clone();
    let run_class_verified = run_class.as_ref().map(|_| false);
    let host_fingerprint = run_class.as_ref().map(|_| HostFingerprint::capture(&env));

    let results = NativeResults {
        environment: env,
        items,
        settings: NativeSettings {
            benchmarks_dir: args.benchmarks_dir.display().to_string(),
            timeout_sec: args.timeout_sec,
            domain: args.domain.to_string(),
            benchmark_count: total,
            runs,
            solver_args: args.solver_args.clone(),
            solver_env,
            artifact_output_dir,
            sat_track: args.sat_track.clone(),
            sat_ai_class: args.sat_ai_class.clone(),
            sat_variant: args.sat_variant.clone(),
            sat_competition_profile: sat_profile,
            resource_plan: args
                .resources
                .as_ref()
                .map(|resources| resources.plan.clone()),
            resource_enforcement: args.resources.as_ref().map(|_| {
                "AY --memory + NBCORE; reference rss_watchdog(grace=0) + MEMLIMIT/NBCORE env"
                    .to_string()
            }),
        },
        comparison,
        comparisons: first_comparison_items,
        run_class,
        run_class_verified,
        host_fingerprint,
        references,
    };

    Ok(results)
}

/// Run one reference solver over the benchmark list and summarize agreement
/// against the already-collected AY items.
fn run_reference_comparison(
    ref_name: &str,
    ref_solver: &Path,
    benchmarks: &[PathBuf],
    items: &[NativeResultItem],
    timeout_sec: f64,
    quiet: bool,
    progress_every: usize,
    resources: Option<&crate::resource::PlannedResources>,
) -> (ComparisonSummary, Vec<ComparisonItem>) {
    let total = benchmarks.len();
    let reference_provenance = crate::environment::SolverProvenance::capture(ref_solver);
    if !quiet {
        eprintln!(
            "[ref] running reference solver {} on {} benchmarks",
            reference_provenance.summary(),
            total
        );
    }
    let mut comp_items = Vec::with_capacity(total);
    let mut agree = 0u32;
    let mut disagree = 0u32;
    let mut ay_only = 0u32;
    let mut ref_only = 0u32;
    let mut both_solved = 0u32;
    let mut ay_faster = 0u32;
    let mut ref_faster = 0u32;
    let mut ay_total = 0.0f64;
    let mut ref_total = 0.0f64;

    for (idx, benchmark) in benchmarks.iter().enumerate() {
        let ay_item = &items[idx];
        let (ref_result, ref_time) =
            run_external_solver(ref_solver, benchmark, timeout_sec, resources);
        let agreement = classify_agreement(&ay_item.result, &ref_result);

        match agreement {
            "agree" => {
                agree += 1;
                both_solved += 1;
                ay_total += ay_item.time_sec;
                ref_total += ref_time;
                if ay_item.time_sec < ref_time {
                    ay_faster += 1;
                } else {
                    ref_faster += 1;
                }
            }
            "disagree" => disagree += 1,
            "ay_only" => ay_only += 1,
            "ref_only" => ref_only += 1,
            _ => {}
        }

        comp_items.push(ComparisonItem {
            file: ay_item.file.clone(),
            ay_result: ay_item.result.clone(),
            ay_time_sec: ay_item.time_sec,
            ref_result: ref_result.clone(),
            ref_time_sec: ref_time,
            agreement,
        });

        if !quiet && should_log_progress(idx, total, progress_every) {
            eprintln!(
                "[ref] {}/{}: {} ({})",
                idx + 1,
                total,
                benchmark.file_name().unwrap_or_default().to_string_lossy(),
                agreement,
            );
        }
    }

    let summary = ComparisonSummary {
        reference_solver: ref_name.to_string(),
        reference_solver_path: reference_provenance.path,
        reference_solver_version: reference_provenance.version_output,
        reference_solver_build_version: reference_provenance.build_version,
        reference_solver_build_commit: reference_provenance.build_commit,
        reference_solver_build_datetime_utc: reference_provenance.build_datetime_utc,
        reference_solver_build_stamp: reference_provenance.build_stamp,
        agree,
        disagree,
        ay_only,
        ref_only,
        both_solved,
        ay_faster,
        ref_faster,
        ay_total_time: round6(ay_total),
        ref_total_time: round6(ref_total),
    };

    (summary, comp_items)
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn pipe_capture_preserves_output_below_limit() {
        let input = vec![b'x'; CAPTURE_HEAD_BYTES + 4096];
        let capture = PipeCapture::start(std::io::Cursor::new(input.clone()));
        assert_eq!(capture.finish().as_bytes(), input);
    }

    #[cfg(unix)]
    fn write_solver_script(
        dir: &TempDir,
        name: &str,
        version_output: &str,
        verdict: &str,
    ) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.path().join(name);
        let body = format!(
            "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then\ncat <<'EOF'\n{version_output}\nEOF\nexit 0\nfi\nprintf '%s\\n' {verdict}\n"
        );
        std::fs::write(&path, body).expect("write solver script");
        let mut perms = std::fs::metadata(&path).expect("metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("chmod");
        path
    }

    #[cfg(unix)]
    fn shell_quote(value: &str) -> String {
        format!("'{}'", value.replace('\'', "'\\''"))
    }

    #[cfg(unix)]
    fn write_artifact_probe_solver_script(
        dir: &TempDir,
        argv_file: &Path,
        env_file: &Path,
    ) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.path().join("artifact-probe-solver.sh");
        let body = format!(
            "#!/bin/sh\n\
             if [ \"$1\" = \"--version\" ]; then\n\
             printf '%s\\n' 'ay artifact probe'\n\
             exit 0\n\
             fi\n\
             printf '%s\\n' \"$@\" > {}\n\
             {{\n\
               printf 'AY_SAT_TRACK=%s\\n' \"$AY_SAT_TRACK\"\n\
               printf 'AY_SAT_AI_CLASS=%s\\n' \"$AY_SAT_AI_CLASS\"\n\
               printf 'AY_SAT_PROFILE_ID=%s\\n' \"$AY_SAT_PROFILE_ID\"\n\
               printf 'AY_SAT_COMPETITION_PROFILE=%s\\n' \"$AY_SAT_COMPETITION_PROFILE\"\n\
             }} > {}\n\
             proof=''\n\
             while [ \"$#\" -gt 0 ]; do\n\
               if [ \"$1\" = \"--proof\" ]; then\n\
                 shift\n\
                 proof=\"$1\"\n\
               fi\n\
               shift\n\
             done\n\
             if [ -n \"$proof\" ]; then\n\
               mkdir -p \"$(dirname \"$proof\")\"\n\
               printf '%s\\n' 'proof-bytes' > \"$proof\"\n\
             fi\n\
             printf '%s\\n' 'c sat.policy: variant=default' >&2\n\
             printf '%s\\n' 'c sat.policy_source: --sat-variant' >&2\n\
             printf '%s\\n' 'c sat.route_profile: official-satcomp-main-lrat' >&2\n\
             printf '%s\\n' 'c sat.route_fail_closed: yes' >&2\n\
             printf '%s\\n' 'c sat.guidance_loaded: no' >&2\n\
             printf '%s\\n' 'c sat.proof_active: yes' >&2\n\
             printf '%s\\n' 'c sat.proof_format: lrat' >&2\n\
             printf '%s\\n' 'c sat.proof_origin: file' >&2\n\
             printf '%s\\n' 'c sat.verify_proof: off' >&2\n\
             printf '%s\\n' 'unsat'\n",
            shell_quote(&argv_file.display().to_string()),
            shell_quote(&env_file.display().to_string())
        );
        std::fs::write(&path, body).expect("write artifact probe solver script");
        let mut perms = std::fs::metadata(&path).expect("metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("chmod");
        path
    }

    #[cfg(unix)]
    fn write_arg_capture_solver_script(dir: &TempDir, name: &str, argv_file: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.path().join(name);
        let body = format!(
            "#!/bin/sh\n\
             if [ \"$1\" = \"--version\" ]; then\n\
             printf '%s\\n' '{} version 1.0'\n\
             exit 0\n\
             fi\n\
             printf '%s\\n' \"$@\" > {}\n\
             printf '%s\\n' 'sat'\n",
            name,
            shell_quote(&argv_file.display().to_string())
        );
        std::fs::write(&path, body).expect("write arg capture solver script");
        let mut perms = std::fs::metadata(&path).expect("metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("chmod");
        path
    }

    #[test]
    fn test_external_solver_args_leave_z3_on_wrapper_timeout() {
        let args = external_solver_args(Path::new("/usr/bin/z3"), Path::new("case.smt2"), 2.4);
        let strings = args
            .iter()
            .map(|arg| arg.to_string_lossy().to_string())
            .collect::<Vec<_>>();
        assert_eq!(strings, vec!["--", "case.smt2"]);
    }

    #[test]
    fn test_external_solver_args_special_case_golem() {
        let args = external_solver_args(Path::new("/tmp/golem"), Path::new("case.smt2"), 30.0);
        let strings = args
            .iter()
            .map(|arg| arg.to_string_lossy().to_string())
            .collect::<Vec<_>>();
        assert_eq!(strings, vec!["-l", "QF_LIA", "-e", "spacer", "case.smt2"]);
    }

    #[cfg(unix)]
    fn write_signaled_reference_solver_script(dir: &TempDir) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.path().join("signaled-reference-solver.sh");
        let body = "#!/bin/sh\n\
                    if [ \"$1\" = \"--version\" ]; then\n\
                    printf '%s\\n' 'signaled reference solver'\n\
                    exit 0\n\
                    fi\n\
                    kill -ABRT $$\n";
        std::fs::write(&path, body).expect("write signaled reference script");
        let mut perms = std::fs::metadata(&path).expect("metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("chmod");
        path
    }

    #[cfg(unix)]
    fn write_forking_timeout_solver_script(dir: &TempDir, pid_file: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.path().join("forking-timeout-solver.sh");
        let body = format!(
            "#!/bin/sh\n\
             if [ \"$1\" = \"--version\" ]; then\n\
             printf '%s\\n' 'forking timeout solver'\n\
             exit 0\n\
             fi\n\
             (\n\
               trap '' TERM\n\
               while :; do sleep 5; done\n\
             ) &\n\
             printf '%s\\n' \"$!\" > {}\n\
             trap '' TERM\n\
             wait\n",
            shell_quote(&pid_file.display().to_string())
        );
        std::fs::write(&path, body).expect("write forking solver script");
        let mut perms = std::fs::metadata(&path).expect("metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("chmod");
        path
    }

    #[cfg(unix)]
    fn write_exiting_pipe_leak_solver_script(dir: &TempDir, pid_file: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.path().join("exiting-pipe-leak-solver.sh");
        let body = format!(
            "#!/bin/sh\n\
             if [ \"$1\" = \"--version\" ]; then\n\
             printf '%s\\n' 'exiting pipe leak solver'\n\
             exit 0\n\
             fi\n\
             printf '%s\\n' 'sat'\n\
             (\n\
               trap '' TERM\n\
               while :; do sleep 5; done\n\
             ) &\n\
             printf '%s\\n' \"$!\" > {}\n\
             exit 0\n",
            shell_quote(&pid_file.display().to_string())
        );
        std::fs::write(&path, body).expect("write pipe leak solver script");
        let mut perms = std::fs::metadata(&path).expect("metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("chmod");
        path
    }

    #[cfg(unix)]
    fn read_pid_file(path: &Path) -> i32 {
        std::fs::read_to_string(path)
            .expect("read child pid file")
            .trim()
            .parse::<i32>()
            .expect("parse child pid")
    }

    #[cfg(unix)]
    fn pid_is_alive(pid: i32) -> bool {
        use nix::errno::Errno;
        use nix::unistd::Pid;

        match nix::sys::signal::kill(Pid::from_raw(pid), None) {
            Ok(()) | Err(Errno::EPERM) => true,
            Err(Errno::ESRCH) => false,
            Err(_) => true,
        }
    }

    #[cfg(unix)]
    fn wait_until_pid_exits(pid: i32, timeout: Duration) -> bool {
        let deadline = Instant::now() + timeout;
        while Instant::now() < deadline {
            if !pid_is_alive(pid) {
                return true;
            }
            std::thread::sleep(Duration::from_millis(25));
        }
        !pid_is_alive(pid)
    }

    #[cfg(unix)]
    struct PidCleanup(Option<i32>);

    #[cfg(unix)]
    impl Drop for PidCleanup {
        fn drop(&mut self) {
            use nix::sys::signal::Signal;
            use nix::unistd::Pid;

            if let Some(pid) = self.0 {
                let _ = nix::sys::signal::kill(Pid::from_raw(pid), Some(Signal::SIGKILL));
            }
        }
    }

    #[cfg(unix)]
    static PROCESS_GROUP_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[cfg(unix)]
    fn process_group_test_guard() -> std::sync::MutexGuard<'static, ()> {
        PROCESS_GROUP_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    #[test]
    fn test_parse_verdict_sat() {
        assert_eq!(parse_verdict("sat\n", None), "sat");
        assert_eq!(parse_verdict("SAT\n", None), "sat");
        assert_eq!(parse_verdict("s satisfiable\n", None), "sat");
    }

    #[test]
    fn test_parse_verdict_unsat() {
        assert_eq!(parse_verdict("unsat\n", None), "unsat");
        assert_eq!(parse_verdict("UNSAT\n", None), "unsat");
        assert_eq!(parse_verdict("s unsatisfiable\n", None), "unsat");
    }

    #[test]
    fn test_parse_verdict_exit_code() {
        assert_eq!(parse_verdict("", Some(10)), "sat");
        assert_eq!(parse_verdict("", Some(20)), "unsat");
        assert_eq!(parse_verdict("", Some(0)), "error");
        assert_eq!(parse_verdict("", None), "error");
    }

    #[test]
    fn test_parse_reference_verdict_signaled_empty_stdout_is_unknown() {
        assert_eq!(parse_reference_verdict("", None), "unknown");
        assert_eq!(parse_reference_verdict("sat\n", None), "sat");
        assert_eq!(parse_reference_verdict("", Some(0)), "error");
    }

    #[test]
    fn test_parse_verdict_unknown() {
        assert_eq!(parse_verdict("unknown\n", None), "unknown");
        assert_eq!(parse_verdict("s unknown\n", None), "unknown");
    }

    #[test]
    fn test_guess_expected_unsat_dir() {
        let path = Path::new("/benchmarks/unsat/foo.cnf");
        assert_eq!(guess_expected_from_path(path), Some("unsat".into()));
    }

    #[test]
    fn test_guess_expected_sat_dir() {
        let path = Path::new("/benchmarks/sat/foo.cnf");
        assert_eq!(guess_expected_from_path(path), Some("sat".into()));
    }

    #[test]
    fn test_guess_expected_uf_prefix() {
        let path = Path::new("/benchmarks/uf100-01.cnf");
        assert_eq!(guess_expected_from_path(path), Some("sat".into()));
    }

    #[test]
    fn test_guess_expected_uuf_prefix() {
        let path = Path::new("/benchmarks/uuf100-01.cnf");
        assert_eq!(guess_expected_from_path(path), Some("unsat".into()));
    }

    #[test]
    fn test_guess_expected_none() {
        let path = Path::new("/benchmarks/problem42.cnf");
        assert_eq!(guess_expected_from_path(path), None);
    }

    #[test]
    fn test_guess_expected_uflra_not_sat() {
        // UFLRA/UFLIA are SMT-LIB logic names, not SATLIB uf-prefix files
        let path = Path::new("/benchmarks/smt/uflra_simple.smt2");
        assert_eq!(guess_expected_from_path(path), None);
        let path = Path::new("/benchmarks/smt/uflia_test.smt2");
        assert_eq!(guess_expected_from_path(path), None);
    }

    #[test]
    fn test_is_benchmark_file_sat() {
        assert!(is_benchmark_file(Path::new("test.cnf"), "sat"));
        assert!(is_benchmark_file(Path::new("test.cnf.xz"), "sat"));
        assert!(is_benchmark_file(Path::new("test.cnf.gz"), "sat"));
        assert!(is_benchmark_file(Path::new("test.cnf.bz2"), "sat"));
        assert!(!is_benchmark_file(Path::new("test.smt2"), "sat"));
    }

    #[test]
    fn test_needs_decompression() {
        assert!(needs_decompression(Path::new("test.cnf.xz")));
        assert!(needs_decompression(Path::new("test.cnf.gz")));
        assert!(needs_decompression(Path::new("test.cnf.bz2")));
        assert!(!needs_decompression(Path::new("test.cnf")));
        assert!(!needs_decompression(Path::new("test.smt2")));
    }

    #[test]
    fn test_is_benchmark_file_smt() {
        assert!(is_benchmark_file(Path::new("test.smt2"), "smt"));
        assert!(!is_benchmark_file(Path::new("test.cnf"), "smt"));
    }

    #[test]
    fn test_is_benchmark_file_sygus() {
        assert!(is_benchmark_file(Path::new("inv.sl"), "sygus"));
        assert!(!is_benchmark_file(Path::new("test.smt2"), "sygus"));
    }

    #[test]
    fn test_is_benchmark_file_maxsat() {
        assert!(is_benchmark_file(Path::new("test.wcnf"), "maxsat"));
        assert!(is_benchmark_file(Path::new("test.wcnf.xz"), "maxsat"));
        assert!(!is_benchmark_file(Path::new("test.cnf"), "maxsat"));
    }

    #[test]
    fn test_is_benchmark_file_qbf() {
        assert!(is_benchmark_file(Path::new("test.qdimacs"), "qbf"));
        assert!(is_benchmark_file(Path::new("test.qdimacs.gz"), "qbf"));
        assert!(!is_benchmark_file(Path::new("test.cnf"), "qbf"));
    }

    #[test]
    fn test_is_benchmark_file_allsat() {
        assert!(is_benchmark_file(Path::new("test.cnf"), "allsat"));
        assert!(is_benchmark_file(Path::new("test.smt2"), "allsat"));
        assert!(is_benchmark_file(Path::new("test.aig"), "allsat"));
        assert!(is_benchmark_file(Path::new("test.aag"), "allsat"));
        assert!(!is_benchmark_file(Path::new("test.sl"), "allsat"));
    }

    #[test]
    fn test_is_benchmark_file_counting() {
        assert!(is_benchmark_file(Path::new("test.cnf"), "counting"));
        assert!(is_benchmark_file(Path::new("test.cnf.gz"), "counting"));
        assert!(is_benchmark_file(Path::new("test.smt2"), "counting"));
        assert!(!is_benchmark_file(Path::new("test.sl"), "counting"));
    }

    #[test]
    fn test_is_benchmark_file_omt() {
        assert!(is_benchmark_file(Path::new("test.smt2"), "omt"));
        assert!(!is_benchmark_file(Path::new("test.cnf"), "omt"));
    }

    #[test]
    fn test_is_benchmark_file_hwmcc() {
        assert!(is_benchmark_file(Path::new("test.btor2"), "hwmcc"));
        assert!(!is_benchmark_file(Path::new("test.cnf"), "hwmcc"));
        assert!(!is_benchmark_file(Path::new("test.smt2"), "hwmcc"));
    }

    #[test]
    fn test_classify_agreement() {
        assert_eq!(classify_agreement("sat", "sat"), "agree");
        assert_eq!(classify_agreement("unsat", "unsat"), "agree");
        assert_eq!(classify_agreement("sat", "unsat"), "disagree");
        assert_eq!(classify_agreement("unsat", "sat"), "disagree");
        assert_eq!(classify_agreement("sat", "timeout"), "ay_only");
        assert_eq!(classify_agreement("unsat", "unknown"), "ay_only");
        assert_eq!(classify_agreement("timeout", "sat"), "ref_only");
        assert_eq!(classify_agreement("error", "unsat"), "ref_only");
        assert_eq!(classify_agreement("timeout", "unknown"), "both_unknown");
        assert_eq!(classify_agreement("error", "error"), "both_unknown");
    }

    #[test]
    fn test_should_log_progress_respects_interval() {
        assert!(should_log_progress(0, 150, 10));
        assert!(!should_log_progress(1, 150, 10));
        assert!(should_log_progress(9, 150, 10));
        assert!(should_log_progress(149, 150, 10));
    }

    #[test]
    fn test_should_log_progress_can_log_every_row() {
        assert!(should_log_progress(0, 3, 1));
        assert!(should_log_progress(1, 3, 1));
        assert!(should_log_progress(2, 3, 1));
    }

    // --- CPU time parsing ---

    #[test]
    fn test_parse_posix_time_basic() {
        let output = "real 1.23\nuser 0.80\nsys 0.05\n";
        let cpu = parse_posix_time_output(output);
        assert!((cpu.unwrap() - 0.85).abs() < 0.001);
    }

    #[test]
    fn test_parse_posix_time_with_solver_stderr() {
        // Solver may print its own stderr before /usr/bin/time output
        let output = "c --- AY statistics ---\n\
                       c ay.mode:          dimacs-sat\n\
                       c ay.result:               sat\n\
                       c ay.wall_time_ms:          42\n\
                       real 1.50\n\
                       user 1.20\n\
                       sys 0.10\n\
                                    1261568  maximum resident set size\n";
        let cpu = parse_posix_time_output(output);
        assert!((cpu.unwrap() - 1.30).abs() < 0.001);
    }

    #[test]
    fn test_parse_posix_time_zero() {
        let output = "real 0.00\nuser 0.00\nsys 0.00\n";
        let cpu = parse_posix_time_output(output);
        assert!((cpu.unwrap()).abs() < 0.001);
    }

    #[test]
    fn test_parse_posix_time_large_values() {
        let output = "real 3600.50\nuser 3590.12\nsys 8.34\n";
        let cpu = parse_posix_time_output(output);
        assert!((cpu.unwrap() - 3598.46).abs() < 0.001);
    }

    #[test]
    fn test_parse_posix_time_missing_fields() {
        // Missing sys line
        let output = "real 1.23\nuser 0.80\n";
        assert!(parse_posix_time_output(output).is_none());

        // Missing user line
        let output = "real 1.23\nsys 0.05\n";
        assert!(parse_posix_time_output(output).is_none());

        // Empty
        assert!(parse_posix_time_output("").is_none());
    }

    #[test]
    fn test_parse_posix_time_macos_extended_output() {
        // macOS /usr/bin/time -lp outputs extra fields after real/user/sys
        let output = "real 0.02\n\
                       user 0.00\n\
                       sys 0.00\n\
                                    1261568  maximum resident set size\n\
                                          0  average shared memory size\n\
                                        229  page reclaims\n";
        let cpu = parse_posix_time_output(output);
        assert!(cpu.unwrap().abs() < 0.001);
    }

    #[test]
    fn test_has_usr_bin_time() {
        // On macOS (test environment), /usr/bin/time should exist
        #[cfg(target_os = "macos")]
        assert!(has_usr_bin_time());
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_timeout_reaps_process_group_descendants() {
        let _guard = process_group_test_guard();
        let tmp = tempfile::tempdir().expect("tempdir");
        let pid_file = tmp.path().join("child.pid");
        let solver = write_forking_timeout_solver_script(&tmp, &pid_file);
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &solver,
            benchmarks_dir: tmp.path(),
            timeout_sec: 5.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        assert_eq!(results.items.len(), 1);
        assert_eq!(results.items[0].result, "timeout");
        let child_pid = read_pid_file(&pid_file);
        let _cleanup = PidCleanup(Some(child_pid));
        assert!(
            wait_until_pid_exits(child_pid, Duration::from_secs(2)),
            "timeout must reap descendant process pid {child_pid}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_external_solver_timeout_reaps_process_group_descendants() {
        let _guard = process_group_test_guard();
        let tmp = tempfile::tempdir().expect("tempdir");
        let pid_file = tmp.path().join("external-child.pid");
        let solver = write_forking_timeout_solver_script(&tmp, &pid_file);
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        // Give the shell helper enough time to write the descendant pid before
        // the timeout path reaps the process group on loaded hosts.
        let (verdict, elapsed) = run_external_solver(&solver, &benchmark, 5.0, None);

        assert_eq!(verdict, "timeout");
        assert_eq!(elapsed, 5.0);
        let child_pid = read_pid_file(&pid_file);
        let _cleanup = PidCleanup(Some(child_pid));
        assert!(
            wait_until_pid_exits(child_pid, Duration::from_secs(2)),
            "reference-solver timeout must reap descendant process pid {child_pid}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_external_solver_empty_signal_is_unknown() {
        let _guard = process_group_test_guard();
        let tmp = tempfile::tempdir().expect("tempdir");
        let solver = write_signaled_reference_solver_script(&tmp);
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let (verdict, elapsed) = run_external_solver(&solver, &benchmark, 5.0, None);

        assert_eq!(verdict, "unknown");
        assert!(elapsed < 5.0);
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_reaps_pipe_leak_descendant_after_wrapper_exit() {
        let _guard = process_group_test_guard();
        let tmp = tempfile::tempdir().expect("tempdir");
        let pid_file = tmp.path().join("pipe-leak-child.pid");
        let solver = write_exiting_pipe_leak_solver_script(&tmp, &pid_file);
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &solver,
            benchmarks_dir: tmp.path(),
            timeout_sec: 15.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        assert_eq!(results.items.len(), 1);
        assert_eq!(results.items[0].result, "sat");
        let child_pid = read_pid_file(&pid_file);
        let _cleanup = PidCleanup(Some(child_pid));
        assert!(
            wait_until_pid_exits(child_pid, Duration::from_secs(2)),
            "successful wrapper exit must reap descendant holding stdout/stderr pid {child_pid}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_external_solver_reaps_pipe_leak_descendant_after_wrapper_exit() {
        let _guard = process_group_test_guard();
        let tmp = tempfile::tempdir().expect("tempdir");
        let pid_file = tmp.path().join("external-pipe-leak-child.pid");
        let solver = write_exiting_pipe_leak_solver_script(&tmp, &pid_file);
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let (verdict, _) = run_external_solver(&solver, &benchmark, 15.0, None);

        assert_eq!(verdict, "sat");
        let child_pid = read_pid_file(&pid_file);
        let _cleanup = PidCleanup(Some(child_pid));
        assert!(
            wait_until_pid_exits(child_pid, Duration::from_secs(2)),
            "reference wrapper exit must reap descendant holding stdout/stderr pid {child_pid}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_preserves_solver_provenance_in_reports() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let ay_version = "\
0.9.0+build.42.abc123@2026-04-21T12:34:56Z
build.version=0.9.0
build.commit=abc123
build.datetime_utc=2026-04-21T12:34:56Z
build.stamp=0.9.0+build.42.abc123@2026-04-21T12:34:56Z";
        let ref_version = "z3 4.13.0";
        let ay = write_solver_script(&tmp, "fake-ay.sh", ay_version, "sat");
        let reference = write_solver_script(&tmp, "fake-ref.sh", ref_version, "sat");
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 1.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: vec![("fake-ref.sh".to_string(), reference.clone())],
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        assert_eq!(results.environment.ay_path, ay.display().to_string());
        assert_eq!(
            results.environment.ay_build_stamp,
            "0.9.0+build.42.abc123@2026-04-21T12:34:56Z"
        );
        assert_eq!(results.environment.ay_version, ay_version);

        let comparison = results.comparison.expect("comparison summary");
        assert_eq!(comparison.reference_solver, "fake-ref.sh");
        assert_eq!(
            comparison.reference_solver_path,
            reference.display().to_string()
        );
        assert_eq!(comparison.reference_solver_version, ref_version);
        assert_eq!(comparison.reference_solver_build_version, ref_version);
        assert_eq!(comparison.reference_solver_build_commit, "unknown");
        assert_eq!(comparison.reference_solver_build_datetime_utc, "unknown");
        assert_eq!(comparison.reference_solver_build_stamp, ref_version);
        assert_eq!(comparison.agree, 1);
        assert_eq!(comparison.disagree, 0);
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_records_sat_profile_argv_and_metadata() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let ay = write_solver_script(&tmp, "fake-ay.sh", "ay test", "sat");
        let benchmark = tmp.path().join("sample.cnf");
        std::fs::write(&benchmark, "p cnf 1 1\n1 0\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 1.0,
            domain: "sat",
            quiet: true,
            file_list: Some(vec![benchmark.clone()]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: vec!["--sat-variant".to_string(), "probe".to_string()],
            sat_track: Some("Main Track".to_string()),
            sat_ai_class: Some("experimental".to_string()),
            sat_variant: Some("probe".to_string()),
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        assert_eq!(results.settings.domain, "sat");
        assert_eq!(results.settings.runs, 1);
        assert_eq!(
            results.settings.solver_args,
            vec!["--sat-variant".to_string(), "probe".to_string()]
        );
        assert_eq!(results.settings.sat_track.as_deref(), Some("Main Track"));
        assert_eq!(
            results.settings.sat_ai_class.as_deref(),
            Some("experimental")
        );
        assert_eq!(results.settings.sat_variant.as_deref(), Some("probe"));
        assert_eq!(
            results
                .settings
                .solver_env
                .get("AY_SAT_TRACK")
                .map(String::as_str),
            Some("main")
        );
        assert_eq!(
            results
                .settings
                .solver_env
                .get("AY_SAT_PROFILE_ID")
                .map(String::as_str),
            Some("ay-sat-experimental-main")
        );
        let profile = results
            .settings
            .sat_competition_profile
            .as_ref()
            .expect("profile metadata");
        assert_eq!(profile.track.as_deref(), Some("Main Track"));
        assert_eq!(profile.normalized_track.as_deref(), Some("main"));

        let item = results.items.first().expect("result item");
        assert_eq!(item.result, "sat");
        assert_eq!(item.benchmark_path, benchmark.display().to_string());
        assert_eq!(item.solver_env, results.settings.solver_env);
        assert_eq!(
            item.solver_argv,
            vec![
                ay.display().to_string(),
                "--sat-variant".to_string(),
                "probe".to_string(),
                "--".to_string(),
                benchmark.display().to_string(),
            ]
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_separates_benchmark_paths_from_solver_options() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let ref_argv_file = tmp.path().join("ref-argv.txt");
        let ay = write_solver_script(&tmp, "fake-ay.sh", "ay test", "sat");
        let reference = write_arg_capture_solver_script(&tmp, "fake-ref.sh", &ref_argv_file);
        let benchmark = tmp
            .path()
            .join("maze-generation-width=15-height=15-density=0.01-run=1.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 1.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark.clone()]),
            runs: 1,
            reference_solvers: vec![(crate::native::reference_display_name(&reference), reference)],
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        let item = results.items.first().expect("result item");
        assert_eq!(
            item.solver_argv,
            vec![
                ay.display().to_string(),
                "--".to_string(),
                benchmark.display().to_string(),
            ]
        );
        assert_eq!(item.result, "sat");
        assert_eq!(results.comparison.expect("comparison").agree, 1);

        let ref_argv = std::fs::read_to_string(ref_argv_file).expect("read ref argv");
        let benchmark_arg = benchmark.display().to_string();
        assert_eq!(
            ref_argv.lines().collect::<Vec<_>>(),
            vec!["--", benchmark_arg.as_str()]
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_captures_sat_artifacts_env_and_run_metadata() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let argv_file = tmp.path().join("argv.txt");
        let env_file = tmp.path().join("env.txt");
        let ay = write_artifact_probe_solver_script(&tmp, &argv_file, &env_file);
        let benchmark = tmp.path().join("sample.cnf");
        let artifact_dir = tmp.path().join("artifacts");
        std::fs::write(&benchmark, "p cnf 1 1\n1 0\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 1.0,
            domain: "sat",
            quiet: true,
            file_list: Some(vec![benchmark.clone()]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: vec!["--sat-variant".to_string(), "default".to_string()],
            sat_track: Some("main".to_string()),
            sat_ai_class: Some("regular".to_string()),
            sat_variant: Some("default".to_string()),
            environment: None,
            artifact_output_dir: Some(artifact_dir.clone()),
            resources: None,
        })
        .expect("run native");

        assert_eq!(
            results.settings.artifact_output_dir.as_deref(),
            Some(artifact_dir.display().to_string().as_str())
        );
        assert_eq!(
            results
                .settings
                .solver_env
                .get("AY_SAT_TRACK")
                .map(String::as_str),
            Some("main")
        );
        assert_eq!(
            results
                .settings
                .solver_env
                .get("AY_SAT_AI_CLASS")
                .map(String::as_str),
            Some("regular")
        );
        assert_eq!(
            results
                .settings
                .solver_env
                .get("AY_SAT_PROFILE_ID")
                .map(String::as_str),
            Some("ay-sat-regular-main")
        );

        let item = results.items.first().expect("result item");
        assert_eq!(item.result, "unsat");
        assert_eq!(item.benchmark_path, benchmark.display().to_string());
        assert_eq!(item.solver_env, results.settings.solver_env);

        let proof_index = item
            .solver_argv
            .iter()
            .position(|arg| arg == "--proof")
            .expect("argv should include explicit proof path");
        let proof_path = PathBuf::from(&item.solver_argv[proof_index + 1]);
        assert_eq!(proof_path.parent(), Some(artifact_dir.as_path()));
        assert_eq!(
            proof_path.extension().and_then(|e| e.to_str()),
            Some("lrat")
        );

        let artifacts = item.artifacts.as_ref().expect("artifact metadata");
        assert_eq!(artifacts.output_dir, artifact_dir.display().to_string());
        assert_eq!(
            artifacts.proof_path.as_deref(),
            Some(proof_path.display().to_string().as_str())
        );
        assert_eq!(artifacts.proof_format.as_deref(), Some("lrat"));
        assert_eq!(artifacts.proof_exists, Some(true));
        assert_eq!(artifacts.proof_bytes, Some(12));
        let proof_hash = artifacts.proof_hash.as_deref().expect("proof hash");
        assert!(proof_hash.starts_with("fh128:"));
        assert_eq!(
            proof_hash,
            content_hash_file(&proof_path)
                .expect("hash proof artifact")
                .as_str()
        );

        let sat_run = item.sat_run.as_ref().expect("SAT applied run metadata");
        assert_eq!(
            sat_run.route_profile.as_deref(),
            Some("official-satcomp-main-lrat")
        );
        assert_eq!(sat_run.proof_active.as_deref(), Some("yes"));
        assert_eq!(sat_run.proof_format.as_deref(), Some("lrat"));

        let env_text = std::fs::read_to_string(env_file).expect("read env capture");
        assert!(env_text.contains("AY_SAT_TRACK=main"));
        assert!(env_text.contains("AY_SAT_AI_CLASS=regular"));
        assert!(env_text.contains("AY_SAT_PROFILE_ID=ay-sat-regular-main"));

        let argv_text = std::fs::read_to_string(argv_file).expect("read argv capture");
        assert!(argv_text.contains("--proof"));
        assert!(argv_text.contains(&proof_path.display().to_string()));
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_records_missing_sat_proof_file_metadata() {
        // Regression for the SAT artifact audit path: a planned proof path that
        // the solver does not write must remain explicit in result metadata.
        let tmp = tempfile::tempdir().expect("tempdir");
        let ay = write_solver_script(&tmp, "fake-ay-no-proof.sh", "ay no proof", "unsat");
        let benchmark = tmp.path().join("missing-proof.cnf");
        let artifact_dir = tmp.path().join("artifacts");
        std::fs::write(&benchmark, "p cnf 1 1\n-1 0\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 1.0,
            domain: "sat",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: vec!["--sat-variant".to_string(), "default".to_string()],
            sat_track: Some("main".to_string()),
            sat_ai_class: Some("regular".to_string()),
            sat_variant: Some("default".to_string()),
            environment: None,
            artifact_output_dir: Some(artifact_dir.clone()),
            resources: None,
        })
        .expect("run native");

        let item = results.items.first().expect("result item");
        assert_eq!(item.result, "unsat");

        let proof_index = item
            .solver_argv
            .iter()
            .position(|arg| arg == "--proof")
            .expect("argv should include explicit proof path");
        let proof_path = PathBuf::from(&item.solver_argv[proof_index + 1]);
        assert_eq!(proof_path.parent(), Some(artifact_dir.as_path()));
        assert!(!proof_path.exists(), "fake solver must not create proof");

        let artifacts = item.artifacts.as_ref().expect("artifact metadata");
        assert_eq!(artifacts.output_dir, artifact_dir.display().to_string());
        assert_eq!(
            artifacts.proof_path.as_deref(),
            Some(proof_path.display().to_string().as_str())
        );
        assert_eq!(artifacts.proof_format.as_deref(), Some("lrat"));
        assert_eq!(artifacts.proof_exists, Some(false));
        assert_eq!(artifacts.proof_bytes, None);
        assert_eq!(artifacts.proof_hash, None);
    }

    #[test]
    fn test_reference_display_name_uses_file_name_with_path_fallback() {
        assert_eq!(
            reference_display_name(Path::new("/opt/solvers/z3")),
            "z3".to_string()
        );
        assert_eq!(
            reference_display_name(Path::new("reference/cadical-1.9.5")),
            "cadical-1.9.5".to_string()
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_multiple_references_populate_references_and_legacy_fields() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let ay = write_solver_script(&tmp, "fake-ay.sh", "ay test", "sat");
        let agreeing = write_solver_script(&tmp, "fake-agree.sh", "agree 1.0", "sat");
        let disagreeing = write_solver_script(&tmp, "fake-disagree.sh", "disagree 1.0", "unsat");
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 5.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: vec![
                ("agree-ref".to_string(), agreeing.clone()),
                ("disagree-ref".to_string(), disagreeing.clone()),
            ],
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        let references = results.references.as_deref().expect("references array");
        assert_eq!(references.len(), 2);
        assert_eq!(references[0].reference_solver, "agree-ref");
        assert_eq!(
            references[0].reference_solver_path,
            agreeing.display().to_string()
        );
        assert_eq!(references[0].reference_solver_version, "agree 1.0");
        assert_eq!(references[0].agree, 1);
        assert_eq!(references[0].disagree, 0);
        assert_eq!(references[1].reference_solver, "disagree-ref");
        assert_eq!(
            references[1].reference_solver_path,
            disagreeing.display().to_string()
        );
        assert_eq!(references[1].reference_solver_version, "disagree 1.0");
        assert_eq!(references[1].agree, 0);
        assert_eq!(references[1].disagree, 1);

        // Legacy fields mirror the FIRST reference for one release.
        let comparison = results.comparison.as_ref().expect("legacy comparison");
        assert_eq!(comparison.reference_solver, "agree-ref");
        assert_eq!(comparison.agree, references[0].agree);
        assert_eq!(comparison.ref_total_time, references[0].ref_total_time);
        let rows = results.comparisons.as_deref().expect("legacy rows");
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].ref_result, "sat");
        assert_eq!(rows[0].agreement, "agree");

        // No --run-class: nothing stamped.
        assert!(results.run_class.is_none());
        assert!(results.run_class_verified.is_none());
        assert!(results.host_fingerprint.is_none());
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_stamps_run_class_unverified_with_host_fingerprint() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let ay = write_solver_script(&tmp, "fake-ay.sh", "ay test", "sat");
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 5.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: Some("laptop".to_string()),
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        assert_eq!(results.run_class.as_deref(), Some("laptop"));
        // A class stamped by plain `bench run` is NEVER verified here.
        assert_eq!(results.run_class_verified, Some(false));
        let host = results.host_fingerprint.as_ref().expect("host fingerprint");
        assert!(!host.hw_model.is_empty());
        assert_eq!(host.cpu_model, results.environment.cpu_model);
        assert_eq!(host.cpu_count, results.environment.cpu_count);
        assert_eq!(host.memory_bytes, results.environment.memory_bytes);
    }

    #[cfg(unix)]
    #[test]
    fn test_results_json_omits_new_fields_when_not_requested() {
        // Backwards compatibility: an invocation without --reference-solver
        // and without --run-class must serialize the same top-level keys as
        // before this extension.
        let tmp = tempfile::tempdir().expect("tempdir");
        let ay = write_solver_script(&tmp, "fake-ay.sh", "ay test", "sat");
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 5.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        let value = serde_json::to_value(&results).expect("serialize results");
        let map = value.as_object().expect("results object");
        assert_eq!(
            map.keys().collect::<Vec<_>>(),
            vec!["environment", "items", "settings"],
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_results_json_shape_with_references_and_run_class() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let ay = write_solver_script(&tmp, "fake-ay.sh", "ay test", "sat");
        let reference = write_solver_script(&tmp, "fake-ref.sh", "ref 2.0", "sat");
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 5.0,
            domain: "smt",
            quiet: true,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: vec![("fake-ref.sh".to_string(), reference)],
            run_class: Some("replay".to_string()),
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            artifact_output_dir: None,
            resources: None,
        })
        .expect("run native");

        let value = serde_json::to_value(&results).expect("serialize results");
        let map = value.as_object().expect("results object");
        let expected_keys = [
            "environment",
            "items",
            "settings",
            "comparison",
            "comparisons",
            "run_class",
            "run_class_verified",
            "host_fingerprint",
            "references",
        ];
        assert_eq!(map.len(), expected_keys.len());
        for key in expected_keys {
            assert!(map.contains_key(key), "results object missing {key}");
        }

        assert_eq!(value["run_class"], "replay");
        assert_eq!(value["run_class_verified"], false);
        for key in ["hw_model", "cpu_model", "cpu_count", "memory_bytes"] {
            assert!(
                value["host_fingerprint"].get(key).is_some(),
                "host_fingerprint missing {key}"
            );
        }

        let references = value["references"].as_array().expect("references array");
        assert_eq!(references.len(), 1);
        // Each references[] entry carries name, path, probed version, and the
        // same summary shape as the legacy comparison block.
        assert_eq!(references[0]["reference_solver"], "fake-ref.sh");
        assert_eq!(
            references[0]["reference_solver_version"],
            value["comparison"]["reference_solver_version"]
        );
        assert_eq!(references[0], value["comparison"]);
    }
}
