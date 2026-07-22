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
use std::process::Stdio;
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
    /// Hash of the exact private bytes passed to the solver. This differs from
    /// `benchmark_content_hash` for compressed corpus entries.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver_input_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver_input_path: Option<String>,
    pub expected: Option<String>,
    pub expected_source: String,
    pub result: String,
    /// Bounded harness diagnostic kept separate so `result` remains a closed
    /// machine-readable verdict.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub harness_error: Option<String>,
    pub time_sec: f64,
    pub cpu_time_sec: f64,
    pub cpu_time_source: String,
    pub exit_code: Option<i32>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub solver_argv: Vec<String>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub solver_env: BTreeMap<String, String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifacts: Option<SolverArtifactMetadata>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sat_run: Option<SatAppliedRunMetadata>,
    /// Structural features extracted from the same private snapshot supplied
    /// to the solver. The runner persists these separately from results JSON.
    #[serde(skip)]
    pub extracted_features: Option<crate::features::ExtractedFeatures>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ComparisonItem {
    pub file: String,
    pub solver_input_hash: String,
    pub ay_result: String,
    pub ay_time_sec: f64,
    pub ref_result: String,
    pub ref_time_sec: f64,
    pub agreement: &'static str,
    pub reference_runs: Vec<ReferenceRunEvidence>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReferenceRunEvidence {
    pub result: String,
    pub time_sec: f64,
    pub exit_code: Option<i32>,
    pub solver_input_path: String,
    pub solver_input_hash: String,
    pub solver_argv: Vec<String>,
    pub solver_env: BTreeMap<String, String>,
    pub stdout_excerpt: String,
    pub stderr_excerpt: String,
    pub stdout_sha256: String,
    pub stderr_sha256: String,
    pub stdout_truncated: bool,
    pub stderr_truncated: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub harness_error: Option<String>,
}

/// Per-benchmark rows for one reference solver. Unlike the legacy
/// `NativeResults::comparisons` field, this preserves evidence for every
/// repeatable `--reference-solver` argument.
#[derive(Debug, Serialize)]
pub(crate) struct ReferenceComparisonItems {
    pub reference_solver: String,
    pub items: Vec<ComparisonItem>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ComparisonSummary {
    pub reference_solver: String,
    pub reference_solver_path: String,
    pub reference_solver_sha256: String,
    pub reference_solver_size_bytes: u64,
    pub reference_solver_version: String,
    pub reference_solver_build_version: String,
    pub reference_solver_build_commit: String,
    pub reference_solver_build_datetime_utc: String,
    pub reference_solver_build_stamp: String,
    pub reference_resource_enforcement: String,
    pub reference_resource_envelope: String,
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
    pub preprocessing: Vec<InputPreparationMetadata>,
    pub settings: NativeSettings,
    /// Legacy single-reference summary, kept populated with the first entry
    /// of `references` for one release (dropped in a schema bump).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparison: Option<ComparisonSummary>,
    /// Per-benchmark agreement rows for the first reference solver.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparisons: Option<Vec<ComparisonItem>>,
    /// Per-benchmark agreement rows for every reference solver, in flag order.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reference_comparisons: Option<Vec<ReferenceComparisonItems>>,
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

#[derive(Debug, Clone, Serialize)]
pub(crate) struct InputPreparationMetadata {
    pub benchmark_path: String,
    pub source_hash: String,
    pub solver_input_hash: String,
    pub source_bytes: u64,
    pub solver_input_bytes: u64,
    pub preprocessing_time_sec: f64,
    pub decompressed: bool,
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
    pub artifact_max_bytes: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_size_enforcement: Option<String>,
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
    /// Closed validation state. Native bench emission does not invoke a proof
    /// checker, so an emitted proof is explicitly `unchecked`.
    pub proof_validation: String,
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

#[derive(Debug)]
struct SolverArtifactPlan {
    output_dir: PathBuf,
    proof_path: PathBuf,
    /// Mode-0700 directory owned by this plan. The `TempDir` is deliberately
    /// disarmed before the path is exposed to the solver: recursive pathname
    /// cleanup must never delete a directory that was swapped after a stat.
    proof_staging: Option<PrivateProofStaging>,
    proof_work_path: PathBuf,
    /// Exact solver-output descriptor retained once finalization opens and
    /// authenticates the work path. Failure cleanup compares against this
    /// descriptor and preserves the staging directory on any replacement.
    proof_work_file: Option<std::fs::File>,
    /// Open descriptor returned only after `persist_noclobber` installed this
    /// plan's inode at `proof_path`. Cleanup must never infer ownership merely
    /// from the public pathname existing.
    published_proof: Option<std::fs::File>,
    proof_format: &'static str,
}

#[derive(Debug)]
struct PrivateProofStaging {
    path: PathBuf,
    /// Retained capability for authenticating the directory after it has
    /// first been moved away from the solver-visible pathname.
    directory: std::fs::File,
}

#[derive(Debug)]
struct NativeSolverRun {
    item: NativeResultItem,
    artifact_plan: Option<SolverArtifactPlan>,
}

#[cfg(target_os = "linux")]
struct ProofPublication(std::fs::File);

#[cfg(target_os = "linux")]
impl ProofPublication {
    fn new(output_dir: &Path) -> std::io::Result<Self> {
        tempfile::tempfile_in(output_dir).map(Self)
    }

    fn as_file_mut(&mut self) -> &mut std::fs::File {
        &mut self.0
    }

    fn persist_noclobber(self, destination: &Path) -> std::io::Result<std::fs::File> {
        use std::os::fd::AsRawFd as _;

        // `tempfile_in` returns an unnamed file on Linux (O_TMPFILE where
        // available, create-and-unlink otherwise). Linking through procfs
        // publishes the exact retained descriptor; there is no mutable source
        // pathname to authenticate and then race.
        let descriptor_path = PathBuf::from(format!("/proc/self/fd/{}", self.0.as_raw_fd()));
        nix::unistd::linkat(
            None,
            descriptor_path.as_path(),
            None,
            destination,
            nix::fcntl::AtFlags::AT_SYMLINK_FOLLOW,
        )
        .map_err(|error| std::io::Error::from_raw_os_error(error as i32))?;
        Ok(self.0)
    }
}

#[cfg(not(target_os = "linux"))]
struct ProofPublication(tempfile::NamedTempFile);

#[cfg(not(target_os = "linux"))]
impl ProofPublication {
    fn new(output_dir: &Path) -> std::io::Result<Self> {
        tempfile::NamedTempFile::new_in(output_dir).map(Self)
    }

    fn as_file_mut(&mut self) -> &mut std::fs::File {
        self.0.as_file_mut()
    }

    fn persist_noclobber(self, destination: &Path) -> std::io::Result<std::fs::File> {
        self.0
            .persist_noclobber(destination)
            .map_err(|error| error.error)
    }
}

impl Drop for SolverArtifactPlan {
    fn drop(&mut self) {
        // Best-effort only: the explicit paths report cleanup failures. The
        // same quarantine implementation is used here so unwinding can never
        // fall back to recursive `TempDir` pathname deletion.
        let _ = cleanup_proof_staging(self);
    }
}

// ===================================================================
// Verdict parsing
// ===================================================================

fn parse_verdict(stdout: &str, stderr: &str, exit_code: Option<i32>) -> &'static str {
    crate::resource::strict_solver_verdict(stdout, stderr, exit_code)
}

fn parse_reference_verdict(stdout: &str, stderr: &str, exit_code: Option<i32>) -> &'static str {
    crate::resource::strict_solver_verdict(stdout, stderr, exit_code)
}

// ===================================================================
// Benchmark discovery
// ===================================================================

fn is_benchmark_file(path: &Path, domain: &str) -> bool {
    let name = match path.file_name().and_then(|n| n.to_str()) {
        Some(n) => n,
        None => return false,
    };
    let lower = name.to_ascii_lowercase();
    let base = [".xz", ".gz", ".bz2"]
        .iter()
        .find_map(|suffix| lower.strip_suffix(suffix))
        .unwrap_or(&lower);
    let extension = base.rsplit_once('.').map_or("", |(_, ext)| ext);
    match domain {
        "sat" => matches!(extension, "cnf" | "dimacs" | "icnf"),
        "chc" | "smt" => extension == "smt2",
        "hwmcc" => extension == "btor2",
        // Security benchmark domains
        "sygus" => extension == "sl",
        "maxsat" => extension == "wcnf",
        "qbf" => extension == "qdimacs",
        "allsat" => matches!(extension, "cnf" | "smt2" | "aig" | "aag"),
        "counting" => matches!(extension, "cnf" | "smt2"),
        "omt" => extension == "smt2",
        _ => matches!(
            extension,
            "smt2" | "cnf" | "btor2" | "sl" | "wcnf" | "qdimacs" | "aig" | "aag"
        ),
    }
}

/// Returns true if the benchmark path needs decompression before solving.
fn needs_decompression(path: &Path) -> bool {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("")
        .to_ascii_lowercase();
    name.ends_with(".xz") || name.ends_with(".gz") || name.ends_with(".bz2")
}

#[cfg(not(test))]
const DECOMPRESSED_FILE_LIMIT_BYTES: u64 = 8 * 1024 * 1024 * 1024;
#[cfg(test)]
const DECOMPRESSED_FILE_LIMIT_BYTES: u64 = 1024 * 1024;
#[cfg(not(test))]
const PROOF_ARTIFACT_LIMIT_BYTES: u64 = 8 * 1024 * 1024 * 1024;
#[cfg(test)]
const PROOF_ARTIFACT_LIMIT_BYTES: u64 = 1024 * 1024;
const MAX_BENCHMARK_RUNS: u32 = 10_000;
const MAX_REFERENCE_SOLVERS: usize = 16;
const MAX_REFERENCE_SNAPSHOT_BYTES: u64 = 4 * 1024 * 1024 * 1024;

/// Decompress a compressed benchmark to a temporary file under the same
/// enforced RSS and wall-clock envelope as a solver child.
/// Returns the path to the decompressed temp file. Caller must delete it.
#[derive(Debug)]
struct DecompressedInput {
    path: PathBuf,
    bytes: u64,
    sha256: String,
}

fn decompress_to_temp(
    path: &Path,
    resources: Option<&crate::resource::PlannedResources>,
    timeout_sec: f64,
) -> Result<DecompressedInput> {
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("bench");
    let lower_name = name.to_ascii_lowercase();
    let (decompressed_name, decompress_cmd) = if lower_name.ends_with(".xz") {
        (&name[..name.len() - ".xz".len()], "xz")
    } else if lower_name.ends_with(".gz") {
        (&name[..name.len() - ".gz".len()], "gzip")
    } else if lower_name.ends_with(".bz2") {
        (&name[..name.len() - ".bz2".len()], "bzip2")
    } else {
        return Err(BenchError::UnsupportedFormat {
            path: path.to_path_buf(),
        });
    };

    let resources = resources.ok_or_else(|| {
        BenchError::msg("compressed benchmarks require a planned resource envelope")
    })?;
    let (temp_path, output_file) = create_decompression_target(decompressed_name)?;

    let mut command = resources.external_command(decompress_cmd);
    command
        .args(["-d", "-k", "-c"])
        .arg(path)
        // Drain through a fixed-size writer. This bounds disk use without
        // retaining a second, potentially multi-gigabyte copy in the parent.
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .stdin(Stdio::null())
        .env("MEMLIMIT", resources.plan.memlimit_mb_per_child.to_string())
        .env("NBCORE", resources.plan.nbcore_per_child.to_string());
    let (mut child, watchdog) =
        match resources.spawn_external_child(&mut command, "ay bench decompress") {
            Ok(guarded) => guarded,
            Err(error) => {
                let _ = std::fs::remove_file(&temp_path);
                return Err(BenchError::msg(format!(
                    "failed to run {decompress_cmd} — is it installed? (needed for {}): {error}",
                    path.display()
                )));
            }
        };
    let Some(stdout_pipe) = child.stdout.take() else {
        let cleanup =
            crate::resource::terminate_guarded_child(&mut child, watchdog, "ay bench decompress");
        let removal = std::fs::remove_file(&temp_path);
        cleanup?;
        removal.with_bench_context(|| format!("removing {}", temp_path.display()))?;
        return Err(BenchError::msg(format!(
            "{decompress_cmd} stdout pipe was unavailable"
        )));
    };
    let output_capture = crate::resource::LimitedFileCapture::start(
        stdout_pipe,
        output_file,
        DECOMPRESSED_FILE_LIMIT_BYTES,
    );
    let output_breach = output_capture.breach_flag();
    let stderr_capture = child.stderr.take().map(PipeCapture::start);
    let timeout = Duration::from_secs_f64(timeout_sec.max(0.001));
    let outcome = crate::resource::wait_for_guarded_child_with_limits(
        &mut child,
        watchdog,
        timeout,
        "ay bench decompress",
        None,
        Some(output_breach.as_ref()),
    );
    let output = output_capture.finish();
    let stderr = stderr_capture
        .map(PipeCapture::finish)
        .unwrap_or_else(CapturedPipe::missing);
    let output = match output {
        Ok(output) => output,
        Err(error) => {
            let _ = std::fs::remove_file(&temp_path);
            return Err(error);
        }
    };
    if output.exceeded {
        let _ = std::fs::remove_file(&temp_path);
        return Err(BenchError::msg(format!(
            "{decompress_cmd} output for {} exceeded the fixed {}-byte decompressed-size cap",
            path.display(),
            DECOMPRESSED_FILE_LIMIT_BYTES
        )));
    }
    if output.write_failed || stderr.incomplete() {
        let _ = std::fs::remove_file(&temp_path);
        return Err(BenchError::msg(format!(
            "{decompress_cmd} output capture was incomplete on {}",
            path.display()
        )));
    }
    let outcome = match outcome {
        Ok(outcome) => outcome,
        Err(error) => {
            let _ = std::fs::remove_file(&temp_path);
            return Err(error);
        }
    };
    if outcome.memout {
        let _ = std::fs::remove_file(&temp_path);
        return Err(BenchError::msg(format!(
            "{decompress_cmd} exceeded the enforced memory envelope on {}",
            path.display()
        )));
    }
    if outcome.timed_out {
        let _ = std::fs::remove_file(&temp_path);
        return Err(BenchError::msg(format!(
            "{decompress_cmd} timed out after {timeout_sec:.3}s on {}",
            path.display()
        )));
    }
    let status = outcome.status.ok_or_else(|| {
        let _ = std::fs::remove_file(&temp_path);
        BenchError::msg(format!(
            "{decompress_cmd} was not reaped on {}",
            path.display()
        ))
    })?;
    if !status.success() {
        let _ = std::fs::remove_file(&temp_path);
        return Err(BenchError::msg(format!(
            "{decompress_cmd} failed on {}: {}",
            path.display(),
            stderr.text.trim()
        )));
    }

    Ok(DecompressedInput {
        path: temp_path,
        bytes: output.bytes_written,
        sha256: output.sha256,
    })
}

fn create_decompression_target(decompressed_name: &str) -> Result<(PathBuf, std::fs::File)> {
    // Do not create or trust a fixed world-writable `/tmp/ay-bench-decompress`
    // directory. `tempfile` creates a randomized mode-0600 file atomically in
    // the OS temp directory, so a pre-planted symlink cannot redirect output.
    let safe_name: String = decompressed_name
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || matches!(character, '.' | '-' | '_') {
                character
            } else {
                '_'
            }
        })
        .take(120)
        .collect();
    let suffix = format!("-{safe_name}");
    let target = tempfile::Builder::new()
        .prefix("ay-bench-")
        .suffix(&suffix)
        .tempfile()?;
    target
        .keep()
        .map(|(file, path)| (path, file))
        .map_err(|error| error.error.into())
}

pub(crate) struct PreparedBenchmark {
    pub(crate) solver_path: PathBuf,
    pub(crate) content_hash: String,
    pub(crate) solver_input_hash: String,
    expected: crate::harvest::ExpectedLabel,
    metadata: InputPreparationMetadata,
    _solver_guard: TempFileGuard,
}

pub(crate) fn prepare_benchmark(
    original: &Path,
    benchmark_id: &str,
    resources: &crate::resource::PlannedResources,
    timeout_sec: f64,
) -> Result<PreparedBenchmark> {
    use sha2::{Digest as _, Sha256};
    use std::io::Write as _;

    let started = Instant::now();
    let mut source_options = std::fs::OpenOptions::new();
    source_options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        source_options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let mut source = source_options.open(original).with_bench_context(|| {
        format!("opening benchmark snapshot source {}", original.display())
    })?;
    let before = source.metadata()?;
    if !before.file_type().is_file() {
        return Err(BenchError::msg(format!(
            "benchmark snapshot source is not a regular file: {}",
            original.display()
        )));
    }
    if before.len() > DECOMPRESSED_FILE_LIMIT_BYTES {
        return Err(BenchError::msg(format!(
            "benchmark {} exceeds the fixed {}-byte snapshot cap",
            original.display(),
            DECOMPRESSED_FILE_LIMIT_BYTES
        )));
    }
    let source_name = original
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| BenchError::msg("benchmark filename is not valid UTF-8"))?;
    let (pinned_source_path, mut pinned_source) = create_decompression_target(source_name)?;
    let source_guard = TempFileGuard(Some(pinned_source_path.clone()));
    let mut hasher = Sha256::new();
    let mut copied = 0_u64;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = source
            .read(&mut buffer)
            .with_bench_context(|| format!("reading benchmark snapshot {}", original.display()))?;
        if read == 0 {
            break;
        }
        copied = copied
            .checked_add(read as u64)
            .ok_or_else(|| BenchError::msg("benchmark snapshot size overflow"))?;
        if copied > DECOMPRESSED_FILE_LIMIT_BYTES {
            return Err(BenchError::msg(format!(
                "benchmark {} exceeds the fixed {}-byte snapshot cap",
                original.display(),
                DECOMPRESSED_FILE_LIMIT_BYTES
            )));
        }
        hasher.update(&buffer[..read]);
        pinned_source.write_all(&buffer[..read])?;
    }
    pinned_source.sync_all()?;
    let after = source.metadata()?;
    let path_after = std::fs::symlink_metadata(original)?;
    if !same_file_identity_without_link_count(&before, &after)
        || !same_file_identity_without_link_count(&after, &path_after)
        || copied != after.len()
    {
        return Err(BenchError::msg(format!(
            "benchmark changed while creating its private snapshot: {}",
            original.display()
        )));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::set_permissions(&pinned_source_path, std::fs::Permissions::from_mode(0o400))?;
    }

    let source_hash = format!("sha256:{:x}", hasher.finalize());
    let decompressed = needs_decompression(original);
    let (solver_path, solver_guard, solver_input_bytes, solver_input_hash) = if decompressed {
        let decompressed_input =
            decompress_to_temp(&pinned_source_path, Some(resources), timeout_sec)?;
        let DecompressedInput {
            path,
            bytes,
            sha256,
        } = decompressed_input;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o400))?;
        }
        drop(source_guard);
        let guard = TempFileGuard(Some(path.clone()));
        (path, guard, bytes, sha256)
    } else {
        (
            pinned_source_path,
            source_guard,
            copied,
            source_hash.clone(),
        )
    };
    let expected = crate::harvest::read_expected_for_id(&solver_path, benchmark_id)?;
    Ok(PreparedBenchmark {
        solver_path,
        content_hash: source_hash.clone(),
        solver_input_hash: solver_input_hash.clone(),
        expected,
        metadata: InputPreparationMetadata {
            benchmark_path: benchmark_id.to_string(),
            source_hash,
            solver_input_hash,
            source_bytes: copied,
            solver_input_bytes,
            preprocessing_time_sec: round6(started.elapsed().as_secs_f64()),
            decompressed,
        },
        _solver_guard: solver_guard,
    })
}

fn same_file_identity_without_link_count(
    before: &std::fs::Metadata,
    after: &std::fs::Metadata,
) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.len() == after.len()
            && before.mtime() == after.mtime()
            && before.mtime_nsec() == after.mtime_nsec()
    }
    #[cfg(not(unix))]
    {
        before.len() == after.len() && before.modified().ok() == after.modified().ok()
    }
}

pub(crate) fn discover_benchmarks(dir: &Path, domain: &str) -> Result<Vec<PathBuf>> {
    let root_metadata = std::fs::symlink_metadata(dir).map_err(|error| {
        if error.kind() == std::io::ErrorKind::NotFound {
            BenchError::BenchmarksDirMissing {
                path: dir.to_path_buf(),
            }
        } else {
            error.into()
        }
    })?;
    if !root_metadata.file_type().is_dir() {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "benchmark corpus root must be a non-symlink directory: {}",
                dir.display()
            ),
        });
    }
    let mut files = Vec::new();
    collect_benchmarks_recursive_with_limits(
        dir,
        domain,
        &mut files,
        crate::resource::MAX_CORPUS_TRAVERSAL_ENTRIES,
        crate::resource::MAX_CORPUS_PENDING_DIRECTORIES,
        crate::resource::MAX_DISCOVERED_BENCHMARKS,
    )?;
    files.sort();
    Ok(files)
}

fn collect_benchmarks_recursive_with_limits(
    dir: &Path,
    domain: &str,
    out: &mut Vec<PathBuf>,
    max_entries: usize,
    max_pending_directories: usize,
    max_benchmarks: usize,
) -> Result<()> {
    // Use an explicit stack so an adversarially deep corpus cannot overflow
    // the parent stack. `DirEntry::file_type` does not follow symlinks: symlink
    // directories (including cycles and corpus escapes) and all non-regular
    // entries (FIFO/device/socket) are ignored.
    let mut pending = vec![dir.to_path_buf()];
    let mut visited_entries = 0_usize;
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(&directory)
            .with_bench_context(|| format!("reading {}", directory.display()))?
        {
            let entry = entry?;
            visited_entries = visited_entries
                .checked_add(1)
                .ok_or_else(|| BenchError::msg("corpus traversal entry count overflow"))?;
            if visited_entries > max_entries {
                return Err(BenchError::msg(format!(
                    "corpus traversal exceeds the fixed {max_entries}-entry cap"
                )));
            }
            let file_type = entry.file_type()?;
            let path = entry.path();
            if file_type.is_dir() {
                if pending.len() >= max_pending_directories {
                    return Err(BenchError::msg(format!(
                        "corpus traversal exceeds the fixed {max_pending_directories}-pending-directory cap"
                    )));
                }
                pending.push(path);
            } else if file_type.is_file() && is_benchmark_file(&path, domain) {
                if out.len() >= max_benchmarks {
                    return Err(BenchError::msg(format!(
                        "corpus contains more than the fixed {max_benchmarks}-benchmark cap"
                    )));
                }
                out.push(path);
            }
        }
    }
    Ok(())
}

fn validate_benchmark_target(path: &Path) -> Result<()> {
    let metadata = std::fs::symlink_metadata(path)
        .with_bench_context(|| format!("stat benchmark target {}", path.display()))?;
    if !metadata.file_type().is_file() {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "benchmark target must be a non-symlink regular file: {}",
                path.display()
            ),
        });
    }
    Ok(())
}

fn benchmark_identifier(path: &Path, corpus_root: &Path) -> Result<String> {
    crate::resource::normalized_relative_id(path, corpus_root)
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
        (Some(u), Some(s)) if u.is_finite() && s.is_finite() && u >= 0.0 && s >= 0.0 => Some(u + s),
        _ => None,
    }
}

// ===================================================================
// Solver execution with timeout
// ===================================================================

const CAPTURE_HEAD_BYTES: usize = 512 * 1024;
const CAPTURE_TAIL_BYTES: usize = 512 * 1024;

#[derive(Default)]
struct CapturedPipe {
    text: String,
    truncated: bool,
    read_failed: bool,
    sha256: String,
}

impl CapturedPipe {
    fn incomplete(&self) -> bool {
        self.truncated || self.read_failed
    }

    fn missing() -> Self {
        Self {
            read_failed: true,
            ..Self::default()
        }
    }
}

struct PipeCapture {
    receiver: std::sync::mpsc::Receiver<CapturedPipe>,
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
            use sha2::{Digest as _, Sha256};

            let mut head = Vec::new();
            let mut tail: VecDeque<Vec<u8>> = VecDeque::new();
            let mut tail_len = 0usize;
            let mut total_len = 0usize;
            let mut read_failed = false;
            let mut hasher = Sha256::new();
            let mut chunk = [0u8; 8192];
            loop {
                let read = match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => read,
                    Err(_) => {
                        read_failed = true;
                        break;
                    }
                };
                hasher.update(&chunk[..read]);
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
            let _ = sender.send(CapturedPipe {
                text: String::from_utf8_lossy(&head).into_owned(),
                truncated: total_len > CAPTURE_HEAD_BYTES + CAPTURE_TAIL_BYTES,
                read_failed,
                sha256: format!("sha256:{:x}", hasher.finalize()),
            });
        });
        Self { receiver }
    }

    fn finish(self) -> CapturedPipe {
        self.receiver
            .recv_timeout(Duration::from_secs(2))
            .unwrap_or(CapturedPipe {
                read_failed: true,
                ..CapturedPipe::default()
            })
    }
}

struct SolverRunRequest<'a> {
    ay_path: &'a Path,
    benchmark: &'a Path,
    solver_input: &'a Path,
    benchmark_content_hash: &'a str,
    solver_input_hash: &'a str,
    benchmark_id: &'a str,
    expected: &'a crate::harvest::ExpectedLabel,
    timeout_sec: f64,
    domain: &'a str,
    solver_args: &'a [String],
    solver_env: &'a BTreeMap<String, String>,
    resources: &'a crate::resource::PlannedResources,
}

fn run_solver(
    request: SolverRunRequest<'_>,
    artifact_plan: Option<SolverArtifactPlan>,
) -> NativeSolverRun {
    let SolverRunRequest {
        ay_path,
        benchmark,
        solver_input,
        benchmark_content_hash,
        solver_input_hash,
        benchmark_id,
        expected,
        timeout_sec,
        domain,
        solver_args,
        solver_env,
        resources,
    } = request;
    let file_name = benchmark_id.to_string();
    let benchmark_path = benchmark.display().to_string();
    let mut command_args = solver_command_args(domain, solver_args);
    command_args.push("--memory".to_string());
    command_args.push(resources.plan.memlimit_mb_per_child.to_string());
    if let Some(proof_path) = artifact_plan.as_ref().map(|plan| &plan.proof_work_path) {
        command_args.push("--proof".to_string());
        command_args.push(proof_path.display().to_string());
    }

    let actual_path = solver_input;

    let start = Instant::now();
    let timeout = Duration::from_secs_f64(timeout_sec);

    // When /usr/bin/time is available, wrap the solver command to get true
    // child-process CPU time (user + sys). This avoids unsafe code while
    // providing accurate CPU time for competition scoring (PAR-2, SMT-COMP).
    let timing_output = has_usr_bin_time()
        .then(|| tempfile::Builder::new().prefix("ay-time-").tempfile())
        .transpose()
        .ok()
        .flatten();
    let use_time_wrapper = timing_output.is_some();

    let mut cmd = if use_time_wrapper {
        let mut c = if artifact_plan.is_some() {
            resources.external_command_with_file_limit("/usr/bin/time", PROOF_ARTIFACT_LIMIT_BYTES)
        } else {
            resources.external_command("/usr/bin/time")
        };
        c.arg("-p"); // POSIX output format on a private timing channel.
        c.arg("-o");
        if let Some(output) = timing_output.as_ref() {
            c.arg(output.path());
        }
        c.arg(ay_path);
        c
    } else {
        if artifact_plan.is_some() {
            resources.external_command_with_file_limit(ay_path, PROOF_ARTIFACT_LIMIT_BYTES)
        } else {
            resources.external_command(ay_path)
        }
    };

    cmd.args(&command_args);
    cmd.env_clear();
    cmd.envs(solver_env);
    cmd.arg("--");
    cmd.arg(actual_path);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());
    let solver_argv = solver_argv(ay_path, &command_args, actual_path);
    let solver_input_path = Some(actual_path.display().to_string());

    let (mut child, watchdog) = match resources.spawn_external_child(&mut cmd, "ay bench run") {
        Ok(guarded) => guarded,
        Err(e) => {
            return prepare_solver_run_artifacts(
                NativeResultItem {
                    file: file_name,
                    benchmark_path,
                    benchmark_content_hash: Some(benchmark_content_hash.to_string()),
                    solver_input_hash: Some(solver_input_hash.to_string()),
                    solver_input_path,
                    expected: expected.value.clone(),
                    expected_source: expected.source.to_string(),
                    result: "error".to_string(),
                    harness_error: Some(bounded_output_excerpt(&format!("spawn failed: {e}"))),
                    time_sec: 0.0,
                    cpu_time_sec: 0.0,
                    cpu_time_source: "unavailable".to_string(),
                    exit_code: None,
                    solver_argv,
                    solver_env: solver_env.clone(),
                    artifacts: None,
                    sat_run: None,
                    extracted_features: None,
                },
                artifact_plan,
            );
        }
    };
    let stdout_capture = child.stdout.take().map(PipeCapture::start);
    let stderr_capture = child.stderr.take().map(PipeCapture::start);

    let proof_limit = artifact_plan
        .as_ref()
        .map(|plan| plan.proof_work_path.as_path())
        .map(|path| (path, PROOF_ARTIFACT_LIMIT_BYTES));
    let outcome = crate::resource::wait_for_guarded_child_with_file_limit(
        &mut child,
        watchdog,
        timeout,
        "ay bench run",
        proof_limit,
    );
    let elapsed = start.elapsed().as_secs_f64();
    let stdout = stdout_capture
        .map(PipeCapture::finish)
        .unwrap_or_else(CapturedPipe::missing);
    let stderr_output = stderr_capture
        .map(PipeCapture::finish)
        .unwrap_or_else(CapturedPipe::missing);
    let capture_incomplete = stdout.incomplete() || stderr_output.incomplete();
    let (result, sat_run, exit_code, harness_error) = match outcome {
        Err(error) => (
            "error".to_string(),
            None,
            None,
            Some(bounded_output_excerpt(&format!(
                "RSS watchdog failure: {error}"
            ))),
        ),
        Ok(outcome) if outcome.memout => ("memout".to_string(), None, None, None),
        Ok(outcome) if outcome.timed_out => ("timeout".to_string(), None, None, None),
        Ok(_) if capture_incomplete => (
            "error".to_string(),
            None,
            None,
            Some("solver output capture was truncated or unreadable".to_string()),
        ),
        Ok(outcome) => match outcome.status {
            Some(status) => (
                parse_verdict(&stdout.text, &stderr_output.text, status.code()).to_string(),
                parse_sat_applied_run_metadata(&stderr_output.text),
                status.code(),
                None,
            ),
            None => (
                "error".to_string(),
                None,
                None,
                Some("solver was not reaped".to_string()),
            ),
        },
    };

    // Extract CPU time from /usr/bin/time output, fall back to wall time.
    let measured_cpu = if use_time_wrapper {
        timing_output
            .as_ref()
            .and_then(|output| {
                crate::resource::read_bounded_text(output.path(), 64 * 1024, "CPU timing output")
                    .ok()
            })
            .and_then(|output| parse_posix_time_output(&output))
    } else {
        None
    };
    let (cpu_time, cpu_time_source) = match (use_time_wrapper, measured_cpu) {
        (true, Some(cpu_time)) => (cpu_time, "posix-time-user+sys"),
        (true, None) => (elapsed, "wall-fallback-malformed-posix-time"),
        (false, _) => (elapsed, "wall-no-posix-time"),
    };

    prepare_solver_run_artifacts(
        NativeResultItem {
            file: file_name,
            benchmark_path,
            benchmark_content_hash: Some(benchmark_content_hash.to_string()),
            solver_input_hash: Some(solver_input_hash.to_string()),
            solver_input_path,
            expected: expected.value.clone(),
            expected_source: expected.source.to_string(),
            result,
            harness_error,
            time_sec: round6(elapsed),
            cpu_time_sec: round6(cpu_time),
            cpu_time_source: cpu_time_source.to_string(),
            exit_code,
            solver_argv,
            solver_env: solver_env.clone(),
            artifacts: None,
            sat_run,
            extracted_features: None,
        },
        artifact_plan,
    )
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

fn external_solver_args(solver_path: &Path, benchmark: &Path) -> Result<Vec<OsString>> {
    let mut args = Vec::new();
    match NativeReferenceKind::detect(solver_path) {
        NativeReferenceKind::Golem => {
            let logic = crate::harvest::read_smt_metadata(benchmark)?
                .logic
                .ok_or_else(|| {
                    BenchError::msg(format!(
                        "Golem reference input has no explicit set-logic: {}",
                        benchmark.display()
                    ))
                })?;
            args.push(OsString::from("-l"));
            args.push(OsString::from(logic));
            args.push(OsString::from("-e"));
            args.push(OsString::from("spacer"));
            args.push(benchmark.as_os_str().to_os_string());
        }
        NativeReferenceKind::Other => {
            args.push(OsString::from("--"));
            args.push(benchmark.as_os_str().to_os_string());
        }
    }
    Ok(args)
}

fn bounded_output_excerpt(text: &str) -> String {
    const LIMIT: usize = 4096;
    const MARKER: &str = "\n[... excerpt truncated ...]\n";
    if text.len() <= LIMIT {
        return text.to_string();
    }
    let payload = LIMIT.saturating_sub(MARKER.len());
    let head_budget = payload / 2;
    let tail_budget = payload - head_budget;
    let head_end = (0..=head_budget)
        .rev()
        .find(|index| text.is_char_boundary(*index))
        .unwrap_or(0);
    let tail_start = (text.len().saturating_sub(tail_budget)..text.len())
        .find(|index| text.is_char_boundary(*index))
        .unwrap_or(text.len());
    format!("{}{MARKER}{}", &text[..head_end], &text[tail_start..])
}

fn empty_sha256() -> String {
    "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855".to_string()
}

fn failed_reference_evidence(
    solver_path: &Path,
    benchmark: &Path,
    solver_input_hash: &str,
    solver_argv: Vec<String>,
    solver_env: BTreeMap<String, String>,
    error: String,
) -> ReferenceRunEvidence {
    let _ = solver_path;
    ReferenceRunEvidence {
        result: "error".to_string(),
        time_sec: 0.0,
        exit_code: None,
        solver_input_path: benchmark.display().to_string(),
        solver_input_hash: solver_input_hash.to_string(),
        solver_argv,
        solver_env,
        stdout_excerpt: String::new(),
        stderr_excerpt: String::new(),
        stdout_sha256: empty_sha256(),
        stderr_sha256: empty_sha256(),
        stdout_truncated: false,
        stderr_truncated: false,
        harness_error: Some(bounded_output_excerpt(&error)),
    }
}

/// Run an external solver (e.g., z3) and retain bounded, independently
/// auditable evidence for the exact invocation and input bytes.
fn run_external_solver(
    solver_path: &Path,
    benchmark: &Path,
    solver_input_hash: &str,
    timeout_sec: f64,
    resources: &crate::resource::PlannedResources,
) -> ReferenceRunEvidence {
    let start = Instant::now();
    let timeout = Duration::from_secs_f64(timeout_sec);

    let mut solver_env = BTreeMap::new();
    solver_env.insert("LC_ALL".to_string(), "C".to_string());
    solver_env.insert("TZ".to_string(), "UTC".to_string());
    solver_env.insert(
        "PATH".to_string(),
        std::env::var("PATH").unwrap_or_else(|_| "/usr/local/bin:/usr/bin:/bin".to_string()),
    );
    solver_env.insert(
        "MEMLIMIT".to_string(),
        resources.plan.memlimit_mb_per_child.to_string(),
    );
    solver_env.insert(
        "NBCORE".to_string(),
        resources.plan.nbcore_per_child.to_string(),
    );
    let args = match external_solver_args(solver_path, benchmark) {
        Ok(args) => args,
        Err(error) => {
            return failed_reference_evidence(
                solver_path,
                benchmark,
                solver_input_hash,
                vec![solver_path.display().to_string()],
                solver_env,
                error.to_string(),
            )
        }
    };
    let mut solver_argv = Vec::with_capacity(args.len() + 1);
    solver_argv.push(solver_path.display().to_string());
    solver_argv.extend(args.iter().map(|arg| arg.to_string_lossy().into_owned()));

    let mut cmd = resources.external_command(solver_path);
    cmd.args(&args);
    // ay-pb consumes these directly; other reference solvers remain under the
    // exact zero-grace RSS watchdog while receiving the planned CPU budget as
    // advisory environment provenance.
    cmd.env_clear();
    cmd.envs(&solver_env);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());

    let (mut child, watchdog) =
        match resources.spawn_external_child(&mut cmd, "ay bench run reference") {
            Ok(guarded) => guarded,
            Err(error) => {
                return failed_reference_evidence(
                    solver_path,
                    benchmark,
                    solver_input_hash,
                    solver_argv,
                    solver_env,
                    error.to_string(),
                )
            }
        };
    let stdout_capture = child.stdout.take().map(PipeCapture::start);
    let stderr_capture = child.stderr.take().map(PipeCapture::start);
    let outcome = crate::resource::wait_for_guarded_child(
        &mut child,
        watchdog,
        timeout,
        "ay bench run reference",
    );
    let elapsed = round6(start.elapsed().as_secs_f64());
    let stdout = stdout_capture
        .map(PipeCapture::finish)
        .unwrap_or_else(CapturedPipe::missing);
    let stderr = stderr_capture
        .map(PipeCapture::finish)
        .unwrap_or_else(CapturedPipe::missing);
    let (result, recorded_time, exit_code, harness_error) = match outcome {
        Err(error) => ("error".to_string(), elapsed, None, Some(error.to_string())),
        Ok(outcome) if outcome.memout => ("memout".to_string(), elapsed, None, None),
        Ok(outcome) if outcome.timed_out => ("timeout".to_string(), timeout_sec, None, None),
        Ok(_) if stdout.incomplete() || stderr.incomplete() => (
            "error".to_string(),
            elapsed,
            None,
            Some("reference output capture was missing, truncated, or unreadable".to_string()),
        ),
        Ok(outcome) => match outcome.status {
            Some(status) => (
                parse_reference_verdict(&stdout.text, &stderr.text, status.code()).to_string(),
                elapsed,
                status.code(),
                None,
            ),
            None => (
                "error".to_string(),
                elapsed,
                None,
                Some("reference solver was not reaped".to_string()),
            ),
        },
    };
    ReferenceRunEvidence {
        result,
        time_sec: round6(recorded_time),
        exit_code,
        solver_input_path: benchmark.display().to_string(),
        solver_input_hash: solver_input_hash.to_string(),
        solver_argv,
        solver_env,
        stdout_excerpt: bounded_output_excerpt(&stdout.text),
        stderr_excerpt: bounded_output_excerpt(&stderr.text),
        stdout_sha256: stdout.sha256,
        stderr_sha256: stderr.sha256,
        stdout_truncated: stdout.truncated,
        stderr_truncated: stderr.truncated,
        harness_error: harness_error.map(|detail| bounded_output_excerpt(&detail)),
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
) -> Result<Option<SolverArtifactPlan>> {
    if domain != "sat" {
        return Ok(None);
    }
    let Some(output_dir) = output_dir else {
        return Ok(None);
    };
    let proof_format = sat_proof_format_for_profile(profile);
    let proof_path = output_dir.join(artifact_file_name(index, benchmark, proof_format));
    match std::fs::symlink_metadata(&proof_path) {
        Ok(_) => {
            return Err(BenchError::msg(format!(
                "refusing to replace existing proof artifact {}",
                proof_path.display()
            )));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    let mut staging_builder = tempfile::Builder::new();
    staging_builder.prefix(".ay-proof-stage-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        staging_builder.permissions(std::fs::Permissions::from_mode(0o700));
    }
    let staging_dir = staging_builder
        .tempdir_in(output_dir)
        .with_bench_context(|| {
            format!(
                "reserving private proof staging directory in {}",
                output_dir.display()
            )
        })?;
    let staging_path = staging_dir.path().to_path_buf();
    let staging_directory = std::fs::File::open(&staging_path).with_bench_context(|| {
        format!(
            "retaining private proof staging directory {}",
            staging_path.display()
        )
    })?;
    // From here on cleanup is explicit and non-recursive. `TempDir::drop`
    // would act on this public pathname and could recursively delete a
    // concurrently substituted directory.
    let staging_path = staging_dir.keep();
    let proof_work_path = staging_path.join(format!("solver-output.{proof_format}"));
    debug_assert!(
        !proof_work_path.exists(),
        "solver proof work path must be absent for create-new output"
    );
    Ok(Some(SolverArtifactPlan {
        output_dir: output_dir.to_path_buf(),
        proof_path,
        proof_staging: Some(PrivateProofStaging {
            path: staging_path,
            directory: staging_directory,
        }),
        proof_work_path,
        proof_work_file: None,
        published_proof: None,
        proof_format,
    }))
}

fn publish_artifact_metadata(plan: &mut SolverArtifactPlan) -> Result<SolverArtifactMetadata> {
    let descriptor_metadata = plan
        .proof_work_file
        .as_ref()
        .ok_or_else(|| BenchError::msg("authenticated solver proof descriptor was lost"))?
        .metadata()
        .with_bench_context(|| format!("stat solver proof {}", plan.proof_work_path.display()))?;
    let path_metadata =
        std::fs::symlink_metadata(&plan.proof_work_path).with_bench_context(|| {
            format!(
                "restatting selected solver proof artifact {}",
                plan.proof_work_path.display()
            )
        })?;
    if !path_metadata.file_type().is_file()
        || !same_file_identity(&descriptor_metadata, &path_metadata)
    {
        return Err(BenchError::msg(format!(
            "selected solver proof changed before publication: {}",
            plan.proof_work_path.display()
        )));
    }
    if path_metadata.len() == 0 || path_metadata.len() > PROOF_ARTIFACT_LIMIT_BYTES {
        return Err(BenchError::msg(format!(
            "proof artifact {} has invalid size {} (limit {})",
            plan.proof_work_path.display(),
            path_metadata.len(),
            PROOF_ARTIFACT_LIMIT_BYTES
        )));
    }
    // Copy from the authenticated solver-output descriptor into a separate
    // parent-owned reservation. The work pathname is never renamed or
    // published directly: AY owns its create-new output, while ay-bench owns
    // the bytes it has copied, hashed, synced, and will install no-clobber.
    let mut publication = ProofPublication::new(&plan.output_dir).with_bench_context(|| {
        format!(
            "reserving proof publication in {}",
            plan.output_dir.display()
        )
    })?;
    let proof_hash = {
        let source = plan
            .proof_work_file
            .as_mut()
            .ok_or_else(|| BenchError::msg("authenticated solver proof descriptor was lost"))?;
        copy_and_hash_proof(
            source,
            publication.as_file_mut(),
            &format!("proof artifact {}", plan.proof_work_path.display()),
            path_metadata.len(),
        )?
    };
    let after_open_copy = plan
        .proof_work_file
        .as_ref()
        .ok_or_else(|| BenchError::msg("authenticated solver proof descriptor was lost"))?
        .metadata()
        .with_bench_context(|| format!("restat solver proof {}", plan.proof_work_path.display()))?;
    let after_hash = std::fs::symlink_metadata(&plan.proof_work_path).with_bench_context(|| {
        format!(
            "restatting solver proof artifact {}",
            plan.proof_work_path.display()
        )
    })?;
    if !same_file_identity(&path_metadata, &after_open_copy)
        || !same_file_identity(&after_open_copy, &after_hash)
    {
        return Err(BenchError::msg(format!(
            "proof artifact changed while copying: {}",
            plan.proof_work_path.display()
        )));
    }
    // Remove only an authenticated work inode from the private staging
    // directory. Any observed replacement preserves the whole directory for
    // inspection rather than letting TempDir pathname cleanup delete it.
    cleanup_proof_staging(plan)?;
    // `persist_noclobber` is the authority here. A separate existence check
    // would only introduce a TOCTOU window in which a concurrently recreated
    // destination could be overwritten.
    let published = publication
        .persist_noclobber(&plan.proof_path)
        .with_bench_context(|| {
            format!("publishing proof artifact {}", plan.proof_path.display())
        })?;
    // Retain the exact installed descriptor before any later fallible step.
    // A no-clobber collision never reaches this assignment, so failure cleanup
    // cannot mistake the concurrent owner's destination for ours.
    plan.published_proof = Some(published);
    #[cfg(unix)]
    std::fs::File::open(&plan.output_dir)
        .and_then(|directory| directory.sync_all())
        .with_bench_context(|| {
            format!(
                "syncing proof artifact directory {}",
                plan.output_dir.display()
            )
        })?;
    Ok(SolverArtifactMetadata {
        output_dir: plan.output_dir.display().to_string(),
        proof_path: Some(plan.proof_path.display().to_string()),
        proof_format: Some(plan.proof_format.to_string()),
        proof_exists: Some(true),
        proof_bytes: Some(path_metadata.len()),
        proof_hash: Some(proof_hash),
        proof_validation: "unchecked".to_string(),
    })
}

fn authenticate_solver_proof_output(
    plan: &mut SolverArtifactPlan,
    required: bool,
) -> Result<Option<std::fs::Metadata>> {
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let proof = match options.open(&plan.proof_work_path) {
        Ok(proof) => proof,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound && !required => return Ok(None),
        Err(error) => {
            return Err(error).with_bench_context(|| {
                format!(
                    "opening solver proof output {}",
                    plan.proof_work_path.display()
                )
            });
        }
    };
    let descriptor_metadata = proof.metadata().with_bench_context(|| {
        format!(
            "stat solver proof descriptor {}",
            plan.proof_work_path.display()
        )
    })?;
    // Retain the descriptor before inspecting the pathname. If the pathname
    // is already a replacement, failure cleanup now has the exact original
    // identity needed to preserve the replacement.
    plan.proof_work_file = Some(proof);
    let path_metadata =
        std::fs::symlink_metadata(&plan.proof_work_path).with_bench_context(|| {
            format!(
                "stat solver proof output {}",
                plan.proof_work_path.display()
            )
        })?;
    if !descriptor_metadata.file_type().is_file()
        || !path_metadata.file_type().is_file()
        || !same_file_identity(&descriptor_metadata, &path_metadata)
    {
        return Err(BenchError::msg(format!(
            "solver proof output path was replaced or is not a regular file: {}",
            plan.proof_work_path.display()
        )));
    }
    Ok(Some(path_metadata))
}

fn copy_and_hash_proof(
    source: &mut std::fs::File,
    destination: &mut std::fs::File,
    label: &str,
    expected_len: u64,
) -> Result<String> {
    use std::io::{Read as _, Seek as _, SeekFrom, Write as _};

    source
        .seek(SeekFrom::Start(0))
        .with_bench_context(|| format!("seeking {label}"))?;
    destination
        .set_len(0)
        .with_bench_context(|| format!("resetting publication reservation for {label}"))?;
    destination
        .seek(SeekFrom::Start(0))
        .with_bench_context(|| format!("seeking publication reservation for {label}"))?;
    let copied = {
        let mut bounded = source.take(PROOF_ARTIFACT_LIMIT_BYTES.saturating_add(1));
        std::io::copy(&mut bounded, destination)
            .with_bench_context(|| format!("copying {label} into publication reservation"))?
    };
    if copied != expected_len || copied > PROOF_ARTIFACT_LIMIT_BYTES {
        return Err(BenchError::msg(format!(
            "proof artifact changed size while copying: expected {expected_len}, copied {copied}"
        )));
    }
    destination
        .flush()
        .with_bench_context(|| format!("flushing publication reservation for {label}"))?;
    destination
        .sync_all()
        .with_bench_context(|| format!("syncing publication reservation for {label}"))?;
    content_hash_open_file(destination, label, PROOF_ARTIFACT_LIMIT_BYTES)
}

fn same_file_identity(before: &std::fs::Metadata, after: &std::fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.dev() == after.dev()
            && before.ino() == after.ino()
            // A single link rules out a hidden hard-link alias that could
            // mutate the inode after validation/publication.
            && before.nlink() == 1
            && after.nlink() == 1
            && before.len() == after.len()
            && before.mtime() == after.mtime()
            && before.mtime_nsec() == after.mtime_nsec()
    }
    #[cfg(not(unix))]
    {
        before.len() == after.len() && before.modified().ok() == after.modified().ok()
    }
}

fn same_directory_identity(before: &std::fs::Metadata, after: &std::fs::Metadata) -> bool {
    if !before.file_type().is_dir() || !after.file_type().is_dir() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.dev() == after.dev() && before.ino() == after.ino()
    }
    #[cfg(not(unix))]
    {
        before.modified().ok() == after.modified().ok()
    }
}

fn not_emitted_artifact_metadata(plan: &SolverArtifactPlan) -> SolverArtifactMetadata {
    SolverArtifactMetadata {
        output_dir: plan.output_dir.display().to_string(),
        proof_path: Some(plan.proof_path.display().to_string()),
        proof_format: Some(plan.proof_format.to_string()),
        proof_exists: Some(false),
        proof_bytes: None,
        proof_hash: None,
        proof_validation: "not-emitted".to_string(),
    }
}

fn set_artifact_failure(
    mut item: NativeResultItem,
    context: &str,
    error: impl std::fmt::Display,
    plan: Option<&mut SolverArtifactPlan>,
) -> NativeResultItem {
    let mut detail = format!("proof artifact {context} failed: {error}");
    if let Some(plan) = plan {
        if let Err(cleanup_error) = cleanup_failed_artifact_plan(plan) {
            detail.push_str(&format!("; cleanup failed: {cleanup_error}"));
        }
    }
    item.artifacts = None;
    item.result = "error".to_string();
    item.harness_error = Some(bounded_output_excerpt(&detail));
    item.exit_code = None;
    item
}

fn prepare_solver_run_artifacts(
    mut item: NativeResultItem,
    mut artifact_plan: Option<SolverArtifactPlan>,
) -> NativeSolverRun {
    let Some(plan) = artifact_plan.as_mut() else {
        return NativeSolverRun {
            item,
            artifact_plan,
        };
    };
    let preparation = if item.result == "unsat" {
        authenticate_solver_proof_output(plan, true).and_then(|metadata| {
            let metadata = metadata.ok_or_else(|| {
                BenchError::msg(format!(
                    "solver did not create proof artifact {}",
                    plan.proof_work_path.display()
                ))
            })?;
            if metadata.len() == 0 || metadata.len() > PROOF_ARTIFACT_LIMIT_BYTES {
                return Err(BenchError::msg(format!(
                    "proof artifact {} has invalid size {} (limit {})",
                    plan.proof_work_path.display(),
                    metadata.len(),
                    PROOF_ARTIFACT_LIMIT_BYTES
                )));
            }
            Ok(())
        })
    } else {
        authenticate_solver_proof_output(plan, false)
            .and_then(|_| cleanup_proof_staging(plan))
            .map(|()| {
                item.artifacts = Some(not_emitted_artifact_metadata(plan));
            })
    };
    if let Err(error) = preparation {
        item = set_artifact_failure(item, "preparation", error, Some(plan));
    }
    NativeSolverRun {
        item,
        artifact_plan,
    }
}

fn finalize_selected_artifacts(mut run: NativeSolverRun) -> NativeResultItem {
    if run.item.result != "unsat" {
        return run.item;
    }
    let Some(plan) = run.artifact_plan.as_mut() else {
        return run.item;
    };
    match publish_artifact_metadata(plan) {
        Ok(artifacts) => {
            run.item.artifacts = Some(artifacts);
            run.item
        }
        Err(error) => set_artifact_failure(run.item, "finalization", error, Some(plan)),
    }
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn rename_noclobber(source: &Path, destination: &Path) -> std::io::Result<()> {
    nix::fcntl::renameat2(
        None,
        source,
        None,
        destination,
        nix::fcntl::RenameFlags::RENAME_NOREPLACE,
    )
    .map_err(|error| std::io::Error::from_raw_os_error(error as i32))
}

#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
fn rename_noclobber(_source: &Path, _destination: &Path) -> std::io::Result<()> {
    // A destination existence check followed by `std::fs::rename` is not a
    // no-clobber operation: another process can create the destination in
    // between and then be overwritten. Preserve both pathnames unless this
    // target has an atomic rename-with-no-replace primitive wired in.
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "atomic no-clobber rename is unavailable on this platform",
    ))
}

fn discard_empty_tempdir(tempdir: tempfile::TempDir) {
    let path = tempdir.keep();
    // This is intentionally non-recursive. If the supposedly empty private
    // directory was replaced or gained contents, preserve it.
    let _ = std::fs::remove_dir(path);
}

fn cleanup_proof_staging(plan: &mut SolverArtifactPlan) -> Result<()> {
    cleanup_proof_staging_with_hook(plan, |_, _| {})
}

fn cleanup_proof_staging_with_hook<F>(
    plan: &mut SolverArtifactPlan,
    after_quarantine: F,
) -> Result<()>
where
    F: FnOnce(&Path, &Path),
{
    let work_name = plan
        .proof_work_path
        .file_name()
        .ok_or_else(|| BenchError::msg("proof work path has no file name"))?
        .to_os_string();
    let Some(staging) = plan.proof_staging.take() else {
        plan.proof_work_file = None;
        return Ok(());
    };
    let mut cleanup_builder = tempfile::Builder::new();
    cleanup_builder.prefix(".ay-proof-cleanup-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        cleanup_builder.permissions(std::fs::Permissions::from_mode(0o700));
    }
    let cleanup_root = match cleanup_builder
        .tempdir_in(&plan.output_dir)
        .with_bench_context(|| {
            format!(
                "reserving private proof cleanup directory in {}",
                plan.output_dir.display()
            )
        }) {
        Ok(cleanup_root) => cleanup_root,
        Err(error) => {
            plan.proof_staging = Some(staging);
            return Err(error);
        }
    };
    let quarantine_path = cleanup_root.path().join("staging");
    if let Err(error) = rename_noclobber(&staging.path, &quarantine_path) {
        discard_empty_tempdir(cleanup_root);
        plan.proof_work_file = None;
        return Err(error).with_bench_context(|| {
            format!(
                "quarantining proof staging directory {}; preserving it",
                staging.path.display()
            )
        });
    }
    // The solver-visible name is no longer cleanup authority. A replacement
    // planted there from this point onward is outside the quarantine and is
    // never traversed or removed.
    after_quarantine(&staging.path, &quarantine_path);

    let directory_identity = staging.directory.metadata();
    let quarantined_identity = std::fs::symlink_metadata(&quarantine_path);
    let directory_is_owned = matches!(
        (&directory_identity, &quarantined_identity),
        (Ok(descriptor), Ok(path)) if same_directory_identity(descriptor, path)
    );
    if !directory_is_owned {
        let preserved = cleanup_root.keep();
        plan.proof_work_file = None;
        return Err(BenchError::msg(format!(
            "refusing to remove replaced proof staging directory {}; preserved under {}",
            staging.path.display(),
            preserved.display()
        )));
    }

    let quarantined_work_path = quarantine_path.join(work_name);
    let retired_work_path = cleanup_root.path().join("retired-proof");
    let moved_work = match rename_noclobber(&quarantined_work_path, &retired_work_path) {
        Ok(()) => true,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
        Err(error) => {
            let preserved = cleanup_root.keep();
            plan.proof_work_file = None;
            return Err(error).with_bench_context(|| {
                format!(
                    "quarantining proof work entry {}; preserved under {}",
                    plan.proof_work_path.display(),
                    preserved.display()
                )
            });
        }
    };

    let retired_identity = if moved_work {
        std::fs::symlink_metadata(&retired_work_path).ok()
    } else {
        None
    };
    let descriptor_identity = plan
        .proof_work_file
        .as_ref()
        .and_then(|file| file.metadata().ok());
    let proof_is_owned = match (&descriptor_identity, &retired_identity) {
        (Some(descriptor), Some(path)) => {
            path.file_type().is_file() && same_file_identity(descriptor, path)
        }
        (None, None) => true,
        _ => false,
    };
    let staging_is_empty = std::fs::read_dir(&quarantine_path)
        .and_then(|mut entries| match entries.next() {
            None => Ok(()),
            Some(Ok(entry)) => Err(std::io::Error::other(format!(
                "unexpected staging entry {}",
                entry.path().display()
            ))),
            Some(Err(error)) => Err(error),
        })
        .is_ok();
    if !proof_is_owned || !staging_is_empty {
        let preserved = cleanup_root.keep();
        plan.proof_work_file = None;
        return Err(BenchError::msg(format!(
            "refusing to remove mutated proof staging contents {}; preserved under {}",
            staging.path.display(),
            preserved.display()
        )));
    }

    // Both names are now private quarantine names produced by no-clobber
    // renames, and every unexpected entry causes preservation. Removal is
    // deliberately leaf-first and non-recursive.
    plan.proof_work_file = None;
    let cleanup_root_path = cleanup_root.keep();
    if moved_work {
        std::fs::remove_file(&retired_work_path).with_bench_context(|| {
            format!("removing quarantined proof {}", retired_work_path.display())
        })?;
    }
    std::fs::remove_dir(&quarantine_path).with_bench_context(|| {
        format!(
            "removing empty quarantined proof directory {}",
            quarantine_path.display()
        )
    })?;
    std::fs::remove_dir(&cleanup_root_path).with_bench_context(|| {
        format!(
            "removing empty proof cleanup directory {}",
            cleanup_root_path.display()
        )
    })?;
    Ok(())
}

fn cleanup_failed_artifact_plan(plan: &mut SolverArtifactPlan) -> Result<()> {
    let mut failures = Vec::new();
    if let Err(error) = cleanup_proof_staging(plan) {
        failures.push(error.to_string());
    }
    if plan.published_proof.is_some() {
        // There is no portable compare-and-unlink operation. Once a proof is
        // public, even a descriptor identity check followed by `remove_file`
        // could delete a replacement. Publication is therefore the terminal
        // pathname mutation: later failures always preserve whatever the
        // public name contains.
        failures.push(format!(
            "preserving public proof path {} after finalization failure",
            plan.proof_path.display()
        ));
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(BenchError::msg(failures.join("; ")))
    }
}

fn content_hash_open_file(file: &mut std::fs::File, label: &str, limit: u64) -> Result<String> {
    use sha2::{Digest as _, Sha256};
    use std::io::{Read as _, Seek as _, SeekFrom};

    file.seek(SeekFrom::Start(0))
        .with_bench_context(|| format!("seeking {label}"))?;
    let mut hasher = Sha256::new();
    let mut total = 0_u64;
    let mut buf = [0_u8; 8192];
    loop {
        let read = file
            .read(&mut buf)
            .with_bench_context(|| format!("reading {label}"))?;
        if read == 0 {
            break;
        }
        total = total
            .checked_add(read as u64)
            .ok_or_else(|| BenchError::msg(format!("{label} size overflow")))?;
        if total > limit {
            return Err(BenchError::msg(format!(
                "{label} exceeds the fixed {limit}-byte hash cap"
            )));
        }
        hasher.update(&buf[..read]);
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
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
    /// Extract structural features from each private solver-input snapshot.
    pub with_features: bool,
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
    /// Optional campaign-owned immutable AY snapshot. Supplying this avoids
    /// hashing and probing the mutable source pathname once per eval.
    pub pinned_ay: Option<&'a crate::environment::PinnedSolver>,
    /// Directory where ay-bench should place per-benchmark artifacts.
    pub artifact_output_dir: Option<PathBuf>,
    /// Resource admission and enforcement produced by `scripts/_oom_guard.py`.
    /// Native execution fails closed when this is absent.
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
#[cfg(test)]
pub(crate) fn select_representative(
    mut results: Vec<NativeResultItem>,
) -> Result<NativeResultItem> {
    if results.is_empty() {
        return Err(BenchError::msg(
            "cannot select a representative from zero runs",
        ));
    }
    let classification = |result: &str| match result {
        "sat" => "sat",
        "unsat" => "unsat",
        "unknown" => "unknown",
        "timeout" => "timeout",
        "memout" => "memout",
        "error" => "error",
        _ => "other",
    };
    let first = classification(&results[0].result);
    if results
        .iter()
        .any(|result| classification(&result.result) != first)
    {
        let classification_error = format!(
            "repeated solver runs produced mixed classifications: {}",
            results
                .iter()
                .map(|result| result.result.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        return Err(BenchError::msg(classification_error));
    }
    results.sort_by(|a, b| a.time_sec.total_cmp(&b.time_sec));
    let mid = (results.len() - 1) / 2;
    Ok(results.remove(mid))
}

fn cleanup_private_solver_runs(results: &mut [NativeSolverRun]) -> Result<()> {
    let mut failures = Vec::new();
    for result in results {
        if let Some(plan) = result.artifact_plan.as_mut() {
            if let Err(error) = cleanup_failed_artifact_plan(plan) {
                failures.push(error.to_string());
            }
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(BenchError::msg(failures.join("; ")))
    }
}

fn select_prepared_representative(mut runs: Vec<NativeSolverRun>) -> Result<NativeResultItem> {
    if runs.is_empty() {
        return Err(BenchError::msg(
            "cannot select a representative from zero runs",
        ));
    }
    let classification = |result: &str| match result {
        "sat" => "sat",
        "unsat" => "unsat",
        "unknown" => "unknown",
        "timeout" => "timeout",
        "memout" => "memout",
        "error" => "error",
        _ => "other",
    };
    let first = classification(&runs[0].item.result);
    if runs
        .iter()
        .any(|run| classification(&run.item.result) != first)
    {
        let classifications = runs
            .iter()
            .map(|run| run.item.result.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let cleanup = cleanup_private_solver_runs(&mut runs).err();
        let detail =
            format!("repeated solver runs produced mixed classifications: {classifications}");
        return Err(BenchError::msg(match cleanup {
            Some(error) => format!("{detail}; private artifact cleanup failed: {error}"),
            None => detail,
        }));
    }

    runs.sort_by(|a, b| a.item.time_sec.total_cmp(&b.item.time_sec));
    let selected_index = (runs.len() - 1) / 2;
    let mut selected = runs.remove(selected_index);
    if let Err(error) = cleanup_private_solver_runs(&mut runs) {
        let selected_cleanup =
            cleanup_private_solver_runs(std::slice::from_mut(&mut selected)).err();
        return Err(BenchError::msg(match selected_cleanup {
            Some(selected_error) => format!(
                "discarded-run private artifact cleanup failed: {error}; selected-run private artifact cleanup also failed: {selected_error}"
            ),
            None => format!("discarded-run private artifact cleanup failed: {error}"),
        }));
    }
    Ok(finalize_selected_artifacts(selected))
}

fn preflight_native_benchmarks(args: &NativeRunArgs<'_>) -> Result<(PathBuf, Vec<PathBuf>)> {
    if let Some(file_list) = args.file_list.as_ref() {
        if file_list.len() > crate::resource::MAX_DISCOVERED_BENCHMARKS {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "native file list exceeds the fixed {}-benchmark cap",
                    crate::resource::MAX_DISCOVERED_BENCHMARKS
                ),
            });
        }
    }
    let discovered_storage;
    let discovered: &[PathBuf] = if let Some(file_list) = args.file_list.as_ref() {
        file_list
    } else {
        discovered_storage = discover_benchmarks(args.benchmarks_dir, args.domain)?;
        &discovered_storage
    };
    let corpus_root = std::fs::canonicalize(args.benchmarks_dir).with_bench_context(|| {
        format!(
            "canonicalizing corpus root {}",
            args.benchmarks_dir.display()
        )
    })?;
    if discovered.is_empty() {
        return Ok((corpus_root, Vec::new()));
    }
    let mut entries = Vec::with_capacity(discovered.len());
    for original in discovered {
        validate_benchmark_target(original)?;
        let canonical = std::fs::canonicalize(original)
            .with_bench_context(|| format!("canonicalizing benchmark {}", original.display()))?;
        let benchmark_id = crate::resource::normalized_relative_id(&canonical, &corpus_root)?;
        let metadata = std::fs::symlink_metadata(&canonical)?;
        #[cfg(unix)]
        let identity = {
            use std::os::unix::fs::MetadataExt as _;
            Some((metadata.dev(), metadata.ino()))
        };
        #[cfg(not(unix))]
        let identity: Option<(u64, u64)> = None;
        entries.push((benchmark_id, canonical, original.to_path_buf(), identity));
    }
    entries.sort_by(|left, right| left.0.cmp(&right.0));
    let mut seen_ids: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut seen_identities: BTreeMap<(u64, u64), (String, PathBuf)> = BTreeMap::new();
    let mut benchmarks = Vec::with_capacity(entries.len());
    for (benchmark_id, canonical, original, identity) in entries {
        if let Some(previous) = seen_ids.insert(benchmark_id.clone(), original.clone()) {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "duplicate native benchmark ID {benchmark_id:?}: {} and {}",
                    previous.display(),
                    original.display()
                ),
            });
        }
        if let Some(identity) = identity {
            if let Some((previous_id, previous)) =
                seen_identities.insert(identity, (benchmark_id.clone(), original.clone()))
            {
                return Err(BenchError::InvalidArgs {
                    reason: format!(
                        "native benchmark IDs {previous_id:?} ({}) and {benchmark_id:?} ({}) alias the same file",
                        previous.display(),
                        original.display()
                    ),
                });
            }
        }
        benchmarks.push(canonical);
    }
    Ok((corpus_root, benchmarks))
}

fn validate_reference_solvers(reference_solvers: &[(String, PathBuf)]) -> Result<()> {
    if reference_solvers.len() > MAX_REFERENCE_SOLVERS {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "reference solver count {} exceeds the fixed {MAX_REFERENCE_SOLVERS}-solver cap",
                reference_solvers.len()
            ),
        });
    }
    let mut names: BTreeMap<&str, &Path> = BTreeMap::new();
    let mut binaries: BTreeMap<PathBuf, (&str, &Path)> = BTreeMap::new();
    let mut identities: BTreeMap<(u64, u64), (&str, &Path)> = BTreeMap::new();
    let mut total_bytes = 0_u64;
    for (name, path) in reference_solvers {
        if name.is_empty()
            || name.len() > 128
            || !name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_'))
        {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "reference solver name {name:?} for {} must be 1-128 path-safe ASCII characters",
                    path.display()
                ),
            });
        }
        if let Some(previous) = names.insert(name, path) {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "duplicate reference solver name {name:?}: {} and {}",
                    previous.display(),
                    path.display()
                ),
            });
        }
        let metadata = std::fs::symlink_metadata(path).with_bench_context(|| {
            format!("statting configured reference solver {}", path.display())
        })?;
        if !metadata.file_type().is_file() {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "reference solver must be a non-symlink regular file: {}",
                    path.display()
                ),
            });
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};
            if metadata.permissions().mode() & 0o111 == 0 {
                return Err(BenchError::InvalidArgs {
                    reason: format!("reference solver is not executable: {}", path.display()),
                });
            }
            let identity = (metadata.dev(), metadata.ino());
            if let Some((previous_name, previous_path)) = identities.insert(identity, (name, path))
            {
                return Err(BenchError::InvalidArgs {
                    reason: format!(
                        "reference solver {name:?} ({}) aliases {previous_name:?} ({})",
                        path.display(),
                        previous_path.display()
                    ),
                });
            }
        }
        let canonical = std::fs::canonicalize(path)
            .with_bench_context(|| format!("canonicalizing reference solver {}", path.display()))?;
        if let Some((previous_name, previous_path)) = binaries.insert(canonical, (name, path)) {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "reference solver {name:?} ({}) duplicates {previous_name:?} ({})",
                    path.display(),
                    previous_path.display()
                ),
            });
        }
        total_bytes = total_bytes
            .checked_add(metadata.len())
            .ok_or_else(|| BenchError::msg("aggregate reference solver size overflow"))?;
        if total_bytes > MAX_REFERENCE_SNAPSHOT_BYTES {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "reference solver snapshots exceed the fixed {MAX_REFERENCE_SNAPSHOT_BYTES}-byte aggregate cap"
                ),
            });
        }
    }
    Ok(())
}

pub(crate) fn run_native(args: &NativeRunArgs<'_>) -> Result<NativeResults> {
    crate::resource::checked_benchmark_timeout(args.timeout_sec, "native benchmark")?;
    validate_native_domain(args.domain)?;
    if args.runs == 0 {
        return Err(BenchError::InvalidArgs {
            reason: "native benchmark repetitions must be positive".to_string(),
        });
    }
    if args.runs > MAX_BENCHMARK_RUNS {
        return Err(BenchError::InvalidArgs {
            reason: format!("native benchmark repetitions must not exceed {MAX_BENCHMARK_RUNS}"),
        });
    }
    let resources = args
        .resources
        .as_ref()
        .ok_or_else(|| BenchError::InvalidArgs {
            reason: "native benchmark execution requires a planned resource envelope".to_string(),
        })?;
    if let Some(argument) = args
        .solver_args
        .iter()
        .find(|argument| argument.as_str() == "--memory" || argument.starts_with("--memory="))
    {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "solver argument {argument:?} conflicts with the planned memory envelope; \
                 ay-bench supplies the exact --memory value"
            ),
        });
    }
    if args
        .run_class
        .as_deref()
        .is_some_and(|class| !matches!(class, "replay" | "laptop"))
    {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "run_class must be 'replay' or 'laptop', got {:?}",
                args.run_class.as_deref().unwrap_or_default()
            ),
        });
    }
    let (corpus_root, benchmarks) = preflight_native_benchmarks(args)?;
    if benchmarks.is_empty() {
        return Err(BenchError::msg(format!(
            "no {} benchmarks found in {}",
            args.domain,
            args.benchmarks_dir.display()
        )));
    }
    validate_reference_solvers(&args.reference_solvers)?;
    let owned_ay_pinned = if args.pinned_ay.is_none() {
        Some(crate::environment::PinnedSolver::capture(
            args.ay,
            resources,
            "ay bench pinned AY version probe",
        )?)
    } else {
        None
    };
    let ay_pinned = args
        .pinned_ay
        .or(owned_ay_pinned.as_ref())
        .ok_or_else(|| BenchError::msg("internal AY snapshot selection failed"))?;
    let owns_ay_snapshot = owned_ay_pinned.is_some();
    let requested_ay = std::fs::canonicalize(args.ay)
        .with_bench_context(|| format!("canonicalizing AY binary {}", args.ay.display()))?;
    if requested_ay.display().to_string() != ay_pinned.provenance().path {
        return Err(BenchError::msg(format!(
            "pre-pinned AY snapshot source {} does not match requested binary {}",
            ay_pinned.provenance().path,
            requested_ay.display()
        )));
    }
    let ay_provenance = ay_pinned.provenance().clone();
    let env = if let Some(environment) = args.environment.clone() {
        if environment.ay_path != ay_provenance.path
            || environment.ay_sha256 != ay_provenance.sha256
            || environment.ay_size_bytes != ay_provenance.size_bytes
            || environment.ay_version != ay_provenance.version_output
        {
            return Err(BenchError::msg(format!(
                "pre-captured AY provenance does not match the solver binary selected for this run: {}",
                ay_provenance.path
            )));
        }
        environment
    } else {
        crate::environment::Environment::capture_with_solver(ay_provenance.clone())
    };

    let total = benchmarks.len();
    let runs = args.runs;
    let sat_profile = sat_competition_profile_metadata(
        args.domain,
        args.sat_track.as_ref(),
        args.sat_ai_class.as_ref(),
        args.sat_variant.as_ref(),
    );
    let mut solver_env = BTreeMap::from([
        ("LC_ALL".to_string(), "C".to_string()),
        ("TZ".to_string(), "UTC".to_string()),
        (
            "PATH".to_string(),
            "/usr/local/bin:/usr/bin:/bin".to_string(),
        ),
        (
            "MEMLIMIT".to_string(),
            resources.plan.memlimit_mb_per_child.to_string(),
        ),
        (
            "NBCORE".to_string(),
            resources.plan.nbcore_per_child.to_string(),
        ),
    ]);
    if let Some(profile) = sat_profile.as_ref() {
        solver_env.extend(profile.env.clone());
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
    let mut reference_campaigns = args
        .reference_solvers
        .iter()
        .map(|(name, path)| ReferenceCampaign::new(name, path, total, resources))
        .collect::<Result<Vec<_>>>()?;
    if !args.quiet {
        for campaign in &reference_campaigns {
            eprintln!(
                "[ref] prepared reference solver {}",
                campaign.pinned.provenance().summary()
            );
        }
    }
    let mut items = Vec::with_capacity(total);
    let mut preprocessing = Vec::with_capacity(total);
    for (idx, benchmark) in benchmarks.iter().enumerate() {
        let benchmark_id = benchmark_identifier(benchmark, &corpus_root)?;
        let prepared = prepare_benchmark(benchmark, &benchmark_id, resources, args.timeout_sec)?;
        let mut extracted_features = args
            .with_features
            .then(|| crate::features::extract_from_file(&prepared.solver_path))
            .transpose()
            .with_bench_context(|| {
                format!(
                    "extracting requested features from private solver input for {benchmark_id}"
                )
            })?;
        if !args.quiet && should_log_progress(idx, total, progress_every) {
            eprintln!(
                "[native] {}/{}: {}",
                idx + 1,
                total,
                benchmark.file_name().unwrap_or_default().to_string_lossy(),
            );
        }
        if runs == 1 {
            let mut artifact_plan = artifact_plan_for_benchmark(
                args.domain,
                sat_profile.as_ref(),
                args.artifact_output_dir.as_deref(),
                idx,
                benchmark,
            )?;
            let run = run_solver(
                SolverRunRequest {
                    ay_path: ay_pinned.execution_path(),
                    benchmark,
                    solver_input: &prepared.solver_path,
                    benchmark_content_hash: &prepared.content_hash,
                    solver_input_hash: &prepared.solver_input_hash,
                    benchmark_id: &benchmark_id,
                    expected: &prepared.expected,
                    timeout_sec: args.timeout_sec,
                    domain: args.domain,
                    solver_args: &args.solver_args,
                    solver_env: &solver_env,
                    resources,
                },
                artifact_plan.take(),
            );
            let mut item = finalize_selected_artifacts(run);
            for campaign in &mut reference_campaigns {
                campaign.run_one(
                    &prepared.solver_path,
                    &prepared.solver_input_hash,
                    &item,
                    runs,
                    args.timeout_sec,
                    resources,
                );
            }
            item.extracted_features = extracted_features.take();
            items.push(item);
        } else {
            let mut run_results = Vec::with_capacity(runs as usize);
            for _run_index in 0..runs {
                let artifact_plan = artifact_plan_for_benchmark(
                    args.domain,
                    sat_profile.as_ref(),
                    args.artifact_output_dir.as_deref(),
                    idx,
                    benchmark,
                )?;
                let item = run_solver(
                    SolverRunRequest {
                        ay_path: ay_pinned.execution_path(),
                        benchmark,
                        solver_input: &prepared.solver_path,
                        benchmark_content_hash: &prepared.content_hash,
                        solver_input_hash: &prepared.solver_input_hash,
                        benchmark_id: &benchmark_id,
                        expected: &prepared.expected,
                        timeout_sec: args.timeout_sec,
                        domain: args.domain,
                        solver_args: &args.solver_args,
                        solver_env: &solver_env,
                        resources,
                    },
                    artifact_plan,
                );
                run_results.push(item);
            }
            let mut item = select_prepared_representative(run_results)?;
            for campaign in &mut reference_campaigns {
                campaign.run_one(
                    &prepared.solver_path,
                    &prepared.solver_input_hash,
                    &item,
                    runs,
                    args.timeout_sec,
                    resources,
                );
            }
            item.extracted_features = extracted_features.take();
            items.push(item);
        }
        preprocessing.push(prepared.metadata.clone());
    }

    // Finalize references in flag order. They ran against the same private
    // per-benchmark snapshots and repetition count as AY above.
    let mut reference_summaries: Vec<ComparisonSummary> = Vec::new();
    let mut first_comparison_items: Option<Vec<ComparisonItem>> = None;
    let mut all_comparison_items: Vec<ReferenceComparisonItems> = Vec::new();
    for campaign in reference_campaigns {
        let (summary, comp_items) = campaign.finish(resources, args.timeout_sec)?;
        let ref_name = summary.reference_solver.clone();
        if first_comparison_items.is_none() {
            first_comparison_items = Some(comp_items.clone());
        }
        all_comparison_items.push(ReferenceComparisonItems {
            reference_solver: ref_name,
            items: comp_items,
        });
        reference_summaries.push(summary);
    }
    let references = if reference_summaries.is_empty() {
        None
    } else {
        Some(reference_summaries)
    };
    let comparison = references.as_ref().and_then(|refs| refs.first().cloned());
    let reference_comparisons = if all_comparison_items.is_empty() {
        None
    } else {
        Some(all_comparison_items)
    };

    // Stamp — never verify — the requested run class with a host fingerprint.
    let run_class = args.run_class.clone();
    let run_class_verified = run_class.as_ref().map(|_| false);
    let host_fingerprint = run_class.as_ref().map(|_| HostFingerprint::capture(&env));

    if owns_ay_snapshot {
        ay_pinned.verify_source()?;
    }

    let results = NativeResults {
        environment: env,
        items,
        preprocessing,
        settings: NativeSettings {
            benchmarks_dir: args.benchmarks_dir.display().to_string(),
            timeout_sec: args.timeout_sec,
            domain: args.domain.to_string(),
            benchmark_count: total,
            runs,
            solver_args: args.solver_args.clone(),
            solver_env,
            artifact_output_dir,
            artifact_max_bytes: args
                .artifact_output_dir
                .as_ref()
                .map(|_| PROOF_ARTIFACT_LIMIT_BYTES),
            artifact_size_enforcement: args.artifact_output_dir.as_ref().map(|_| {
                "RLIMIT_FSIZE inherited before exec + 20ms live regular-file monitor; reserved unique temp, identity check, hash, atomic publish"
                    .to_string()
            }),
            sat_track: args.sat_track.clone(),
            sat_ai_class: args.sat_ai_class.clone(),
            sat_variant: args.sat_variant.clone(),
            sat_competition_profile: sat_profile,
            resource_plan: args
                .resources
                .as_ref()
                .map(|resources| resources.plan.clone()),
            resource_enforcement: args.resources.as_ref().map(|_| {
                crate::resource::ENFORCEMENT_AY_MEMORY_RSS_V1.to_string()
            }),
        },
        comparison,
        comparisons: first_comparison_items,
        reference_comparisons,
        run_class,
        run_class_verified,
        host_fingerprint,
        references,
    };

    Ok(results)
}

pub(crate) fn validate_native_domain(domain: &str) -> Result<()> {
    if matches!(domain, "sat" | "smt" | "chc") {
        Ok(())
    } else {
        Err(BenchError::InvalidArgs {
            reason: format!(
                "native benchmark domain {domain:?} is not yet supported by the solver invocation and scoring pipeline; supported domains are sat, smt, and chc"
            ),
        })
    }
}

struct ReferenceCampaign {
    name: String,
    pinned: crate::environment::PinnedSolver,
    items: Vec<ComparisonItem>,
    agree: u32,
    disagree: u32,
    ay_only: u32,
    ref_only: u32,
    both_solved: u32,
    ay_faster: u32,
    ref_faster: u32,
    ay_total: f64,
    ref_total: f64,
}

impl ReferenceCampaign {
    fn new(
        name: &str,
        solver: &Path,
        capacity: usize,
        resources: &crate::resource::PlannedResources,
    ) -> Result<Self> {
        let pinned = crate::environment::PinnedSolver::capture(
            solver,
            resources,
            "ay bench pinned reference version probe",
        )?;
        Ok(Self {
            name: name.to_string(),
            pinned,
            items: Vec::with_capacity(capacity),
            agree: 0,
            disagree: 0,
            ay_only: 0,
            ref_only: 0,
            both_solved: 0,
            ay_faster: 0,
            ref_faster: 0,
            ay_total: 0.0,
            ref_total: 0.0,
        })
    }

    fn run_one(
        &mut self,
        solver_input: &Path,
        solver_input_hash: &str,
        ay_item: &NativeResultItem,
        runs: u32,
        timeout_sec: f64,
        resources: &crate::resource::PlannedResources,
    ) {
        let mut outcomes = (0..runs)
            .map(|_| {
                run_external_solver(
                    self.pinned.execution_path(),
                    solver_input,
                    solver_input_hash,
                    timeout_sec,
                    resources,
                )
            })
            .collect::<Vec<_>>();
        let consistent = outcomes.first().is_some_and(|first| {
            outcomes
                .iter()
                .all(|outcome| outcome.result == first.result)
        });
        let reference_runs = outcomes.clone();
        outcomes.sort_by(|left, right| left.time_sec.total_cmp(&right.time_sec));
        let representative = &outcomes[(outcomes.len() - 1) / 2];
        let mut ref_result = representative.result.clone();
        let ref_time = representative.time_sec;
        if !consistent {
            ref_result = "error".to_string();
        }
        let agreement = classify_agreement(&ay_item.result, &ref_result);
        match agreement {
            "agree" => {
                self.agree += 1;
                self.both_solved += 1;
                self.ay_total += ay_item.time_sec;
                self.ref_total += ref_time;
                if ay_item.time_sec < ref_time {
                    self.ay_faster += 1;
                } else if ay_item.time_sec > ref_time {
                    self.ref_faster += 1;
                }
            }
            "disagree" => self.disagree += 1,
            "ay_only" => self.ay_only += 1,
            "ref_only" => self.ref_only += 1,
            _ => {}
        }
        self.items.push(ComparisonItem {
            file: ay_item.file.clone(),
            solver_input_hash: solver_input_hash.to_string(),
            ay_result: ay_item.result.clone(),
            ay_time_sec: ay_item.time_sec,
            ref_result,
            ref_time_sec: ref_time,
            agreement,
            reference_runs,
        });
    }

    fn finish(
        self,
        resources: &crate::resource::PlannedResources,
        timeout_sec: f64,
    ) -> Result<(ComparisonSummary, Vec<ComparisonItem>)> {
        self.pinned.verify_source()?;
        let provenance = self.pinned.provenance();
        let reference_resource_envelope = crate::resource::effective_execution_envelope(
            &resources.plan,
            crate::resource::ENFORCEMENT_RSS_WATCHDOG_V1,
            timeout_sec,
        )?;
        let summary = ComparisonSummary {
            reference_solver: self.name,
            reference_solver_path: provenance.path.clone(),
            reference_solver_sha256: provenance.sha256.clone(),
            reference_solver_size_bytes: provenance.size_bytes,
            reference_solver_version: provenance.version_output.clone(),
            reference_solver_build_version: provenance.build_version.clone(),
            reference_solver_build_commit: provenance.build_commit.clone(),
            reference_solver_build_datetime_utc: provenance.build_datetime_utc.clone(),
            reference_solver_build_stamp: provenance.build_stamp.clone(),
            reference_resource_enforcement: crate::resource::ENFORCEMENT_RSS_WATCHDOG_V1
                .to_string(),
            reference_resource_envelope,
            agree: self.agree,
            disagree: self.disagree,
            ay_only: self.ay_only,
            ref_only: self.ref_only,
            both_solved: self.both_solved,
            ay_faster: self.ay_faster,
            ref_faster: self.ref_faster,
            ay_total_time: round6(self.ay_total),
            ref_total_time: round6(self.ref_total),
        };
        Ok((summary, self.items))
    }
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn tree_contains_file(root: &Path, expected: &[u8]) -> bool {
        let Ok(entries) = std::fs::read_dir(root) else {
            return false;
        };
        entries.filter_map(std::result::Result::ok).any(|entry| {
            let path = entry.path();
            match entry.file_type() {
                Ok(kind) if kind.is_dir() => tree_contains_file(&path, expected),
                Ok(kind) if kind.is_file() => {
                    std::fs::read(path).is_ok_and(|bytes| bytes == expected)
                }
                _ => false,
            }
        })
    }

    fn artifact_test_item(time_sec: f64, result: &str) -> NativeResultItem {
        NativeResultItem {
            file: "case.cnf".to_string(),
            benchmark_path: "case.cnf".to_string(),
            benchmark_content_hash: Some("sha256:benchmark".to_string()),
            solver_input_hash: Some("sha256:input".to_string()),
            solver_input_path: Some("private-case.cnf".to_string()),
            expected: Some("unsat".to_string()),
            expected_source: "test".to_string(),
            result: result.to_string(),
            harness_error: None,
            time_sec,
            cpu_time_sec: time_sec,
            cpu_time_source: "test".to_string(),
            exit_code: Some(0),
            solver_argv: Vec::new(),
            solver_env: BTreeMap::new(),
            artifacts: None,
            sat_run: None,
            extracted_features: None,
        }
    }

    fn test_resources() -> crate::resource::PlannedResources {
        crate::resource::PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000)
    }

    #[test]
    fn native_domain_validation_is_closed() {
        for domain in ["sat", "smt", "chc"] {
            validate_native_domain(domain).expect("supported native domain");
        }

        for domain in ["", "pb", "mip", "SAT", "sat ", "unknown"] {
            assert!(
                validate_native_domain(domain).is_err(),
                "unexpectedly accepted native domain {domain:?}"
            );
        }
    }

    #[test]
    fn native_file_list_preflight_sorts_and_rejects_duplicate_ids() {
        let temp = tempfile::tempdir().expect("tempdir");
        let first = temp.path().join("a.smt2");
        let second = temp.path().join("b.smt2");
        std::fs::write(&first, "(check-sat)\n").expect("first");
        std::fs::write(&second, "(check-sat)\n").expect("second");
        let make_args = |file_list| NativeRunArgs {
            ay: Path::new("unused"),
            benchmarks_dir: temp.path(),
            timeout_sec: 1.0,
            domain: "smt",
            quiet: true,
            with_features: false,
            file_list: Some(file_list),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        };

        let (_, sorted) =
            preflight_native_benchmarks(&make_args(vec![second.clone(), first.clone()]))
                .expect("preflight");
        assert_eq!(sorted, vec![first.clone(), second]);
        let error = preflight_native_benchmarks(&make_args(vec![first.clone(), first]))
            .expect_err("duplicate IDs must fail");
        assert!(error.to_string().contains("duplicate native benchmark ID"));
    }

    #[cfg(unix)]
    #[test]
    fn reference_preflight_rejects_ambiguous_names_and_count_overflow() {
        let root = tempfile::tempdir().expect("tempdir");
        let first_dir = tempfile::tempdir_in(root.path()).expect("first dir");
        let second_dir = tempfile::tempdir_in(root.path()).expect("second dir");
        let first = write_solver_script(&first_dir, "solver", "v1", "sat");
        let second = write_solver_script(&second_dir, "solver", "v2", "sat");
        let error = validate_reference_solvers(&[
            ("solver".to_string(), first),
            ("solver".to_string(), second),
        ])
        .expect_err("duplicate display names must fail");
        assert!(error
            .to_string()
            .contains("duplicate reference solver name"));

        let too_many = (0..=MAX_REFERENCE_SOLVERS)
            .map(|index| {
                (
                    format!("ref-{index}"),
                    PathBuf::from(format!("ref-{index}")),
                )
            })
            .collect::<Vec<_>>();
        let error = validate_reference_solvers(&too_many).expect_err("count cap must fail");
        assert!(error.to_string().contains("solver cap"));
    }

    #[test]
    fn pipe_capture_preserves_output_below_limit() {
        let input = vec![b'x'; CAPTURE_HEAD_BYTES + 4096];
        let capture = PipeCapture::start(std::io::Cursor::new(input.clone()));
        let output = capture.finish();
        assert!(!output.incomplete());
        assert_eq!(output.text.as_bytes(), input);
    }

    #[test]
    fn pipe_capture_marks_output_over_limit_incomplete() {
        let input = vec![b'x'; CAPTURE_HEAD_BYTES + CAPTURE_TAIL_BYTES + 1];
        let output = PipeCapture::start(std::io::Cursor::new(input)).finish();
        assert!(output.truncated);
        assert!(output.incomplete());
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
    fn write_environment_isolation_solver_script(dir: &TempDir) -> PathBuf {
        use std::os::unix::fs::PermissionsExt as _;

        let path = dir.path().join("environment-isolation-solver.sh");
        std::fs::write(
            &path,
            "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then echo test-version; exit 0; fi\nif [ -n \"${AY_BENCH_UNRECORDED_SENTINEL+x}\" ]; then echo unsat; else echo sat; fi\n",
        )
        .expect("write environment probe");
        let mut permissions = std::fs::metadata(&path).expect("metadata").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&path, permissions).expect("chmod");
        path
    }

    #[cfg(unix)]
    struct EnvironmentRestore {
        name: &'static str,
        previous: Option<std::ffi::OsString>,
    }

    #[cfg(unix)]
    impl EnvironmentRestore {
        fn set(name: &'static str, value: &str) -> Self {
            let previous = std::env::var_os(name);
            std::env::set_var(name, value);
            Self { name, previous }
        }
    }

    #[cfg(unix)]
    impl Drop for EnvironmentRestore {
        fn drop(&mut self) {
            if let Some(previous) = self.previous.take() {
                std::env::set_var(self.name, previous);
            } else {
                std::env::remove_var(self.name);
            }
        }
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
               set -e\n\
               set -C\n\
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
    fn write_oversized_artifact_solver_script(dir: &TempDir) -> PathBuf {
        use std::os::unix::fs::PermissionsExt as _;

        let path = dir.path().join("oversized-artifact-solver.sh");
        let body = "#!/bin/sh\n\
                    if [ \"$1\" = \"--version\" ]; then\n\
                      printf '%s\\n' 'oversized artifact solver'\n\
                      exit 0\n\
                    fi\n\
                    set -e\n\
                    proof=''\n\
                    while [ \"$#\" -gt 0 ]; do\n\
                      if [ \"$1\" = \"--proof\" ]; then shift; proof=\"$1\"; fi\n\
                      shift\n\
                    done\n\
                    dd if=/dev/zero of=\"$proof\" bs=1048576 count=2 2>/dev/null\n\
                    printf '%s\\n' unsat\n";
        std::fs::write(&path, body).expect("write oversized artifact solver");
        let mut permissions = std::fs::metadata(&path).expect("metadata").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&path, permissions).expect("chmod");
        path
    }

    #[cfg(unix)]
    fn write_planted_destination_solver_script(dir: &TempDir, destination: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt as _;

        let path = dir.path().join("planted-destination-solver.sh");
        let body = format!(
            "#!/bin/sh\n\
             if [ \"$1\" = \"--version\" ]; then\n\
               printf '%s\\n' 'planted destination solver'\n\
               exit 0\n\
             fi\n\
             set -e\n\
             proof=''\n\
             while [ \"$#\" -gt 0 ]; do\n\
               if [ \"$1\" = \"--proof\" ]; then shift; proof=\"$1\"; fi\n\
               shift\n\
             done\n\
             printf '%s\\n' 'validated-proof' > \"$proof\"\n\
             printf '%s\\n' 'concurrent-owner' > {}\n\
             printf '%s\\n' 'unsat'\n",
            shell_quote(&destination.display().to_string())
        );
        std::fs::write(&path, body).expect("write planted destination solver");
        let mut permissions = std::fs::metadata(&path).expect("metadata").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&path, permissions).expect("chmod");
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
        let args = external_solver_args(Path::new("/usr/bin/z3"), Path::new("case.smt2"))
            .expect("z3 args");
        let strings = args
            .iter()
            .map(|arg| arg.to_string_lossy().to_string())
            .collect::<Vec<_>>();
        assert_eq!(strings, vec!["--", "case.smt2"]);
    }

    #[test]
    fn test_external_solver_args_special_case_golem() {
        let dir = tempfile::tempdir().expect("tempdir");
        let benchmark = dir.path().join("case.smt2");
        std::fs::write(&benchmark, "(set-logic QF_LRA)\n(check-sat)\n").expect("write benchmark");
        let args = external_solver_args(Path::new("/tmp/golem"), &benchmark).expect("golem args");
        let strings = args
            .iter()
            .map(|arg| arg.to_string_lossy().to_string())
            .collect::<Vec<_>>();
        assert_eq!(strings[0..4], ["-l", "QF_LRA", "-e", "spacer"]);
        assert_eq!(strings[4], benchmark.display().to_string());
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
        assert_eq!(parse_verdict("sat\n", "", Some(0)), "sat");
        assert_eq!(parse_verdict("SAT\n", "", Some(10)), "sat");
        assert_eq!(parse_verdict("s satisfiable\n", "", Some(0)), "sat");
    }

    #[test]
    fn test_parse_verdict_unsat() {
        assert_eq!(parse_verdict("unsat\n", "", Some(0)), "unsat");
        assert_eq!(parse_verdict("UNSAT\n", "", Some(20)), "unsat");
        assert_eq!(parse_verdict("s unsatisfiable\n", "", Some(0)), "unsat");
    }

    #[test]
    fn test_parse_verdict_exit_code() {
        assert_eq!(parse_verdict("", "", Some(10)), "sat");
        assert_eq!(parse_verdict("", "", Some(20)), "unsat");
        assert_eq!(parse_verdict("", "", Some(0)), "error");
        assert_eq!(parse_verdict("", "", None), "error");
    }

    #[test]
    fn test_parse_reference_verdict_requires_normal_exit() {
        assert_eq!(parse_reference_verdict("", "", None), "error");
        assert_eq!(parse_reference_verdict("sat\n", "", None), "error");
        assert_eq!(parse_reference_verdict("", "", Some(0)), "error");
    }

    #[test]
    fn test_parse_verdict_unknown() {
        assert_eq!(parse_verdict("unknown\n", "", Some(0)), "unknown");
        assert_eq!(parse_verdict("s unknown\n", "", Some(0)), "unknown");
    }

    #[test]
    fn test_parse_verdict_rejects_crashes_contradictions_and_fatal_diagnostics() {
        assert_eq!(parse_verdict("sat\n", "", Some(1)), "error");
        assert_eq!(parse_verdict("sat\nunsat\n", "", Some(0)), "error");
        assert_eq!(
            parse_verdict("sat\n", "error: corrupted state\n", Some(0)),
            "error"
        );
    }

    #[cfg(unix)]
    #[test]
    fn benchmark_discovery_does_not_follow_symlink_cycles() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("tempdir");
        let nested = temp.path().join("nested");
        std::fs::create_dir(&nested).expect("nested dir");
        let benchmark = nested.join("case.cnf");
        std::fs::write(&benchmark, "p cnf 0 0\n").expect("benchmark");
        symlink(temp.path(), nested.join("cycle")).expect("cycle symlink");

        let discovered = discover_benchmarks(temp.path(), "sat").expect("discover");
        assert_eq!(discovered, vec![benchmark]);
    }

    #[cfg(unix)]
    #[test]
    fn benchmark_preflight_rejects_fifo_without_blocking() {
        let temp = tempfile::tempdir().expect("tempdir");
        let fifo = temp.path().join("blocking.cnf");
        let status = std::process::Command::new("mkfifo")
            .arg(&fifo)
            .status()
            .expect("run mkfifo");
        assert!(status.success());

        let started = Instant::now();
        assert!(validate_benchmark_target(&fifo).is_err());
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn native_run_rejects_unrepresentable_timeout_before_spawning() {
        let resources = test_resources();
        let error = run_native(&NativeRunArgs {
            ay: Path::new("definitely-not-a-solver"),
            benchmarks_dir: Path::new("."),
            timeout_sec: f64::MAX,
            domain: "smt",
            quiet: true,
            with_features: false,
            file_list: Some(vec![PathBuf::from("unused.smt2")]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(resources),
        })
        .expect_err("huge timeout must fail");
        assert!(error.to_string().contains("timeout"));
    }

    #[cfg(unix)]
    #[test]
    fn native_solver_does_not_inherit_unrecorded_parent_environment() {
        let temp = tempfile::tempdir().expect("tempdir");
        let solver = write_environment_isolation_solver_script(&temp);
        let benchmark = temp.path().join("case.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("benchmark");
        let _restore = EnvironmentRestore::set("AY_BENCH_UNRECORDED_SENTINEL", "present");

        let results = run_native(&NativeRunArgs {
            ay: &solver,
            benchmarks_dir: temp.path(),
            timeout_sec: 1.0,
            domain: "smt",
            quiet: true,
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        })
        .expect("run native");

        let item = results.items.first().expect("result item");
        assert_eq!(item.result, "sat");
        assert!(!item.solver_env.contains_key("AY_BENCH_UNRECORDED_SENTINEL"));
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
    fn benchmark_discovery_rejects_file_count_overflow() {
        let temp = tempfile::tempdir().expect("tempdir");
        for name in ["a.cnf", "b.cnf", "c.cnf"] {
            std::fs::write(temp.path().join(name), "p cnf 0 0\n").expect("benchmark");
        }
        let mut files = Vec::new();
        let error =
            collect_benchmarks_recursive_with_limits(temp.path(), "sat", &mut files, 100, 100, 2)
                .expect_err("discovery must enforce its benchmark cap");
        assert!(error.to_string().contains("2-benchmark cap"));
        assert!(files.len() <= 2);
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
    fn decompression_targets_are_unique_and_created_exclusively() {
        let (first, first_file) = create_decompression_target("case.cnf").expect("first target");
        let (second, second_file) = create_decompression_target("case.cnf").expect("second target");
        drop((first_file, second_file));

        assert_ne!(first, second);
        assert!(first.is_file());
        assert!(second.is_file());
        assert_ne!(
            first.parent().and_then(Path::file_name),
            Some(std::ffi::OsStr::new("ay-bench-decompress"))
        );
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            assert_eq!(
                std::fs::metadata(&first)
                    .expect("first metadata")
                    .permissions()
                    .mode()
                    & 0o777,
                0o600
            );
        }
        std::fs::remove_file(first).expect("remove first");
        std::fs::remove_file(second).expect("remove second");
    }

    #[cfg(unix)]
    #[test]
    fn decompression_rejects_output_past_fixed_file_cap() {
        let dir = tempfile::tempdir().expect("tempdir");
        let source = dir.path().join("bomb.smt2");
        std::fs::write(
            &source,
            vec![b'x'; DECOMPRESSED_FILE_LIMIT_BYTES as usize + 4096],
        )
        .expect("write source");
        let compressed = dir.path().join("bomb.smt2.gz");
        let output = std::fs::File::create(&compressed).expect("create gzip");
        let status = std::process::Command::new("gzip")
            .arg("-c")
            .arg(&source)
            .stdout(Stdio::from(output))
            .status()
            .expect("gzip must be installed for compressed benchmark support");
        assert!(status.success());

        let error = decompress_to_temp(&compressed, Some(&test_resources()), 5.0)
            .expect_err("decompression bomb must hit the fixed file cap");
        assert!(error.to_string().contains("decompressed-size cap"));
    }

    #[cfg(unix)]
    #[test]
    fn decompression_accepts_mixed_case_compression_suffix() {
        let dir = tempfile::tempdir().expect("tempdir");
        let source = dir.path().join("case.CNF");
        std::fs::write(&source, b"p cnf 0 0\n").expect("source");
        let compressed = dir.path().join("case.CNF.GZ");
        let output = std::fs::File::create(&compressed).expect("create gzip");
        let status = std::process::Command::new("gzip")
            .arg("-c")
            .arg(&source)
            .stdout(Stdio::from(output))
            .status()
            .expect("gzip must be installed for compressed benchmark support");
        assert!(status.success());

        let decompressed =
            decompress_to_temp(&compressed, Some(&test_resources()), 5.0).expect("decompress");
        assert_eq!(
            std::fs::read(&decompressed.path).expect("read decompressed"),
            b"p cnf 0 0\n"
        );
        std::fs::remove_file(decompressed.path).expect("remove decompressed temp");
    }

    #[cfg(unix)]
    #[test]
    fn requested_features_are_bound_to_private_decompressed_solver_input() {
        let dir = tempfile::tempdir().expect("tempdir");
        let solver = write_solver_script(&dir, "feature-solver.sh", "feature solver", "sat");
        let source = dir.path().join("feature.CNF");
        std::fs::write(&source, b"p cnf 2 1\n1 -2 0\n").expect("source");
        let compressed = dir.path().join("feature.CNF.GZ");
        let output = std::fs::File::create(&compressed).expect("create gzip");
        let status = std::process::Command::new("gzip")
            .arg("-c")
            .arg(&source)
            .stdout(Stdio::from(output))
            .status()
            .expect("gzip must be installed for compressed benchmark support");
        assert!(status.success());
        std::fs::remove_file(source).expect("remove uncompressed source");

        let results = run_native(&NativeRunArgs {
            ay: &solver,
            benchmarks_dir: dir.path(),
            timeout_sec: 2.0,
            domain: "sat",
            quiet: true,
            with_features: true,
            file_list: Some(vec![compressed]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        })
        .expect("feature run");
        let item = results.items.first().expect("result item");
        let extracted = item.extracted_features.as_ref().expect("features");
        assert_eq!(extracted.features.clause_width_max, 2);
        assert_ne!(item.benchmark_content_hash, item.solver_input_hash);
    }

    #[test]
    fn content_hash_uses_stable_sha256_storage_format() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = tmp.path().join("input.smt2");
        std::fs::write(&path, b"abc").expect("write input");
        let mut file = std::fs::File::open(&path).expect("open input");
        assert_eq!(
            content_hash_open_file(&mut file, "benchmark input", DECOMPRESSED_FILE_LIMIT_BYTES)
                .expect("hash input"),
            "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
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
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
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
        let resources = test_resources();
        let evidence = run_external_solver(&solver, &benchmark, "sha256:test", 5.0, &resources);

        assert_eq!(evidence.result, "timeout");
        assert_eq!(evidence.time_sec, 5.0);
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

        let resources = test_resources();
        let evidence = run_external_solver(&solver, &benchmark, "sha256:test", 5.0, &resources);

        assert_eq!(evidence.result, "error");
        assert!(evidence.time_sec < 5.0);
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
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
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

        let resources = test_resources();
        let evidence = run_external_solver(&solver, &benchmark, "sha256:test", 15.0, &resources);

        assert_eq!(evidence.result, "sat");
        let child_pid = read_pid_file(&pid_file);
        let _cleanup = PidCleanup(Some(child_pid));
        assert!(
            wait_until_pid_exits(child_pid, Duration::from_secs(2)),
            "reference wrapper exit must reap descendant holding stdout/stderr pid {child_pid}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn pre_pinned_ay_snapshot_is_probed_once_and_reused_without_source_rehash() {
        use std::os::unix::fs::PermissionsExt as _;

        let tmp = tempfile::tempdir().expect("tempdir");
        let version_count = tmp.path().join("version-count.txt");
        let ay = tmp.path().join("fake-ay.sh");
        std::fs::write(
            &ay,
            format!(
                "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then printf 'probe\\n' >> '{}'; printf 'ay test\\n'; exit 0; fi\nprintf 'sat\\n'\n",
                version_count.display()
            ),
        )
        .expect("write solver");
        let mut permissions = std::fs::metadata(&ay)
            .expect("solver metadata")
            .permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&ay, permissions).expect("chmod solver");
        let benchmark = tmp.path().join("sample.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");
        let resources = test_resources();
        let pinned =
            crate::environment::PinnedSolver::capture(&ay, &resources, "pre-pinned AY regression")
                .expect("pin solver");
        std::fs::write(&ay, "#!/bin/sh\nprintf 'unsat\\n'\n").expect("mutate source after pin");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: tmp.path(),
            timeout_sec: 5.0,
            domain: "smt",
            quiet: true,
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: Some(&pinned),
            artifact_output_dir: None,
            resources: Some(resources),
        })
        .expect("run with pre-pinned solver");

        assert_eq!(results.items[0].result, "sat");
        assert_eq!(
            std::fs::read_to_string(version_count)
                .expect("version counter")
                .lines()
                .count(),
            1,
            "native execution must not hash or probe a second AY snapshot"
        );
        assert!(
            pinned.verify_source().is_err(),
            "the campaign owner must detect source mutation at final verification"
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
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: vec![("fake-ref.sh".to_string(), reference.clone())],
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        })
        .expect("run native");

        assert_eq!(results.environment.ay_path, ay.display().to_string());
        assert_eq!(
            results.environment.ay_build_stamp, "0.9.0+build.42.abc123@2026-04-21T12:34:56Z",
            "version output was {:?}",
            results.environment.ay_version,
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
            with_features: false,
            file_list: Some(vec![benchmark.clone()]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: vec!["--sat-variant".to_string(), "probe".to_string()],
            sat_track: Some("Main Track".to_string()),
            sat_ai_class: Some("experimental".to_string()),
            sat_variant: Some("probe".to_string()),
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
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
        let solver_input = item
            .solver_input_path
            .as_deref()
            .expect("private solver input");
        assert_ne!(item.solver_argv[0], ay.display().to_string());
        assert!(item.solver_argv[0].ends_with("/fake-ay.sh"));
        assert_eq!(
            &item.solver_argv[1..],
            vec![
                "--sat-variant".to_string(),
                "probe".to_string(),
                "--memory".to_string(),
                "10000".to_string(),
                "--".to_string(),
                solver_input.to_string(),
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
            with_features: false,
            file_list: Some(vec![benchmark.clone()]),
            runs: 1,
            reference_solvers: vec![(crate::native::reference_display_name(&reference), reference)],
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        })
        .expect("run native");

        let item = results.items.first().expect("result item");
        let solver_input = item
            .solver_input_path
            .as_deref()
            .expect("private solver input");
        assert_ne!(item.solver_argv[0], ay.display().to_string());
        assert!(item.solver_argv[0].ends_with("/fake-ay.sh"));
        assert_eq!(
            &item.solver_argv[1..],
            vec![
                "--memory".to_string(),
                "10000".to_string(),
                "--".to_string(),
                solver_input.to_string(),
            ]
        );
        assert_eq!(item.result, "sat");
        assert_eq!(results.comparison.expect("comparison").agree, 1);

        let ref_argv = std::fs::read_to_string(ref_argv_file).expect("read ref argv");
        assert_eq!(
            ref_argv.lines().collect::<Vec<_>>(),
            vec!["--", solver_input]
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
            with_features: false,
            file_list: Some(vec![benchmark.clone()]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: vec!["--sat-variant".to_string(), "default".to_string()],
            sat_track: Some("main".to_string()),
            sat_ai_class: Some("regular".to_string()),
            sat_variant: Some("default".to_string()),
            environment: None,
            pinned_ay: None,
            artifact_output_dir: Some(artifact_dir.clone()),
            resources: Some(test_resources()),
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
        let proof_work_path = PathBuf::from(&item.solver_argv[proof_index + 1]);
        let proof_staging_path = proof_work_path.parent().expect("proof staging directory");
        assert_eq!(proof_staging_path.parent(), Some(artifact_dir.as_path()));
        assert!(
            !proof_work_path.exists(),
            "temporary proof path is consumed"
        );
        assert!(
            !proof_staging_path.exists(),
            "private proof staging directory is consumed"
        );

        let artifacts = item.artifacts.as_ref().expect("artifact metadata");
        let proof_path = PathBuf::from(
            artifacts
                .proof_path
                .as_deref()
                .expect("published proof path"),
        );
        assert_eq!(artifacts.output_dir, artifact_dir.display().to_string());
        assert_ne!(proof_path, proof_work_path);
        assert_eq!(proof_path.parent(), Some(artifact_dir.as_path()));
        assert_eq!(
            proof_path.extension().and_then(|e| e.to_str()),
            Some("lrat")
        );
        assert_eq!(artifacts.proof_format.as_deref(), Some("lrat"));
        assert_eq!(artifacts.proof_exists, Some(true));
        assert_eq!(artifacts.proof_bytes, Some(12));
        let proof_hash = artifacts.proof_hash.as_deref().expect("proof hash");
        assert!(proof_hash.starts_with("sha256:"));
        assert_eq!(
            proof_hash,
            {
                let mut proof = std::fs::File::open(&proof_path).expect("open proof artifact");
                content_hash_open_file(&mut proof, "proof artifact", PROOF_ARTIFACT_LIMIT_BYTES)
                    .expect("hash proof artifact")
            }
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
        assert!(argv_text.contains(&proof_work_path.display().to_string()));
    }

    #[cfg(unix)]
    #[test]
    fn actual_ay_binary_emits_unsat_proof_to_absent_work_path() {
        let Some(ay_path) = std::env::var_os("AY_BENCH_TEST_AY_BIN").map(PathBuf::from) else {
            return;
        };
        assert!(
            ay_path.is_file(),
            "AY_BENCH_TEST_AY_BIN must name an AY executable"
        );

        let temp = tempfile::tempdir().expect("tempdir");
        let benchmark = temp.path().join("contradiction.cnf");
        let artifact_dir = temp.path().join("artifacts");
        std::fs::write(&benchmark, "p cnf 1 2\n1 0\n-1 0\n").expect("write benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay_path,
            benchmarks_dir: temp.path(),
            timeout_sec: 10.0,
            domain: "sat",
            quiet: true,
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: Some("main".to_string()),
            sat_ai_class: Some("regular".to_string()),
            sat_variant: Some("default".to_string()),
            environment: None,
            pinned_ay: None,
            artifact_output_dir: Some(artifact_dir.clone()),
            resources: Some(test_resources()),
        })
        .expect("run actual AY");

        let item = results.items.first().expect("result item");
        assert_eq!(
            item.result, "unsat",
            "actual AY failed to produce an UNSAT proof: {:?}",
            item.harness_error
        );
        let proof_index = item
            .solver_argv
            .iter()
            .position(|arg| arg == "--proof")
            .expect("argv should include explicit proof path");
        let work_path = PathBuf::from(&item.solver_argv[proof_index + 1]);
        let staging_path = work_path.parent().expect("proof staging directory");
        assert_eq!(staging_path.parent(), Some(artifact_dir.as_path()));
        assert!(!work_path.exists(), "solver work proof is consumed");
        assert!(
            !staging_path.exists(),
            "solver staging directory is consumed"
        );

        let artifacts = item.artifacts.as_ref().expect("proof artifact metadata");
        assert_eq!(artifacts.proof_exists, Some(true));
        assert!(artifacts.proof_bytes.is_some_and(|bytes| bytes > 0));
        let proof_path = artifacts
            .proof_path
            .as_deref()
            .map(PathBuf::from)
            .expect("published proof path");
        assert!(
            std::fs::metadata(&proof_path)
                .expect("published proof metadata")
                .len()
                > 0
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_run_native_rejects_missing_sat_proof_file() {
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
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: vec!["--sat-variant".to_string(), "default".to_string()],
            sat_track: Some("main".to_string()),
            sat_ai_class: Some("regular".to_string()),
            sat_variant: Some("default".to_string()),
            environment: None,
            pinned_ay: None,
            artifact_output_dir: Some(artifact_dir.clone()),
            resources: Some(test_resources()),
        })
        .expect("run native");

        let item = results.items.first().expect("result item");
        assert_eq!(item.result, "error");
        assert!(item
            .harness_error
            .as_deref()
            .is_some_and(|detail| detail.starts_with("proof artifact preparation failed:")));

        let proof_index = item
            .solver_argv
            .iter()
            .position(|arg| arg == "--proof")
            .expect("argv should include explicit proof path");
        let proof_work_path = PathBuf::from(&item.solver_argv[proof_index + 1]);
        let proof_staging_path = proof_work_path.parent().expect("proof staging directory");
        assert_eq!(proof_staging_path.parent(), Some(artifact_dir.as_path()));
        assert!(!proof_work_path.exists(), "failed proof temp is cleaned");
        assert!(
            !proof_staging_path.exists(),
            "empty proof staging directory is cleaned"
        );
        assert!(item.artifacts.is_none());
        assert_eq!(
            std::fs::read_dir(&artifact_dir)
                .expect("read artifacts")
                .count(),
            0
        );
    }

    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn atomic_noclobber_rename_preserves_an_existing_destination() {
        let temp = tempfile::tempdir().expect("tempdir");
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        std::fs::write(&source, b"source-owner").expect("write source");
        std::fs::write(&destination, b"destination-owner").expect("write destination");

        let error = rename_noclobber(&source, &destination)
            .expect_err("atomic no-clobber rename must reject an existing destination");
        assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
        assert_eq!(
            std::fs::read(&source).expect("source survives collision"),
            b"source-owner"
        );
        assert_eq!(
            std::fs::read(&destination).expect("destination survives collision"),
            b"destination-owner"
        );
    }

    #[cfg(not(all(target_os = "linux", target_env = "gnu")))]
    #[test]
    fn unavailable_noclobber_rename_fails_without_mutating_either_path() {
        let temp = tempfile::tempdir().expect("tempdir");
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        std::fs::write(&source, b"source-owner").expect("write source");

        let error = rename_noclobber(&source, &destination)
            .expect_err("unsupported no-clobber rename must fail closed");
        assert_eq!(error.kind(), std::io::ErrorKind::Unsupported);
        assert_eq!(
            std::fs::read(&source).expect("source survives unsupported operation"),
            b"source-owner"
        );
        assert!(!destination.exists(), "destination remains absent");

        std::fs::write(&destination, b"destination-owner").expect("write destination");
        let error = rename_noclobber(&source, &destination)
            .expect_err("unsupported no-clobber rename must not inspect-and-rename");
        assert_eq!(error.kind(), std::io::ErrorKind::Unsupported);
        assert_eq!(
            std::fs::read(&source).expect("source still survives"),
            b"source-owner"
        );
        assert_eq!(
            std::fs::read(&destination).expect("destination survives"),
            b"destination-owner"
        );
    }

    #[cfg(unix)]
    #[test]
    fn artifact_plan_uses_absent_path_in_private_staging_directory() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().expect("tempdir");
        let plan =
            artifact_plan_for_benchmark("sat", None, Some(temp.path()), 0, Path::new("case.cnf"))
                .expect("plan")
                .expect("SAT artifact plan");
        let staging_path = plan
            .proof_staging
            .as_ref()
            .expect("proof staging directory")
            .path
            .clone();

        assert_eq!(plan.proof_work_path.parent(), Some(staging_path.as_path()));
        assert_eq!(staging_path.parent(), Some(temp.path()));
        assert!(
            !plan.proof_work_path.exists(),
            "solver must receive an absent create-new path"
        );
        assert_eq!(
            std::fs::metadata(&staging_path)
                .expect("staging metadata")
                .permissions()
                .mode()
                & 0o777,
            0o700
        );

        drop(plan);
        assert!(
            !staging_path.exists(),
            "unused private staging directory is cleaned"
        );
    }

    #[test]
    fn staging_cleanup_never_follows_a_post_quarantine_replacement() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut plan =
            artifact_plan_for_benchmark("sat", None, Some(temp.path()), 0, Path::new("case.cnf"))
                .expect("plan")
                .expect("SAT artifact plan");
        let staging_path = plan.proof_staging.as_ref().expect("staging").path.clone();

        cleanup_proof_staging_with_hook(&mut plan, |retired_path, _| {
            std::fs::create_dir(retired_path).expect("plant replacement directory");
            std::fs::write(retired_path.join("owner-data"), b"concurrent-owner")
                .expect("plant replacement file");
        })
        .expect("clean authenticated quarantined staging");

        assert_eq!(
            std::fs::read(staging_path.join("owner-data")).expect("replacement survives"),
            b"concurrent-owner"
        );
    }

    #[test]
    fn staging_cleanup_preserves_a_pre_quarantine_directory_replacement() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut plan =
            artifact_plan_for_benchmark("sat", None, Some(temp.path()), 0, Path::new("case.cnf"))
                .expect("plan")
                .expect("SAT artifact plan");
        let staging_path = plan.proof_staging.as_ref().expect("staging").path.clone();
        let authentic_path = temp.path().join("authentic-staging-moved-away");
        std::fs::rename(&staging_path, &authentic_path).expect("move authentic directory");
        std::fs::create_dir(&staging_path).expect("plant replacement directory");
        std::fs::write(staging_path.join("owner-data"), b"concurrent-owner")
            .expect("plant replacement file");

        let error = cleanup_proof_staging(&mut plan).expect_err("replacement must be preserved");
        assert!(error
            .to_string()
            .contains("refusing to remove replaced proof staging directory"));
        assert!(
            authentic_path.exists(),
            "authentic directory was not inferred by path"
        );
        assert!(
            tree_contains_file(temp.path(), b"concurrent-owner"),
            "replacement contents survive under quarantine"
        );
    }

    #[test]
    fn repeated_runs_publish_only_the_selected_private_proof() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut runs = Vec::new();
        let mut staging_paths = Vec::new();
        for (time, proof) in [
            (3.0, b"slow-proof".as_slice()),
            (1.0, b"fast-proof".as_slice()),
            (2.0, b"median-proof".as_slice()),
        ] {
            let plan = artifact_plan_for_benchmark(
                "sat",
                None,
                Some(temp.path()),
                0,
                Path::new("case.cnf"),
            )
            .expect("plan")
            .expect("SAT artifact plan");
            staging_paths.push(plan.proof_staging.as_ref().expect("staging").path.clone());
            std::fs::write(&plan.proof_work_path, proof).expect("write private proof");
            runs.push(prepare_solver_run_artifacts(
                artifact_test_item(time, "unsat"),
                Some(plan),
            ));
        }

        assert_eq!(
            std::fs::read_dir(temp.path())
                .expect("artifact directory")
                .count(),
            3,
            "all repeated proofs remain private before selection"
        );
        let selected = select_prepared_representative(runs).expect("select median run");
        assert_eq!(selected.time_sec, 2.0);
        let proof_path = PathBuf::from(
            selected
                .artifacts
                .as_ref()
                .and_then(|artifacts| artifacts.proof_path.as_deref())
                .expect("published selected proof"),
        );
        assert_eq!(
            std::fs::read(&proof_path).expect("selected proof bytes"),
            b"median-proof"
        );
        assert!(staging_paths.iter().all(|path| !path.exists()));
        let entries = std::fs::read_dir(temp.path())
            .expect("artifact directory")
            .collect::<std::io::Result<Vec<_>>>()
            .expect("artifact entries");
        assert_eq!(entries.len(), 1, "discarded private artifacts do not leak");
        assert_eq!(entries[0].path(), proof_path);
        assert!(!proof_path
            .file_name()
            .and_then(|name| name.to_str())
            .expect("UTF-8 proof name")
            .contains(".run-"));
    }

    #[test]
    fn proof_publication_never_clobbers_concurrently_created_destination() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut plan =
            artifact_plan_for_benchmark("sat", None, Some(temp.path()), 0, Path::new("case.cnf"))
                .expect("plan")
                .expect("SAT artifact plan");
        std::fs::write(&plan.proof_work_path, b"validated-proof").expect("write proof");
        std::fs::write(&plan.proof_path, b"concurrent-owner").expect("create destination");

        authenticate_solver_proof_output(&mut plan, true)
            .expect("authenticate proof")
            .expect("proof metadata");
        let error = publish_artifact_metadata(&mut plan)
            .expect_err("no-clobber publication must reject destination");
        assert!(error.to_string().contains("publishing proof artifact"));
        cleanup_failed_artifact_plan(&mut plan).expect("cleanup unowned collision");
        assert_eq!(
            std::fs::read(&plan.proof_path).expect("destination survives"),
            b"concurrent-owner"
        );
    }

    #[cfg(unix)]
    #[test]
    fn failed_cleanup_preserves_replaced_solver_work_path() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut plan =
            artifact_plan_for_benchmark("sat", None, Some(temp.path()), 0, Path::new("case.cnf"))
                .expect("plan")
                .expect("SAT artifact plan");
        let work_path = plan.proof_work_path.clone();
        let staging_path = work_path
            .parent()
            .expect("proof staging directory")
            .to_path_buf();
        std::fs::write(&work_path, b"solver-owned").expect("write solver proof");
        authenticate_solver_proof_output(&mut plan, true)
            .expect("authenticate solver proof")
            .expect("solver proof metadata");

        std::fs::remove_file(&work_path).expect("unlink authenticated proof");
        std::fs::write(&work_path, b"concurrent-owner").expect("plant replacement");

        let error =
            cleanup_failed_artifact_plan(&mut plan).expect_err("replacement must be preserved");
        assert!(error
            .to_string()
            .contains("refusing to remove mutated proof staging contents"));
        assert!(
            tree_contains_file(temp.path(), b"concurrent-owner"),
            "replacement bytes survive in the private quarantine"
        );
        drop(plan);
        assert!(
            tree_contains_file(temp.path(), b"concurrent-owner"),
            "replacement survives plan drop"
        );
        assert!(!staging_path.exists(), "public staging name stays retired");
    }

    #[cfg(unix)]
    #[test]
    fn failed_cleanup_preserves_replaced_published_proof_path() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut plan =
            artifact_plan_for_benchmark("sat", None, Some(temp.path()), 0, Path::new("case.cnf"))
                .expect("plan")
                .expect("SAT artifact plan");
        std::fs::write(&plan.proof_work_path, b"validated-proof").expect("write proof");
        authenticate_solver_proof_output(&mut plan, true)
            .expect("authenticate proof")
            .expect("proof metadata");
        publish_artifact_metadata(&mut plan).expect("publish proof");
        let proof_path = plan.proof_path.clone();

        std::fs::remove_file(&proof_path).expect("unlink published proof");
        std::fs::write(&proof_path, b"concurrent-owner").expect("plant replacement");

        let error =
            cleanup_failed_artifact_plan(&mut plan).expect_err("replacement must be preserved");
        assert!(error.to_string().contains("preserving public proof path"));
        assert_eq!(
            std::fs::read(&proof_path).expect("replacement survives cleanup"),
            b"concurrent-owner"
        );
        drop(plan);
        assert_eq!(
            std::fs::read(&proof_path).expect("replacement survives plan drop"),
            b"concurrent-owner"
        );
    }

    #[test]
    fn failed_cleanup_preserves_authenticated_published_proof() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut plan =
            artifact_plan_for_benchmark("sat", None, Some(temp.path()), 0, Path::new("case.cnf"))
                .expect("plan")
                .expect("SAT artifact plan");
        std::fs::write(&plan.proof_work_path, b"validated-proof").expect("write proof");
        authenticate_solver_proof_output(&mut plan, true)
            .expect("authenticate proof")
            .expect("proof metadata");
        publish_artifact_metadata(&mut plan).expect("publish proof");

        let error =
            cleanup_failed_artifact_plan(&mut plan).expect_err("published proof is preserved");
        assert!(error.to_string().contains("preserving public proof path"));
        assert_eq!(
            std::fs::read(&plan.proof_path).expect("published proof survives cleanup"),
            b"validated-proof"
        );
    }

    #[cfg(unix)]
    #[test]
    fn run_native_cleanup_preserves_planted_public_proof_destination() {
        let temp = tempfile::tempdir().expect("tempdir");
        let benchmark = temp.path().join("planted.cnf");
        let artifact_dir = temp.path().join("artifacts");
        std::fs::create_dir(&artifact_dir).expect("artifact directory");
        std::fs::write(&benchmark, "p cnf 1 1\n-1 0\n").expect("benchmark");
        let destination = artifact_dir.join(artifact_file_name(0, &benchmark, "lrat"));
        let ay = write_planted_destination_solver_script(&temp, &destination);

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: temp.path(),
            timeout_sec: 2.0,
            domain: "sat",
            quiet: true,
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: Some("main".to_string()),
            sat_ai_class: Some("regular".to_string()),
            sat_variant: Some("default".to_string()),
            environment: None,
            pinned_ay: None,
            artifact_output_dir: Some(artifact_dir),
            resources: Some(test_resources()),
        })
        .expect("run native");

        let item = results.items.first().expect("item");
        assert_eq!(item.result, "error");
        assert!(item
            .harness_error
            .as_deref()
            .is_some_and(|detail| detail.contains("publishing proof artifact")));
        assert_eq!(
            std::fs::read(&destination).expect("planted destination survives cleanup"),
            b"concurrent-owner\n"
        );
    }

    #[cfg(unix)]
    #[test]
    fn run_native_enforces_hard_proof_size_limit() {
        let temp = tempfile::tempdir().expect("tempdir");
        let ay = write_oversized_artifact_solver_script(&temp);
        let benchmark = temp.path().join("oversized.cnf");
        let artifact_dir = temp.path().join("artifacts");
        std::fs::write(&benchmark, "p cnf 1 1\n-1 0\n").expect("benchmark");

        let results = run_native(&NativeRunArgs {
            ay: &ay,
            benchmarks_dir: temp.path(),
            timeout_sec: 2.0,
            domain: "sat",
            quiet: true,
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: Some("main".to_string()),
            sat_ai_class: Some("regular".to_string()),
            sat_variant: Some("default".to_string()),
            environment: None,
            pinned_ay: None,
            artifact_output_dir: Some(artifact_dir.clone()),
            resources: Some(test_resources()),
        })
        .expect("run native");

        let item = results.items.first().expect("item");
        assert_eq!(item.result, "error");
        assert!(item
            .artifacts
            .as_ref()
            .is_some_and(|artifacts| artifacts.proof_exists == Some(false)));
        assert_eq!(
            std::fs::read_dir(&artifact_dir)
                .expect("artifact dir")
                .count(),
            0
        );
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
            with_features: false,
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
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
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
        let all_rows = results
            .reference_comparisons
            .as_deref()
            .expect("all reference rows");
        assert_eq!(all_rows.len(), 2);
        assert_eq!(all_rows[0].reference_solver, "agree-ref");
        assert_eq!(all_rows[0].items[0].agreement, "agree");
        assert_eq!(all_rows[1].reference_solver, "disagree-ref");
        assert_eq!(all_rows[1].items[0].agreement, "disagree");

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
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: Some("laptop".to_string()),
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
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

    #[test]
    fn test_run_native_rejects_unrecognized_run_class() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let err = run_native(&NativeRunArgs {
            ay: Path::new("unused"),
            benchmarks_dir: tmp.path(),
            timeout_sec: 1.0,
            domain: "smt",
            quiet: true,
            with_features: false,
            file_list: Some(vec![tmp.path().join("unused.smt2")]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: Some("desktop".to_string()),
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        })
        .expect_err("invalid run class must fail before execution");
        assert!(err.to_string().contains("replay"));
    }

    #[test]
    fn test_run_native_rejects_solver_memory_override() {
        let tmp = tempfile::tempdir().expect("tempdir");
        for solver_args in [
            vec!["--memory".to_string(), "0".to_string()],
            vec!["--memory=1".to_string()],
        ] {
            let err = run_native(&NativeRunArgs {
                ay: Path::new("unused"),
                benchmarks_dir: tmp.path(),
                timeout_sec: 1.0,
                domain: "smt",
                quiet: true,
                with_features: false,
                file_list: Some(vec![tmp.path().join("unused.smt2")]),
                runs: 1,
                reference_solvers: Vec::new(),
                run_class: None,
                solver_args,
                sat_track: None,
                sat_ai_class: None,
                sat_variant: None,
                environment: None,
                pinned_ay: None,
                artifact_output_dir: None,
                resources: Some(test_resources()),
            })
            .expect_err("a caller must not override the planned --memory value");
            assert!(err.to_string().contains("planned memory envelope"));
        }
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
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: Vec::new(),
            run_class: None,
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        })
        .expect("run native");

        let value = serde_json::to_value(&results).expect("serialize results");
        let map = value.as_object().expect("results object");
        assert_eq!(
            map.keys().collect::<Vec<_>>(),
            vec!["environment", "items", "preprocessing", "settings"],
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
            with_features: false,
            file_list: Some(vec![benchmark]),
            runs: 1,
            reference_solvers: vec![("fake-ref.sh".to_string(), reference)],
            run_class: Some("replay".to_string()),
            solver_args: Vec::new(),
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            environment: None,
            pinned_ay: None,
            artifact_output_dir: None,
            resources: Some(test_resources()),
        })
        .expect("run native");

        let value = serde_json::to_value(&results).expect("serialize results");
        let map = value.as_object().expect("results object");
        let expected_keys = [
            "environment",
            "items",
            "preprocessing",
            "settings",
            "comparison",
            "comparisons",
            "reference_comparisons",
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
