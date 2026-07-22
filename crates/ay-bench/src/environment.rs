// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture machine and build environment for reproducible benchmarking.
//!
//! Every results.json includes an `environment` block so that scores can be
//! compared across machines with full context on hardware and load.

use serde::Serialize;
use sha2::{Digest as _, Sha256};
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::error::{BenchError, Result, WithContext as _};

/// Parent-side cap for solver snapshots and provenance revalidation. Solver
/// executables are metadata, not corpus payloads; refusing a pathological
/// stream prevents a procfs/FUSE source from filling the temp volume.
const MAX_SOLVER_BINARY_BYTES: u64 = 1024 * 1024 * 1024;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct SolverProvenance {
    pub path: String,
    pub sha256: String,
    pub size_bytes: u64,
    pub version_output: String,
    pub build_version: String,
    pub build_commit: String,
    pub build_datetime_utc: String,
    pub build_stamp: String,
}

pub(crate) struct PinnedSolver {
    source_path: PathBuf,
    execution_path: PathBuf,
    _directory: tempfile::TempDir,
    provenance: SolverProvenance,
}

impl PinnedSolver {
    pub(crate) fn capture(
        path: &Path,
        resources: &crate::resource::PlannedResources,
        label: &str,
    ) -> Result<Self> {
        use std::io::Write as _;

        let source_path = std::fs::canonicalize(path)
            .with_bench_context(|| format!("canonicalizing solver binary {}", path.display()))?;
        let mut source_options = std::fs::OpenOptions::new();
        source_options.read(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            source_options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
        }
        let mut source = source_options
            .open(&source_path)
            .with_bench_context(|| format!("opening solver binary {}", source_path.display()))?;
        let before = source.metadata()?;
        if !before.file_type().is_file() {
            return Err(BenchError::msg(format!(
                "solver path is not a regular file: {}",
                source_path.display()
            )));
        }
        if before.len() > MAX_SOLVER_BINARY_BYTES {
            return Err(BenchError::msg(format!(
                "solver binary exceeds the fixed {MAX_SOLVER_BINARY_BYTES}-byte snapshot cap: {}",
                source_path.display()
            )));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            if before.permissions().mode() & 0o111 == 0 {
                return Err(BenchError::msg(format!(
                    "solver path is not executable: {}",
                    source_path.display()
                )));
            }
        }

        let directory = tempfile::Builder::new()
            .prefix("ay-solver-pin-")
            .tempdir()?;
        let executable_name = source_path
            .file_name()
            .ok_or_else(|| BenchError::msg("solver binary path has no file name"))?;
        let execution_path = directory.path().join(executable_name);
        let mut destination_options = std::fs::OpenOptions::new();
        destination_options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            destination_options.mode(0o700);
        }
        let mut destination = destination_options.open(&execution_path)?;
        let mut hasher = Sha256::new();
        let mut size_bytes = 0_u64;
        let mut buffer = [0_u8; 64 * 1024];
        loop {
            let read = source.read(&mut buffer).with_bench_context(|| {
                format!("copying pinned solver binary {}", source_path.display())
            })?;
            if read == 0 {
                break;
            }
            size_bytes = size_bytes
                .checked_add(read as u64)
                .ok_or_else(|| BenchError::msg("solver binary size overflow"))?;
            if size_bytes > MAX_SOLVER_BINARY_BYTES {
                return Err(BenchError::msg(format!(
                    "solver binary exceeds the fixed {MAX_SOLVER_BINARY_BYTES}-byte snapshot cap: {}",
                    source_path.display()
                )));
            }
            hasher.update(&buffer[..read]);
            destination.write_all(&buffer[..read])?;
        }
        destination.sync_all()?;
        // Linux rejects executing a file while any process retains it open for
        // writing (ETXTBSY). Close the completed snapshot before probing it.
        drop(destination);
        let after = source.metadata()?;
        let path_after = std::fs::symlink_metadata(&source_path)?;
        if !same_file_snapshot(&before, &after)
            || !same_file_snapshot(&after, &path_after)
            || after.len() != size_bytes
        {
            return Err(BenchError::msg(format!(
                "solver binary changed while creating its pinned snapshot: {}",
                source_path.display()
            )));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            std::fs::set_permissions(&execution_path, std::fs::Permissions::from_mode(0o500))?;
        }
        let output = resources.capture_external_output(
            &execution_path,
            ["--version"],
            Duration::from_secs(10),
            label,
        )?;
        if !output.status.success() {
            return Err(BenchError::msg(format!(
                "{label}: pinned solver version probe exited {}: {}",
                output.status,
                sanitize_metadata_text(output.stderr.trim())
            )));
        }
        let text = if output.stdout.trim().is_empty() {
            output.stderr
        } else {
            output.stdout
        };
        let version_output = sanitize_metadata_text(text.trim());
        if version_output.is_empty() {
            return Err(BenchError::msg(format!(
                "{label}: pinned solver version probe produced no output"
            )));
        }
        let provenance = SolverProvenance::from_version_output(
            &source_path,
            format!("sha256:{:x}", hasher.finalize()),
            size_bytes,
            version_output,
        );
        Ok(Self {
            source_path,
            execution_path,
            _directory: directory,
            provenance,
        })
    }

    pub(crate) fn execution_path(&self) -> &Path {
        &self.execution_path
    }

    pub(crate) fn provenance(&self) -> &SolverProvenance {
        &self.provenance
    }

    pub(crate) fn verify_source(&self) -> Result<()> {
        let _ = &self.source_path;
        self.provenance.verify_current()
    }
}

impl SolverProvenance {
    #[cfg(test)]
    pub(crate) fn capture(path: &Path) -> Self {
        let path_string = path.display().to_string();
        let version_output = crate::resource::capture_local_output(
            path,
            ["--version"],
            Duration::from_secs(10),
            "test solver version probe",
        )
        .ok()
        .and_then(|output| {
            if !output.status.success() {
                return None;
            }
            let text = if output.stdout.is_empty() {
                output.stderr
            } else {
                output.stdout
            };
            Some(text)
        })
        .map(|s| sanitize_metadata_text(s.trim()))
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| format!("unknown ({path_string})"));

        let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
        let (sha256, size_bytes) =
            Self::file_identity(&canonical).unwrap_or_else(|_| ("unknown".to_string(), 0));
        Self::from_version_output(&canonical, sha256, size_bytes, version_output)
    }

    fn from_version_output(
        path: &Path,
        sha256: String,
        size_bytes: u64,
        version_output: String,
    ) -> Self {
        let primary_line = version_output
            .lines()
            .map(str::trim)
            .find(|line| !line.is_empty())
            .unwrap_or("unknown")
            .to_string();
        let primary_fallback = if primary_line.starts_with("unknown (") {
            "unknown".to_string()
        } else {
            primary_line.clone()
        };

        let build_version = Self::field(&version_output, "build.version")
            .unwrap_or_else(|| primary_fallback.clone());
        let build_commit =
            Self::field(&version_output, "build.commit").unwrap_or_else(|| "unknown".to_string());
        let build_datetime_utc = Self::field(&version_output, "build.datetime_utc")
            .unwrap_or_else(|| "unknown".to_string());
        let build_stamp = Self::field(&version_output, "build.stamp").unwrap_or(primary_fallback);

        Self {
            path: path.display().to_string(),
            sha256,
            size_bytes,
            version_output,
            build_version,
            build_commit,
            build_datetime_utc,
            build_stamp,
        }
    }

    pub(crate) fn summary(&self) -> String {
        format!(
            "{} ({}; {}; {} bytes)",
            self.build_stamp, self.path, self.sha256, self.size_bytes
        )
    }

    pub(crate) fn verify_current(&self) -> Result<()> {
        let canonical = std::fs::canonicalize(&self.path)
            .with_bench_context(|| format!("re-canonicalizing solver binary {}", self.path))?;
        if canonical.display().to_string() != self.path {
            return Err(BenchError::msg(format!(
                "solver binary path changed during benchmark campaign: {} -> {}",
                self.path,
                canonical.display()
            )));
        }
        let (sha256, size_bytes) = Self::file_identity(&canonical)?;
        if sha256 != self.sha256 || size_bytes != self.size_bytes {
            return Err(BenchError::msg(format!(
                "solver binary changed during benchmark campaign: {} (expected {} / {} bytes, found {} / {} bytes)",
                self.path, self.sha256, self.size_bytes, sha256, size_bytes
            )));
        }
        Ok(())
    }

    fn file_identity(path: &Path) -> Result<(String, u64)> {
        let mut options = std::fs::OpenOptions::new();
        options.read(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
        }
        let mut file = options
            .open(path)
            .with_bench_context(|| format!("opening solver binary {}", path.display()))?;
        let metadata = file
            .metadata()
            .with_bench_context(|| format!("stat open solver binary {}", path.display()))?;
        if !metadata.file_type().is_file() {
            return Err(BenchError::msg(format!(
                "solver path is not a regular file: {}",
                path.display()
            )));
        }
        if metadata.len() > MAX_SOLVER_BINARY_BYTES {
            return Err(BenchError::msg(format!(
                "solver binary exceeds the fixed {MAX_SOLVER_BINARY_BYTES}-byte provenance cap: {}",
                path.display()
            )));
        }
        let mut hasher = Sha256::new();
        let mut size_bytes = 0_u64;
        let mut buffer = [0_u8; 64 * 1024];
        loop {
            let read = file
                .read(&mut buffer)
                .with_bench_context(|| format!("hashing solver binary {}", path.display()))?;
            if read == 0 {
                break;
            }
            size_bytes = size_bytes
                .checked_add(read as u64)
                .ok_or_else(|| BenchError::msg("solver binary size overflow"))?;
            if size_bytes > MAX_SOLVER_BINARY_BYTES {
                return Err(BenchError::msg(format!(
                    "solver binary exceeds the fixed {MAX_SOLVER_BINARY_BYTES}-byte provenance cap: {}",
                    path.display()
                )));
            }
            hasher.update(&buffer[..read]);
        }
        let metadata_after = file
            .metadata()
            .with_bench_context(|| format!("restatting solver binary {}", path.display()))?;
        if !same_file_snapshot(&metadata, &metadata_after) {
            return Err(BenchError::msg(format!(
                "solver binary changed while hashing: {}",
                path.display()
            )));
        }
        Ok((format!("sha256:{:x}", hasher.finalize()), size_bytes))
    }

    fn field(version_output: &str, key: &str) -> Option<String> {
        version_output.lines().find_map(|line| {
            let (field, value) = line.split_once('=')?;
            if field.trim() == key {
                Some(value.trim().to_string())
            } else {
                None
            }
        })
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct Environment {
    pub timestamp: String,
    pub git_commit: String,
    pub git_dirty: Option<bool>,
    pub comparable_git_state: bool,
    pub ay_path: String,
    pub ay_sha256: String,
    pub ay_size_bytes: u64,
    pub ay_version: String,
    pub ay_build_version: String,
    pub ay_build_commit: String,
    pub ay_build_datetime_utc: String,
    pub ay_build_stamp: String,
    pub hostname: String,
    pub os: &'static str,
    pub arch: &'static str,
    pub cpu_model: String,
    pub cpu_count: u32,
    pub memory_bytes: u64,
    pub load_avg: [f64; 3],
}

impl Environment {
    /// Capture current environment. Call once at the start of a benchmark run.
    #[cfg(test)]
    pub(crate) fn capture(ay_path: &Path) -> Self {
        let ay = SolverProvenance::capture(ay_path);
        Self::capture_with_solver(ay)
    }

    pub(crate) fn capture_with_solver(ay: SolverProvenance) -> Self {
        let repo_root = crate::runner::repo_root_public();
        Self::capture_with_solver_in_repo(ay, &repo_root)
    }

    pub(crate) fn capture_with_solver_in_repo(ay: SolverProvenance, repo_root: &Path) -> Self {
        let (git_commit, git_dirty) = Self::git_state(repo_root);
        Self {
            timestamp: Self::now_utc(),
            comparable_git_state: valid_full_commit(&git_commit) && git_dirty == Some(false),
            git_commit,
            git_dirty,
            ay_path: ay.path.clone(),
            ay_sha256: ay.sha256,
            ay_size_bytes: ay.size_bytes,
            ay_version: ay.version_output.clone(),
            ay_build_version: ay.build_version,
            ay_build_commit: ay.build_commit,
            ay_build_datetime_utc: ay.build_datetime_utc,
            ay_build_stamp: ay.build_stamp,
            hostname: Self::hostname(),
            os: std::env::consts::OS,
            arch: std::env::consts::ARCH,
            cpu_model: Self::cpu_model(),
            cpu_count: Self::cpu_count(),
            memory_bytes: Self::memory_bytes(),
            load_avg: Self::load_avg(),
        }
    }

    fn now_utc() -> String {
        cmd_stdout("date", &["-u", "+%Y-%m-%dT%H:%M:%SZ"]).unwrap_or_else(|| "unknown".to_string())
    }

    pub(crate) fn git_state(repo_root: &Path) -> (String, Option<bool>) {
        let repo = repo_root.to_string_lossy();
        let commit = cmd_stdout(
            "git",
            &["-C", repo.as_ref(), "rev-parse", "--verify", "HEAD"],
        )
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "unknown".to_string());
        let dirty = cmd_stdout(
            "git",
            &[
                "-C",
                repo.as_ref(),
                "status",
                "--porcelain=v1",
                "--untracked-files=normal",
            ],
        )
        .map(|s| !s.is_empty());
        (commit, dirty)
    }

    fn hostname() -> String {
        cmd_stdout("hostname", &[]).unwrap_or_else(|| "unknown".to_string())
    }

    #[cfg(target_os = "macos")]
    fn cpu_model() -> String {
        cmd_stdout("sysctl", &["-n", "machdep.cpu.brand_string"])
            .unwrap_or_else(|| "unknown".to_string())
    }

    #[cfg(not(target_os = "macos"))]
    fn cpu_model() -> String {
        std::fs::read_to_string("/proc/cpuinfo")
            .ok()
            .map(|text| linux_cpu_model(&text, std::env::consts::ARCH))
            .unwrap_or_else(|| std::env::consts::ARCH.to_string())
    }

    #[cfg(target_os = "macos")]
    fn cpu_count() -> u32 {
        cmd_stdout("sysctl", &["-n", "hw.logicalcpu"])
            .and_then(|s| s.parse().ok())
            .unwrap_or(0)
    }

    #[cfg(not(target_os = "macos"))]
    fn cpu_count() -> u32 {
        std::fs::read_to_string("/proc/cpuinfo")
            .ok()
            .map(|text| text.lines().filter(|l| l.starts_with("processor")).count() as u32)
            .unwrap_or(0)
    }

    #[cfg(target_os = "macos")]
    fn memory_bytes() -> u64 {
        cmd_stdout("sysctl", &["-n", "hw.memsize"])
            .and_then(|s| s.parse().ok())
            .unwrap_or(0)
    }

    #[cfg(not(target_os = "macos"))]
    fn memory_bytes() -> u64 {
        // Linux: parse MemTotal from /proc/meminfo (in kB)
        std::fs::read_to_string("/proc/meminfo")
            .ok()
            .and_then(|text| {
                text.lines()
                    .find(|l| l.starts_with("MemTotal:"))
                    .and_then(|l| {
                        l.split_whitespace()
                            .nth(1)
                            .and_then(|s| s.parse::<u64>().ok())
                    })
            })
            .map(|kb| kb * 1024)
            .unwrap_or(0)
    }

    fn load_avg() -> [f64; 3] {
        // Parse from `uptime` output — works on macOS and Linux
        cmd_stdout("uptime", &[])
            .and_then(|s| {
                // "... load averages: 2.50 3.10 2.80" (macOS)
                // "... load average: 2.50, 3.10, 2.80" (Linux)
                let after = s.split("load average").last()?;
                let nums: Vec<f64> = after
                    .split(|c: char| !c.is_ascii_digit() && c != '.')
                    .filter_map(|tok| tok.parse().ok())
                    .collect();
                if nums.len() >= 3 {
                    Some([nums[0], nums[1], nums[2]])
                } else {
                    None
                }
            })
            .unwrap_or([0.0; 3])
    }
}

/// Extract a deterministic Linux CPU identity without inventing a marketing
/// name. x86 usually supplies `model name`; ARM commonly exposes only numeric
/// implementer/part pairs, possibly with multiple distinct core types.
fn linux_cpu_model(cpuinfo: &str, arch: &str) -> String {
    if let Some(model) = cpuinfo.lines().find_map(|line| {
        let (key, value) = line.split_once(':')?;
        key.trim()
            .eq_ignore_ascii_case("model name")
            .then(|| value.trim())
            .filter(|value| !value.is_empty())
            .map(str::to_string)
    }) {
        return model;
    }

    let mut identities = std::collections::BTreeSet::new();
    for record in cpuinfo.split("\n\n") {
        let mut implementer = None;
        let mut part = None;
        for line in record.lines() {
            let Some((key, value)) = line.split_once(':') else {
                continue;
            };
            match key.trim() {
                "CPU implementer" => implementer = Some(value.trim()),
                "CPU part" => part = Some(value.trim()),
                _ => {}
            }
        }
        if let (Some(implementer), Some(part)) = (implementer, part) {
            if !implementer.is_empty() && !part.is_empty() {
                identities.insert(format!("implementer {implementer} part {part}"));
            }
        }
    }

    if identities.is_empty() {
        arch.to_string()
    } else {
        format!(
            "{arch} [{}]",
            identities.into_iter().collect::<Vec<_>>().join(", ")
        )
    }
}

fn sanitize_metadata_text(value: &str) -> String {
    value
        .chars()
        .filter(|character| !character.is_control() || matches!(character, '\n' | '\r' | '\t'))
        .collect()
}

pub(crate) fn valid_full_commit(value: &str) -> bool {
    matches!(value.len(), 40 | 64) && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn same_file_snapshot(before: &std::fs::Metadata, after: &std::fs::Metadata) -> bool {
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

/// Hardware model identifier (e.g. "MacBookPro18,3" on macOS, the DMI
/// product name on Linux), "unknown" when unavailable. Recorded in the
/// host fingerprint beside a stamped run class.
#[cfg(target_os = "macos")]
pub(crate) fn hw_model() -> String {
    cmd_stdout("sysctl", &["-n", "hw.model"])
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Hardware model identifier (e.g. "MacBookPro18,3" on macOS, the DMI
/// product name on Linux), "unknown" when unavailable. Recorded in the
/// host fingerprint beside a stamped run class.
#[cfg(not(target_os = "macos"))]
pub(crate) fn hw_model() -> String {
    std::fs::read_to_string("/sys/devices/virtual/dmi/id/product_name")
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_string())
}

fn cmd_stdout(program: &str, args: &[&str]) -> Option<String> {
    let output =
        crate::resource::capture_local_output(program, args, Duration::from_secs(10), program)
            .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(output.stdout.trim().to_string())
}

impl std::fmt::Display for Environment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mem_gb = self.memory_bytes as f64 / (1024.0 * 1024.0 * 1024.0);
        write!(
            f,
            "{} | {} {} | {} ({} cores, {:.0} GB) | load {:.1}/{:.1}/{:.1} | ay {} | {}{}",
            self.timestamp,
            self.os,
            self.arch,
            self.cpu_model,
            self.cpu_count,
            mem_gb,
            self.load_avg[0],
            self.load_avg[1],
            self.load_avg[2],
            format_args!("{} ({})", self.ay_build_stamp, self.ay_path),
            self.git_commit,
            match self.git_dirty {
                Some(true) => " (dirty)",
                Some(false) => "",
                None => " (git status unknown)",
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[cfg(unix)]
    fn write_solver_script(dir: &tempfile::TempDir, name: &str, version_output: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.path().join(name);
        let body = format!(
            "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then\ncat <<'EOF'\n{version_output}\nEOF\nexit 0\nfi\nprintf '%s\\n' sat\n"
        );
        std::fs::write(&path, body).expect("write solver script");
        let mut perms = std::fs::metadata(&path).expect("metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("chmod");
        path
    }

    #[test]
    fn test_capture_does_not_panic() {
        let env = Environment::capture(&PathBuf::from("/nonexistent/ay"));
        assert!(!env.timestamp.is_empty());
        assert!(!env.os.is_empty());
        assert!(!env.arch.is_empty());
        assert!(!env.ay_path.is_empty());
        assert!(!env.ay_build_stamp.is_empty());
    }

    #[test]
    fn test_display() {
        let env = Environment::capture(&PathBuf::from("/nonexistent/ay"));
        let s = format!("{env}");
        assert!(s.contains(env.os));
        assert!(s.contains(&env.ay_path));
        assert!(s.contains(&env.ay_build_stamp));
    }

    #[test]
    fn linux_cpu_model_prefers_marketing_name() {
        assert_eq!(
            linux_cpu_model("processor : 0\nmodel name : Example CPU 123\n", "x86_64"),
            "Example CPU 123"
        );
    }

    #[test]
    fn linux_cpu_model_preserves_sorted_distinct_arm_parts() {
        let cpuinfo = "\
processor : 0\n\
CPU implementer : 0x41\n\
CPU part : 0xd87\n\
\n\
processor : 1\n\
CPU implementer : 0x41\n\
CPU part : 0xd87\n\
\n\
processor : 2\n\
CPU implementer : 0x41\n\
CPU part : 0xd4f\n";
        assert_eq!(
            linux_cpu_model(cpuinfo, "aarch64"),
            "aarch64 [implementer 0x41 part 0xd4f, implementer 0x41 part 0xd87]"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_capture_parses_structured_solver_provenance() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let version_output = "\
0.9.0+build.42.abc123@2026-04-21T12:34:56Z
build.version=0.9.0
build.commit=abc123
build.datetime_utc=2026-04-21T12:34:56Z
build.stamp=0.9.0+build.42.abc123@2026-04-21T12:34:56Z";
        let solver = write_solver_script(&tmp, "fake-ay.sh", version_output);

        let env = Environment::capture(&solver);

        assert_eq!(env.ay_path, solver.display().to_string());
        assert_eq!(env.ay_version, version_output);
        assert_eq!(env.ay_build_version, "0.9.0");
        assert_eq!(env.ay_build_commit, "abc123");
        assert_eq!(env.ay_build_datetime_utc, "2026-04-21T12:34:56Z");
        assert_eq!(
            env.ay_build_stamp,
            "0.9.0+build.42.abc123@2026-04-21T12:34:56Z"
        );
    }
}
