// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture machine and build environment for reproducible benchmarking.
//!
//! Every results.json includes an `environment` block so that scores can be
//! compared across machines with full context on hardware and load.

use serde::Serialize;
use std::path::Path;
use std::process::Command;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct SolverProvenance {
    pub path: String,
    pub version_output: String,
    pub build_version: String,
    pub build_commit: String,
    pub build_datetime_utc: String,
    pub build_stamp: String,
}

impl SolverProvenance {
    pub(crate) fn capture(path: &Path) -> Self {
        let path_string = path.display().to_string();
        let version_output = Command::new(path)
            .arg("--version")
            .output()
            .ok()
            .and_then(|output| {
                let bytes = if output.stdout.is_empty() {
                    output.stderr
                } else {
                    output.stdout
                };
                String::from_utf8(bytes).ok()
            })
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| format!("unknown ({path_string})"));

        Self::from_version_output(path, version_output)
    }

    fn from_version_output(path: &Path, version_output: String) -> Self {
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
            version_output,
            build_version,
            build_commit,
            build_datetime_utc,
            build_stamp,
        }
    }

    pub(crate) fn summary(&self) -> String {
        format!("{} ({})", self.build_stamp, self.path)
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
    pub git_dirty: bool,
    pub ay_path: String,
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
    pub(crate) fn capture(ay_path: &Path) -> Self {
        let ay = SolverProvenance::capture(ay_path);
        Self {
            timestamp: Self::now_utc(),
            git_commit: Self::git_commit(),
            git_dirty: Self::git_dirty(),
            ay_path: ay.path.clone(),
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

    fn git_commit() -> String {
        cmd_stdout("git", &["rev-parse", "--short", "HEAD"])
            .unwrap_or_else(|| "unknown".to_string())
    }

    fn git_dirty() -> bool {
        cmd_stdout("git", &["status", "--porcelain"])
            .map(|s| !s.is_empty())
            .unwrap_or(false)
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
        // Linux: parse /proc/cpuinfo
        std::fs::read_to_string("/proc/cpuinfo")
            .ok()
            .and_then(|text| {
                text.lines()
                    .find(|l| l.starts_with("model name"))
                    .and_then(|l| l.split(':').nth(1))
                    .map(|s| s.trim().to_string())
            })
            .unwrap_or_else(|| "unknown".to_string())
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
    Command::new(program)
        .args(args)
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
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
            if self.git_dirty { " (dirty)" } else { "" },
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
