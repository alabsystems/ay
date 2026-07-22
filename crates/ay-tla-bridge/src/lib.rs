// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! ay-tla-bridge: TLA+/TLC integration helpers
//!
//! This crate provides a small wrapper around the TLC model checker so AY can:
//! - Run TLA+ specs from tests or tooling
//! - Parse TLC's textual output into a structured outcome
//!
//! The runner supports two backends:
//! - `tlc` executable on `PATH`
//! - `java -cp tla2tools.jar tlc2.TLC ...` when `TLA2TOOLS_JAR` is provided

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output};

use thiserror::Error;

mod parse;
mod tla2;

// Re-export parse and generic TLA2 trace-validation functions.
#[cfg(test)]
pub(crate) use parse::{extract_trace, suggest_fix};
pub use parse::{extract_violation, parse_tlc_outcome};
pub use tla2::{
    find_tla2_binary, tla2_validate_trace, tla2_validate_trace_with_timeout, Tla2TraceError,
};

#[derive(Debug, Error)]
pub enum TlcError {
    #[error("failed to discover a TLC runner; set `TLC_BIN` or `TLA2TOOLS_JAR`")]
    NotFound,

    #[error("TLC execution failed: {0}")]
    Io(#[from] std::io::Error),

    #[error("TLC output was not valid UTF-8")]
    NonUtf8Output,
}

#[derive(Clone, Debug)]
pub enum TlcBackend {
    /// Run an installed `tlc` executable (or wrapper script).
    Cli { tlc_bin: PathBuf },
    /// Run TLC via `java -cp <jar> tlc2.TLC`.
    JavaJar {
        java_bin: PathBuf,
        tla2tools_jar: PathBuf,
    },
}

impl TlcBackend {
    /// Discover a TLC backend.
    ///
    /// Priority:
    /// 1) `TLC_BIN` env var
    /// 2) `tlc` found on `PATH`
    /// 3) `TLA2TOOLS_JAR` env var (uses `java` on `PATH`)
    pub fn discover() -> Result<Self, TlcError> {
        if let Some(p) = env_path("TLC_BIN") {
            return Ok(Self::Cli { tlc_bin: p });
        }

        if let Ok(p) = which::which("tlc") {
            return Ok(Self::Cli { tlc_bin: p });
        }

        if let Some(jar) = env_path("TLA2TOOLS_JAR") {
            return Ok(Self::JavaJar {
                java_bin: PathBuf::from("java"),
                tla2tools_jar: jar,
            });
        }

        Err(TlcError::NotFound)
    }
}

#[derive(Clone, Debug, Default)]
pub struct TlcArgs {
    pub config: Option<PathBuf>,
    pub cwd: Option<PathBuf>,
    pub workers: Option<u32>,
    pub max_heap_mb: Option<u32>,
    pub extra_args: Vec<OsString>,
}

/// Error code categories matching TLC's internal taxonomy.
///
/// These codes provide machine-readable classification of TLC errors
/// for programmatic handling by verification toolchains.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TlcErrorCode {
    ConfigParse,
    SpecParse,
    TypeError,
    Deadlock,
    InvariantViolation,
    LivenessViolation,
    AssertionFailure,
    ResourceExhausted,
    InternalError,
    Unknown,
}

/// A structured representation of a TLC violation.
///
/// This provides machine-readable error information suitable for
/// AI agents and automated tooling.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlcViolation {
    /// The error code category
    pub code: TlcErrorCode,
    /// Human-readable error message
    pub message: String,
    /// The name of the violated property (if applicable)
    pub property_name: Option<String>,
    /// The counterexample trace (state sequence leading to violation)
    pub trace: Option<Vec<String>>,
    /// Suggested fix or action
    pub suggestion: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TlcOutcome {
    /// Model checking completed successfully with no errors
    NoError,
    /// Deadlock detected (no enabled transitions from some state)
    Deadlock,
    /// Safety property (invariant) violation
    InvariantViolation { name: Option<String> },
    /// Liveness/temporal property violation
    LivenessViolation,
    /// Assertion failure in spec
    AssertionFailure { message: Option<String> },
    /// Type error in spec or config
    TypeError,
    /// Parse error in spec
    ParseError,
    /// Config file error
    ConfigError,
    /// State space exhausted (out of memory, too many states)
    StateSpaceExhausted,
    /// TLC execution failed with non-zero exit
    ExecutionFailed { exit_code: Option<i32> },
    /// Unknown outcome
    Unknown { exit_code: Option<i32> },
}

impl TlcOutcome {
    /// Returns the error code category for this outcome.
    pub fn error_code(&self) -> Option<TlcErrorCode> {
        match self {
            Self::NoError => None,
            Self::Deadlock => Some(TlcErrorCode::Deadlock),
            Self::InvariantViolation { .. } => Some(TlcErrorCode::InvariantViolation),
            Self::LivenessViolation => Some(TlcErrorCode::LivenessViolation),
            Self::AssertionFailure { .. } => Some(TlcErrorCode::AssertionFailure),
            Self::TypeError => Some(TlcErrorCode::TypeError),
            Self::ParseError => Some(TlcErrorCode::SpecParse),
            Self::ConfigError => Some(TlcErrorCode::ConfigParse),
            Self::StateSpaceExhausted => Some(TlcErrorCode::ResourceExhausted),
            Self::ExecutionFailed { .. } => Some(TlcErrorCode::InternalError),
            Self::Unknown { .. } => Some(TlcErrorCode::Unknown),
        }
    }

    /// Returns true if this outcome indicates a successful run.
    pub fn is_success(&self) -> bool {
        matches!(self, Self::NoError)
    }

    /// Returns true if this outcome indicates a property violation.
    pub fn is_violation(&self) -> bool {
        matches!(
            self,
            Self::Deadlock
                | Self::InvariantViolation { .. }
                | Self::LivenessViolation
                | Self::AssertionFailure { .. }
        )
    }

    /// Returns true if this outcome indicates a spec/config error.
    pub fn is_spec_error(&self) -> bool {
        matches!(self, Self::TypeError | Self::ParseError | Self::ConfigError)
    }
}

#[derive(Clone, Debug)]
pub struct TlcRun {
    pub backend: TlcBackend,
    pub args: TlcArgs,
    pub spec: PathBuf,
    pub exit_status: ExitStatus,
    pub stdout: String,
    pub stderr: String,
    pub outcome: TlcOutcome,
}

impl TlcRun {
    /// Returns true if model checking completed successfully.
    pub fn is_success(&self) -> bool {
        self.outcome.is_success()
    }

    /// Returns true if a property violation was detected.
    pub fn is_violation(&self) -> bool {
        self.outcome.is_violation()
    }

    /// Extract a structured violation from this run.
    ///
    /// Returns `None` if the run was successful.
    pub fn violation(&self) -> Option<TlcViolation> {
        extract_violation(&self.stdout, &self.stderr, self.exit_status.code())
    }
}

#[derive(Clone, Debug)]
pub struct TlcRunner {
    backend: TlcBackend,
}

impl TlcRunner {
    pub fn new(backend: TlcBackend) -> Self {
        Self { backend }
    }

    pub fn discover() -> Result<Self, TlcError> {
        Ok(Self::new(TlcBackend::discover()?))
    }

    pub fn backend(&self) -> &TlcBackend {
        &self.backend
    }

    pub fn run(&self, spec: impl AsRef<Path>, args: TlcArgs) -> Result<TlcRun, TlcError> {
        let spec = spec.as_ref().to_path_buf();

        let mut cmd = match &self.backend {
            TlcBackend::Cli { tlc_bin } => {
                let mut cmd = Command::new(tlc_bin);
                // Prefer standard ordering: options first, then the spec module/file.
                if let Some(cfg) = &args.config {
                    cmd.arg("-config").arg(cfg);
                }
                if let Some(workers) = args.workers {
                    cmd.arg("-workers").arg(workers.to_string());
                }
                cmd.arg(&spec);
                cmd
            }
            TlcBackend::JavaJar {
                java_bin,
                tla2tools_jar,
            } => {
                let mut cmd = Command::new(java_bin);
                if let Some(max_heap_mb) = args.max_heap_mb {
                    cmd.arg(format!("-Xmx{max_heap_mb}m"));
                }
                cmd.arg("-cp").arg(tla2tools_jar);
                cmd.arg("tlc2.TLC");
                if let Some(cfg) = &args.config {
                    cmd.arg("-config").arg(cfg);
                }
                if let Some(workers) = args.workers {
                    cmd.arg("-workers").arg(workers.to_string());
                }
                cmd.arg(&spec);
                cmd
            }
        };

        cmd.args(&args.extra_args);
        if let Some(cwd) = &args.cwd {
            cmd.current_dir(cwd);
        }

        let Output {
            status,
            stdout,
            stderr,
        } = cmd.output()?;

        let stdout = String::from_utf8(stdout).map_err(|_| TlcError::NonUtf8Output)?;
        let stderr = String::from_utf8(stderr).map_err(|_| TlcError::NonUtf8Output)?;
        let outcome = parse_tlc_outcome(&stdout, &stderr, status.code());

        Ok(TlcRun {
            backend: self.backend.clone(),
            args,
            spec,
            exit_status: status,
            stdout,
            stderr,
            outcome,
        })
    }
}

// TLC output parsing is in parse.rs.
// TLA2 trace validation is in tla2.rs.

fn env_path(name: &str) -> Option<PathBuf> {
    let v = std::env::var_os(name)?;
    if v.is_empty() {
        return None;
    }
    Some(PathBuf::from(v))
}

// Minimal `which` implementation avoids pulling in extra dependencies.
mod which {
    use std::path::{Path, PathBuf};

    pub(crate) fn which(bin: &str) -> Result<PathBuf, ()> {
        let path_var = std::env::var_os("PATH").ok_or(())?;
        for dir in std::env::split_paths(&path_var) {
            let p = dir.join(bin);
            if is_executable(&p) {
                return Ok(p);
            }
        }
        Err(())
    }

    fn is_executable(p: &Path) -> bool {
        if !p.is_file() {
            return false;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(meta) = p.metadata() {
                return (meta.permissions().mode() & 0o111) != 0;
            }
        }
        #[cfg(not(unix))]
        {
            // On Windows we rely on PATH search semantics; existence is good enough.
            return p.is_file();
        }
        false
    }
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
