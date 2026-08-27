// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lean kernel verification glue for `--lean-verify`.
//!
//! The emitted theorem imports `AySoundness.Lrat`; running an arbitrary `lean`
//! process from the caller's working directory would not resolve that module
//! and would leave the checker version ambiguous. This module materializes the
//! exact soundness source and toolchain metadata embedded in the `ay` binary,
//! builds that private project, and checks the authenticated proof snapshot in
//! its environment.

mod project;

use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use project::SoundnessProject;

/// Outcome of invoking the Lean kernel on an emitted `.lean4` proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum LeanVerificationOutcome {
    /// Lean accepted the proof (exit 0, no kernel errors).
    Accepted,
    /// Lean rejected the proof. Carries combined diagnostics and exit code.
    Rejected { diagnostic: String, exit_code: i32 },
    /// The pinned project or Lean executable was unavailable.
    Unavailable { reason: String },
}

/// Verify a proof against the binary-embedded `AySoundness.Lrat` project.
///
/// The `--lean-verify` CLI flag constructs one of these per UNSAT result,
/// invokes [`LeanVerifier::verify_descriptor`] on an authenticated proof
/// snapshot, and routes the outcome to the exit-code contract documented in
/// `crates/ay/README.md`.
#[derive(Debug, Clone)]
pub(crate) struct LeanVerifier {
    lean_path: Option<PathBuf>,
    timeout: Option<Duration>,
}

impl LeanVerifier {
    /// Use the pinned project's `lake env lean` with a 300s timeout.
    pub(crate) fn new() -> Self {
        Self {
            lean_path: None,
            timeout: Some(Duration::from_mins(5)),
        }
    }

    /// Use a specific Lean binary after building the pinned checker module.
    ///
    /// The override must be compatible with the repository's pinned Lean
    /// toolchain; otherwise the explicit verification request fails closed.
    pub(crate) fn with_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.lean_path = Some(path.into());
        self
    }

    fn prepare_soundness_project(&self) -> Result<SoundnessProject, LeanVerificationOutcome> {
        let project =
            SoundnessProject::create().map_err(|error| LeanVerificationOutcome::Unavailable {
                reason: format!("failed to materialize embedded AySoundness project: {error}"),
            })?;
        match self.run_command(project.build_command()) {
            LeanVerificationOutcome::Accepted => Ok(project),
            LeanVerificationOutcome::Rejected {
                diagnostic,
                exit_code,
            } => {
                Err(LeanVerificationOutcome::Unavailable {
                    reason: format!(
                        "failed to build embedded AySoundness.Lrat with the pinned toolchain (exit {exit_code}): {}",
                        diagnostic_summary(&diagnostic)
                    ),
                })
            }
            LeanVerificationOutcome::Unavailable { reason } => {
                Err(LeanVerificationOutcome::Unavailable {
                    reason: format!("could not prepare embedded AySoundness.Lrat: {reason}"),
                })
            }
        }
    }

    fn proof_command(&self, project: &SoundnessProject) -> Command {
        let Some(path) = &self.lean_path else {
            return project.pinned_lean_command();
        };
        let mut command = Command::new(path);
        command
            .current_dir(project.root())
            .env("LEAN_PATH", project.module_path());
        command
    }

    /// Invoke Lean on the exact inode named by `proof_file`, not on a mutable
    /// public pathname. The cloned descriptor is inherited across `exec`, and
    /// Lean receives the child-local descriptor path.
    #[cfg(target_os = "linux")]
    pub(crate) fn verify_descriptor(&self, proof_file: &std::fs::File) -> LeanVerificationOutcome {
        let project = match self.prepare_soundness_project() {
            Ok(project) => project,
            Err(outcome) => return outcome,
        };
        let inherited = match proof_file.try_clone() {
            Ok(file) => file,
            Err(error) => {
                return LeanVerificationOutcome::Unavailable {
                    reason: format!("failed to clone authenticated Lean snapshot: {error}"),
                };
            }
        };
        let descriptor_path = PathBuf::from("/proc/self/fd/0");
        let mut cmd = self.proof_command(&project);
        cmd.arg(descriptor_path)
            .stdin(std::process::Stdio::from(inherited));
        normalize_project_failure(self.run_command(cmd))
    }

    fn spawn_command(
        &self,
        mut cmd: Command,
    ) -> Result<std::process::Child, LeanVerificationOutcome> {
        let program = cmd.get_program().to_string_lossy().into_owned();
        // Lean may report elaboration errors on stdout or stderr. Capture both
        // so an exit-zero diagnostic can never be mistaken for acceptance.
        cmd.stdout(std::process::Stdio::piped());
        cmd.stderr(std::process::Stdio::piped());

        match cmd.spawn() {
            Ok(child) => Ok(child),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                Err(LeanVerificationOutcome::Unavailable {
                    reason: format!("verification executable not found at '{program}'"),
                })
            }
            Err(err) => Err(LeanVerificationOutcome::Unavailable {
                reason: format!("failed to spawn '{program}': {err}"),
            }),
        }
    }

    fn run_command(&self, cmd: Command) -> LeanVerificationOutcome {
        match self.spawn_command(cmd) {
            Ok(child) => self.wait_child(child),
            Err(outcome) => outcome,
        }
    }

    fn wait_child(&self, child: std::process::Child) -> LeanVerificationOutcome {
        let Some(timeout) = self.timeout else {
            return run_until_exit(child);
        };
        run_with_timeout(child, timeout)
    }
}

fn run_until_exit(child: std::process::Child) -> LeanVerificationOutcome {
    let output = match child.wait_with_output() {
        Ok(o) => o,
        Err(err) => {
            return LeanVerificationOutcome::Unavailable {
                reason: format!("failed to wait on lean: {err}"),
            };
        }
    };
    classify_output(
        output.status.code().unwrap_or(-1),
        combine_diagnostics(&output.stdout, &output.stderr),
    )
}

fn read_pipe<R: std::io::Read>(stream: Option<R>) -> std::io::Result<Vec<u8>> {
    let Some(mut stream) = stream else {
        return Ok(Vec::new());
    };
    let mut bytes = Vec::new();
    stream.read_to_end(&mut bytes)?;
    Ok(bytes)
}

struct DiagnosticReaders {
    stdout: std::thread::JoinHandle<std::io::Result<Vec<u8>>>,
    stderr: std::thread::JoinHandle<std::io::Result<Vec<u8>>>,
}

impl DiagnosticReaders {
    fn start(child: &mut std::process::Child) -> Self {
        Self {
            stdout: spawn_pipe_reader(child.stdout.take()),
            stderr: spawn_pipe_reader(child.stderr.take()),
        }
    }

    fn finish(self) -> Result<(Vec<u8>, Vec<u8>), String> {
        let stdout = join_pipe_reader(self.stdout, "stdout")?;
        let stderr = join_pipe_reader(self.stderr, "stderr")?;
        Ok((stdout, stderr))
    }
}

fn spawn_pipe_reader<R>(stream: Option<R>) -> std::thread::JoinHandle<std::io::Result<Vec<u8>>>
where
    R: std::io::Read + Send + 'static,
{
    std::thread::spawn(move || read_pipe(stream))
}

fn join_pipe_reader(
    reader: std::thread::JoinHandle<std::io::Result<Vec<u8>>>,
    name: &str,
) -> Result<Vec<u8>, String> {
    reader
        .join()
        .map_err(|_| format!("Lean {name} reader panicked"))?
        .map_err(|error| format!("failed to read Lean {name}: {error}"))
}

fn combine_diagnostics(stdout: &[u8], stderr: &[u8]) -> String {
    match (stdout.is_empty(), stderr.is_empty()) {
        (true, _) => String::from_utf8_lossy(stderr).into_owned(),
        (_, true) => String::from_utf8_lossy(stdout).into_owned(),
        (false, false) => format!(
            "{}\n{}",
            String::from_utf8_lossy(stdout),
            String::from_utf8_lossy(stderr)
        ),
    }
}

fn run_with_timeout(mut child: std::process::Child, timeout: Duration) -> LeanVerificationOutcome {
    // We intentionally do not pull in `wait_timeout` here to avoid expanding
    // the ay dependency surface for a Phase 1 thin wrapper. Simple polling is
    // adequate for the typical lean proof check (seconds to minutes) and the
    // default 300s timeout.
    let start = std::time::Instant::now();
    let poll = Duration::from_millis(50);
    // Drain both pipes from launch onward. Waiting until the child exits can
    // deadlock once either OS pipe buffer fills, preventing the exit we poll.
    let readers = DiagnosticReaders::start(&mut child);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let (stdout, stderr) = match readers.finish() {
                    Ok(output) => output,
                    Err(reason) => {
                        return LeanVerificationOutcome::Unavailable { reason };
                    }
                };
                return classify_output(
                    status.code().unwrap_or(-1),
                    combine_diagnostics(&stdout, &stderr),
                );
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = readers.finish();
                    return LeanVerificationOutcome::Unavailable {
                        reason: format!(
                            "lean verification exceeded timeout of {}s",
                            timeout.as_secs()
                        ),
                    };
                }
                std::thread::sleep(poll);
            }
            Err(err) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = readers.finish();
                return LeanVerificationOutcome::Unavailable {
                    reason: format!("failed polling lean child: {err}"),
                };
            }
        }
    }
}

fn classify_output(exit_code: i32, diagnostic: String) -> LeanVerificationOutcome {
    if exit_code == 0 {
        if diagnostic_indicates_rejection(&diagnostic) {
            return LeanVerificationOutcome::Rejected {
                diagnostic,
                exit_code,
            };
        }
        LeanVerificationOutcome::Accepted
    } else {
        LeanVerificationOutcome::Rejected {
            diagnostic,
            exit_code,
        }
    }
}

fn diagnostic_indicates_rejection(diagnostic: &str) -> bool {
    diagnostic.contains("error:")
        || diagnostic.contains("proof failed")
        || diagnostic.contains("declaration uses 'sorry'")
        || diagnostic.contains("declaration uses `sorry`")
}

fn normalize_project_failure(outcome: LeanVerificationOutcome) -> LeanVerificationOutcome {
    let LeanVerificationOutcome::Rejected {
        diagnostic,
        exit_code,
    } = outcome
    else {
        return outcome;
    };
    if !(0..128).contains(&exit_code) || resource_exhaustion_diagnostic(&diagnostic) {
        return LeanVerificationOutcome::Unavailable {
            reason: format!(
                "Lean verification exhausted resources or terminated abnormally (exit {exit_code}): {}",
                diagnostic_summary(&diagnostic)
            ),
        };
    }
    if soundness_project_diagnostic(&diagnostic) {
        return LeanVerificationOutcome::Unavailable {
            reason: format!(
                "embedded AySoundness.Lrat could not be loaded by the selected Lean toolchain (exit {exit_code}): {}",
                diagnostic_summary(&diagnostic)
            ),
        };
    }
    LeanVerificationOutcome::Rejected {
        diagnostic,
        exit_code,
    }
}

fn resource_exhaustion_diagnostic(diagnostic: &str) -> bool {
    let diagnostic = diagnostic.to_ascii_lowercase();
    [
        "maximum recursion depth",
        "recursion depth limit",
        "maximum heartbeats",
        "heartbeat limit",
        "deterministic timeout",
        "timeout at",
        "resource exhausted",
        "out of memory",
        "memory exhausted",
        "memory allocation",
        "cannot allocate memory",
        "failed to allocate",
    ]
    .iter()
    .any(|marker| diagnostic.contains(marker))
}

fn soundness_project_diagnostic(diagnostic: &str) -> bool {
    let names_checker =
        diagnostic.contains("AySoundness.Lrat") || diagnostic.contains("AySoundness/Lrat.olean");
    let describes_load_failure = diagnostic.contains("unknown module")
        || diagnostic.contains("object file")
        || diagnostic.contains("cannot load")
        || diagnostic.contains("does not exist")
        || diagnostic.contains("different version");
    names_checker && describes_load_failure
}

fn diagnostic_summary(diagnostic: &str) -> String {
    let compact = diagnostic.split_whitespace().collect::<Vec<_>>().join(" ");
    if compact.is_empty() {
        return "no diagnostic output".to_string();
    }
    compact.chars().take(500).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn test_spawn_reports_unavailable_for_missing_binary() {
        let verifier = LeanVerifier::new();
        let outcome =
            match verifier.spawn_command(Command::new("/nonexistent/bogus-lean-binary-xyz")) {
                Ok(mut child) => {
                    let _ = child.kill();
                    panic!("missing verifier binary unexpectedly spawned")
                }
                Err(outcome) => outcome,
            };
        assert!(
            matches!(outcome, LeanVerificationOutcome::Unavailable { .. }),
            "expected Unavailable for missing binary, got {outcome:?}"
        );
    }

    #[test]
    fn test_classify_output_exit_zero_clean_diagnostic_accepts() {
        let outcome = classify_output(0, String::new());
        assert_eq!(outcome, LeanVerificationOutcome::Accepted);
    }

    #[test]
    fn test_classify_output_exit_zero_error_diagnostic_rejects() {
        let outcome = classify_output(0, "error: something broke\n".to_string());
        assert!(matches!(outcome, LeanVerificationOutcome::Rejected { .. }));
    }

    #[test]
    fn test_classify_output_exit_zero_sorry_warning_rejects() {
        let outcome = classify_output(0, "warning: declaration uses 'sorry'\n".to_string());
        assert!(matches!(outcome, LeanVerificationOutcome::Rejected { .. }));

        let outcome = classify_output(0, "warning: declaration uses `sorry`\n".to_string());
        assert!(matches!(outcome, LeanVerificationOutcome::Rejected { .. }));
    }

    #[test]
    fn test_classify_output_nonzero_exit_rejects() {
        let outcome = classify_output(1, String::new());
        assert!(matches!(outcome, LeanVerificationOutcome::Rejected { .. }));
    }

    #[test]
    fn project_import_failure_is_unavailable_not_a_proof_rejection() {
        let outcome = normalize_project_failure(LeanVerificationOutcome::Rejected {
            diagnostic: "error: unknown module 'AySoundness.Lrat'".to_string(),
            exit_code: 1,
        });
        assert!(matches!(
            outcome,
            LeanVerificationOutcome::Unavailable { .. }
        ));
    }

    #[test]
    fn resource_failures_are_unavailable_not_proof_rejections() {
        for diagnostic in [
            "error: maximum recursion depth has been reached",
            "error: maximum heartbeats exceeded",
            "fatal: out of memory",
        ] {
            let outcome = normalize_project_failure(LeanVerificationOutcome::Rejected {
                diagnostic: diagnostic.to_string(),
                exit_code: 1,
            });
            assert!(
                matches!(outcome, LeanVerificationOutcome::Unavailable { .. }),
                "resource failure was mislabeled as proof rejection: {outcome:?}"
            );
        }
        let outcome = normalize_project_failure(LeanVerificationOutcome::Rejected {
            diagnostic: String::new(),
            exit_code: -1,
        });
        assert!(matches!(
            outcome,
            LeanVerificationOutcome::Unavailable { .. }
        ));
    }

    #[cfg(unix)]
    #[test]
    fn timeout_runner_concurrently_drains_verbose_child() {
        let mut command = Command::new("sh");
        command
            .arg("-c")
            .arg(
                "i=0; while [ \"$i\" -lt 12000 ]; do echo verbose-output-line; echo verbose-diagnostic-line >&2; i=$((i + 1)); done",
            )
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        let child = command.spawn().expect("spawn verbose test child");

        assert_eq!(
            run_with_timeout(child, Duration::from_secs(10)),
            LeanVerificationOutcome::Accepted
        );
    }
}
