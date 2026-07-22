// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lean kernel verification glue for `--lean-verify` (#8773, Phase 1).
//!
//! This module is the **Phase 1 thin wrapper** described in
//! the development design notes. It exposes a minimal
//! [`LeanVerifier`] that shells out to the `lean` binary on a previously
//! emitted `.lean4` kernel-checked proof and classifies the outcome.
//!
//! # Why it lives in `ay` (not `ay-lean-bridge`) in Phase 1
//!
//! `ay-lean-bridge` currently depends on `ay` (for the `ay::api::Solver`
//! facade), so `ay -> ay-lean-bridge` would be a dependency cycle. The
//! canonical home for this verifier is `ay-lean-bridge::verify` per the
//! design doc. Phase 2 of that migration lifts the LRAT emitter into
//! `ay-lean-bridge` without a `ay` dep (design §2, Option B), at which
//! point this shim becomes a one-line delegation to
//! `ay_lean_bridge::verify::LeanVerifier`.
//!
//! Until that migration lands, this module IS the canonical verification
//! entry point invoked by `--lean-verify`.

use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

/// Outcome of invoking the Lean kernel on an emitted `.lean4` proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum LeanVerificationOutcome {
    /// Lean accepted the proof (exit 0, no kernel errors).
    Accepted,
    /// Lean rejected the proof. Carries captured stderr and exit code.
    Rejected { stderr: String, exit_code: i32 },
    /// Lean binary unavailable (missing / not on PATH / timed out / IO error).
    Unavailable { reason: String },
}

/// Thin wrapper that invokes `lean <proof-file>`.
///
/// The `--lean-verify` CLI flag constructs one of these per UNSAT result,
/// invokes [`LeanVerifier::verify_descriptor`] on an authenticated proof
/// snapshot, and routes the outcome to the exit-code contract documented in
/// `crates/ay/README.md`.
#[derive(Debug, Clone)]
pub(crate) struct LeanVerifier {
    lean_path: PathBuf,
    timeout: Option<Duration>,
}

impl LeanVerifier {
    /// Construct a verifier targeting `lean` on PATH with a 300s timeout.
    pub(crate) fn new() -> Self {
        Self {
            lean_path: PathBuf::from("lean"),
            timeout: Some(Duration::from_mins(5)),
        }
    }

    /// Use a specific `lean` binary (for sandboxed or pinned builds).
    pub(crate) fn with_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.lean_path = path.into();
        self
    }

    /// Invoke Lean on the exact inode named by `proof_file`, not on a mutable
    /// public pathname. The cloned descriptor is inherited across `exec`, and
    /// Lean receives the child-local descriptor path.
    #[cfg(unix)]
    pub(crate) fn verify_descriptor(&self, proof_file: &std::fs::File) -> LeanVerificationOutcome {
        let inherited = match proof_file.try_clone() {
            Ok(file) => file,
            Err(error) => {
                return LeanVerificationOutcome::Unavailable {
                    reason: format!("failed to clone authenticated Lean snapshot: {error}"),
                };
            }
        };
        #[cfg(any(target_os = "linux", target_os = "android"))]
        let descriptor_path = PathBuf::from("/proc/self/fd/0");
        #[cfg(not(any(target_os = "linux", target_os = "android")))]
        let descriptor_path = PathBuf::from("/dev/stdin");
        let mut cmd = Command::new(&self.lean_path);
        cmd.arg(descriptor_path)
            .stdin(std::process::Stdio::from(inherited));
        self.run_command(cmd)
    }

    /// Invoke Lean on a retained private snapshot stage plus the pinned
    /// descriptor on stdin. Used on hosts without a re-openable descriptor
    /// pathname: macOS has no `/proc/self/fd`, and its `/dev/fd` entries have
    /// dup-offset semantics, so a verifier that opens its input path more
    /// than once would read from EOF. The caller re-authenticates the pinned
    /// descriptor bytes against the published digest before and after this
    /// call, so the private stage pathname is never the trust root for the
    /// verified-content claim.
    #[cfg(unix)]
    pub(crate) fn verify_snapshot_path(
        &self,
        snapshot_path: &std::path::Path,
        proof_file: &std::fs::File,
    ) -> LeanVerificationOutcome {
        let inherited = match proof_file.try_clone() {
            Ok(file) => file,
            Err(error) => {
                return LeanVerificationOutcome::Unavailable {
                    reason: format!("failed to clone authenticated Lean snapshot: {error}"),
                };
            }
        };
        let mut cmd = Command::new(&self.lean_path);
        cmd.arg(snapshot_path)
            .stdin(std::process::Stdio::from(inherited));
        self.run_command(cmd)
    }

    fn spawn_command(
        &self,
        mut cmd: Command,
    ) -> Result<std::process::Child, LeanVerificationOutcome> {
        // Capture both streams so Accepted warnings don't leak to the user's
        // stderr and Rejected stderr can be surfaced on failure.
        cmd.stdout(std::process::Stdio::piped());
        cmd.stderr(std::process::Stdio::piped());

        match cmd.spawn() {
            Ok(child) => Ok(child),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                Err(LeanVerificationOutcome::Unavailable {
                    reason: format!(
                        "lean binary not found at '{}' (use --lean-path to override)",
                        self.lean_path.display()
                    ),
                })
            }
            Err(err) => Err(LeanVerificationOutcome::Unavailable {
                reason: format!("failed to spawn '{}': {err}", self.lean_path.display()),
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
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn run_with_timeout(mut child: std::process::Child, timeout: Duration) -> LeanVerificationOutcome {
    // We intentionally do not pull in `wait_timeout` here to avoid expanding
    // the ay dependency surface for a Phase 1 thin wrapper. Simple polling is
    // adequate for the typical lean proof check (seconds to minutes) and the
    // default 300s timeout.
    let start = std::time::Instant::now();
    let poll = Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                // Child exited; drain stderr.
                let stderr_bytes = child
                    .stderr
                    .take()
                    .map(|mut s| {
                        use std::io::Read;
                        let mut buf = Vec::new();
                        let _ = s.read_to_end(&mut buf);
                        buf
                    })
                    .unwrap_or_default();
                return classify_output(
                    status.code().unwrap_or(-1),
                    String::from_utf8_lossy(&stderr_bytes).into_owned(),
                );
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
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
                return LeanVerificationOutcome::Unavailable {
                    reason: format!("failed polling lean child: {err}"),
                };
            }
        }
    }
}

fn classify_output(exit_code: i32, stderr: String) -> LeanVerificationOutcome {
    if exit_code == 0 {
        // Lean emits warnings on stderr even when the kernel accepts. Treat
        // any non-zero-indicating stderr (unknown identifier, error:, failed
        // to verify) as Rejected even on exit 0 — defensive for future Lean
        // toolchains that may not propagate every kernel error to exit code.
        if stderr_indicates_rejection(&stderr) {
            return LeanVerificationOutcome::Rejected { stderr, exit_code };
        }
        LeanVerificationOutcome::Accepted
    } else {
        LeanVerificationOutcome::Rejected { stderr, exit_code }
    }
}

fn stderr_indicates_rejection(stderr: &str) -> bool {
    stderr.contains("error:")
        || stderr.contains("proof failed")
        || stderr.contains("declaration uses 'sorry'")
        || stderr.contains("declaration uses `sorry`")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn test_verifier_reports_unavailable_for_missing_binary() {
        let verifier = LeanVerifier::new().with_path("/nonexistent/bogus-lean-binary-xyz");
        let tmp = std::env::temp_dir().join("ay-lean-verify-unit-test.lean4");
        std::fs::write(&tmp, "theorem t : True := trivial\n").expect("write tmp");
        let proof = std::fs::File::open(&tmp).expect("open tmp");
        let outcome = verifier.verify_descriptor(&proof);
        let _ = std::fs::remove_file(&tmp);
        assert!(
            matches!(outcome, LeanVerificationOutcome::Unavailable { .. }),
            "expected Unavailable for missing binary, got {outcome:?}"
        );
    }

    #[test]
    fn test_classify_output_exit_zero_clean_stderr_accepts() {
        let outcome = classify_output(0, String::new());
        assert_eq!(outcome, LeanVerificationOutcome::Accepted);
    }

    #[test]
    fn test_classify_output_exit_zero_error_stderr_rejects() {
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
}
