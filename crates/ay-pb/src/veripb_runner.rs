// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded external VeriPB execution for opt-in tests and developer tools.
//!
//! This module is feature-only. It does not participate in solver decisions:
//! callers use it solely to turn generated proof text into an externally
//! checked verification receipt.

use std::fmt;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(unix)]
use nix::errno::Errno;
#[cfg(unix)]
use nix::sys::signal::{killpg, Signal};
#[cfg(unix)]
use nix::unistd::Pid;
#[cfg(unix)]
use std::os::unix::process::CommandExt;

const DEFAULT_TIMEOUT: Duration = Duration::from_secs(60);
const DEFAULT_STREAM_LIMIT_BYTES: usize = 1024 * 1024;
const POLL_INTERVAL: Duration = Duration::from_millis(10);
const TERMINATION_REAP_TIMEOUT: Duration = Duration::from_secs(2);
const CAPTURE_FINISH_TIMEOUT: Duration = Duration::from_secs(2);
const VERIFIED_UNSAT_MARKER: &str = "VERIFIED UNSATISFIABLE";

/// Exact limits enforced around one external VeriPB checker process.
///
/// The checker runs serially. Wall time and retained output are bounded; no
/// checker RSS limit is enforced, and the stable record says so explicitly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VeriPbEnvelope {
    timeout: Duration,
    stdout_limit_bytes: usize,
    stderr_limit_bytes: usize,
}

impl VeriPbEnvelope {
    /// Fixed fail-closed limits shared by the certification tests and dev tool.
    pub const fn bounded_default() -> Self {
        Self {
            timeout: DEFAULT_TIMEOUT,
            stdout_limit_bytes: DEFAULT_STREAM_LIMIT_BYTES,
            stderr_limit_bytes: DEFAULT_STREAM_LIMIT_BYTES,
        }
    }

    /// Stable, machine-readable resource-envelope record suitable for a sidecar.
    pub fn record(self) -> String {
        let process_scope = if cfg!(unix) {
            "unix_process_group"
        } else {
            "direct_child_only"
        };
        format!(
            "wall_timeout_ms={} stdout_limit_bytes={} stderr_limit_bytes={} \
             termination_reap_timeout_ms={} capture_finish_timeout_ms_per_stream={} \
             checker_processes=1 process_scope={} checker_rss_limit=unenforced",
            self.timeout.as_millis(),
            self.stdout_limit_bytes,
            self.stderr_limit_bytes,
            TERMINATION_REAP_TIMEOUT.as_millis(),
            CAPTURE_FINISH_TIMEOUT.as_millis(),
            process_scope,
        )
    }
}

impl Default for VeriPbEnvelope {
    fn default() -> Self {
        Self::bounded_default()
    }
}

impl fmt::Display for VeriPbEnvelope {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.record())
    }
}

/// Receipt returned only after VeriPB exits successfully and prints its UNSAT
/// verification marker.
#[derive(Debug)]
pub struct VerifiedUnsat {
    elapsed: Duration,
    stdout: String,
    stderr: String,
    stdout_truncated: bool,
    stderr_truncated: bool,
}

impl VerifiedUnsat {
    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }

    pub fn stdout(&self) -> &str {
        &self.stdout
    }

    pub fn stderr(&self) -> &str {
        &self.stderr
    }

    pub fn stdout_truncated(&self) -> bool {
        self.stdout_truncated
    }

    pub fn stderr_truncated(&self) -> bool {
        self.stderr_truncated
    }
}

/// Failures from the bounded external checker.
#[derive(Debug, thiserror::Error)]
pub enum VeriPbRunError {
    #[error("{action} {path}: {source}")]
    Io {
        action: &'static str,
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    #[error("capture VeriPB {stream}: {source}")]
    Capture {
        stream: &'static str,
        #[source]
        source: io::Error,
    },
    #[error("VeriPB {stream} capture thread panicked")]
    CaptureThreadPanicked { stream: &'static str },
    #[error("VeriPB {stream} capture did not finish within {timeout_ms} ms")]
    CaptureTimedOut {
        stream: &'static str,
        timeout_ms: u128,
    },
    #[cfg(unix)]
    #[error("VeriPB child PID {pid} does not fit a Unix process-group identifier")]
    InvalidProcessGroupId { pid: u32 },
    #[cfg(unix)]
    #[error("signal VeriPB process group {process_group} with SIGKILL: {source}")]
    ProcessGroupSignal {
        process_group: i32,
        #[source]
        source: Errno,
    },
    #[error("VeriPB checker did not become reapable within {timeout_ms} ms after termination")]
    ReapTimedOut { timeout_ms: u128 },
    #[error(
        "VeriPB timed out after {elapsed_ms} ms ({envelope}); \
         stdout{stdout_suffix}:\n{stdout}\nstderr{stderr_suffix}:\n{stderr}"
    )]
    TimedOut {
        elapsed_ms: u128,
        envelope: VeriPbEnvelope,
        stdout: String,
        stderr: String,
        stdout_suffix: &'static str,
        stderr_suffix: &'static str,
    },
    #[error(
        "VeriPB rejected the proof (status {status}; {envelope}); \
         stdout{stdout_suffix}:\n{stdout}\nstderr{stderr_suffix}:\n{stderr}"
    )]
    Rejected {
        status: ExitStatus,
        envelope: VeriPbEnvelope,
        stdout: String,
        stderr: String,
        stdout_suffix: &'static str,
        stderr_suffix: &'static str,
    },
}

#[derive(Debug)]
struct CapturedStream {
    text: String,
    truncated: bool,
}

struct CaptureThread {
    receiver: Receiver<Result<CapturedStream, io::Error>>,
}

fn capture_stream(
    mut stream: impl Read,
    retained_limit: usize,
) -> Result<CapturedStream, io::Error> {
    let mut retained = Vec::with_capacity(retained_limit.min(8192));
    let mut truncated = false;
    let mut buffer = [0u8; 8192];
    loop {
        let count = stream.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        let remaining = retained_limit.saturating_sub(retained.len());
        let keep = remaining.min(count);
        retained.extend_from_slice(&buffer[..keep]);
        truncated |= keep != count;
    }
    Ok(CapturedStream {
        text: String::from_utf8_lossy(&retained).into_owned(),
        truncated,
    })
}

fn spawn_capture(
    name: &'static str,
    stream: impl Read + Send + 'static,
    retained_limit: usize,
) -> Result<CaptureThread, io::Error> {
    let (sender, receiver) = mpsc::sync_channel(1);
    // Completion is observed through the bounded receiver below. Intentionally
    // detach the handle so a stuck inherited pipe cannot make Drop block.
    let _detached = thread::Builder::new()
        .name(name.to_owned())
        .spawn(move || {
            let result = capture_stream(stream, retained_limit);
            let _ = sender.send(result);
        })?;
    Ok(CaptureThread { receiver })
}

fn finish_capture(
    stream: &'static str,
    capture: CaptureThread,
) -> Result<CapturedStream, VeriPbRunError> {
    match capture.receiver.recv_timeout(CAPTURE_FINISH_TIMEOUT) {
        Ok(Ok(captured)) => Ok(captured),
        Ok(Err(source)) => Err(VeriPbRunError::Capture { stream, source }),
        Err(RecvTimeoutError::Timeout) => Err(VeriPbRunError::CaptureTimedOut {
            stream,
            timeout_ms: CAPTURE_FINISH_TIMEOUT.as_millis(),
        }),
        Err(RecvTimeoutError::Disconnected) => {
            Err(VeriPbRunError::CaptureThreadPanicked { stream })
        }
    }
}

#[cfg(unix)]
fn kill_process_group(child: &Child) -> Result<(), VeriPbRunError> {
    let raw_pid = i32::try_from(child.id())
        .map_err(|_| VeriPbRunError::InvalidProcessGroupId { pid: child.id() })?;
    let process_group = Pid::from_raw(raw_pid);
    match killpg(process_group, Signal::SIGKILL) {
        Ok(()) | Err(Errno::ESRCH) => Ok(()),
        Err(source) => Err(VeriPbRunError::ProcessGroupSignal {
            process_group: raw_pid,
            source,
        }),
    }
}

fn terminate_and_reap(child: &mut Child, checker: &Path) -> Result<ExitStatus, VeriPbRunError> {
    #[cfg(unix)]
    kill_process_group(child)?;
    #[cfg(not(unix))]
    if let Err(kill_source) = child.kill() {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(status),
            Ok(None) => {
                return Err(VeriPbRunError::Io {
                    action: "kill VeriPB checker",
                    path: checker.to_path_buf(),
                    source: kill_source,
                });
            }
            Err(source) => {
                return Err(VeriPbRunError::Io {
                    action: "poll VeriPB checker after failed kill",
                    path: checker.to_path_buf(),
                    source,
                });
            }
        }
    }
    let termination_started = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(status),
            Ok(None) if termination_started.elapsed() < TERMINATION_REAP_TIMEOUT => {
                let remaining =
                    TERMINATION_REAP_TIMEOUT.saturating_sub(termination_started.elapsed());
                thread::sleep(POLL_INTERVAL.min(remaining));
            }
            Ok(None) => {
                return Err(VeriPbRunError::ReapTimedOut {
                    timeout_ms: TERMINATION_REAP_TIMEOUT.as_millis(),
                });
            }
            Err(source) => {
                return Err(VeriPbRunError::Io {
                    action: "poll terminated VeriPB checker for reaping",
                    path: checker.to_path_buf(),
                    source,
                });
            }
        }
    }
}

fn finish_terminal_child(
    _child: &Child,
    observed_status: ExitStatus,
) -> Result<ExitStatus, VeriPbRunError> {
    // On Unix the direct checker may have exited after spawning a descendant
    // that inherited its output pipes. Kill the isolated checker process group
    // before joining the drainers so those inherited descriptors cannot keep
    // this bounded runner alive.
    #[cfg(unix)]
    kill_process_group(_child)?;
    Ok(observed_status)
}

fn truncation_suffix(truncated: bool) -> &'static str {
    if truncated {
        " [retained prefix truncated]"
    } else {
        ""
    }
}

/// Run VeriPB against `formula` and `proof` under `envelope`.
///
/// Success means all three conditions held: the checker completed before the
/// timeout, exited successfully, and its bounded stdout contained
/// `VERIFIED UNSATISFIABLE`. Timeout paths kill and reap the checker before
/// returning.
pub fn verify_unsat(
    checker: &Path,
    formula: &Path,
    proof: &Path,
    envelope: VeriPbEnvelope,
) -> Result<VerifiedUnsat, VeriPbRunError> {
    let started = Instant::now();
    let mut command = Command::new(checker);
    command
        .arg(formula)
        .arg(proof)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    #[cfg(unix)]
    command.process_group(0);
    let mut child = command.spawn().map_err(|source| VeriPbRunError::Io {
        action: "spawn VeriPB checker",
        path: checker.to_path_buf(),
        source,
    })?;

    let stdout_pipe = match child.stdout.take() {
        Some(stdout) => stdout,
        None => {
            let source = io::Error::other("checker stdout was not piped");
            if let Err(error) = terminate_and_reap(&mut child, checker) {
                return Err(error);
            }
            return Err(VeriPbRunError::Io {
                action: "capture VeriPB stdout for",
                path: checker.to_path_buf(),
                source,
            });
        }
    };
    let stderr_pipe = match child.stderr.take() {
        Some(stderr) => stderr,
        None => {
            let source = io::Error::other("checker stderr was not piped");
            if let Err(error) = terminate_and_reap(&mut child, checker) {
                return Err(error);
            }
            return Err(VeriPbRunError::Io {
                action: "capture VeriPB stderr for",
                path: checker.to_path_buf(),
                source,
            });
        }
    };

    let stdout_limit = envelope.stdout_limit_bytes;
    let stdout_capture = match spawn_capture("ay-veripb-stdout", stdout_pipe, stdout_limit) {
        Ok(capture) => capture,
        Err(source) => {
            if let Err(error) = terminate_and_reap(&mut child, checker) {
                return Err(error);
            }
            return Err(VeriPbRunError::Io {
                action: "start VeriPB stdout capture for",
                path: checker.to_path_buf(),
                source,
            });
        }
    };
    let stderr_limit = envelope.stderr_limit_bytes;
    let stderr_capture = match spawn_capture("ay-veripb-stderr", stderr_pipe, stderr_limit) {
        Ok(capture) => capture,
        Err(source) => {
            if let Err(error) = terminate_and_reap(&mut child, checker) {
                return Err(error);
            }
            let _ = finish_capture("stdout", stdout_capture);
            return Err(VeriPbRunError::Io {
                action: "start VeriPB stderr capture for",
                path: checker.to_path_buf(),
                source,
            });
        }
    };

    let process_result = loop {
        match child.try_wait() {
            Ok(Some(observed_status)) => {
                let status = match finish_terminal_child(&child, observed_status) {
                    Ok(status) => status,
                    Err(error) => return Err(error),
                };
                break Ok((status, false));
            }
            Ok(None) if started.elapsed() < envelope.timeout => {
                let remaining = envelope.timeout.saturating_sub(started.elapsed());
                thread::sleep(POLL_INTERVAL.min(remaining));
            }
            Ok(None) => {
                let status = match terminate_and_reap(&mut child, checker) {
                    Ok(status) => status,
                    Err(error) => return Err(error),
                };
                break Ok((status, true));
            }
            Err(source) => {
                if let Err(error) = terminate_and_reap(&mut child, checker) {
                    return Err(error);
                }
                break Err(VeriPbRunError::Io {
                    action: "poll VeriPB checker",
                    path: checker.to_path_buf(),
                    source,
                });
            }
        }
    };
    let elapsed = started.elapsed();
    // Await both drainers under their own caps before propagating any process
    // or capture error. On Unix, successful process cleanup has already closed
    // every pipe holder in the isolated checker process group.
    let stdout_result = finish_capture("stdout", stdout_capture);
    let stderr_result = finish_capture("stderr", stderr_capture);
    let (status, timed_out) = process_result?;
    let stdout = stdout_result?;
    let stderr = stderr_result?;

    if timed_out {
        return Err(VeriPbRunError::TimedOut {
            elapsed_ms: elapsed.as_millis(),
            envelope,
            stdout_suffix: truncation_suffix(stdout.truncated),
            stderr_suffix: truncation_suffix(stderr.truncated),
            stdout: stdout.text,
            stderr: stderr.text,
        });
    }
    if !status.success() || !stdout.text.contains(VERIFIED_UNSAT_MARKER) {
        return Err(VeriPbRunError::Rejected {
            status,
            envelope,
            stdout_suffix: truncation_suffix(stdout.truncated),
            stderr_suffix: truncation_suffix(stderr.truncated),
            stdout: stdout.text,
            stderr: stderr.text,
        });
    }

    Ok(VerifiedUnsat {
        elapsed,
        stdout: stdout.text,
        stderr: stderr.text,
        stdout_truncated: stdout.truncated,
        stderr_truncated: stderr.truncated,
    })
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;
    #[cfg(unix)]
    use std::path::Path;
    #[cfg(unix)]
    use std::time::{Duration, Instant};

    use super::capture_stream;
    #[cfg(unix)]
    use super::{verify_unsat, VeriPbEnvelope, VeriPbRunError};

    #[test]
    fn capture_stream_retains_only_the_configured_prefix() {
        let captured =
            capture_stream(Cursor::new(b"abcdefghij"), 4).expect("in-memory capture succeeds");

        assert_eq!(captured.text, "abcd");
        assert!(captured.truncated);
    }

    #[cfg(unix)]
    #[test]
    fn timeout_kills_and_reaps_the_checker() {
        let envelope = VeriPbEnvelope {
            timeout: Duration::from_millis(25),
            stdout_limit_bytes: 64,
            stderr_limit_bytes: 64,
        };
        let started = Instant::now();
        let result = verify_unsat(
            Path::new("/bin/sh"),
            Path::new("-c"),
            Path::new("sleep 30 & wait"),
            envelope,
        );

        assert!(matches!(result, Err(VeriPbRunError::TimedOut { .. })));
        assert!(
            started.elapsed() < Duration::from_secs(2),
            "timeout path did not promptly kill and reap the checker"
        );
    }

    #[cfg(unix)]
    #[test]
    fn terminal_checker_kills_descendants_that_inherited_its_pipes() {
        let envelope = VeriPbEnvelope {
            timeout: Duration::from_secs(5),
            stdout_limit_bytes: 64,
            stderr_limit_bytes: 64,
        };
        let started = Instant::now();
        let result = verify_unsat(
            Path::new("/bin/sh"),
            Path::new("-c"),
            Path::new("sleep 30 & exit 7"),
            envelope,
        );

        assert!(matches!(result, Err(VeriPbRunError::Rejected { .. })));
        assert!(
            started.elapsed() < Duration::from_secs(2),
            "terminal checker left an inherited-pipe descendant running"
        );
    }
}
