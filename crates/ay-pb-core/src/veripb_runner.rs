// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded external VeriPB execution for opt-in tests and developer tools.
//!
//! This module is feature-only. It does not participate in solver decisions:
//! callers use it solely to turn generated proof text into an externally
//! checked verification receipt.

// The public typed error intentionally retains the bounded checker transcript
// inline. Boxing it would break the existing pattern-matching API; both output
// strings are already capped by `VeriPbEnvelope`.
#![allow(clippy::result_large_err)]

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

const DEFAULT_TIMEOUT: Duration = Duration::from_mins(1);
const DEFAULT_STREAM_LIMIT_BYTES: usize = 1024 * 1024;
const POLL_INTERVAL: Duration = Duration::from_millis(10);
const TERMINATION_REAP_TIMEOUT: Duration = Duration::from_secs(2);
const CAPTURE_FINISH_TIMEOUT: Duration = Duration::from_secs(2);
/// VeriPB prints its verdict on a `s `-prefixed line, and only there.
const VERDICT_PREFIX: &str = "s ";
/// The status token of a FULLY checked acceptance. `UNDER WEAKENED GUARANTEES`
/// — what `veripb -u` prints — is deliberately absent: this runner never asks
/// for unchecked deletions, so it must never accept a run that gave it them.
const VERIFIED_STATUS: &str = "VERIFIED";
/// The one conclusion this runner asks about.
const UNSAT_CONCLUSION: &str = "UNSATISFIABLE";

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

/// True when `stdout` carries VeriPB's `s VERIFIED UNSATISFIABLE` verdict.
///
/// STRUCTURAL, NEVER A SUBSTRING SCAN. This function used to be
/// `stdout.contains("VERIFIED UNSATISFIABLE")`, and that spelling accepted a
/// checker that had REFUSED the proof: `ci/fake-checkers/comment-verified.sh`
/// prints `s NOT VERIFIED` under a `c` comment line mentioning the words, and
/// the substring test could not tell the comment from the verdict. So could
/// `s NOT VERIFIED UNSATISFIABLE`, where the substring is on the verdict line
/// itself. A refusal read as an acceptance is the worst failure a verification
/// path has, and the hazard was already written down as live in
/// `crates/ay/src/maxsat_cert.rs` before it was closed here.
///
/// The contract is the one `crates/ay-test-support/src/veripb.rs` and
/// `scripts/lib/veripb_verdict.sh` already enforce, narrowed to the single
/// conclusion this runner asks about:
///
/// * the verdict is the FIRST `s `-prefixed line and nothing else on stdout is
///   a verdict — a checker that refuses and then chatters must not be read from
///   the bottom, and a comment is never a verdict;
/// * its status token must be `VERIFIED` as a WHOLE WORD (`s VERIFIEDX ...` is
///   not `s VERIFIED X ...`), so `s NOT VERIFIED ...` and the weaker
///   `s UNDER WEAKENED GUARANTEES ...` are both refusals here;
/// * its conclusion must be EXACTLY `UNSATISFIABLE`. `NO CONCLUSION` (which
///   real veripb 3.0.2 prints, with exit 0, for a proof that concludes nothing)
///   establishes nothing, and `SATISFIABLE` is the checker confirming the
///   OPPOSITE of the claim under test.
///
/// The caller pairs this with `ExitStatus::success()`, because neither half is
/// sufficient alone: `/usr/bin/true` exits 0 having checked nothing, and a
/// correct verdict printed by a run that then crashed is not evidence that the
/// check finished.
fn accepts_unsat_verdict(stdout: &str) -> bool {
    let Some(body) = stdout
        .lines()
        .map(str::trim_end)
        .find_map(|line| line.strip_prefix(VERDICT_PREFIX))
    else {
        return false;
    };
    let Some(conclusion) = body.trim_start().strip_prefix(VERIFIED_STATUS) else {
        return false;
    };
    if !(conclusion.is_empty() || conclusion.starts_with(char::is_whitespace)) {
        return false;
    }
    conclusion.trim() == UNSAT_CONCLUSION
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
/// timeout, exited successfully, and its bounded stdout carried the verdict
/// LINE `s VERIFIED UNSATISFIABLE` — see [`accepts_unsat_verdict`], which is
/// structural and is not a substring scan. Timeout paths kill and reap the
/// checker before returning.
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
            terminate_and_reap(&mut child, checker)?;
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
            terminate_and_reap(&mut child, checker)?;
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
            terminate_and_reap(&mut child, checker)?;
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
            terminate_and_reap(&mut child, checker)?;
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
                let status = finish_terminal_child(&child, observed_status)?;
                break Ok((status, false));
            }
            Ok(None) if started.elapsed() < envelope.timeout => {
                let remaining = envelope.timeout.saturating_sub(started.elapsed());
                thread::sleep(POLL_INTERVAL.min(remaining));
            }
            Ok(None) => {
                let status = terminate_and_reap(&mut child, checker)?;
                break Ok((status, true));
            }
            Err(source) => {
                terminate_and_reap(&mut child, checker)?;
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
    if !status.success() || !accepts_unsat_verdict(&stdout.text) {
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

// ------------------------------------------------------------------ self-test
//
// WHY THIS EXISTS. [`verify_unsat`] reads the checker's verdict correctly, and
// that is not enough. Reading a verdict correctly only tells you what the
// binary SAID; it cannot tell you whether the binary is a proof checker.
// `ci/fake-checkers/always-unsat.sh` prints a perfectly well-formed
// `s VERIFIED UNSATISFIABLE` and exits 0 for every input, and
// `ci/fake-checkers/parrot.sh` reads the conclusion out of the proof and
// restates it; both satisfy every structural rule in `accepts_unsat_verdict`.
// The certification surface that takes a checker PATH FROM THE USER
// (`ay-pb-dev certify-unsat --veripb`) therefore had a live hole: it pinned the
// binary's sha256, which fixes WHICH bytes it ran but says nothing about what
// those bytes DO.
//
// Only behaviour is an identity. Before a verdict from `checker` is believed,
// [`self_test`] makes it verify a proof it MUST accept and refuse three it MUST
// reject.

/// Probe labels, in execution order. Also the scratch-file stems.
const PROBE_GOOD_UNSAT: &str = "selftest-good-unsat";
const PROBE_FALSE_UNSAT: &str = "selftest-false-unsat";
const PROBE_GARBAGE: &str = "selftest-garbage";
const PROBE_NO_CONCLUSION: &str = "selftest-no-conclusion";

/// How many probes [`self_test`] runs. Recorded in the campaign receipt so a
/// reader can tell a four-probe run from a future one.
pub const SELF_TEST_PROBES: usize = 4;

// The probe fixtures. Each is BYTE-IDENTICAL to the constant of the same name
// in `crates/ay-test-support/src/veripb.rs`, and
// `self_test_fixtures_match_the_shared_battery` asserts it. That crate is a
// dev-dependency, so this module cannot link it and must hold the bytes; the
// test is what keeps the copy from becoming a second, divergent battery.

/// An unsatisfiable formula: `x1 >= 1` and `-x1 >= 0`.
const SELF_TEST_UNSAT_OPB: &str = "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
/// A valid refutation of it.
const SELF_TEST_GOOD_UNSAT_PBP: &str = "pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 2 +;\nrup >= 1 ;\noutput NONE;\nconclusion UNSAT : 4;\nend pseudo-Boolean proof;\n";
/// A well-formed proof over the same formula that derives and concludes
/// NOTHING. Real VeriPB answers `s VERIFIED NO CONCLUSION` and exits 0.
const SELF_TEST_NO_CONCLUSION_PBP: &str = "pseudo-Boolean proof version 3.0\nf 2 ;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n";
/// A SATISFIABLE formula: `x1 + x2 >= 1`.
const SELF_TEST_SAT_OPB: &str = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
/// A LIE about it: claims UNSAT, citing a satisfiable input row as the
/// contradiction. This is the probe that states something FALSE, and it is the
/// only kind of probe a rubber stamp or a parrot cannot survive.
const SELF_TEST_FALSE_UNSAT_PBP: &str = "pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion UNSAT : 1;\nend pseudo-Boolean proof;\n";
/// Not a proof at all.
const SELF_TEST_GARBAGE_PBP: &str = "this file is not a pseudo-Boolean proof\n";

/// Evidence that a checker demonstrated it can both accept and refuse.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SelfTestReport {
    probes: usize,
    elapsed: Duration,
}

impl SelfTestReport {
    /// How many probes the checker answered correctly.
    #[must_use]
    pub const fn probes(self) -> usize {
        self.probes
    }

    /// Wall time the whole battery took, scratch-file writes included.
    #[must_use]
    pub const fn elapsed(self) -> Duration {
        self.elapsed
    }
}

impl fmt::Display for SelfTestReport {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "PASSED ({}/{} probes, {} ms)",
            self.probes,
            SELF_TEST_PROBES,
            self.elapsed.as_millis()
        )
    }
}

fn self_test_scratch() -> Result<PathBuf, String> {
    for attempt in 0..100u32 {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |elapsed| elapsed.as_nanos());
        let path = std::env::temp_dir().join(format!(
            "ay-veripb-selftest-{}-{attempt}-{nanos}",
            std::process::id()
        ));
        match std::fs::create_dir(&path) {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("create {}: {error}", path.display())),
        }
    }
    Err("could not reserve a VeriPB self-test scratch directory".to_owned())
}

fn write_fixture(directory: &Path, name: &str, text: &str) -> Result<PathBuf, String> {
    let path = directory.join(name);
    std::fs::write(&path, text)
        .map_err(|error| format!("write self-test fixture {}: {error}", path.display()))?;
    Ok(path)
}

/// One probe whose proof states something FALSE about its formula, or is not a
/// proof at all. The checker must REFUSE it.
///
/// Fails closed on a run that did not complete: a spawn failure, a capture
/// failure or a timeout is NOT a refusal, and must never be counted as one. A
/// binary that cannot be run is not a binary that rejects bad proofs.
fn must_refuse(
    label: &str,
    checker: &Path,
    formula: &Path,
    proof: &Path,
    envelope: VeriPbEnvelope,
    what: &str,
) -> Result<(), String> {
    match verify_unsat(checker, formula, proof, envelope) {
        Err(VeriPbRunError::Rejected { .. }) => Ok(()),
        Ok(receipt) => Err(format!(
            "probe `{label}`: it ACCEPTED {what}, answering \
             `s VERIFIED UNSATISFIABLE` with exit 0. It cannot be a sound \
             checker; stdout:\n{}",
            receipt.stdout().trim()
        )),
        Err(error) => Err(format!(
            "probe `{label}`: the checker did not REFUSE {what} — it failed to \
             run at all ({error}). A run that could not complete is not a refusal"
        )),
    }
}

fn run_self_test_probes(
    checker: &Path,
    envelope: VeriPbEnvelope,
    directory: &Path,
) -> Result<(), String> {
    let unsat_opb = write_fixture(directory, "selftest-unsat.opb", SELF_TEST_UNSAT_OPB)?;
    let sat_opb = write_fixture(directory, "selftest-sat.opb", SELF_TEST_SAT_OPB)?;
    let good_unsat = write_fixture(
        directory,
        "selftest-good-unsat.pbp",
        SELF_TEST_GOOD_UNSAT_PBP,
    )?;
    let false_unsat = write_fixture(
        directory,
        "selftest-false-unsat.pbp",
        SELF_TEST_FALSE_UNSAT_PBP,
    )?;
    let garbage = write_fixture(directory, "selftest-garbage.pbp", SELF_TEST_GARBAGE_PBP)?;
    let no_conclusion = write_fixture(
        directory,
        "selftest-no-conclusion.pbp",
        SELF_TEST_NO_CONCLUSION_PBP,
    )?;

    if let Err(error) = verify_unsat(checker, &unsat_opb, &good_unsat, envelope) {
        return Err(format!(
            "probe `{PROBE_GOOD_UNSAT}`: it did not answer `s VERIFIED \
             UNSATISFIABLE` with exit 0 for a VALID refutation ({error}). \
             It cannot be a working checker"
        ));
    }
    must_refuse(
        PROBE_FALSE_UNSAT,
        checker,
        &sat_opb,
        &false_unsat,
        envelope,
        "a proof claiming UNSAT for a SATISFIABLE formula",
    )?;
    must_refuse(
        PROBE_GARBAGE,
        checker,
        &unsat_opb,
        &garbage,
        envelope,
        "a file that is not a proof at all",
    )?;
    must_refuse(
        PROBE_NO_CONCLUSION,
        checker,
        &unsat_opb,
        &no_conclusion,
        envelope,
        "a proof that concludes NOTHING as though it concluded UNSAT",
    )
}

/// Prove that `checker` really is a proof checker, before any verdict of its
/// is treated as evidence.
///
/// Four probes, each run through [`verify_unsat`] itself — the same spawn, the
/// same argument shape (`checker FORMULA PROOF`, positional, which is NOT the
/// `--opb FORMULA PROOF` shape `ay_test_support::veripb` and
/// `scripts/lib/veripb_verdict.sh` use) and the same verdict reader the
/// campaign will use. A self-test that exercised a different call path would
/// be evidence about a different thing.
///
/// | probe | requirement | catches |
/// | --- | --- | --- |
/// | `selftest-good-unsat` | verify a valid refutation, exit 0 | `/usr/bin/true`, `/usr/bin/false`, `silent-exit0.sh`, `verdict-then-exit1.sh` (right verdict, exit 1), `comment-verified.sh` (refuses on the verdict line) |
/// | `selftest-false-unsat` | REFUSE a proof claiming UNSAT for a SATISFIABLE formula | `always-unsat.sh` and `parrot.sh` — the two fakes that today's structural verdict reader accepts, because what they print really is a well-formed acceptance |
/// | `selftest-garbage` | REFUSE a file that is not a proof | rubber stamps, a second and independent way |
/// | `selftest-no-conclusion` | not read `NO CONCLUSION` as acceptance | the GATE rather than the checker: real veripb 3.0.2 prints `s VERIFIED NO CONCLUSION` and exits 0 here |
///
/// # Why four and not the six in `ay_test_support::veripb::self_test`
///
/// The two omitted probes (`good-sat`, `false-sat`) ask the checker to VERIFY
/// and to REFUSE a SATISFIABLE conclusion. [`verify_unsat`] structurally cannot
/// ask that question — it accepts the conclusion `UNSATISFIABLE` and nothing
/// else — so running them here would test a code path this surface never uses.
/// Nothing is lost: `false-unsat` alone catches both fakes those two probes
/// exist for (`always-unsat.sh` via `good-sat`, `parrot.sh` via `false-sat`),
/// because a parrot handed a proof that CLAIMS `conclusion UNSAT` about a
/// satisfiable formula restates the lie as `s VERIFIED UNSATISFIABLE`. This is
/// the same narrowing, for the same reason, that `crates/ay/src/maxsat_cert.rs`
/// documents for its two-probe `BOUNDS` battery.
///
/// # Errors
/// A description of the FIRST failed probe, naming the observed verdict and
/// exit code. Callers must treat it as fatal and must not report a
/// verification: a verdict from a binary that fails this battery is not
/// evidence of anything.
pub fn self_test(checker: &Path, envelope: VeriPbEnvelope) -> Result<SelfTestReport, String> {
    let started = Instant::now();
    let directory = self_test_scratch()?;
    let outcome = run_self_test_probes(checker, envelope, &directory);
    let _ = std::fs::remove_dir_all(&directory);
    outcome?;
    Ok(SelfTestReport {
        probes: SELF_TEST_PROBES,
        elapsed: started.elapsed(),
    })
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;
    #[cfg(unix)]
    use std::path::Path;
    #[cfg(unix)]
    use std::time::{Duration, Instant};

    use super::{accepts_unsat_verdict, capture_stream};
    #[cfg(unix)]
    use super::{self_test, PROBE_FALSE_UNSAT, PROBE_GOOD_UNSAT, SELF_TEST_PROBES};
    #[cfg(unix)]
    use super::{verify_unsat, VeriPbEnvelope, VeriPbRunError};
    use super::{
        SELF_TEST_FALSE_UNSAT_PBP, SELF_TEST_GARBAGE_PBP, SELF_TEST_GOOD_UNSAT_PBP,
        SELF_TEST_NO_CONCLUSION_PBP, SELF_TEST_SAT_OPB, SELF_TEST_UNSAT_OPB,
    };

    /// The verdict shapes the acceptance test must separate, and why each one
    /// is here. The rows marked THE DEFECT are the ones the substring scan this
    /// replaced ACCEPTED; the rest pin the surrounding contract so the new
    /// reader cannot drift into a different wrong answer.
    #[test]
    fn only_a_structural_verified_unsatisfiable_verdict_line_is_an_acceptance() {
        // (stdout, accepted, what it is)
        let cases: &[(&str, bool, &str)] = &[
            (
                "Running VeriPB version 3.0.2\ns VERIFIED UNSATISFIABLE\n",
                true,
                "the genuine acceptance; without this row the rest is vacuous",
            ),
            (
                "s VERIFIED UNSATISFIABLE",
                true,
                "the same verdict on an unterminated final line",
            ),
            (
                "s VERIFIED UNSATISFIABLE\r\n",
                true,
                "trailing carriage return is not part of the conclusion",
            ),
            (
                "c the proof under test is NOT VERIFIED UNSATISFIABLE\ns NOT VERIFIED\n",
                false,
                "THE DEFECT: a REFUSAL whose comment line carries the words",
            ),
            (
                "s NOT VERIFIED UNSATISFIABLE\n",
                false,
                "THE DEFECT again: the substring on the verdict line, negated",
            ),
            (
                "s UNDER WEAKENED GUARANTEES UNSATISFIABLE\n",
                false,
                "veripb -u: an acceptance, but not the check this runner asked for",
            ),
            (
                "c s VERIFIED UNSATISFIABLE\n",
                false,
                "THE DEFECT: a comment carrying the verdict and no verdict at all",
            ),
            (
                "s VERIFIED SATISFIABLE\n",
                false,
                "the checker confirming the OPPOSITE conclusion",
            ),
            (
                "s VERIFIED NO CONCLUSION\n",
                false,
                "exit 0, real veripb, a proof that concluded nothing",
            ),
            (
                "s VERIFIEDX UNSATISFIABLE\n",
                false,
                "`VERIFIED` must be a whole word",
            ),
            (
                "s VERIFIED UNSATISFIABLE EXCEPT NOT\n",
                false,
                "the conclusion is the WHOLE remainder of the line, not a prefix",
            ),
            (
                "s NOT VERIFIED\ns VERIFIED UNSATISFIABLE\n",
                false,
                "FIRST verdict line, not last: a refusal that then chatters",
            ),
            (
                "c s VERIFIED UNSATISFIABLE\ns VERIFIED NO CONCLUSION\n",
                false,
                "a comment carrying a COMPLETE verdict is still not a verdict",
            ),
            (
                "Running VeriPB version 3.0.2\n",
                false,
                "silence: what real veripb prints for a refusal AND for a crash",
            ),
            ("", false, "nothing at all"),
            (
                "s VERIFIED UNSATISF",
                false,
                "a verdict truncated by the stdout cap must fail closed",
            ),
        ];
        for (stdout, expected, why) in cases {
            assert_eq!(
                accepts_unsat_verdict(stdout),
                *expected,
                "{why}: {stdout:?}"
            );
        }
    }

    /// The defect end to end, through the real spawn path, against the fake
    /// checker committed for it.
    ///
    /// `ci/fake-checkers/comment-verified.sh` exits 0 — so the exit-status half
    /// of the contract is satisfied — and REFUSES the proof on its verdict
    /// line while printing the accepting words in a `c` comment. The
    /// anti-vacuity assertion is the first one: if the fake ever stops carrying
    /// the substring, this test stops testing the defect.
    #[cfg(unix)]
    #[test]
    fn a_refusal_that_merely_mentions_the_words_is_not_an_acceptance() {
        let fake = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../ci/fake-checkers/comment-verified.sh");
        assert!(
            fake.is_file(),
            "the committed fake checker is missing: {}",
            fake.display()
        );
        let envelope = VeriPbEnvelope {
            timeout: Duration::from_secs(10),
            stdout_limit_bytes: 4096,
            stderr_limit_bytes: 4096,
        };
        let result = verify_unsat(
            &fake,
            Path::new("/dev/null"),
            Path::new("/dev/null"),
            envelope,
        );
        let Err(VeriPbRunError::Rejected { status, stdout, .. }) = result else {
            panic!("a checker that REFUSED the proof was accepted: {result:?}");
        };
        assert!(
            stdout.contains("VERIFIED UNSATISFIABLE"),
            "anti-vacuity: the fake must still carry the substring that used to \
             be the whole acceptance test; got {stdout:?}"
        );
        assert!(
            status.success(),
            "anti-vacuity: the fake must still exit 0, or the exit-status half \
             of the contract is what rejected it"
        );
    }

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

    // ------------------------------------------------------------- self-test

    /// The copy in this module must be the SAME battery as the shared one, not
    /// a second one that happens to look similar. `ay-test-support` is a
    /// dev-dependency, so production code here cannot link it; this test is
    /// what makes holding the bytes twice safe. Change either side and it goes
    /// red.
    #[test]
    fn self_test_fixtures_match_the_shared_battery() {
        use ay_test_support::veripb as shared;

        let pairs: [(&str, &str, &str); 6] = [
            (
                "UNSAT_OPB",
                SELF_TEST_UNSAT_OPB,
                shared::SELF_TEST_UNSAT_OPB,
            ),
            (
                "GOOD_UNSAT_PBP",
                SELF_TEST_GOOD_UNSAT_PBP,
                shared::SELF_TEST_GOOD_UNSAT_PBP,
            ),
            (
                "NO_CONCLUSION_PBP",
                SELF_TEST_NO_CONCLUSION_PBP,
                shared::SELF_TEST_NO_CONCLUSION_PBP,
            ),
            ("SAT_OPB", SELF_TEST_SAT_OPB, shared::SELF_TEST_SAT_OPB),
            (
                "FALSE_UNSAT_PBP",
                SELF_TEST_FALSE_UNSAT_PBP,
                shared::SELF_TEST_FALSE_UNSAT_PBP,
            ),
            (
                "GARBAGE_PBP",
                SELF_TEST_GARBAGE_PBP,
                shared::SELF_TEST_GARBAGE_PBP,
            ),
        ];

        for (name, local, expected) in pairs {
            assert_eq!(
                local, expected,
                "SELF_TEST_{name} has drifted from ay_test_support::veripb. \
                 Two batteries that disagree about what a valid refutation \
                 looks like are two different claims about the same checker."
            );
        }
    }

    /// And the shell battery is a third copy, for the same unavoidable reason
    /// (a POSIX `sh` gate cannot link Rust). `scripts/lib/veripb_verdict.sh`
    /// writes each fixture with a single-quoted `printf` whose only escape is
    /// `\n`, so the Rust bytes with newlines re-escaped must appear verbatim in
    /// that file.
    #[test]
    fn self_test_fixtures_match_the_shell_battery() {
        let path = ay_test_support::veripb::pin::repo_root().join("scripts/lib/veripb_verdict.sh");
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));

        for (name, text) in [
            ("UNSAT_OPB", SELF_TEST_UNSAT_OPB),
            ("GOOD_UNSAT_PBP", SELF_TEST_GOOD_UNSAT_PBP),
            ("NO_CONCLUSION_PBP", SELF_TEST_NO_CONCLUSION_PBP),
            ("SAT_OPB", SELF_TEST_SAT_OPB),
            ("FALSE_UNSAT_PBP", SELF_TEST_FALSE_UNSAT_PBP),
            ("GARBAGE_PBP", SELF_TEST_GARBAGE_PBP),
        ] {
            let escaped = text.replace('\n', "\\n");
            assert!(
                source.contains(&escaped),
                "SELF_TEST_{name} does not appear in {}; the shell battery and \
                 the Rust one have drifted apart.\n  looked for: {escaped}",
                path.display()
            );
        }
    }

    /// `/usr/bin/true` and `/usr/bin/false` are the two degenerate checkers the
    /// resolver incident was about: one accepts everything by saying nothing,
    /// the other refuses everything. Neither may pass.
    #[cfg(unix)]
    #[test]
    fn self_test_rejects_the_two_degenerate_binaries() {
        let envelope = VeriPbEnvelope::bounded_default();
        for binary in ["/usr/bin/true", "/usr/bin/false"] {
            let error = self_test(Path::new(binary), envelope)
                .expect_err("a binary that checks nothing must not pass the self-test");
            assert!(
                error.contains(PROBE_GOOD_UNSAT),
                "{binary} should fail at the first probe, not somewhere else: {error}"
            );
        }
    }

    /// The headline for THIS surface. Every committed fake that needs no real
    /// checker to be dangerous is run, and each is rejected.
    ///
    /// ANTI-VACUITY, asserted before the rejection in every case: each fake is
    /// first shown to get PAST the acceptance contract that guards
    /// `certify-unsat` today. For `always-unsat.sh` and `parrot.sh` that is the
    /// strong form — `verify_unsat` returns Ok for them on a genuine refutation,
    /// i.e. the pre-self-test surface would have certified an AY answer against
    /// a binary that checks nothing — so their rejection cannot be coming from
    /// the verdict reader or the exit code. For `silent-exit0.sh` and
    /// `comment-verified.sh` the honest anti-vacuity is narrower and is
    /// asserted as such: they exit 0, so the exit-status half of the contract
    /// is not what rejects them.
    #[cfg(unix)]
    #[test]
    fn self_test_rejects_every_committed_fake_checker() {
        let envelope = VeriPbEnvelope::bounded_default();
        let fakes = ay_test_support::veripb::pin::repo_root().join("ci/fake-checkers");
        let directory = super::self_test_scratch().expect("scratch directory");
        let unsat_opb =
            super::write_fixture(&directory, "unsat.opb", SELF_TEST_UNSAT_OPB).expect("fixture");
        let good_unsat = super::write_fixture(&directory, "good.pbp", SELF_TEST_GOOD_UNSAT_PBP)
            .expect("fixture");

        // (fake, does today's `verify_unsat` ACCEPT it on a valid refutation?)
        let cases: [(&str, bool); 4] = [
            ("always-unsat.sh", true),
            ("parrot.sh", true),
            ("silent-exit0.sh", false),
            ("comment-verified.sh", false),
        ];

        let mut survivors = Vec::new();
        for (fake, accepted_today) in cases {
            let path = fakes.join(fake);
            assert!(
                path.is_file(),
                "committed fake checker is missing: {}",
                path.display()
            );

            let today = verify_unsat(&path, &unsat_opb, &good_unsat, envelope);
            assert_eq!(
                today.is_ok(),
                accepted_today,
                "anti-vacuity: {fake} must {} the acceptance contract that \
                 guards certify-unsat today, or the self-test below is not what \
                 rejects it",
                if accepted_today {
                    "PASS"
                } else {
                    "be caught by"
                }
            );
            if !accepted_today {
                // The narrower anti-vacuity claim for the two that the verdict
                // reader already catches: it is not the exit code doing it.
                let Err(VeriPbRunError::Rejected { status, .. }) = &today else {
                    panic!("{fake} must be REFUSED, not fail to run: {today:?}");
                };
                assert!(
                    status.success(),
                    "anti-vacuity: {fake} must still exit 0, so the exit-status \
                     half of the contract is not what rejected it"
                );
            }

            if self_test(&path, envelope).is_ok() {
                survivors.push(fake);
            }
        }

        let _ = std::fs::remove_dir_all(&directory);
        assert!(
            survivors.is_empty(),
            "{} fake checker(s) passed the certify-unsat self-test and would be \
             trusted to certify AY's answers: {survivors:?}",
            survivors.len()
        );
    }

    /// Which probe catches which fake is part of the contract, not an accident.
    /// A future edit that reordered or dropped `false-unsat` would still leave
    /// the test above green (the fakes would fail some other probe or none at
    /// all), so the attribution is pinned separately.
    #[cfg(unix)]
    #[test]
    fn the_false_unsat_probe_is_what_catches_the_rubber_stamp_and_the_parrot() {
        let envelope = VeriPbEnvelope::bounded_default();
        let fakes = ay_test_support::veripb::pin::repo_root().join("ci/fake-checkers");
        for fake in ["always-unsat.sh", "parrot.sh"] {
            let error = self_test(&fakes.join(fake), envelope)
                .expect_err("a rubber stamp must not pass the self-test");
            assert!(
                error.contains(PROBE_FALSE_UNSAT),
                "{fake} must be caught by `{PROBE_FALSE_UNSAT}` — the only probe \
                 whose proof states something FALSE — and not by anything else: \
                 {error}"
            );
        }
    }

    /// A self-test that no real checker could pass would be worse than none:
    /// every campaign would fail closed and the surface would be unusable. The
    /// real checker is not installed on every host, so the positive control
    /// here is the closest thing that is always available — a stub that answers
    /// the four probes exactly as a sound checker does. It proves the battery
    /// is SATISFIABLE, and it is deliberately a stub rather than a fake: it
    /// discriminates on the fixture it is handed.
    #[cfg(unix)]
    #[test]
    fn a_checker_that_answers_all_four_probes_correctly_passes() {
        use std::os::unix::fs::PermissionsExt;

        let directory = super::self_test_scratch().expect("scratch directory");
        let stub = directory.join("discriminating-stub.sh");
        // Accept exactly the refutation whose formula is UNSAT and whose proof
        // concludes UNSAT; refuse everything else. That is the weakest
        // behaviour that is not a rubber stamp.
        std::fs::write(
            &stub,
            "#!/bin/sh\n\
             grep -q '^-1 x1 >= 0 ;$' \"$1\" || { echo 's NOT VERIFIED'; exit 1; }\n\
             grep -q '^conclusion UNSAT : 4;$' \"$2\" || { echo 's NOT VERIFIED'; exit 1; }\n\
             echo 's VERIFIED UNSATISFIABLE'\n\
             exit 0\n",
        )
        .expect("write stub");
        std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).expect("chmod");

        let report = self_test(&stub, VeriPbEnvelope::bounded_default())
            .expect("the battery must be satisfiable, or it gates nothing usable");
        assert_eq!(report.probes(), SELF_TEST_PROBES);
        // The battery's own overhead — six fixture writes and four bounded
        // spawns — measured on whatever host is running the suite. Run with
        // `--nocapture` to see it. A real checker adds its own time on top, but
        // only on 1- and 2-variable formulas, and only ONCE PER CAMPAIGN.
        println!("veripb self-test overhead against a shell stub: {report}");

        let _ = std::fs::remove_dir_all(&directory);
    }
}
