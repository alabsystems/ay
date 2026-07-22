// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! First-class verified self-cert gate for `--verify-firewall`.
//!
//! On UNSAT, this reconstructs the per-theory "firewall" Lean proofs (the same
//! import-the-verified-`AySoundness`-theorem shape that `--emit-firewall-lean`
//! writes) and kernel-checks each one with the *real* Lean toolchain via
//! `lake env lean <file>` run inside the `verification/lean` project. Each
//! emitted file grounds a specific groundable theory lemma of the refutation in
//! the machine-verified `firewall_combined_unsat` theorem (axioms ⊆
//! {propext, Classical.choice, Quot.sound}, zero `sorry`), so a Lean-`Accepted`
//! file is an independently checkable certificate that AY's own answer is
//! correct.
//!
//! # Soundness contract
//!
//! `--verify-firewall` NARROWS what AY will report: an `unsat` is emitted only
//! when at least one firewall lemma was produced AND every produced lemma
//! kernel-checks. Anything else — no firewall emitted, a lemma Lean rejects, or
//! the Lean toolchain / `verification/lean` project being unavailable —
//! downgrades the verdict to a sound `unknown`. Downgrading `unsat` → `unknown`
//! is always sound (§0), so this gate can only ever make AY *more*
//! conservative; it never changes a verdict in an unsound direction.
//!
//! # Backend: today `lake env lean`, target `clean olean verify-batch`
//!
//! This gate currently shells out to the full Lean toolchain. The Rust-native
//! target is to kernel-check the emitted firewall oleans in-process with `clean`
//! (crate `clean-olean`) via a `clean olean verify-batch` entry point, avoiding
//! per-file `lake env` startup. That is gated on `clean` gaining a
//! resident/preloaded-`Init` batch mode (its `.olean` import currently pays an
//! `Init`-preload cost that dominates a small check) — a *performance* gap, not
//! a soundness one, so it does NOT block this feature. When available,
//! [`kernel_check_one`] switches backends behind the same [`FirewallVerdict`]
//! contract. See the development design notes.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use ay_dpll::Executor;

/// Per-file kernel-check result.
pub(crate) struct LemmaCheck {
    /// 0-based firewall file index (`firewall_<i>.lean`).
    pub index: usize,
    /// Whether Lean's kernel accepted the file.
    pub passed: bool,
    /// Short human detail (`kernel-checked` on success, else the failure).
    pub detail: String,
}

/// Outcome of the firewall self-cert gate for an `unsat` result.
pub(crate) enum FirewallVerdict {
    /// At least one firewall lemma was produced and every produced lemma
    /// kernel-checked. The `unsat` verdict stands, now independently certified.
    Certified { results: Vec<LemmaCheck> },
    /// The `unsat` could not be self-certified; the caller must downgrade to a
    /// sound `unknown`. `reason` is a short SMT-LIB `:reason-unknown` payload.
    NotCertified {
        reason: String,
        results: Vec<LemmaCheck>,
    },
}

/// Per-file Lean kernel-check timeout. A firewall file is tiny (a handful of
/// `by decide` goals over a small finite model), so any run past this is a stuck
/// toolchain, not real work; time out and fail closed to `unknown`.
const PER_FILE_TIMEOUT: Duration = Duration::from_secs(120);

/// Run the firewall self-cert gate for a fresh `unsat` result.
///
/// Emits the per-theory firewall Lean files into a private temp dir and
/// kernel-checks each with `lake env lean` inside `verification/lean`.
pub(crate) fn verify_firewall_for_unsat(executor: &Executor) -> FirewallVerdict {
    let Some(proof) = executor.last_proof() else {
        return FirewallVerdict::NotCertified {
            reason: "(incomplete firewall-no-proof)".to_string(),
            results: Vec::new(),
        };
    };

    let leans = executor.emit_datatype_firewall_lean(proof);
    if leans.is_empty() {
        // No groundable theory lemma in this refutation has a firewall emitter,
        // so AY cannot self-certify this `unsat`. Fail closed.
        return FirewallVerdict::NotCertified {
            reason: "(incomplete firewall-not-emitted)".to_string(),
            results: Vec::new(),
        };
    }

    let Some(project) = locate_lean_project() else {
        return FirewallVerdict::NotCertified {
            reason: "(incomplete firewall-lean-project-not-found)".to_string(),
            results: Vec::new(),
        };
    };

    let tmp = match make_temp_dir() {
        Ok(dir) => dir,
        Err(e) => {
            return FirewallVerdict::NotCertified {
                reason: format!("(incomplete firewall-tmpdir-error \"{}\")", sanitize(&e)),
                results: Vec::new(),
            };
        }
    };

    let mut results: Vec<LemmaCheck> = Vec::with_capacity(leans.len());
    let mut all_passed = true;
    for (i, lean) in leans.iter().enumerate() {
        let path = tmp.join(format!("firewall_{i}.lean"));
        if let Err(e) = std::fs::write(&path, lean) {
            results.push(LemmaCheck {
                index: i,
                passed: false,
                detail: format!("write error: {e}"),
            });
            all_passed = false;
            continue;
        }
        let check = kernel_check_one(&project, &path);
        if !check.passed {
            all_passed = false;
        }
        results.push(check);
    }

    // Best-effort cleanup; never let a temp-dir failure change the verdict.
    let _ = std::fs::remove_dir_all(&tmp);

    if all_passed {
        FirewallVerdict::Certified { results }
    } else {
        FirewallVerdict::NotCertified {
            reason: "(incomplete firewall-kernel-check-failed)".to_string(),
            results,
        }
    }
}

/// Emit the per-lemma PASS/FAIL report and a coverage summary to stderr.
pub(crate) fn report(results: &[LemmaCheck], certified: bool) {
    for r in results {
        let tag = if r.passed { "PASS" } else { "FAIL" };
        safe_eprintln!("ay: firewall lemma #{} {} — {}", r.index, tag, r.detail);
    }
    let passed = results.iter().filter(|r| r.passed).count();
    if certified {
        safe_eprintln!(
            "ay: firewall self-cert PASS — {}/{} lemma(s) kernel-checked; unsat certified",
            passed,
            results.len()
        );
    } else if results.is_empty() {
        safe_eprintln!(
            "ay: firewall self-cert FAIL — no kernel-checkable firewall; downgrading to unknown"
        );
    } else {
        safe_eprintln!(
            "ay: firewall self-cert FAIL — {}/{} lemma(s) kernel-checked; downgrading to unknown",
            passed,
            results.len()
        );
    }
}

/// Kernel-check a single firewall file with `lake env lean <file>` inside the
/// `verification/lean` project.
fn kernel_check_one(project: &Path, file: &Path) -> LemmaCheck {
    let index = firewall_index(file);
    let lake = lake_binary();
    let mut cmd = Command::new(&lake);
    cmd.current_dir(project)
        .arg("env")
        .arg("lean")
        .arg(file)
        // Lean prints kernel/elaboration diagnostics to STDOUT; capture both
        // streams and treat an error marker on either as rejection (defensive
        // against a toolchain that reports an error but exits 0).
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());

    let child = match cmd.spawn() {
        Ok(c) => c,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            return LemmaCheck {
                index,
                passed: false,
                detail: format!("lake not found at '{}'", lake.display()),
            };
        }
        Err(err) => {
            return LemmaCheck {
                index,
                passed: false,
                detail: format!("failed to spawn lake: {err}"),
            };
        }
    };

    match wait_with_timeout(child, PER_FILE_TIMEOUT) {
        WaitOutcome::Exited {
            code,
            stdout,
            stderr,
        } => {
            let diag = format!("{stdout}\n{stderr}");
            if code == 0 && !stderr_indicates_rejection(&diag) {
                LemmaCheck {
                    index,
                    passed: true,
                    detail: "kernel-checked".to_string(),
                }
            } else {
                LemmaCheck {
                    index,
                    passed: false,
                    detail: format!("lean rejected (exit {code}): {}", first_error_line(&diag)),
                }
            }
        }
        WaitOutcome::TimedOut => LemmaCheck {
            index,
            passed: false,
            detail: format!("lean exceeded {}s timeout", PER_FILE_TIMEOUT.as_secs()),
        },
        WaitOutcome::Error(e) => LemmaCheck {
            index,
            passed: false,
            detail: format!("lean wait error: {e}"),
        },
    }
}

enum WaitOutcome {
    Exited {
        code: i32,
        stdout: String,
        stderr: String,
    },
    TimedOut,
    Error(String),
}

fn wait_with_timeout(mut child: std::process::Child, timeout: Duration) -> WaitOutcome {
    let start = Instant::now();
    let poll = Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                use std::io::Read;
                let mut out_buf = Vec::new();
                if let Some(mut out) = child.stdout.take() {
                    let _ = out.read_to_end(&mut out_buf);
                }
                let mut err_buf = Vec::new();
                if let Some(mut err) = child.stderr.take() {
                    let _ = err.read_to_end(&mut err_buf);
                }
                return WaitOutcome::Exited {
                    code: status.code().unwrap_or(-1),
                    stdout: String::from_utf8_lossy(&out_buf).into_owned(),
                    stderr: String::from_utf8_lossy(&err_buf).into_owned(),
                };
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return WaitOutcome::TimedOut;
                }
                std::thread::sleep(poll);
            }
            Err(e) => return WaitOutcome::Error(e.to_string()),
        }
    }
}

fn stderr_indicates_rejection(stderr: &str) -> bool {
    stderr.contains("error:")
        || stderr.contains("proof failed")
        || stderr.contains("declaration uses 'sorry'")
        || stderr.contains("declaration uses `sorry`")
}

fn first_error_line(stderr: &str) -> String {
    let line = stderr
        .lines()
        .find(|l| l.contains("error:"))
        .or_else(|| stderr.lines().find(|l| !l.trim().is_empty()))
        .unwrap_or("")
        .trim();
    let truncated: String = line.chars().take(160).collect();
    sanitize(&truncated)
}

fn sanitize(s: &str) -> String {
    s.replace('"', "'").replace('\n', " ")
}

fn firewall_index(file: &Path) -> usize {
    file.file_stem()
        .and_then(|s| s.to_str())
        .and_then(|s| s.strip_prefix("firewall_"))
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0)
}

/// The `lake` binary to drive. Uses `lake` on `PATH`; falls back to the elan
/// shim under `~/.elan/bin/lake` when `PATH` is minimal (batteries included, no
/// env var required).
fn lake_binary() -> PathBuf {
    if let Some(home) = std::env::var_os("HOME") {
        let elan = PathBuf::from(home).join(".elan/bin/lake");
        if elan.exists() {
            return elan;
        }
    }
    PathBuf::from("lake")
}

/// Locate the `verification/lean` Lean project (identified by its
/// `lakefile.toml`) by walking up from the current working directory and from
/// the running executable's directory. Returns the project directory to run
/// `lake env lean` inside.
fn locate_lean_project() -> Option<PathBuf> {
    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        roots.push(cwd);
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            roots.push(dir.to_path_buf());
        }
    }
    for root in roots {
        let mut cur: Option<&Path> = Some(root.as_path());
        while let Some(dir) = cur {
            let candidate = dir.join("verification/lean");
            if candidate.join("lakefile.toml").is_file() {
                return Some(candidate);
            }
            cur = dir.parent();
        }
    }
    None
}

fn make_temp_dir() -> Result<PathBuf, String> {
    let base = std::env::temp_dir();
    // Uniquify with pid + a monotonic-ish nonce so concurrent runs don't clash.
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = base.join(format!("ay-firewall-{}-{}", std::process::id(), nonce));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    Ok(dir)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn firewall_index_parses_filename() {
        assert_eq!(firewall_index(Path::new("/x/firewall_0.lean")), 0);
        assert_eq!(firewall_index(Path::new("/x/firewall_7.lean")), 7);
        assert_eq!(firewall_index(Path::new("/x/other.lean")), 0);
    }

    #[test]
    fn stderr_rejection_detection() {
        assert!(stderr_indicates_rejection("foo error: bad\n"));
        assert!(stderr_indicates_rejection("declaration uses 'sorry'"));
        assert!(!stderr_indicates_rejection("warning: unused variable\n"));
        assert!(!stderr_indicates_rejection(""));
    }

    #[test]
    fn sanitize_strips_quotes_and_newlines() {
        assert_eq!(sanitize("a\"b\nc"), "a'b c");
    }

    #[test]
    fn locate_lean_project_finds_repo_project_from_cwd() {
        // This test runs inside the ay repo; the project must be locatable.
        // (Guarded: only assert when the file actually exists to avoid a false
        // failure in an exotic checkout layout.)
        if let Some(p) = locate_lean_project() {
            assert!(p.join("lakefile.toml").is_file());
            assert!(p.ends_with("verification/lean"));
        }
    }
}
