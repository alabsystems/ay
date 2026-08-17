// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::generator::AcceptedClause;
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::io::{Read, Write as IoWrite};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::thread;
use std::time::Duration;
use wait_timeout::ChildExt as _;

const BEGIN: &str = "FP_AUDIT_FRAME_BEGIN_";
const END: &str = "FP_AUDIT_FRAME_END_";
const QUERY_TIMEOUT_MILLIS: u64 = 30_000;
const LANE_TIMEOUT: Duration = Duration::from_mins(2);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ClauseVerdict {
    Valid,
    Invalid,
}

pub(super) struct Oracle {
    path: PathBuf,
}

impl Oracle {
    pub(super) fn resolve() -> Option<Self> {
        resolve_z3_from(
            std::env::var_os("Z3_PATH").as_deref(),
            std::env::var_os("PATH").as_deref(),
            Path::is_file,
        )
        .map(|path| Self { path })
    }

    pub(super) fn path(&self) -> &Path {
        &self.path
    }

    pub(super) fn check_clauses(
        &self,
        clauses: &[AcceptedClause],
    ) -> Result<Vec<ClauseVerdict>, String> {
        if clauses.is_empty() {
            return Err("refusing to run a vacuous Z3 batch".to_string());
        }
        let script = render_script(clauses);
        let mut child = Command::new(&self.path)
            .args(["-in", "-smt2"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|error| format!("could not spawn: {error}"))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| "spawned without piped stdin".to_string())?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| "spawned without piped stdout".to_string())?;
        let stderr = child
            .stderr
            .take()
            .ok_or_else(|| "spawned without piped stderr".to_string())?;

        let writer = thread::spawn(move || write_script(stdin, &script));
        let stdout_reader = thread::spawn(move || read_pipe(stdout));
        let stderr_reader = thread::spawn(move || read_pipe(stderr));
        let status = wait_for_child(&mut child);
        let write_result = join_thread(writer, "stdin writer");
        let stdout = join_thread(stdout_reader, "stdout reader")?;
        let stderr = join_thread(stderr_reader, "stderr reader")?;
        let status = status?;
        write_result?;
        validate_transcript(status.success(), &stdout, &stderr, clauses.len())
    }
}

pub(super) fn differential_required() -> bool {
    std::env::var("Z3_DIFFERENTIAL_REQUIRED")
        .map(|value| is_truthy(&value))
        .unwrap_or(false)
}

fn is_truthy(value: &str) -> bool {
    matches!(
        value.trim().to_ascii_lowercase().as_str(),
        "1" | "true" | "yes" | "on"
    )
}

fn resolve_z3_from(
    configured: Option<&OsStr>,
    path: Option<&OsStr>,
    exists: impl Fn(&Path) -> bool,
) -> Option<PathBuf> {
    if let Some(configured) = configured.filter(|value| !value.is_empty()) {
        let candidate = PathBuf::from(configured);
        if exists(&candidate) {
            return Some(candidate);
        }
    }
    let executable = if cfg!(windows) { "z3.exe" } else { "z3" };
    std::env::split_paths(path?).find_map(|directory| {
        let candidate = directory.join(executable);
        exists(&candidate).then_some(candidate)
    })
}

fn render_script(clauses: &[AcceptedClause]) -> String {
    let mut script = String::new();
    for (index, clause) in clauses.iter().enumerate() {
        writeln!(script, "(echo \"{BEGIN}{index}\")").expect("write to String");
        writeln!(script, "(set-option :timeout {QUERY_TIMEOUT_MILLIS})").expect("write to String");
        for declaration in &clause.declarations {
            writeln!(script, "{declaration}").expect("write to String");
        }
        let disjunction = match clause.literals.as_slice() {
            [literal] => literal.clone(),
            literals => format!("(or {})", literals.join(" ")),
        };
        writeln!(script, "(assert (not {disjunction}))").expect("write to String");
        script.push_str("(check-sat)\n");
        writeln!(script, "(echo \"{END}{index}\")").expect("write to String");
        script.push_str("(reset)\n");
    }
    script
}

fn write_script(mut stdin: impl IoWrite, script: &str) -> Result<(), String> {
    stdin
        .write_all(script.as_bytes())
        .map_err(|error| format!("failed to write batch to stdin: {error}"))
}

fn read_pipe(mut pipe: impl Read) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    pipe.read_to_end(&mut bytes)
        .map_err(|error| format!("failed to read solver pipe: {error}"))?;
    Ok(bytes)
}

fn join_thread<T>(handle: thread::JoinHandle<Result<T, String>>, name: &str) -> Result<T, String> {
    handle.join().map_err(|_| format!("{name} panicked"))?
}

fn wait_for_child(child: &mut Child) -> Result<ExitStatus, String> {
    match child.wait_timeout(LANE_TIMEOUT) {
        Ok(Some(status)) => Ok(status),
        Ok(None) => {
            let kill = child.kill();
            let wait = child.wait();
            let cleanup = match (kill, wait) {
                (Ok(()), Ok(_)) => String::new(),
                (kill, wait) => format!("; kill={kill:?}; wait={wait:?}"),
            };
            Err(format!(
                "timed out after {} seconds{cleanup}",
                LANE_TIMEOUT.as_secs()
            ))
        }
        Err(error) => {
            let kill = child.kill();
            let wait = child.wait();
            Err(format!(
                "OS wait failed: {error}; cleanup kill={kill:?}; wait={wait:?}"
            ))
        }
    }
}

fn validate_transcript(
    success: bool,
    stdout: &[u8],
    stderr: &[u8],
    expected: usize,
) -> Result<Vec<ClauseVerdict>, String> {
    let stdout =
        std::str::from_utf8(stdout).map_err(|error| format!("stdout was not UTF-8: {error}"))?;
    let stderr =
        std::str::from_utf8(stderr).map_err(|error| format!("stderr was not UTF-8: {error}"))?;
    if !success {
        return Err(format!(
            "exited nonzero; stdout={stdout:?}; stderr={stderr:?}"
        ));
    }
    if !stderr.trim().is_empty() {
        return Err(format!("wrote an error to stderr: {stderr}"));
    }
    parse_verdicts(stdout, expected)
}

fn parse_verdicts(stdout: &str, expected: usize) -> Result<Vec<ClauseVerdict>, String> {
    let mut verdicts = Vec::with_capacity(expected);
    let mut current = None;
    for line in stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
    {
        let index = verdicts.len();
        if current.is_none() {
            if line == format!("{BEGIN}{index}") {
                current = Some(None);
                continue;
            }
            return Err(format!("unexpected output before case {index}: {line:?}"));
        }
        if line == format!("{END}{index}") {
            let verdict = current
                .take()
                .flatten()
                .ok_or_else(|| format!("case {index} had no verdict"))?;
            verdicts.push(verdict);
            continue;
        }
        let verdict = match line {
            "unsat" => ClauseVerdict::Valid,
            "sat" => ClauseVerdict::Invalid,
            "unknown" => return Err(format!("case {index} returned unknown")),
            _ => return Err(format!("case {index} emitted unexpected output: {line:?}")),
        };
        if current.replace(Some(verdict)) != Some(None) {
            return Err(format!("case {index} returned more than one verdict"));
        }
    }
    if current.is_some() {
        return Err(format!(
            "case {} was missing its end delimiter",
            verdicts.len()
        ));
    }
    if verdicts.len() != expected {
        return Err(format!(
            "verdict count mismatch: expected {expected}, got {}",
            verdicts.len()
        ));
    }
    Ok(verdicts)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truthy_values_are_explicit() {
        for value in ["1", "TRUE", " yes ", "On"] {
            assert!(is_truthy(value), "{value:?} should be truthy");
        }
        for value in ["", "0", "false", "required", "2"] {
            assert!(!is_truthy(value), "{value:?} should not be truthy");
        }
    }

    #[test]
    fn resolver_prefers_existing_configured_path_then_path() {
        let search = std::env::join_paths([Path::new("first"), Path::new("second")])
            .expect("join test PATH");
        let executable = if cfg!(windows) { "z3.exe" } else { "z3" };
        let configured = Path::new("configured-z3");
        assert_eq!(
            resolve_z3_from(Some(configured.as_os_str()), Some(&search), |candidate| {
                candidate == configured || candidate == Path::new("second").join(executable)
            }),
            Some(configured.to_path_buf())
        );
        assert_eq!(
            resolve_z3_from(Some(OsStr::new("missing")), Some(&search), |candidate| {
                candidate == Path::new("second").join(executable)
            }),
            Some(Path::new("second").join(executable))
        );
    }

    #[test]
    fn parser_requires_one_framed_definite_verdict_per_case() {
        let stdout = concat!(
            "FP_AUDIT_FRAME_BEGIN_0\nunsat\nFP_AUDIT_FRAME_END_0\n",
            "FP_AUDIT_FRAME_BEGIN_1\nsat\nFP_AUDIT_FRAME_END_1\n"
        );
        assert_eq!(
            parse_verdicts(stdout, 2),
            Ok(vec![ClauseVerdict::Valid, ClauseVerdict::Invalid])
        );
        assert!(parse_verdicts("FP_AUDIT_FRAME_BEGIN_0\nunknown\n", 1).is_err());
        assert!(parse_verdicts("FP_AUDIT_FRAME_BEGIN_0\nFP_AUDIT_FRAME_END_0\n", 1).is_err());
        assert!(parse_verdicts("FP_AUDIT_FRAME_BEGIN_0\nsat\n", 1).is_err());
        assert!(parse_verdicts("", 1).is_err());
    }

    #[test]
    fn process_failures_and_stderr_are_rejected() {
        let good = b"FP_AUDIT_FRAME_BEGIN_0\nunsat\nFP_AUDIT_FRAME_END_0\n";
        assert!(validate_transcript(false, good, b"", 1).is_err());
        assert!(validate_transcript(true, good, b"(error bad)\n", 1).is_err());
        assert_eq!(
            validate_transcript(true, good, b"", 1),
            Ok(vec![ClauseVerdict::Valid])
        );
    }
}
