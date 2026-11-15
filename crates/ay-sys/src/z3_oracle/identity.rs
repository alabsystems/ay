// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! How one candidate proves it is z3, and how that is read without trusting
//! it: the banner rule, the negative control that refuses an AY drop-in, the
//! reroute-stub signature read without executing the file, and a bounded
//! probe. Where candidates come from, and what a caller gets back, is the
//! parent module's business.

use std::io::Read as _;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// The exact second line of an aterm reroute stub script. A candidate whose
/// second line is this is never executed.
pub const REROUTE_STUB_SIGNATURE: &str = "# atpkg reroute stub v1";

/// The upper bound on each identity probe of one candidate.
pub const PROBE_TIMEOUT: Duration = Duration::from_secs(10);

/// The prefix of the first stdout line of `z3 --version`.
pub const BANNER_PREFIX: &str = "Z3 version ";

/// The most stdout bytes a probe reads; a version banner is one short line.
const PROBE_OUTPUT_LIMIT: u64 = 64 * 1024;

/// The banner line of a completed `--version` run when it identifies z3: exit
/// success and a first stdout line starting [`BANNER_PREFIX`]. A refusing stub
/// (non-zero exit, empty stdout) and any other program are not z3.
pub fn z3_version_banner(success: bool, stdout: &str) -> Option<&str> {
    let banner = stdout.trim_start().lines().next()?.trim_end();
    (success && banner.starts_with(BANNER_PREFIX)).then_some(banner)
}

/// `Z3 version 4.8.12 - 64 bit` -> `(4, 8, 12)`; a missing patch is 0.
pub fn parse_banner_version(banner: &str) -> Option<(u32, u32, u32)> {
    let version = banner
        .split_whitespace()
        .skip_while(|word| *word != "version")
        .nth(1)?;
    let mut parts = version.split('.').map(|part| part.parse::<u32>().ok());
    let major = parts.next()??;
    let minor = parts.next()??;
    Some((major, minor, parts.next().flatten().unwrap_or(0)))
}

/// True when `path`'s second line is [`REROUTE_STUB_SIGNATURE`], read without
/// executing it (an unreadable file is not a stub).
pub fn is_reroute_stub(path: &Path) -> bool {
    let Ok(file) = std::fs::File::open(path) else {
        return false;
    };
    let mut head = Vec::new();
    if file.take(4096).read_to_end(&mut head).is_err() {
        return false;
    }
    head.split(|byte| *byte == b'\n')
        .nth(1)
        .is_some_and(|line| line == REROUTE_STUB_SIGNATURE.as_bytes())
}

/// The identity check: the banner, then the negative control. Returns the
/// banner, or why the candidate is not z3.
pub(super) fn vet(candidate: &Path) -> Result<String, String> {
    if is_reroute_stub(candidate) {
        return Err("aterm reroute stub".to_string());
    }
    let version = probe(candidate, &["--version"])?;
    let Some(banner) = z3_version_banner(version.success, &version.stdout) else {
        return Err(format!(
            "`--version` did not print a Z3 banner (success={}, stdout={:?})",
            version.success,
            first_line(&version.stdout)
        ));
    };
    let control = probe(candidate, &["--z3-mode", "--version"])
        .map_err(|reason| format!("negative control `--z3-mode --version`: {reason}"))?;
    // Any Z3 banner in the control's output refuses, whatever its exit code:
    // real z3 rejects the unknown `--z3-mode` flag without printing one, so a
    // program that prints it there is answering in z3's name.
    if z3_version_banner(true, &control.stdout).is_some() {
        return Err(
            "answers `--z3-mode --version` with a Z3 banner: an AY drop-in, not z3".to_string(),
        );
    }
    Ok(banner.to_string())
}

struct Probed {
    success: bool,
    stdout: String,
}

/// Run `program args`, bounded by [`PROBE_TIMEOUT`], with stdin closed.
fn probe(program: &Path, args: &[&str]) -> Result<Probed, String> {
    let rendered = args.join(" ");
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|error| format!("`{rendered}` could not run: {error}"))?;
    let deadline = Instant::now() + PROBE_TIMEOUT;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(5)),
            waited => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(match waited {
                    Err(error) => format!("`{rendered}` could not be waited on: {error}"),
                    Ok(_) => format!(
                        "`{rendered}` did not answer within {} s",
                        PROBE_TIMEOUT.as_secs()
                    ),
                });
            }
        }
    };
    let mut stdout = Vec::new();
    if let Some(pipe) = child.stdout.take() {
        let _ = pipe.take(PROBE_OUTPUT_LIMIT).read_to_end(&mut stdout);
    }
    Ok(Probed {
        success: status.success(),
        stdout: String::from_utf8_lossy(&stdout).into_owned(),
    })
}

pub(super) fn is_executable(path: &Path) -> bool {
    let Ok(metadata) = std::fs::metadata(path) else {
        return false;
    };
    if metadata.is_dir() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        metadata.is_file()
    }
}

fn first_line(text: &str) -> &str {
    text.trim_start().lines().next().unwrap_or("").trim_end()
}
