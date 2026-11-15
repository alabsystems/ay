// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native stopped-exec component, packaged alongside the benchmark CLI.
//! This enforces a local launch barrier, not shared-machine admission.

#![forbid(unsafe_code)]

#[cfg(unix)]
fn run() -> Result<(), Box<dyn std::error::Error>> {
    use nix::sys::resource::{getrlimit, setrlimit, Resource};
    use nix::sys::signal::{raise, Signal};
    use nix::unistd::{execvp, getpgrp, getpid, getppid};
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt as _;

    let parent = getppid();
    if getpgrp() != getpid() || parent.as_raw() <= 0 {
        return Err("stopped-exec requires its original parent and isolated group".into());
    }
    let mut arguments = std::env::args_os().skip(1);
    let first = arguments.next().ok_or("missing stopped-exec delimiter")?;
    if first == "--fsize-bytes" {
        let value = arguments.next().ok_or("missing file limit")?;
        let text = value.to_str().ok_or("invalid file limit")?;
        if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err("invalid file limit".into());
        }
        let bytes: u64 = text.parse()?;
        if bytes == 0 {
            return Err("file limit must be positive".into());
        }
        let (soft, hard) = getrlimit(Resource::RLIMIT_FSIZE)?;
        let cap = bytes.min(soft).min(hard);
        setrlimit(Resource::RLIMIT_FSIZE, cap, cap)?;
        if arguments.next().as_deref() != Some(std::ffi::OsStr::new("--")) {
            return Err("missing stopped-exec delimiter".into());
        }
    } else if first != "--" {
        return Err("invalid stopped-exec arguments".into());
    }
    let command = arguments
        .map(|argument| CString::new(argument.as_bytes()))
        .collect::<Result<Vec<_>, _>>()?;
    let executable = command.first().ok_or("missing stopped-exec target")?;
    // Command::spawn has completed the helper's exec handshake. Stopping here
    // therefore cannot deadlock the parent's spawn error pipe, and none of the
    // target's instructions have run. Only the actual Child owner may resume it.
    raise(Signal::SIGSTOP)?;
    if getppid() != parent {
        return Err("stopped-exec original parent was lost".into());
    }
    match execvp(executable, &command) {
        Err(error) => Err(error.into()),
        Ok(never) => match never {},
    }
}

fn main() -> std::process::ExitCode {
    #[cfg(unix)]
    {
        match run() {
            Ok(()) => std::process::ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("ay-bench-resource: {error}");
                std::process::ExitCode::FAILURE
            }
        }
    }
    #[cfg(not(unix))]
    {
        eprintln!("ay-bench-resource: stopped execution requires POSIX process groups");
        std::process::ExitCode::FAILURE
    }
}
