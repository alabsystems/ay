// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! `criterion_main!` for AY's `harness = false` bench targets, accepting the
//! libtest arguments `cargo test -- …` forwards to every target it runs.
//!
//! Cargo hands everything after `--` to EVERY target, benches included.
//! Criterion 0.5 parses the process arguments with a clap command that knows
//! only its own options, so a libtest option such as `--test-threads=1` makes
//! it exit 2 (`error: unexpected argument '--test-threads' found`) before any
//! routine runs: `cargo test --all-targets -- --test-threads=1` is red on every
//! Criterion target while printing no test line. Criterion reads the arguments
//! from the process itself, exposes no way to hand it a different list, and
//! reaches its test mode only through that parse, so the normalized list is
//! delivered the one way Criterion can see it: the target re-executes itself
//! with that list before Criterion starts.
//!
//! `normalize_libtest_args` is the whole policy. Every libtest option (the
//! set `library/test/src/cli.rs` defines) falls in exactly one class:
//!
//! * **Understood by Criterion with libtest's meaning** — forwarded unchanged:
//!   `--test`, `--bench`, `--list`, `--ignored`, `--exact`, `--nocapture`,
//!   `--show-output`, `--color`, `--format pretty|terse`, `--help`, and the
//!   positional filter.
//! * **Same option, other spelling** — rewritten: `-q` becomes `--quiet`.
//! * **Cannot change which routine runs or whether it passes** — dropped:
//!   `--test-threads N` (Criterion runs routines one at a time, which any
//!   thread count admits), `--report-time`, `--shuffle`, `--shuffle-seed N`,
//!   `--force-run-in-process` (Criterion always runs in process), `--fail-fast`
//!   (a failing routine panics out of `main`), `--exclude-should-panic` and
//!   `--include-ignored` (no Criterion routine is `should_panic` or ignored),
//!   `--no-capture` (Criterion ignores capture), `--logfile PATH`,
//!   `-Z unstable-options`, and `--format json|junit` (Criterion reports as
//!   text; the exit status still carries the verdict).
//! * **Narrows the selection in a way Criterion cannot express** — dropped, so
//!   MORE routines run, never fewer: `--skip FILTER`. Running a routine the
//!   caller meant to skip can add a failure; it can never hide one.
//! * **Adds a failure condition Criterion cannot enforce** — NOT dropped:
//!   `--ensure-time` reaches Criterion, which refuses it. Dropping it would turn
//!   a run the caller asked to fail on slowness into a pass.
//!
//! An option whose value is missing, or is not a value libtest itself accepts,
//! is forwarded unchanged, so Criterion refuses it exactly as it did before.
//! Everything after a bare `--` is forwarded unchanged. Nothing here makes a
//! failing routine pass: each routine still runs in Criterion's own test mode,
//! and its panic still fails the process.

use std::env;
use std::ffi::OsString;
use std::io;
use std::process::Command;

#[cfg(test)]
mod tests;

/// The argument list Criterion receives, and how it differs from the list the
/// process was given.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct NormalizedArgs {
    /// Arguments handed to Criterion, in their original order.
    forwarded: Vec<OsString>,
    /// Libtest arguments taken out, in their original order; an option given
    /// with a separate value contributes both tokens.
    dropped: Vec<OsString>,
    /// Libtest spellings replaced by Criterion's spelling of the same option,
    /// as `(given, forwarded)` pairs.
    rewritten: Vec<(OsString, OsString)>,
}

impl NormalizedArgs {
    /// Whether Criterion would receive exactly the arguments it was given.
    #[must_use]
    fn is_identity(&self) -> bool {
        self.dropped.is_empty() && self.rewritten.is_empty()
    }

    /// One line saying what changed, for the target's stderr.
    #[must_use]
    fn notice(&self, program: &str) -> String {
        let mut changes: Vec<String> = Vec::new();
        if !self.dropped.is_empty() {
            changes.push(format!("dropped {}", render(&self.dropped)));
        }
        for (given, forwarded) in &self.rewritten {
            changes.push(format!(
                "rewrote {} as {}",
                given.to_string_lossy(),
                forwarded.to_string_lossy()
            ));
        }
        format!(
            "{program}: libtest arguments Criterion does not take: {}; running Criterion with [{}]",
            changes.join("; "),
            render(&self.forwarded)
        )
    }
}

fn render(args: &[OsString]) -> String {
    args.iter()
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Which values a dropped libtest option may carry. A value outside this set
/// is one libtest itself refuses, so the option is forwarded for Criterion to
/// refuse as well.
#[derive(Clone, Copy)]
enum Accepts {
    /// Any string (`--skip`, `--logfile`).
    Anything,
    /// `usize` other than zero (`--test-threads`; libtest refuses `0`).
    PositiveCount,
    /// `u64` (`--shuffle-seed`).
    Seed,
    /// Exactly `unstable-options` (`-Z`).
    UnstableOptions,
    /// `json` or `junit` (`--format`; `pretty` and `terse` are Criterion's too).
    MachineFormat,
}

impl Accepts {
    fn admits(self, value: &str) -> bool {
        match self {
            Self::Anything => true,
            Self::PositiveCount => value.parse::<usize>().is_ok_and(|count| count > 0),
            Self::Seed => value.parse::<u64>().is_ok(),
            Self::UnstableOptions => value == "unstable-options",
            Self::MachineFormat => matches!(value, "json" | "junit"),
        }
    }
}

/// Libtest flags that take no value and cannot change a Criterion verdict.
const DROPPED_FLAGS: [&str; 7] = [
    "--exclude-should-panic",
    "--fail-fast",
    "--force-run-in-process",
    "--include-ignored",
    "--no-capture",
    "--report-time",
    "--shuffle",
];

/// Libtest options that take a value, as `--name value` or `--name=value`.
const DROPPED_LONG_OPTIONS: [(&str, Accepts); 5] = [
    ("--format", Accepts::MachineFormat),
    ("--logfile", Accepts::Anything),
    ("--shuffle-seed", Accepts::Seed),
    ("--skip", Accepts::Anything),
    ("--test-threads", Accepts::PositiveCount),
];

/// Libtest's `-Z`, as `-Z value` or `-Zvalue`.
const UNSTABLE_SHORT_OPTION: &str = "-Z";

/// Libtest's short `--quiet`; Criterion has only the long spelling.
const REWRITTEN: [(&str, &str); 1] = [("-q", "--quiet")];

/// How a token that names a valued option carries its value.
enum ValuedOption<'a> {
    /// The value is the next token.
    Separate(Accepts),
    /// The value is attached (`--name=value`, `-Zvalue`).
    Attached(Accepts, &'a str),
}

fn valued_option(text: &str) -> Option<ValuedOption<'_>> {
    for (name, accepts) in DROPPED_LONG_OPTIONS {
        if text == name {
            return Some(ValuedOption::Separate(accepts));
        }
        if let Some(value) = text
            .strip_prefix(name)
            .and_then(|rest| rest.strip_prefix('='))
        {
            return Some(ValuedOption::Attached(accepts, value));
        }
    }
    match text.strip_prefix(UNSTABLE_SHORT_OPTION) {
        Some("") => Some(ValuedOption::Separate(Accepts::UnstableOptions)),
        Some(value) => Some(ValuedOption::Attached(Accepts::UnstableOptions, value)),
        None => None,
    }
}

/// Split `args` (without the program name) into what Criterion receives and
/// what was removed or respelled. The crate documentation states the policy.
///
/// The result is a fixed point: normalizing `forwarded` again changes nothing.
#[must_use]
fn normalize_libtest_args<I>(args: I) -> NormalizedArgs
where
    I: IntoIterator<Item = OsString>,
{
    let mut normalized = NormalizedArgs::default();
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        let Some(text) = arg.to_str() else {
            normalized.forwarded.push(arg);
            continue;
        };
        if text == "--" {
            normalized.forwarded.push(arg);
            normalized.forwarded.extend(args);
            break;
        }
        if let Some((_, spelling)) = REWRITTEN.iter().find(|(given, _)| *given == text) {
            let spelling = OsString::from(*spelling);
            normalized.forwarded.push(spelling.clone());
            normalized.rewritten.push((arg, spelling));
            continue;
        }
        if DROPPED_FLAGS.contains(&text) {
            normalized.dropped.push(arg);
            continue;
        }
        match valued_option(text) {
            Some(ValuedOption::Attached(accepts, value)) => {
                if accepts.admits(value) {
                    normalized.dropped.push(arg);
                } else {
                    normalized.forwarded.push(arg);
                }
            }
            Some(ValuedOption::Separate(accepts)) => match args.next() {
                Some(value) if value.to_str().is_some_and(|value| accepts.admits(value)) => {
                    normalized.dropped.push(arg);
                    normalized.dropped.push(value);
                }
                Some(value) => {
                    normalized.forwarded.push(arg);
                    normalized.forwarded.push(value);
                }
                None => normalized.forwarded.push(arg),
            },
            None => normalized.forwarded.push(arg),
        }
    }
    normalized
}

/// Return if this process's arguments are already Criterion's; otherwise
/// replace the process with this same executable run on the normalized
/// arguments, so Criterion's own parse sees them. Never returns in that case:
/// if the re-execution cannot start, this panics and the target fails.
pub fn reexec_without_libtest_args() {
    let mut args = env::args_os();
    let Some(program) = args.next() else {
        return;
    };
    let normalized = normalize_libtest_args(args);
    if normalized.is_identity() {
        return;
    }
    // The re-executed process normalizes again and must find nothing to do;
    // a list that still changed would re-execute forever instead of failing.
    assert!(
        normalize_libtest_args(normalized.forwarded.iter().cloned()).is_identity(),
        "libtest argument normalization is not a fixed point for {:?}",
        normalized.forwarded
    );
    let name = program.to_string_lossy().into_owned();
    eprintln!("{}", normalized.notice(&name));
    let error = reexec(program, &normalized.forwarded);
    panic!("{name}: cannot re-execute with the normalized arguments: {error}");
}

#[cfg(unix)]
fn reexec(program: OsString, args: &[OsString]) -> io::Error {
    use std::os::unix::process::CommandExt as _;
    match env::current_exe() {
        Ok(executable) => Command::new(executable).arg0(program).args(args).exec(),
        Err(error) => error,
    }
}

#[cfg(not(unix))]
fn reexec(_program: OsString, args: &[OsString]) -> io::Error {
    match env::current_exe().and_then(|executable| Command::new(executable).args(args).status()) {
        Ok(status) => std::process::exit(status.code().unwrap_or(101)),
        Err(error) => error,
    }
}

/// Drop-in replacement for `criterion::criterion_main!`: the same `main`,
/// preceded by [`reexec_without_libtest_args`]. The invoking crate must depend
/// on `criterion` under that name, as every Criterion bench already does.
#[macro_export]
macro_rules! criterion_main {
    ( $( $group:path ),+ $(,)? ) => {
        fn main() {
            $crate::reexec_without_libtest_args();
            $( $group(); )+
            ::criterion::Criterion::default()
                .configure_from_args()
                .final_summary();
        }
    };
}
