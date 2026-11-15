// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Run process-global state scenarios in a fresh execution of the same test.
//! Selection uses actual libtest arguments, never an environment marker.

use std::io;
use std::process::{Command, Output};

pub(crate) enum Execution {
    Here,
    Reexecuted { exact: String, output: Output },
}

/// Run this test alone on one test thread. Call first in a normal test body;
/// return from that body when this answers false. Do not use on a
/// `#[should_panic]` test: expected failures should be asserted by the parent.
pub fn run_alone(module_path: &str, test: &str) -> io::Result<bool> {
    match execute(module_path, test, |_| {})? {
        Execution::Here => Ok(true),
        Execution::Reexecuted { exact, output } => {
            require_passed(&exact, &output);
            Ok(false)
        }
    }
}

pub(crate) fn execute(
    module_path: &str,
    test: &str,
    configure: impl FnOnce(&mut Command),
) -> io::Result<Execution> {
    let exact = exact_test_name(module_path, test);
    if running_exactly(&exact, std::env::args().skip(1)) {
        return Ok(Execution::Here);
    }
    let mut command = Command::new(std::env::current_exe()?);
    command
        .args(["--exact", &exact, "--nocapture", "--test-threads=1"])
        .stdin(std::process::Stdio::null());
    configure(&mut command);
    if !running_exactly(
        &exact,
        command
            .get_args()
            .map(|arg| arg.to_string_lossy().into_owned()),
    ) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "configured test command is not isolated",
        ));
    }
    let output = command.output()?;
    Ok(Execution::Reexecuted { exact, output })
}

pub(crate) fn require_passed(exact: &str, output: &Output) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "`{exact}` failed when run alone ({}):\n{stdout}{stderr}",
        output.status
    );
    assert!(
        stdout.contains("1 passed"),
        "`{exact}` must actually run in the re-exec:\n{stdout}{stderr}"
    );
}

pub(crate) fn exact_test_name(module_path: &str, test: &str) -> String {
    match module_path.split_once("::") {
        Some((_crate, module)) => format!("{module}::{test}"),
        None => test.to_owned(),
    }
}

pub(crate) fn running_exactly(exact: &str, args: impl IntoIterator<Item = String>) -> bool {
    let mut exact_flag = false;
    let mut single_thread = false;
    let mut selected = false;
    for arg in args {
        match arg.as_str() {
            "--exact" if !exact_flag => exact_flag = true,
            "--test-threads=1" if !single_thread => single_thread = true,
            "--nocapture" | "--ignored" | "--include-ignored" => {}
            value if value == exact && !selected => selected = true,
            _ => return false,
        }
    }
    exact_flag && single_thread && selected
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_self_reexecution_runs_the_case_alone() {
        if !run_alone(
            module_path!(),
            "actual_self_reexecution_runs_the_case_alone",
        )
        .expect("isolate")
        {
            return;
        }
        assert!(running_exactly(
            "isolated_test::tests::actual_self_reexecution_runs_the_case_alone",
            std::env::args().skip(1)
        ));
    }

    #[test]
    fn ambiguous_filters_and_skip_options_are_not_isolation() {
        let exact = "module::case";
        let args = |extra: &[&str]| {
            ["--exact", exact, "--test-threads=1"]
                .into_iter()
                .chain(extra.iter().copied())
                .map(str::to_owned)
                .collect::<Vec<_>>()
        };
        assert!(running_exactly(exact, args(&[])));
        assert!(!running_exactly(exact, args(&["other::case"])));
        assert!(!running_exactly(exact, args(&["--skip", exact])));
        assert!(!running_exactly(exact, args(&["--test-threads=2"])));
    }

    fn refusal(helper: &str) -> String {
        let execution = execute(module_path!(), helper, |_| {}).expect("real child");
        let Execution::Reexecuted { exact, output } = execution else {
            panic!("parent must execute child");
        };
        let panic = std::panic::catch_unwind(|| require_passed(&exact, &output))
            .expect_err("child failure must not pass");
        panic
            .downcast::<String>()
            .map(|message| *message)
            .unwrap_or_default()
    }

    #[test]
    fn real_child_panics_and_exit_failures_are_refused() {
        assert!(refusal("panic_probe").contains("isolated-panic-sentinel"));
        assert!(refusal("exit_probe").contains("19"));
        assert!(refusal("missing_probe").contains("must actually run"));
    }

    // The probes act only under the refusal control's exact re-exec; in a
    // plain suite run they return at once. No `#[ignore]`: disabled tests
    // are banned workspace-wide, and this module already ships the argv
    // discriminator (`running_exactly`) for exactly this selection.
    fn invoked_as_probe(test: &str) -> bool {
        running_exactly(
            &exact_test_name(module_path!(), test),
            std::env::args().skip(1),
        )
    }

    #[test]
    fn panic_probe() {
        if !invoked_as_probe("panic_probe") {
            return;
        }
        panic!("isolated-panic-sentinel");
    }

    #[test]
    fn exit_probe() {
        if !invoked_as_probe("exit_probe") {
            return;
        }
        std::process::exit(19);
    }
}
