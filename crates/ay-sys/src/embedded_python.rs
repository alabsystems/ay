// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Running a Python program compiled into a binary, however large it is.
//!
//! Linux refuses to exec a process any one of whose `argv` strings is longer
//! than `MAX_ARG_STRLEN` (32 pages, 131,072 bytes) with `E2BIG`. Binaries
//! that ship `scripts/_oom_guard.py` for use outside a checkout (`ay`'s
//! MaxSAT campaigns, `ay-bisect`'s trial planner) handed it to `python3` as
//! the single string after `-c`, and the script outgrew that bound at
//! eecc804d1 (122,872 -> 152,194 bytes): every embedded lease, plan and
//! watchdog spawn then failed with "Argument list too long".
//!
//! [`embed_program`] passes the source as several `argv` strings of at most
//! [`ARG_CHUNK`] bytes each, after its file name and their count. A fixed
//! bootstrap passed with `-c` joins them, removes them from `sys.argv`, and
//! executes the program in `__main__`, so the program sees exactly what
//! `python3 -c SOURCE ARGS...` showed it: `sys.argv == ["-c", ARGS...]`,
//! `__name__ == "__main__"`, no `__file__`. No temporary file is written and
//! stdin stays the caller's. The whole `argv` stays far inside `ARG_MAX`.

use std::process::Command;

/// The largest piece of the program's source one `argv` string carries: half
/// of `MAX_ARG_STRLEN`, so a piece never nears the per-string bound.
const ARG_CHUNK: usize = 64 * 1024;

/// Reads the file name and the piece count after it, joins the pieces,
/// drops all of them from `sys.argv`, and runs the result as `__main__`'s
/// code.
const BOOTSTRAP: &str = "import sys as _s\n\
_f, _n = _s.argv[1], int(_s.argv[2])\n\
_c = compile(''.join(_s.argv[3:3 + _n]), _f, 'exec')\n\
del _s.argv[1:3 + _n]\n\
del _s, _f, _n\n\
exec(_c)\n";

/// Make `command` (a `python3` invocation with no arguments yet) run
/// `source`, reported as `filename` in tracebacks. Arguments added to
/// `command` afterwards reach the program as `sys.argv[1:]`.
pub fn embed_program(command: &mut Command, filename: &str, source: &str) {
    let pieces = split_at_char_boundaries(source, ARG_CHUNK);
    command
        .arg("-c")
        .arg(BOOTSTRAP)
        .arg(filename)
        .arg(pieces.len().to_string())
        .args(pieces);
}

/// `text` cut into consecutive pieces of at most `max` bytes, each ending on
/// a char boundary (`max` must be at least 4, the longest UTF-8 char).
fn split_at_char_boundaries(text: &str, max: usize) -> Vec<&str> {
    debug_assert!(max >= 4);
    let mut pieces = Vec::new();
    let mut rest = text;
    while !rest.is_empty() {
        let mut end = rest.len().min(max);
        while !rest.is_char_boundary(end) {
            end -= 1;
        }
        let (piece, tail) = rest.split_at(end);
        pieces.push(piece);
        rest = tail;
    }
    pieces
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Linux's `MAX_ARG_STRLEN`.
    const MAX_ARG_STRLEN: usize = 32 * 4096;

    #[test]
    fn the_split_keeps_every_char_whole() {
        let text = "aé€😀b".repeat(7);
        for max in 4..=9 {
            let pieces = split_at_char_boundaries(&text, max);
            assert!(pieces
                .iter()
                .all(|piece| !piece.is_empty() && piece.len() <= max));
            assert_eq!(pieces.concat(), text);
        }
        assert_eq!(split_at_char_boundaries("", 4), Vec::<&str>::new());
    }

    /// A program twice the kernel's per-string bound, which `python3 -c`
    /// cannot even be started with, runs as `__main__` with its own argv,
    /// and no `argv` string of the command nears the bound.
    #[cfg(unix)]
    #[test]
    fn a_program_past_the_per_string_bound_runs_as_main_with_its_own_argv() {
        let padding = format!("# {}\n", "é".repeat(MAX_ARG_STRLEN));
        let source =
            format!("{padding}import sys\nprint(__name__, sys.argv, '__file__' in globals())\n");
        assert!(source.len() > 2 * MAX_ARG_STRLEN);

        let mut command = Command::new("python3");
        embed_program(&mut command, "embedded:probe.py", &source);
        command.arg("lease").arg("--label").arg("x y");
        assert!(command.get_args().all(|arg| arg.len() < MAX_ARG_STRLEN));
        let output = command.output().expect("python3 runs");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).expect("utf-8"),
            "__main__ ['-c', 'lease', '--label', 'x y'] False\n"
        );

        // The per-string bound this module exists for is Linux's; macOS has
        // no 32-page per-string limit and happily execs the oversized `-c`,
        // so the refusal half of the probe only holds where the kernel
        // refuses.
        #[cfg(target_os = "linux")]
        {
            let mut single = Command::new("python3");
            single.arg("-c").arg(&source);
            let refused = single.output().expect_err("one oversized argv string");
            assert_eq!(refused.raw_os_error(), Some(7), "E2BIG");
        }
    }

    /// A traceback names the program by the file name it was given.
    #[cfg(unix)]
    #[test]
    fn a_traceback_names_the_embedded_file() {
        let mut command = Command::new("python3");
        embed_program(&mut command, "embedded:probe.py", "raise SystemExit(3)\n");
        assert_eq!(command.status().expect("python3 runs").code(), Some(3));

        let mut command = Command::new("python3");
        embed_program(&mut command, "embedded:probe.py", "\n\n1 / 0\n");
        let output = command.output().expect("python3 runs");
        let stderr = String::from_utf8(output.stderr).expect("utf-8");
        assert!(
            stderr.contains("File \"embedded:probe.py\", line 3"),
            "{stderr}"
        );
    }
}
