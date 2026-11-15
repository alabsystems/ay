// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CLI optimization and input dispatch against the current genuine Z3 oracle.
use super::z3_compat_args::{ay_binary, run_program_stdin_with_args, write_temp};
use ntest::timeout;
use std::process::Command;

#[test]
#[timeout(30_000)]
fn z3_optimization_stdin_modes_match_reference() {
    let z3 = ay_test_support::z3::require_z3("z3_optimization_stdin_modes_match_reference").path();
    for (flag, input) in [
        ("-wcnf", "p wcnf 1 1 2\n1 1 0\n"),
        (
            "-pbo",
            "* #variable= 1 #constraint= 1\nmin: +1 x1;\n+1 x1 >= 1;\n",
        ),
        ("-lp", "minimize\nx\nsubject to\nx >= 2\nend\n"),
    ] {
        let expected = run_program_stdin_with_args(z3, &[flag], input, false);
        let actual = run_program_stdin_with_args(ay_binary(), &[flag], input, true);
        assert_eq!(actual.status.code(), expected.status.code(), "{flag}");
        assert_eq!(actual.stdout, expected.stdout, "{flag} stdout");
        assert_eq!(actual.stderr, expected.stderr, "{flag} stderr");
    }
}

#[test]
#[timeout(30_000)]
fn z3_opb_extension_dispatch_matches_reference() {
    let z3 = ay_test_support::z3::require_z3("z3_opb_extension_dispatch_matches_reference").path();
    let input = "* #variable= 1 #constraint= 1\nmin: +1 x1;\n+1 x1 >= 1;\n";
    let (path, _cleanup) = write_temp(input, "opb");
    let expected = Command::new(z3).arg(&path).output().expect("spawn z3 OPB");
    let actual = Command::new(ay_binary())
        .arg(&path)
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .output()
        .expect("spawn ay OPB");
    assert_eq!(actual.status.code(), expected.status.code());
    assert_eq!(actual.stdout, expected.stdout);
    assert_eq!(actual.stderr, expected.stderr);
}
