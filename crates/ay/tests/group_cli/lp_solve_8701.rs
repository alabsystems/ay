// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CLI coverage for the first-class LP/MIP public boundary (#8701).

use std::io::Write;
use std::process::Command;

#[test]
fn lp_cli_solves_free_variable_instance() {
    let mut file = tempfile::Builder::new()
        .suffix(".lp")
        .tempfile()
        .expect("temp lp");
    writeln!(
        file,
        "Minimize
 x
Subject To
 lower: x >= -2
Bounds
 x free
End"
    )
    .expect("write lp");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("lp")
        .arg("solve")
        .arg(file.path())
        .output()
        .expect("spawn ay lp solve");

    assert!(
        output.status.success(),
        "ay lp solve should succeed: status={:?} stdout={} stderr={}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("s OPTIMAL"), "stdout={stdout}");
    assert!(stdout.contains("o -2"), "stdout={stdout}");
    assert!(stdout.contains("v x = -2"), "stdout={stdout}");
}
