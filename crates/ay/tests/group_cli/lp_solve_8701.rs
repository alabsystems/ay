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

/// Review finding (200554215): a SIGTERM while an incumbent block was being
/// written ended the run with a cut-off last block, which the competition
/// wrapper takes as the answer. The block is now finished first.
///
/// The block here (one `v` line per column of a 100000-column model) is far
/// larger than a pipe buffer: the test reads its start, stops reading so
/// that `ay` blocks in the middle of the block, sends SIGTERM, then reads
/// the rest. The last block must be whole, and the run still ends by the
/// signal.
#[cfg(unix)]
#[test]
fn lp_cli_sigterm_during_an_incumbent_block_leaves_the_block_whole() {
    use std::io::Read;
    use std::os::unix::process::ExitStatusExt;
    use std::process::Stdio;

    let n = 100_000;
    let mut text = String::from("NAME BIG\nROWS\n N OBJ\nCOLUMNS\n");
    for i in 0..n {
        text.push_str(&format!("    X{i} OBJ 0\n"));
    }
    text.push_str("BOUNDS\n");
    for i in 0..n {
        text.push_str(&format!(" UP BND X{i} 1\n"));
    }
    text.push_str("ENDATA\n");
    let mut file = tempfile::Builder::new()
        .suffix(".mps")
        .tempfile()
        .expect("temp mps");
    file.write_all(text.as_bytes()).expect("write mps");

    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("lp")
        .arg("solve")
        .arg(file.path())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn ay lp solve");
    let mut stdout = child.stdout.take().expect("stdout");
    let mut head = vec![0u8; 70_000];
    stdout
        .read_exact(&mut head)
        .expect("read the start of the block");
    // `ay` now fills the pipe and blocks inside the same block.
    std::thread::sleep(std::time::Duration::from_millis(500));
    let pid = i32::try_from(child.id()).expect("pid");
    nix::sys::signal::kill(
        nix::unistd::Pid::from_raw(pid),
        nix::sys::signal::Signal::SIGTERM,
    )
    .expect("send SIGTERM");
    let mut rest = Vec::new();
    stdout.read_to_end(&mut rest).expect("read the rest");
    let status = child.wait().expect("wait");
    head.extend_from_slice(&rest);
    let out = String::from_utf8(head).expect("utf8");
    let last_o = out.rfind("\no ").expect("an o line");
    let block = &out[last_o + 1..];
    let v_lines = block.lines().filter(|l| l.starts_with("v ")).count();
    assert_eq!(v_lines, n, "cut-off block: {} bytes", block.len());
    assert!(block.ends_with(&format!("v X{} = 0\nc solution end {n}\n", n - 1)));
    assert_eq!(status.signal(), Some(libc_sigterm()), "{status:?}");
}

#[cfg(unix)]
fn libc_sigterm() -> i32 {
    nix::sys::signal::Signal::SIGTERM as i32
}
