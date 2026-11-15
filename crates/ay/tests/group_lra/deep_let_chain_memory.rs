// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A body-position chain of nested `let`s elaborates in memory linear in its
//! depth, so an incremental run keeps answering after it.
//!
//! Every file of the 2025 incremental `QF_LRA/hybrid_networks` selection
//! asserts 8,550-deep chains of the shape `(let ((d0 ..)) (let ((d1 ..)) ..))`.
//! The public-sort pass cloned its whole binder environment once per level and
//! held every clone alive down its recursion — `O(d²)` memory (4.2 GB RSS for
//! 8,000 levels) — so at `--memory 3000` the allocator ceiling ended each run
//! right after its first `check-sat`. Because a verdict had already been
//! printed, that exit was silent and left with code 124, which read as a
//! timeout after 0.6-1.0 s. At a 256 MB budget a 6,000-deep chain reproduces
//! it: the pre-fix binary answers the first `check-sat` and exits 124.

use std::fmt::Write as _;
use std::process::Command;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

const DEPTH: usize = 6_000;

/// `sat`, then a `DEPTH`-deep chain whose body `d_last < y < x` is
/// unsatisfiable (`d_last = x + DEPTH`), then `sat` again after the pop.
fn deep_chain_script() -> String {
    let mut script = String::from(
        "(set-logic QF_LRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n\
         (push 1)\n(assert (< x y))\n(check-sat)\n(pop 1)\n(push 1)\n(assert ",
    );
    for level in 0..DEPTH {
        let previous = if level == 0 {
            "x".to_string()
        } else {
            format!("d{}", level - 1)
        };
        let _ = write!(script, "(let ((d{level} (+ {previous} 1.0))) ");
    }
    let _ = write!(script, "(and (< d{} y) (< y x))", DEPTH - 1);
    script.push_str(&")".repeat(DEPTH));
    script.push_str(")\n(check-sat)\n(pop 1)\n(check-sat)\n");
    script
}

fn run_incremental(extra: &[&str]) -> (Option<i32>, Vec<String>, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(extra)
        .args(["--memory", "256", "-T:20", "--incremental"])
        .output_timeout_with_stdin(deep_chain_script().as_bytes(), DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay --incremental");
    let answers = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect();
    (
        output.status.code(),
        answers,
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn deep_let_chain_keeps_the_incremental_run_answering_under_a_small_memory_budget() {
    for posture in [&["--z3-mode"][..], &[][..]] {
        let (code, answers, stderr) = run_incremental(posture);
        assert_eq!(
            answers,
            ["sat", "unsat", "sat"],
            "posture {posture:?}: every check-sat answered (exit {code:?}); stderr:\n{stderr}"
        );
        assert_eq!(code, Some(0), "posture {posture:?}; stderr:\n{stderr}");
    }
}
