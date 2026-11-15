// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-mode `-pbo` owes z3's stderr, which is silent for a solved instance.
//!
//! The PB engines announce each improved dual as `c dual N` on stderr — PB
//! competition telemetry, read by nobody in Z3 mode. `cmd_pb::run_z3_compat`
//! captures and translates the competition STDOUT transcript, but that line
//! bypassed it, and whether an engine reached it before the portfolio winner
//! stopped it was a thread race: ~10% of runs on a one-variable instance, and
//! every run on this one, measured on the unfixed binary. The byte-exact leg in
//! the reference comparison caught it only on a host carrying Z3; this
//! test needs no reference, because no z3 release prints that line.

use super::z3_compat_args::{ay_binary, run_program_stdin_with_args};
use ntest::timeout;

/// A fixed 80-variable PB minimization (random-looking covering rows from a
/// fixed LCG) large enough that the core-guided engine reaches its dual report
/// before the portfolio finishes. Optimum 173, as z3 also reports.
fn covering_instance() -> String {
    let mut state: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = |bound: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % bound
    };
    let variables = 80;
    let objective: Vec<String> = (1..=variables)
        .map(|variable| format!("+{} x{variable}", 1 + next(9)))
        .collect();
    let mut opb = format!(
        "* #variable= {variables} #constraint= {variables}\nmin: {} ;\n",
        objective.join(" ")
    );
    for _ in 0..variables {
        let mut chosen: Vec<u64> = Vec::new();
        while chosen.len() < 6 {
            let variable = 1 + next(variables);
            if !chosen.contains(&variable) {
                chosen.push(variable);
            }
        }
        let terms: Vec<String> = chosen
            .iter()
            .map(|variable| format!("+{} x{variable}", 1 + next(4)))
            .collect();
        opb.push_str(&format!("{} >= {} ;\n", terms.join(" "), 4 + next(5)));
    }
    opb
}

#[test]
#[timeout(120_000)]
fn z3_mode_pbo_stderr_carries_no_pb_competition_telemetry() {
    let input = covering_instance();
    for run in 0..3 {
        let output = run_program_stdin_with_args(ay_binary(), &["-pbo"], &input, true);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(0), "run {run}: stderr={stderr}");
        assert_eq!(stdout, "sat\n   173\n", "run {run}: stderr={stderr}");
        assert!(
            stderr.is_empty(),
            "run {run}: Z3-mode -pbo leaked engine output onto stderr, which z3 \
             never prints: {stderr}"
        );
    }
}
