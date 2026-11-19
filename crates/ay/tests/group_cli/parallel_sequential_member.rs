// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay solve <cnf> --parallel N` races the sequential default route beside
//! the portfolio (2026-11-12).
//!
//! The portfolio workers do not look for the structure the sequential route
//! detects, so on the SAT Competition 2026 parallel sample `--parallel 8`
//! timed out on pigeonhole-shaped instances that one sequential thread
//! refutes in a fraction of a second. Without a proof to write, one of the N
//! threads now runs the sequential route; these tests hold the two properties
//! that matter: the route's answer arrives under `--parallel`, and the race
//! prints one verdict.

use crate::spawn::OutputTimeout;
use ntest::timeout;
use std::fmt::Write as _;
use std::io::Write as _;
use std::process::Command;
use std::time::Duration;

/// The stderr note of a run answered by its sequential member.
const SEQUENTIAL_MEMBER_ANSWER: &str = "c parallel: answer from the sequential-route member";

fn ay_command() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    clear_sat_env(&mut command);
    command
}

fn clear_sat_env(command: &mut Command) {
    for name in [
        "AY_SAT_VARIANT",
        "AY_INTERNAL_SATCOMP_WRAPPER",
        "AY_SAT_PROFILE_ID",
        "AY_SAT_COMPETITION_PROFILE",
        "AY_SAT_TRACK",
        "AY_SAT_AI_CLASS",
        "AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT",
    ] {
        command.env_remove(name);
    }
}

/// The CPUs this test process may run on, from `Cpus_allowed_list` of
/// `/proc/self/status` (`0-3,8,10-11`), in order.
#[cfg(target_os = "linux")]
fn allowed_cpus() -> Vec<String> {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let Some(list) = status
        .lines()
        .find_map(|line| line.strip_prefix("Cpus_allowed_list:"))
    else {
        return Vec::new();
    };
    let mut cpus = Vec::new();
    for range in list.trim().split(',').filter(|range| !range.is_empty()) {
        let (first, last) = range.split_once('-').unwrap_or((range, range));
        let (Ok(first), Ok(last)) = (first.parse::<usize>(), last.parse::<usize>()) else {
            return Vec::new();
        };
        cpus.extend((first..=last).map(|cpu| cpu.to_string()));
    }
    cpus
}

/// `ay solve --parallel 4 --competition` on a satisfiable formula, pinned
/// with `taskset` to `cpus`; `None` when `taskset` is not installed.
#[cfg(target_os = "linux")]
fn run_pinned_parallel(cpus: &[String], cnf: &std::path::Path) -> Option<std::process::Output> {
    let mut command = Command::new("taskset");
    clear_sat_env(&mut command);
    command
        .args(["-c", &cpus.join(",")])
        .arg(env!("CARGO_BIN_EXE_ay"))
        .args([
            "solve",
            "--parallel",
            "4",
            "--competition",
            "--timeout=60000",
        ])
        .arg(cnf);
    match command.output_timeout(Duration::from_secs(90)) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        output => Some(output.expect("run ay --parallel under taskset")),
    }
}

/// The member counts against the process compute budget (review of
/// 2026-11-13). Its ceiling is the CPUs the process may use: on one CPU it
/// leaves no unit beside the caller's, so `--parallel 4` takes the route of
/// `--parallel 1`, the portfolio alone. Before, the member ran uncounted
/// beside the only portfolio worker, two search threads on one CPU. On two
/// CPUs the member has its unit and runs.
#[cfg(target_os = "linux")]
#[test]
#[timeout(240_000)]
fn the_sequential_member_runs_only_on_a_unit_of_the_compute_budget() {
    const MEMBER_STARTED: &str = "c parallel: 4 threads: the sequential default route on 1";
    const NO_MEMBER_UNIT: &str =
        "c parallel: the process CPU ceiling leaves no unit for the sequential-route member";
    let cpus = allowed_cpus();
    if cpus.is_empty() {
        eprintln!("skipped: no Cpus_allowed_list");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let sat = dir.path().join("sat.cnf");
    std::fs::write(&sat, "p cnf 4 5\n1 2 0\n-1 3 0\n-2 -3 0\n3 4 0\n-4 -1 0\n").expect("write CNF");
    let mut widths = vec![(1, NO_MEMBER_UNIT, MEMBER_STARTED)];
    if cpus.len() >= 2 {
        widths.push((2, MEMBER_STARTED, NO_MEMBER_UNIT));
    }
    for (width, expected, absent) in widths {
        let Some(output) = run_pinned_parallel(&cpus[..width], &sat) else {
            eprintln!("skipped: taskset is not installed");
            return;
        };
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(10),
            "{width} CPU(s): stdout={stdout} stderr={stderr}"
        );
        assert_eq!(
            verdict_lines(&stdout),
            ["s SATISFIABLE"],
            "{width} CPU(s): {stderr}"
        );
        assert!(stderr.contains(expected), "{width} CPU(s): {stderr}");
        assert!(!stderr.contains(absent), "{width} CPU(s): {stderr}");
    }
}

/// Pigeonhole: `holes + 1` pigeons into `holes` holes, unsatisfiable. Every
/// pigeon sits in a hole; no hole takes two pigeons.
fn pigeonhole(holes: usize) -> String {
    let pigeons = holes + 1;
    let var = |pigeon: usize, hole: usize| 1 + pigeon * holes + hole;
    let mut clauses = Vec::new();
    for pigeon in 0..pigeons {
        let mut clause = String::new();
        for hole in 0..holes {
            write!(clause, "{} ", var(pigeon, hole)).expect("format clause");
        }
        clauses.push(format!("{clause}0"));
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in (first + 1)..pigeons {
                clauses.push(format!("-{} -{} 0", var(first, hole), var(second, hole)));
            }
        }
    }
    format!(
        "p cnf {} {}\n{}\n",
        pigeons * holes,
        clauses.len(),
        clauses.join("\n")
    )
}

fn verdict_lines(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .filter(|line| line.starts_with("s "))
        .collect()
}

/// 16 pigeons, 15 holes: resolution needs exponentially many steps, so no
/// portfolio worker answers inside the test's budget; the sequential route's
/// symmetry handling refutes it at once. Before the race this run timed out.
#[test]
#[timeout(120_000)]
fn parallel_answers_what_the_sequential_route_refutes_structurally() {
    let dir = tempfile::tempdir().expect("tempdir");
    let cnf = dir.path().join("php-16-15.cnf");
    std::fs::write(&cnf, pigeonhole(15)).expect("write CNF");
    let output = ay_command()
        .args([
            "solve",
            "--parallel",
            "4",
            "--competition",
            "--timeout=60000",
        ])
        .arg(&cnf)
        .output_timeout(Duration::from_secs(90))
        .expect("run ay --parallel");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "stdout={stdout} stderr={stderr}"
    );
    assert_eq!(
        verdict_lines(&stdout),
        ["s UNSATISFIABLE"],
        "stderr={stderr}"
    );
    assert!(stderr.contains(SEQUENTIAL_MEMBER_ANSWER), "{stderr}");
}

/// Both members answer a tiny formula at almost the same moment. Whichever
/// wins, the run prints exactly one verdict, the right one, with the matching
/// exit code, and a SAT answer carries a model of the formula.
#[test]
#[timeout(300_000)]
fn the_race_prints_one_verdict() {
    const SAT_CNF: &str = "p cnf 4 5\n1 2 0\n-1 3 0\n-2 -3 0\n3 4 0\n-4 -1 0\n";
    const SAT_CLAUSES: [&[i32]; 5] = [&[1, 2], &[-1, 3], &[-2, -3], &[3, 4], &[-4, -1]];
    let dir = tempfile::tempdir().expect("tempdir");
    let sat = dir.path().join("sat.cnf");
    std::fs::write(&sat, SAT_CNF).expect("write CNF");
    let unsat = dir.path().join("php-4-3.cnf");
    std::fs::write(&unsat, pigeonhole(3)).expect("write CNF");
    for round in 0..20 {
        let output = ay_command()
            .args([
                "solve",
                "--parallel",
                "3",
                "--competition",
                "--timeout=60000",
            ])
            .arg(&sat)
            .output_timeout(Duration::from_secs(90))
            .expect("run ay --parallel on a satisfiable formula");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(10),
            "round {round}: {stdout} {stderr}"
        );
        assert_eq!(
            verdict_lines(&stdout),
            ["s SATISFIABLE"],
            "round {round}: {stderr}"
        );
        let model: Vec<i32> = stdout
            .lines()
            .filter(|line| line.starts_with("v "))
            .flat_map(|line| line[2..].split_whitespace())
            .map(|token| token.parse().expect("model literal"))
            .filter(|&literal| literal != 0)
            .collect();
        for clause in SAT_CLAUSES {
            assert!(
                clause.iter().any(|literal| model.contains(literal)),
                "round {round}: model {model:?} falsifies {clause:?}"
            );
        }

        let output = ay_command()
            .args([
                "solve",
                "--parallel",
                "3",
                "--competition",
                "--timeout=60000",
            ])
            .arg(&unsat)
            .output_timeout(Duration::from_secs(90))
            .expect("run ay --parallel on an unsatisfiable formula");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(20),
            "round {round}: {stdout} {stderr}"
        );
        assert_eq!(
            verdict_lines(&stdout),
            ["s UNSATISFIABLE"],
            "round {round}: {stderr}"
        );
    }
}

/// A 3-colouring of a 2,000-vertex graph with about 166,000 edges and no
/// per-vertex at-most-one clauses (the fixture of
/// `orbitope_detection_honors_the_deadline`): 500,000 clauses, unsatisfiable.
/// A portfolio worker refutes it in under a second; the sequential route
/// spends about 44 s (release) detecting an orbitope first.
fn write_colouring(path: &std::path::Path) {
    const VERTICES: u64 = 2_000;
    const COLOURS: u64 = 3;
    let edges: Vec<(u64, u64)> = (0..VERTICES)
        .flat_map(|u| ((u + 1)..VERTICES).map(move |v| (u, v)))
        .filter(|&(u, v)| ((u.wrapping_mul(2_654_435_761) ^ v.wrapping_mul(40_503)) >> 7) % 12 == 0)
        .collect();
    let var = |v: u64, c: u64| 1 + COLOURS * v + c;
    let mut out = std::io::BufWriter::new(std::fs::File::create(path).expect("create CNF"));
    let clauses = VERTICES + COLOURS * edges.len() as u64;
    writeln!(out, "p cnf {} {clauses}", VERTICES * COLOURS).expect("write CNF");
    for v in 0..VERTICES {
        writeln!(out, "{} {} {} 0", var(v, 0), var(v, 1), var(v, 2)).expect("write CNF");
    }
    for &(u, v) in &edges {
        for c in 0..COLOURS {
            writeln!(out, "-{} -{} 0", var(u, c), var(v, c)).expect("write CNF");
        }
    }
    out.flush().expect("flush CNF");
}

/// A portfolio answer is published at once, while the sequential member is
/// still working: the run must not wait for that member. The first build of
/// the race left its thread scope before publishing, which joins the member:
/// on e1292f8d of the 2026 sample the portfolio had its model after 0.4 s and
/// the run ended at the 150 s timeout with no verdict. Here the portfolio
/// answers in about a second (release) and the member needs about 44 s more;
/// a run that waited would end at the 300 s timeout, because a member that
/// answers after the portfolio claimed the race parks.
#[test]
#[timeout(280_000)]
fn a_portfolio_answer_is_published_without_waiting_for_the_sequential_member() {
    let dir = tempfile::tempdir().expect("tempdir");
    let cnf = dir.path().join("colouring-2000x3.cnf");
    write_colouring(&cnf);
    let started = std::time::Instant::now();
    let output = ay_command()
        .args([
            "solve",
            "--parallel",
            "2",
            "--competition",
            "--timeout=300000",
        ])
        .arg(&cnf)
        .output_timeout(Duration::from_secs(240))
        .expect("run ay --parallel");
    let elapsed = started.elapsed();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "stdout={stdout} stderr={stderr}"
    );
    assert_eq!(
        verdict_lines(&stdout),
        ["s UNSATISFIABLE"],
        "stderr={stderr}"
    );
    assert!(
        elapsed < Duration::from_secs(200),
        "the run waited for the losing member: {elapsed:?}; stderr={stderr}"
    );
}
