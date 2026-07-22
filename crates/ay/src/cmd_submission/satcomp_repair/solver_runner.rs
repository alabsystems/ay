// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External-process solver/version runners, DRAT verification, and model
//! parsing/writing for satcomp_repair. Extracted from satcomp_repair.rs.

use super::*;
use std::fs::{self, File};
use std::io::Write;
#[cfg(unix)]
use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use ay_drat_check::checker::DratChecker;
use ay_drat_check::{cnf_parser, drat_parser};
use serde_json::{json, Value as JsonValue};

pub(super) fn run_solver(
    ay_bin: &Path,
    cnf: &Path,
    proof: &Path,
    timeout_sec: u64,
) -> Result<CommandResult> {
    let command = [
        ay_bin.display().to_string(),
        "solve".to_string(),
        "--proof".to_string(),
        proof.display().to_string(),
        cnf.display().to_string(),
    ];
    run_command_timeout(ay_bin, &command[1..], timeout_sec)
}

pub(super) fn run_version(ay_bin: &Path) -> Result<CommandResult> {
    run_command_timeout(ay_bin, &["--version".to_string()], 10)
}

fn run_command_timeout(program: &Path, args: &[String], timeout_sec: u64) -> Result<CommandResult> {
    let started = Instant::now();
    let mut command = Command::new(program);
    command
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    isolate_process_group(&mut command);
    let mut child = command
        .spawn()
        .with_context(|| format!("failed to run '{}'", program.display()))?;
    let timeout = Duration::from_secs(timeout_sec);
    let mut timed_out = false;
    loop {
        if child.try_wait()?.is_some() {
            break;
        }
        if started.elapsed() >= timeout {
            timed_out = true;
            terminate_process_tree(&mut child);
            break;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output()?;
    Ok(CommandResult {
        command: std::iter::once(program.display().to_string())
            .chain(args.iter().cloned())
            .collect(),
        exit_code: output.status.code(),
        timed_out,
        wall_time_ms: started.elapsed().as_millis(),
        stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
    })
}

#[cfg(unix)]
fn isolate_process_group(command: &mut Command) {
    command.process_group(0);
}

#[cfg(not(unix))]
fn isolate_process_group(_command: &mut Command) {}

#[cfg(unix)]
fn terminate_process_tree(child: &mut Child) {
    let pgid = nix::unistd::Pid::from_raw(child.id() as i32);
    let _ = nix::sys::signal::killpg(pgid, nix::sys::signal::Signal::SIGKILL);
    let _ = child.kill();
}

#[cfg(not(unix))]
fn terminate_process_tree(child: &mut Child) {
    let _ = child.kill();
}

pub(super) fn verify_drat(cnf: &Path, proof: &Path) -> CommandResult {
    let started = Instant::now();
    let command = vec![
        "ay_drat_check::DratChecker".to_string(),
        cnf.display().to_string(),
        proof.display().to_string(),
    ];
    let result = (|| -> Result<()> {
        let cnf_file = File::open(cnf)?;
        let parsed = cnf_parser::parse_cnf(cnf_file)?;
        anyhow::ensure!(
            parsed.num_vars <= ay_drat_check::checker::MAX_DENSE_VARS,
            "formula variable count {} exceeds DRAT checker's dense maximum {}",
            parsed.num_vars,
            ay_drat_check::checker::MAX_DENSE_VARS
        );
        let proof_bytes = fs::read(proof)?;
        let steps = drat_parser::parse_drat(&proof_bytes)?;
        let mut checker = DratChecker::new(parsed.num_vars, true);
        checker.verify(&parsed.clauses, &steps)?;
        Ok(())
    })();
    match result {
        Ok(()) => CommandResult {
            command,
            exit_code: Some(0),
            timed_out: false,
            wall_time_ms: started.elapsed().as_millis(),
            stdout: "s VERIFIED\n".to_string(),
            stderr: String::new(),
        },
        Err(error) => CommandResult {
            command,
            exit_code: Some(1),
            timed_out: false,
            wall_time_ms: started.elapsed().as_millis(),
            stdout: "s NOT VERIFIED\n".to_string(),
            stderr: format!("{error:#}"),
        },
    }
}

pub(super) fn parse_solver_model(stdout: &str, num_vars: usize) -> (Option<Vec<bool>>, JsonValue) {
    let mut assignment = vec![None; num_vars];
    let mut seen_lits = 0usize;
    let mut duplicate_same = 0usize;
    let mut duplicate_conflict = 0usize;
    let mut out_of_range = 0usize;
    let mut malformed = 0usize;
    for line in stdout
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with('v'))
    {
        for cell in line.split_whitespace().skip(1) {
            let Ok(lit) = cell.parse::<i32>() else {
                malformed += 1;
                continue;
            };
            if lit == 0 {
                continue;
            }
            seen_lits += 1;
            let var = lit.unsigned_abs() as usize - 1;
            if var >= num_vars {
                out_of_range += 1;
                continue;
            }
            let value = lit > 0;
            match assignment[var] {
                None => assignment[var] = Some(value),
                Some(existing) if existing == value => duplicate_same += 1,
                Some(_) => duplicate_conflict += 1,
            }
        }
    }
    let missing: Vec<usize> = assignment
        .iter()
        .enumerate()
        .filter_map(|(idx, value)| if value.is_none() { Some(idx + 1) } else { None })
        .collect();
    let stats = json!({
        "model_lits_seen": seen_lits,
        "duplicate_same_value_lits": duplicate_same,
        "duplicate_conflicting_lits": duplicate_conflict,
        "out_of_range_lits": out_of_range,
        "malformed_lits": malformed,
        "missing_model_var_count": missing.len(),
        "first_missing_model_vars": missing.iter().take(16).copied().collect::<Vec<_>>(),
    });
    if missing.is_empty() && duplicate_conflict == 0 && out_of_range == 0 && malformed == 0 {
        (
            Some(assignment.into_iter().map(Option::unwrap).collect()),
            stats,
        )
    } else {
        (None, stats)
    }
}

pub(super) fn falsified_clause_ids(clauses: &[Vec<i32>], assignment: &[bool]) -> Vec<usize> {
    clauses
        .iter()
        .enumerate()
        .filter_map(|(idx, clause)| {
            if clause.iter().any(|&lit| literal_satisfied(lit, assignment)) {
                None
            } else {
                Some(idx)
            }
        })
        .collect()
}

pub(super) fn write_dimacs_model(path: &Path, assignment: &[bool]) -> Result<()> {
    let mut file = File::create(path)?;
    writeln!(file, "s SATISFIABLE")?;
    for chunk in assignment.chunks(16).enumerate() {
        let (chunk_idx, values) = chunk;
        write!(file, "v")?;
        for (idx, value) in values.iter().enumerate() {
            let var = chunk_idx * 16 + idx + 1;
            let lit = if *value { var as i32 } else { -(var as i32) };
            write!(file, " {lit}")?;
        }
        writeln!(file)?;
    }
    writeln!(file, "v 0")?;
    Ok(())
}
