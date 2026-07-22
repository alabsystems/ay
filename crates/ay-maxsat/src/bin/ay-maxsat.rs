// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::Path;

use ay_maxsat::{MaxSatResult, MaxSatSolver};

#[derive(Debug, Clone, PartialEq, Eq)]
struct MaxSatInstance {
    num_vars: usize,
    hard: Vec<Vec<i32>>,
    soft: Vec<(u64, Vec<i32>)>,
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match run(args) {
        Ok(exit_code) => std::process::exit(exit_code),
        Err(message) => {
            eprintln!("ERROR: {message}");
            std::process::exit(2);
        }
    }
}

fn run(args: Vec<String>) -> Result<i32, String> {
    if args == ["--version"] || args == ["-V"] {
        println!("ay-maxsat {}", env!("CARGO_PKG_VERSION"));
        return Ok(0);
    }

    let file = match args.as_slice() {
        [cmd, subcmd, file] if cmd == "maxsat" && subcmd == "solve" => file,
        [subcmd, file] if subcmd == "solve" => file,
        [file] if !file.starts_with('-') => file,
        _ => return Err(usage()),
    };

    solve(Path::new(file))
}

fn usage() -> String {
    "usage: ay-maxsat maxsat solve FILE".to_string()
}

fn solve(path: &Path) -> Result<i32, String> {
    let input = fs::read_to_string(path)
        .map_err(|err| format!("failed to read '{}': {err}", path.display()))?;
    let instance =
        parse_wcnf(&input).map_err(|err| format!("failed to parse '{}': {err}", path.display()))?;

    let mut solver = MaxSatSolver::new();
    for clause in &instance.hard {
        solver.add_hard_clause(clause.clone());
    }
    for (weight, clause) in &instance.soft {
        solver.add_soft_clause(clause.clone(), *weight);
    }

    match solver.solve() {
        MaxSatResult::Optimal { model, cost } => {
            println!("o {cost}");
            println!("s OPTIMUM FOUND");
            print_assignment(instance.num_vars, &model);
            Ok(30)
        }
        MaxSatResult::Unsatisfiable => {
            println!("s UNSATISFIABLE");
            Ok(20)
        }
        MaxSatResult::Unknown => {
            println!("s UNKNOWN");
            Ok(0)
        }
    }
}

fn print_assignment(num_vars: usize, model: &[bool]) {
    print!("v");
    for var in 1..=num_vars {
        let value = if model.get(var).copied().unwrap_or(false) {
            '1'
        } else {
            '0'
        };
        print!(" {value}");
    }
    println!();
}

fn parse_wcnf(input: &str) -> Result<MaxSatInstance, String> {
    let mut declared_vars: Option<usize> = None;
    let mut declared_clauses: Option<usize> = None;
    let mut old_top: Option<u64> = None;
    let mut hard = Vec::new();
    let mut soft = Vec::new();
    let mut seen_clauses = 0usize;
    let mut max_var = 0usize;

    for (line_no, raw_line) in input.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }

        if line.starts_with('p') {
            let fields: Vec<&str> = line.split_whitespace().collect();
            if fields.len() < 4 || fields[0] != "p" || fields[1] != "wcnf" {
                return Err(format!(
                    "line {}: expected 'p wcnf <vars> <clauses> [top]'",
                    line_no.saturating_add(1)
                ));
            }
            declared_vars = Some(parse_usize(fields[2], line_no, "variable count")?);
            declared_clauses = Some(parse_usize(fields[3], line_no, "clause count")?);
            if let Some(top) = fields.get(4) {
                old_top = Some(parse_u64(top, line_no, "top weight")?);
            }
            continue;
        }

        let mut fields = line.split_whitespace();
        let Some(first) = fields.next() else {
            continue;
        };

        let is_hard_new = first == "h";
        let weight = if is_hard_new {
            None
        } else {
            Some(parse_u64(first, line_no, "clause weight")?)
        };

        let mut clause = Vec::new();
        let mut terminated = false;
        for token in fields {
            let lit = token.parse::<i32>().map_err(|_| {
                format!(
                    "line {}: invalid literal '{token}'",
                    line_no.saturating_add(1)
                )
            })?;
            if lit == 0 {
                terminated = true;
                break;
            }
            let var = lit.unsigned_abs() as usize;
            if var == 0 {
                return Err(format!(
                    "line {}: zero literal inside clause",
                    line_no.saturating_add(1)
                ));
            }
            max_var = max_var.max(var);
            clause.push(lit);
        }
        if !terminated {
            return Err(format!(
                "line {}: clause missing terminating 0",
                line_no.saturating_add(1)
            ));
        }

        match (is_hard_new, weight, old_top) {
            (true, None, _) => hard.push(clause),
            (false, Some(w), Some(top)) if w >= top => hard.push(clause),
            (false, Some(w), _) => {
                if w == 0 {
                    return Err(format!(
                        "line {}: soft weight must be positive",
                        line_no.saturating_add(1)
                    ));
                }
                soft.push((w, clause));
            }
            _ => unreachable!(),
        }
        seen_clauses = seen_clauses.saturating_add(1);
    }

    if let Some(expected) = declared_clauses {
        if expected != seen_clauses {
            return Err(format!(
                "declared {expected} clauses but parsed {seen_clauses}"
            ));
        }
    }

    let num_vars = declared_vars.unwrap_or(max_var);
    if max_var > num_vars {
        return Err(format!(
            "literal variable {max_var} exceeds declared variable count {num_vars}"
        ));
    }

    Ok(MaxSatInstance {
        num_vars,
        hard,
        soft,
    })
}

fn parse_usize(value: &str, line_no: usize, label: &str) -> Result<usize, String> {
    value
        .parse()
        .map_err(|_| format!("line {}: invalid {label}", line_no.saturating_add(1)))
}

fn parse_u64(value: &str, line_no: usize, label: &str) -> Result<u64, String> {
    value
        .parse()
        .map_err(|_| format!("line {}: invalid {label}", line_no.saturating_add(1)))
}
