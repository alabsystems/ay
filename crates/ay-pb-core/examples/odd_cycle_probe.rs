// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Probes the odd-cycle certifier DIRECTLY, given an instance and an incumbent.
//!
//! The OPT-LIN chain only reaches a floor certifier after the search has PROVED
//! optimality, so `ay pb solve` cannot show what this route costs on an instance
//! whose optimum it merely FOUND. This binary supplies the incumbent from a
//! solution file and times the route alone.
//!
//! Usage: `odd_cycle_probe <instance.opb> <solution.sol> <optimum> [<out.pbp>]`
//!
//! The solution file is the solver's own `v` lines (`v x1 -x2 x3 ...`).

use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let instance_text = std::fs::read_to_string(&args[1]).expect("instance");
    let solution_text = std::fs::read_to_string(&args[2]).expect("solution");
    let optimum: i128 = args[3].parse().expect("optimum");

    let instance = ay_pb_core::parse_opb(&instance_text).expect("parse");
    let mut incumbent = vec![false; instance.num_vars as usize];
    let mut seen = 0usize;
    for token in solution_text.split_whitespace() {
        let token = token.strip_prefix('v').unwrap_or(token);
        if token.is_empty() {
            continue;
        }
        let (value, name) = match token.strip_prefix('-') {
            Some(rest) => (false, rest),
            None => (true, token),
        };
        let Some(digits) = name.strip_prefix('x') else {
            continue;
        };
        let Ok(var) = digits.parse::<usize>() else {
            continue;
        };
        if var >= 1 && var <= incumbent.len() {
            incumbent[var - 1] = value;
            seen += 1;
        }
    }
    let start = Instant::now();
    let proof = ay_pb_core::proof::certify_opt_lin_odd_cycle_cover(&instance, &incumbent, optimum);
    let micros = start.elapsed().as_micros();
    match proof {
        Some(text) => {
            println!(
                "CERTIFIED vars={} rows={} assigned={seen} optimum={optimum} route_us={micros} bytes={} lines={}",
                instance.num_vars,
                instance.constraints.len(),
                text.len(),
                text.lines().count()
            );
            if let Some(out) = args.get(4) {
                std::fs::write(out, &text).expect("write");
            }
        }
        None => println!(
            "DECLINED vars={} rows={} assigned={seen} optimum={optimum} route_us={micros}",
            instance.num_vars,
            instance.constraints.len()
        ),
    }
}
