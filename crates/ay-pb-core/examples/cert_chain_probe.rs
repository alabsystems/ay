// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Runs the WHOLE OPT-LIN certificate chain against an instance and a supplied
//! incumbent, and reports which rung (if any) certified.
//!
//! This isolates the certification delta between two trees from the SEARCH that
//! precedes it: `ay pb solve` only reaches the chain after it has proved
//! optimality, so a whole-solve A/B measures the search, not the chain.
//!
//! Usage: `cert_chain_probe <instance.opb> <solution> <optimum> <deadline_ms> [<out.pbp>]`

use std::time::{Duration, Instant};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let instance_text = std::fs::read_to_string(&args[1]).expect("instance");
    let solution_text = std::fs::read_to_string(&args[2]).expect("solution");
    let optimum: i128 = args[3].parse().expect("optimum");
    let budget: u64 = args[4].parse().expect("deadline ms");

    let instance = ay_pb_core::parse_opb(&instance_text).expect("parse");
    let mut incumbent = vec![false; instance.num_vars as usize];
    for token in solution_text.split_whitespace() {
        let token = token.strip_prefix('v').unwrap_or(token);
        if token.is_empty() {
            continue;
        }
        let (value, name) = match token.strip_prefix('-') {
            Some(rest) => (false, rest),
            None => (true, token),
        };
        if let Some(digits) = name.strip_prefix('x') {
            if let Ok(var) = digits.parse::<usize>() {
                if var >= 1 && var <= incumbent.len() {
                    incumbent[var - 1] = value;
                }
            }
        }
    }
    let deadline = Instant::now() + Duration::from_millis(budget);
    let start = Instant::now();
    let got = ay_pb_core::proof::certify_opt_lin_any_interruptible(
        &instance,
        &incumbent,
        optimum,
        Some(deadline),
        &|| Instant::now() >= deadline,
    );
    let ms = start.elapsed().as_millis();
    match got {
        Some((text, route)) => {
            println!(
                "CERTIFIED route={} ms={ms} bytes={}",
                route.as_str(),
                text.len()
            );
            if let Some(out) = args.get(5) {
                std::fs::write(out, &text).expect("write");
            }
        }
        None => println!("NO-PROOF route=none ms={ms} bytes=0"),
    }
}
