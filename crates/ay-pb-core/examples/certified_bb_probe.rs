// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Drives the `certified-bb` route ALONE against an instance and an incumbent
//! given as 0-based variable indices (the prototype's `sol.json` shape), and
//! prints the route's own diagnosis.
//!
//! Isolating one rung matters here for the same reason `cert_chain_probe`
//! isolates the chain from the search: this route runs LAST among the
//! unscheduled rungs, so a whole-chain probe reports whichever cheaper rung
//! fires first and says nothing about this one.
//!
//! Usage: `certified_bb_probe <instance.opb> <sol.json> <optimum> [<out.pbp>]`

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let instance_text = std::fs::read_to_string(&args[1]).expect("instance");
    let solution_text = std::fs::read_to_string(&args[2]).expect("solution");
    let optimum: i128 = args[3].parse().expect("optimum");

    let instance = ay_pb_core::parse_opb(&instance_text).expect("parse");
    let mut incumbent = vec![false; instance.num_vars as usize];
    // `[0, 3, 17]`: the 0-based indices set to 1. Parsed by splitting on
    // everything that is not a digit, so the file's brackets and commas need no
    // JSON dependency.
    for token in solution_text.split(|c: char| !c.is_ascii_digit()) {
        if token.is_empty() {
            continue;
        }
        let index: usize = token.parse().expect("index");
        assert!(index < incumbent.len(), "solution index out of range");
        incumbent[index] = true;
    }

    let start = std::time::Instant::now();
    let proof = ay_pb_core::proof::certify_opt_lin_certified_bb(&instance, &incumbent, optimum);
    let ms = start.elapsed().as_millis();
    // The diagnosis re-runs the search. That is the price of reporting the
    // COUNTS the budgets are expressed in, and this is a probe, so it is worth
    // paying on both paths rather than only on the failing one.
    let diagnosis = ay_pb_core::proof::certified_bb_diagnosis(&instance, &incumbent, optimum);
    match proof {
        Some(text) => {
            println!(
                "CERTIFIED bytes={} lines={} ms={ms} {diagnosis}",
                text.len(),
                text.lines().count()
            );
            if let Some(out) = args.get(4) {
                std::fs::write(out, &text).expect("write");
            }
        }
        None => println!("NO-PROOF ms={ms} {diagnosis}"),
    }
}
