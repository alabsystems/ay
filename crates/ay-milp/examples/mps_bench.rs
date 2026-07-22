// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Timing harness for SMALL instances: solve the same MPS model N times in one
//! process and print each wall time plus the median. In-process repetition
//! averages out scheduler noise on a loaded laptop and gives a sampling
//! profiler something long enough to see.
//!
//! ```text
//! cargo run --release -p ay-milp --example mps_bench -- gt2.mps 9 [seconds]
//! ```

use std::time::{Duration, Instant};

use ay_milp::{BabSession, Outcome, SolveOpts};

fn main() {
    let mut args = std::env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("usage: mps_bench <file.mps> [reps] [seconds]");
        std::process::exit(2);
    };
    let reps: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(9);
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60.0);

    let text = std::fs::read_to_string(&path).expect("read mps");
    let t_parse = Instant::now();
    let p = ay_milp::read_mps(&text).expect("parse mps");
    let parse_s = t_parse.elapsed().as_secs_f64();

    let mut walls = Vec::with_capacity(reps);
    let mut value = String::new();
    for _ in 0..reps {
        let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
        let mut s = BabSession::new(p.model.clone(), &opts).expect("model");
        let t0 = Instant::now();
        let out = s.check();
        walls.push(t0.elapsed().as_secs_f64());
        value = match out {
            Ok(Outcome::Optimal { value, .. }) => {
                use num_traits::ToPrimitive;
                let v = p.unscale(&value);
                v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}"))
            }
            other => format!("{other:?}"),
        };
    }
    let mut sorted = walls.clone();
    sorted.sort_by(f64::total_cmp);
    let med = sorted[sorted.len() / 2];
    let per: Vec<String> = walls.iter().map(|w| format!("{w:.4}")).collect();
    println!(
        "{} value={value} parse={parse_s:.4} median={med:.4} runs=[{}]",
        p.name,
        per.join(", ")
    );
}
