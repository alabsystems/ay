// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-search phase profiler: breaks down where wall time goes between
//! process start and the first search step on one OPB instance.
//!
//!     cargo run --release -p ay-pb --example presearch_profile -- FILE [reps]
//!
//! Phases measured independently (each on fresh inputs where possible):
//!   read      — file IO (`std::fs::read`)
//!   utf8      — `std::str::from_utf8` validation
//!   parse     — `ay_pb::parse_opb`
//!   preprocess— `ay_pb::preprocess`
//!   import    — full `PbCdclSolver::new_interruptible` construction
//!               (preprocess + propagator import + mirror + activity/heap)
//!   clone     — `instance.clone()` (the old parallel-portfolio per-solve cost)

use std::time::Instant;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect("usage: presearch_profile FILE [reps]");
    let reps: usize = args.next().map_or(3, |s| s.parse().expect("reps"));

    for rep in 0..reps {
        let t = Instant::now();
        let bytes = std::fs::read(&path).expect("read");
        let read_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let text = std::str::from_utf8(&bytes).expect("utf8");
        let utf8_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let instance = ay_pb::parse_opb(text).expect("parse");
        let parse_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let pre = ay_pb::preprocess(&instance);
        let preprocess_s = t.elapsed().as_secs_f64();
        std::hint::black_box(&pre);
        drop(pre);

        let t = Instant::now();
        let solver = ay_pb::PbCdclSolver::new_interruptible(&instance, || false);
        let import_s = t.elapsed().as_secs_f64();
        std::hint::black_box(&solver);
        drop(solver);

        let t = Instant::now();
        let solver = ay_pb::PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
        let raw_import_s = t.elapsed().as_secs_f64();
        std::hint::black_box(&solver);
        drop(solver);

        let t = Instant::now();
        let cloned = instance.clone();
        let clone_s = t.elapsed().as_secs_f64();
        std::hint::black_box(&cloned);
        drop(cloned);

        println!(
            "rep={rep} read={read_s:.3} utf8={utf8_s:.3} parse={parse_s:.3} \
             preprocess={preprocess_s:.3} import(full-ctor)={import_s:.3} \
             import(raw)={raw_import_s:.3} clone={clone_s:.3} \
             rows={} vars={}",
            instance.constraints.len(),
            instance.num_vars
        );
    }
}
