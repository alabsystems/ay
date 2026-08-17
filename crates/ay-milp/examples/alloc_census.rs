// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![expect(
    unsafe_code,
    reason = "the diagnostic's global allocator must implement and call the unsafe allocation API"
)]

//! `mps_solve` with a COUNTING global allocator.
//!
//! Wall clock on a loaded box is not evidence; allocation count is. This binary is
//! byte-identical to `mps_solve` in the search it runs (same `SolveOpts`, same session) and
//! differs only in that every `alloc`/`dealloc` bumps a relaxed counter, and the census is
//! printed on exit. Kept OUT of `mps_solve` so the timing binary stays pristine.
//!
//! ```text
//! alloc_census file.mps 60   (with --acensus on the solve CLI)
//! ```

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use ay_milp::acensus::{ALLOC_B, ALLOC_N, DEALLOC_N};
use ay_milp::{BabSession, Outcome, SolveOpts};

struct Counting;

// SAFETY: every method forwards to `System`, which is a correct allocator; the only added work
// is three relaxed atomic adds, which cannot affect the pointers returned.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOC_N.fetch_add(1, Ordering::Relaxed);
        ALLOC_B.fetch_add(l.size() as u64, Ordering::Relaxed);
        // SAFETY: `GlobalAlloc::alloc` supplies a valid layout, which is forwarded unchanged.
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        DEALLOC_N.fetch_add(1, Ordering::Relaxed);
        // SAFETY: the caller guarantees that `p` came from this allocator with layout `l`;
        // this allocator obtains every pointer from `System` with that same layout.
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        ALLOC_N.fetch_add(1, Ordering::Relaxed);
        ALLOC_B.fetch_add(new as u64, Ordering::Relaxed);
        // SAFETY: the caller supplies a pointer/layout pair previously returned by this
        // allocator, and both are forwarded unchanged with the requested new size.
        unsafe { System.realloc(p, l, new) }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        ALLOC_N.fetch_add(1, Ordering::Relaxed);
        ALLOC_B.fetch_add(l.size() as u64, Ordering::Relaxed);
        // SAFETY: `GlobalAlloc::alloc_zeroed` supplies a valid layout, forwarded unchanged.
        unsafe { System.alloc_zeroed(l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

fn main() {
    let mut args = std::env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("usage: alloc_census <file.mps> [seconds]");
        std::process::exit(2);
    };
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60.0);

    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        std::process::exit(2);
    });
    let p = ay_milp::read_mps(&text).unwrap_or_else(|e| {
        eprintln!("PARSE_ERROR {e}");
        std::process::exit(3);
    });

    // Same deterministic root-cut lane as `alloc_ub`, so the two binaries price and count the
    // SAME fixed workload.
    if std::env::args().any(|a| a == "--root-closure") {
        let t = Instant::now();
        let line = ay_milp::diag_root_closure(&p.model, secs);
        println!("{line} wall={:.3}", t.elapsed().as_secs_f64());
        eprint!("{}", ay_milp::acensus::dump(1));
        return;
    }

    let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    let mut s = match BabSession::new(p.model, &opts) {
        Ok(s) => s,
        Err(e) => {
            println!("SETUP_ERROR {e:?} - -");
            return;
        }
    };
    let t0 = Instant::now();
    let out = s.check();
    let dt = t0.elapsed().as_secs_f64();
    let nodes = ay_milp::nodes_explored();

    match out {
        Ok(Outcome::Optimal { value, .. }) => {
            println!(
                "OPTIMAL {} {dt:.3} {nodes}",
                ratio_str(&(&value / &p.obj_scale))
            );
        }
        Ok(Outcome::Feasible { model_values, .. }) => {
            let v = s.model().objective_value_at(&model_values);
            println!(
                "FEASIBLE {} {dt:.3} {nodes}",
                ratio_str(&(&v / &p.obj_scale))
            );
        }
        Ok(Outcome::Infeasible { .. }) => println!("INFEASIBLE - {dt:.3} {nodes}"),
        Ok(Outcome::Unbounded) => println!("UNBOUNDED - {dt:.3} {nodes}"),
        Ok(Outcome::Unknown { reason }) => println!("UNKNOWN {reason:?} {dt:.3} {nodes}"),
        Err(e) => println!("ERROR {e:?} {dt:.3} {nodes}"),
        Ok(other) => println!("OTHER {other:?} {dt:.3} {nodes}"),
    }
    eprint!("{}", ay_milp::acensus::dump(nodes));
    eprint!("{}", ay_milp::acensus::dump_segments(nodes));
}

/// A rational objective as a decimal, which is what every other solver prints.
fn ratio_str(v: &num_rational::BigRational) -> String {
    use num_traits::ToPrimitive;
    v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}"))
}
