// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// MEASUREMENT SCRATCH (design worktree, not for shipping): WHAT HOLDS THE
// MEMORY in a certifying optimality descent, and what streaming it costs.
//
// the development design notes measured that `khb05250`
// and `fiber` are SIGKILLed at the 3,072 MiB jetsam bound when given more
// budget, and ATTRIBUTED that to the in-memory `OptTreeNode` graph. The
// attribution was an estimate ("~17k leaves x 1,326 columns is ~23M
// `Multiplier` values"), never a measurement.
//
// This probe measures it, and measures it the load-invariant way: ONE binary,
// TWO sinks, arms INTERLEAVED. `held` is `derive_optimality_tree_reported`
// (the tree is retained); `stream` is `stream_optimality_tree` (each leaf is
// written and dropped). Only the sink differs, so the footprint difference is
// attributable to the sink and to nothing else.
//
//   cargo run --release -p ay-milp --example opt_tree_mem_probe -- f.mps 60 w8888,w71104
//
// The reported `phys_footprint` is the metric jetsam kills on, so an arm that
// dies is reporting the same number the kernel used.

use std::io::Write as _;
use std::time::{Duration, Instant};

use ay_milp::engine_cli::parse_applied;
use ay_milp::{BabSession, Outcome, SolveOpts};
use num_rational::BigRational;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let flags = parse_applied(&raw, &[], &[]).map_err(std::io::Error::other)?;
    let mut args = flags.positional.iter().cloned();
    let path = args.next().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "usage: opt_tree_mem_probe <file.mps> [solve_secs] [w<work>,...] [leaf_cap]",
        )
    })?;
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(600.0);
    let ladder: Vec<u64> = args
        .next()
        .unwrap_or_else(|| "0".to_string())
        .split(',')
        .filter_map(|s| s.trim_start_matches('w').parse::<u64>().ok())
        .collect();
    let leaf_cap: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(20_000);
    // ONE ARM PER PROCESS, deliberately. `ru_maxrss` is a high-water mark over
    // the whole process, so two arms in one image would report the LARGER
    // arm's peak for both; and an arm that is SIGKILLed cannot be followed by
    // anything at all. The caller interleaves at the process level instead.
    let arms: Vec<String> = args
        .next()
        .map_or_else(|| vec!["held".into(), "stream".into()], |a| vec![a]);

    let name = std::path::Path::new(&path)
        .file_stem()
        .map_or_else(|| path.clone(), |s| s.to_string_lossy().into_owned());

    let text = if path.ends_with(".gz") {
        decompress_gz(&path)?
    } else {
        std::fs::read_to_string(&path)?
    };
    let p = ay_milp::read_mps(&text)?;
    let cols = p.model.num_cols();

    let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    let opts = ay_milp::engine_cli::apply(&flags, opts).map_err(std::io::Error::other)?;
    // The report is this probe's output, so a failed write is the run's error
    // rather than a panic. Each line takes stdout's lock only while it is
    // written (as `println!` does), never across a solve or a derivation.
    let mut stdout = std::io::stdout();
    let mut s = BabSession::new(p.model, &opts)?;
    let out = s.check();
    let Ok(Outcome::Optimal {
        value,
        model_values,
        ..
    }) = &out
    else {
        writeln!(stdout, "{name}\tNOT-OPTIMAL")?;
        return Ok(());
    };

    let base = ay_sys::current_footprint_bytes();
    writeln!(stdout, "{name}\tcols={cols}\tfp_after_solve={base}")?;

    for work in &ladder {
        let budget = ay_milp::OptimalityTreeBudget::new(leaf_cap).with_work(*work);
        // INTERLEAVED at the rung, not blocked: held then stream at the same
        // budget, so a drifting machine cannot line up with an arm.
        for arm in &arms {
            let t = Instant::now();
            let (ok, bytes, rep) = run_arm(arm, s.model(), value, model_values, &budget);
            let dt = t.elapsed().as_secs_f64();
            // `current_rss_bytes` is `ru_maxrss`, a HIGH-WATER mark: it reports
            // the largest the process ever was, which for a single-arm image is
            // that arm's peak. `current_footprint_bytes` is the live figure and
            // is reported alongside so the two can be read against each other.
            let fp = ay_sys::current_rss_bytes();
            let live = ay_sys::current_footprint_bytes();
            writeln!(
                stdout,
                "{name}\twork={work}\tarm={arm}\tresult={}\tleaves={}\tbody_bytes={bytes}\t\
                 peak_rss={fp}\tfp_live={live}\tfp_delta={}\twork_spent={}\t\
                 derive_secs={dt:.3}\tdecline={}",
                if ok { "OK" } else { "declined" },
                rep.leaves,
                live.saturating_sub(base),
                rep.work,
                rep.decline.map_or("-".to_string(), |d| d.tag().to_string()),
            )?;
        }
    }
    Ok(())
}

/// Derive one arm's tree: `held` retains it (`derive_optimality_tree_reported`),
/// any other arm streams it (`stream_optimality_tree`). Returns whether a tree
/// came back, its WIRE bytes (the held tree is measured by the bytes it would
/// print, so the two arms report the same currency), and the derivation report.
fn run_arm(
    arm: &str,
    model: &ay_milp::Model,
    value: &BigRational,
    witness: &[BigRational],
    budget: &ay_milp::OptimalityTreeBudget,
) -> (bool, usize, ay_milp::OptTreeReport) {
    if arm == "held" {
        let (cert, rep) = ay_milp::derive_optimality_tree_reported(model, value, witness, budget);
        let bytes = cert.as_ref().map_or(0, |c| c.wire_body().len());
        (cert.is_some(), bytes, rep)
    } else {
        let (cert, rep) = ay_milp::stream_optimality_tree(model, value, witness, budget);
        let bytes = cert.as_ref().map_or(0, |c| c.body().len());
        (cert.is_some(), bytes, rep)
    }
}

/// Inflate `path` with the system `gzip`, which reads the file itself: no pipe
/// is written, so a `gzip` that stops early (a corrupt file) is its non-zero
/// exit, not a SIGPIPE that kills this probe (`unix_hardened` builds run with
/// SIGPIPE at its default action), and its output can never fill a pipe this
/// process is blocked writing into.
fn decompress_gz(path: &str) -> Result<String, Box<dyn std::error::Error>> {
    let out = std::process::Command::new("gzip")
        .args(["-dc", "--", path])
        .output()?;
    if !out.status.success() {
        return Err(format!(
            "gzip -dc {path}: {} ({})",
            String::from_utf8_lossy(&out.stderr).trim(),
            out.status
        )
        .into());
    }
    Ok(String::from_utf8(out.stdout)?)
}
