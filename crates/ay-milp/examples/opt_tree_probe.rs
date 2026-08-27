// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// MEASUREMENT SCRATCH (design worktree, not for shipping): solve an MPS file
// ONCE and then run `derive_optimality_tree` at a LADDER of budgets against the
// same verdict, reporting the `OptTreeReport` for each.
//
// The point is to separate the two events the shipped message used to spell
// "budget or model out of reach": a descent that ran out of clock and one that
// hit a wall no clock can move. Re-solving per budget would pay the solve cost
// once per rung and make the comparison wall-coupled on the wrong term; one
// solve, N derivations keeps the only varying input the budget.
//
//   cargo run --release -p ay-milp --example opt_tree_probe -- f.mps 300 0.25,5,30 20000

use std::time::{Duration, Instant};

use ay_milp::engine_cli::parse_applied;
use ay_milp::{BabSession, Outcome, SolveOpts};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    // `parse_applied`, NOT `Flags::parse(.., VALUE_FLAGS, ..)`. This probe reads
    // its budgets and leaf cap POSITIONALLY, so handing it the `solve`
    // subcommand's value table would make it accept 14 names it cannot carry --
    // including `--opt-tree-secs` and `--opt-tree-leaves`, the two settings this
    // probe exists to sweep. That is the failure mode `knob_census`'s
    // `no_surface_accepts_a_flag_only_solve_can_carry` was built to catch, and
    // it caught this file on the first merge that put them in one tree.
    let flags = parse_applied(&raw, &[], &[]).map_err(std::io::Error::other)?;
    let mut args = flags.positional.iter().cloned();
    let path = args.next().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "usage: opt_tree_probe <file.mps> [solve_secs] [budget,budget,...] [leaf_cap]",
        )
    })?;
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(600.0);
    let ladder: Vec<Rung> = args
        .next()
        .unwrap_or_else(|| "5".to_string())
        .split(',')
        .filter_map(Rung::parse)
        .collect();
    let leaf_cap: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(20_000);

    let name = std::path::Path::new(&path)
        .file_stem()
        .map_or_else(|| path.clone(), |s| s.to_string_lossy().into_owned());

    let text = if path.ends_with(".gz") {
        let bytes = std::fs::read(&path)?;
        decompress_gz(&bytes)?
    } else {
        std::fs::read_to_string(&path)?
    };
    let p = ay_milp::read_mps(&text)?;
    let model = p.model.clone();
    let n_int = (0..model.num_cols())
        .filter(|&j| {
            model.col_at(j).is_some_and(|c| {
                matches!(
                    model.col_kind(c),
                    ay_milp::ColKind::Binary | ay_milp::ColKind::Integer
                )
            })
        })
        .count();

    // Matrix nonzeros: the per-instance scale factor for every exact pass the
    // certifying descent runs, and therefore the thing a work UNIT has to be
    // tested against before a flat cap can be believed.
    let nnz: usize = (0..model.num_rows())
        .filter_map(|r| model.row_at(r))
        .map(|r| model.row(r).0.len())
        .sum();

    let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    let opts = ay_milp::engine_cli::apply(&flags, opts).map_err(std::io::Error::other)?;
    let mut s = BabSession::new(p.model, &opts)?;
    let t0 = Instant::now();
    let out = s.check();
    let solve_secs = t0.elapsed().as_secs_f64();
    let nodes = ay_milp::nodes_explored();

    let Ok(Outcome::Optimal {
        value,
        model_values,
        ..
    }) = &out
    else {
        println!("{name}\tNOT-OPTIMAL\tsolve_secs={solve_secs:.3}");
        return Ok(());
    };

    // WALL BUDGETS ARE ONLY HALF THE LADDER NOW. A rung is `w<n>` for a
    // deterministic work cap and a bare number for the old wall budget, so the
    // two can be swept against each other in one run and the same derivation
    // reports both what it SPENT (`work=`) and what stopped it.
    for (rule, tag) in [
        (ay_milp::OptTreeBranch::FirstFractional, "first"),
        (ay_milp::OptTreeBranch::MostFractional, "mostfrac"),
    ] {
        for b in &ladder {
            let budget = ay_milp::OptimalityTreeBudget::new(leaf_cap).with_branch(rule);
            let budget = match b {
                Rung::Wall(secs) => {
                    budget.with_deadline(Some(Instant::now() + Duration::from_secs_f64(*secs)))
                }
                Rung::Work(units) => budget.with_work(*units),
            };
            let t = Instant::now();
            let (cert, rep) =
                ay_milp::derive_optimality_tree_reported(s.model(), value, model_values, &budget);
            let dt = t.elapsed().as_secs_f64();
            println!(
                "{name}\trows={}\tcols={}\tnnz={nnz}\tint={n_int}\tsolve_secs={solve_secs:.3}\t\
             solve_nodes={nodes}\trule={tag}\tbudget={b}\tleaf_cap={leaf_cap}\t\
             derive_secs={dt:.3}\tresult={}\tcert_leaves={}\tleaves={}\tdepth={}\t\
             float_lps={}\trim_lps={}\tnodes_visited={}\tfloat_iters={}\trim_iters={}\t\
             work={}\troot_gap={}",
                model.num_rows(),
                model.num_cols(),
                cert.as_ref().map_or_else(
                    || rep
                        .decline
                        .map_or("unknown".to_string(), |d| d.tag().to_string()),
                    |_| "OK".to_string()
                ),
                cert.as_ref()
                    .map_or(0, ay_milp::MilpOptimalityCertificate::num_leaves),
                rep.leaves,
                rep.max_depth,
                rep.float_solves,
                rep.rim_solves,
                rep.nodes,
                rep.float_iters,
                rep.rim_iters,
                rep.work,
                rep.root_gap_rel
                    .map_or_else(|| "n/a".to_string(), |g| format!("{g:.8}")),
            );
        }
    }
    Ok(())
}

/// One rung of the budget ladder: a wall-clock deadline (the OLD bound) or a
/// deterministic work cap (the shipped one).
#[derive(Clone, Copy)]
enum Rung {
    Wall(f64),
    Work(u64),
}

impl Rung {
    fn parse(s: &str) -> Option<Self> {
        s.strip_prefix('w').map_or_else(
            || s.parse().ok().map(Rung::Wall),
            |n| n.parse().ok().map(Rung::Work),
        )
    }
}

impl std::fmt::Display for Rung {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Wall(s) => write!(f, "{s}s"),
            Self::Work(n) => write!(f, "w{n}"),
        }
    }
}

/// Minimal gzip inflate via the `gzip` binary; the corpus ships `.mps.gz` and
/// this example is scratch, so shelling out beats a dependency.
fn decompress_gz(bytes: &[u8]) -> Result<String, Box<dyn std::error::Error>> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut c = Command::new("gzip")
        .arg("-dc")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    c.stdin.as_mut().ok_or("no stdin")?.write_all(bytes)?;
    let out = c.wait_with_output()?;
    Ok(String::from_utf8(out.stdout)?)
}
