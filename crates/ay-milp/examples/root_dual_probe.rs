// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// MEASUREMENT SCRATCH: read an MPS file and run `derive_root_dual_bound` on it
// with the exact rim ENABLED and DISABLED, reporting what each lane cost and
// what bound it proved.
//
// No solve. The question this answers is exactly "what does the root-only dual
// lane cost, and how much tightness does the cheap lane give up", and a solve
// would put the answer behind a variable that has nothing to do with either.
//
//   cargo run --release -p ay-milp --example root_dual_probe -- f.mps[.gz] [secs]

use std::time::{Duration, Instant};

use num_traits::ToPrimitive;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .ok_or("usage: root_dual_probe <file.mps[.gz]> [secs]")?;
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60.0);

    let stem = std::path::Path::new(&path)
        .file_stem()
        .map_or_else(|| path.clone(), |s| s.to_string_lossy().into_owned());
    let name = stem.trim_end_matches(".mps").to_owned();

    let text = if path.ends_with(".gz") {
        decompress_gz(&std::fs::read(&path)?)?
    } else {
        std::fs::read_to_string(&path)?
    };
    let problem = ay_milp::read_mps(&text)?;
    let model = problem.model;
    let scale = &problem.obj_scale;

    for (tag, rim) in [("float-only", 0u64), ("with-rim", u64::MAX)] {
        let mut budget = ay_milp::RootDualBudget::new(&model)
            .with_deadline(Some(Instant::now() + Duration::from_secs_f64(secs)));
        if rim == 0 {
            budget = budget.with_rim_iters(0);
        }
        let t = Instant::now();
        let (certificate, report) = ay_milp::derive_root_dual_bound(&model, &budget);
        let derive_secs = t.elapsed().as_secs_f64();
        // The bound is printed in the FILE frame (the units the input is
        // written in), which is the frame a reader compares against a published
        // optimum. f64 here and only here: this is a scratch probe whose output
        // is a magnitude, not evidence.
        let bound = certificate.as_ref().map(|c| {
            (ay_milp::root_dual_bound_in_model_frame(c, &model) / scale)
                .to_f64()
                .unwrap_or(f64::NAN)
        });
        println!(
            "{name}\trows={}\tcols={}\tlane_req={tag}\tresult={}\tlane={}\t\
             derive_secs={derive_secs:.3}\trim_iters={}\tbound={}",
            model.num_rows(),
            model.num_cols(),
            certificate.as_ref().map_or_else(
                || report
                    .decline
                    .map_or("unknown".to_owned(), |d| d.tag().to_owned()),
                |_| "OK".to_owned()
            ),
            report.lane.map_or("-", ay_milp::RootDualLane::tag),
            report.rim_iters,
            bound.map_or_else(|| "-".to_owned(), |b| format!("{b}")),
        );
    }
    Ok(())
}

fn decompress_gz(bytes: &[u8]) -> Result<String, Box<dyn std::error::Error>> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("gzip")
        .arg("-dc")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    child.stdin.as_mut().ok_or("no stdin")?.write_all(bytes)?;
    let out = child.wait_with_output()?;
    Ok(String::from_utf8(out.stdout)?)
}
