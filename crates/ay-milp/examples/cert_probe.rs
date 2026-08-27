// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// MEASUREMENT SCRATCH (design worktree, not for shipping): solve an MPS file
// twice-comparable — once with `require_certificates` off (today's default)
// and once with it on — and report which evidence the verdict actually
// carried. This is the only way to price "batteries on".
//
//   cargo run --release -p ay-milp --example cert_probe -- file.mps 60 [0|1]

use std::time::{Duration, Instant};

use ay_milp::{BabSession, Outcome, SolveOpts};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Trailing `--<engine-flag>` args ride the shared engine CLI, exactly as
    // `mps_solve` does, so an evidence measurement can be taken under the same
    // configuration the throughput measurement was.
    let raw: Vec<String> = std::env::args().skip(1).collect();
    // `applied_flags()` ONLY: this harness has no flags of its own, and it took
    // `VALUE_FLAGS` — `ay-milp solve`'s table — until this commit. That
    // accepted `--require` and `--emit-cert`, neither of which it can carry:
    // `require` is POSITIONAL #3 here, so `cert_probe m 5 --require optimal`
    // reported `require_certificates=0` on 3 of 3 interleaved reps while
    // `cert_probe m 5 1` reported `1` on 3 of 3 — the flag named one arm and
    // measured the other. `--emit-cert F` left F absent on 3 of 3 while
    // `ay-milp solve` wrote 11,304 bytes. Both are now refused by name.
    let flags =
        ay_milp::engine_cli::parse_applied(&raw, &[], &[]).map_err(std::io::Error::other)?;
    let mut args = flags.positional.iter().cloned();
    let path = args.next().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "usage: cert_probe <file.mps> [secs] [0|1] [--engine-flags]",
        )
    })?;
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60.0);
    let require: bool = args.next().map(|s| s == "1").unwrap_or(false);

    let text = std::fs::read_to_string(&path)?;
    let p = ay_milp::read_mps(&text)?;
    let model = p.model.clone();

    let opts = SolveOpts::new()
        .with_time_limit(Duration::from_secs_f64(secs))
        .with_require_certificates(require);
    let opts = ay_milp::engine_cli::apply(&flags, opts).map_err(std::io::Error::other)?;
    let mut s = BabSession::new(p.model, &opts)?;
    let t0 = Instant::now();
    let out = s.check();
    let dt = t0.elapsed().as_secs_f64();
    let nodes = ay_milp::nodes_explored();

    let (status, value, evidence) = match &out {
        Ok(Outcome::Optimal { value, cert, .. }) => {
            let ev = match cert {
                Some(c) => {
                    // Timed: this is the SAME `verify` call the release exit
                    // gate (`session::validate_witnesses`) already makes, so
                    // the number below prices one certificate re-derivation —
                    // i.e. what a second, redundant release check would cost.
                    let t = Instant::now();
                    let ok = c.verify(&model).is_ok();
                    let verify_secs = t.elapsed().as_secs_f64();
                    format!(
                        "dual-cert(mults={},verify={},verify_secs={verify_secs:.6})+witness",
                        c.multipliers.len(),
                        if ok { "OK" } else { "FAIL" }
                    )
                }
                None => "witness-only(NO-DUAL-CERT)".to_string(),
            };
            ("OPTIMAL", ratio(&(value / &p.obj_scale)), ev)
        }
        Ok(Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        }) => {
            let v = s.model().objective_value_at(model_values);
            let ev = match dual_bound {
                Some(_) => "witness+uncertified-dual-bound".to_string(),
                None => "witness-only".to_string(),
            };
            ("FEASIBLE", ratio(&(&v / &p.obj_scale)), ev)
        }
        Ok(Outcome::Infeasible { cert, tree_cert }) => {
            let ev = match (cert, tree_cert) {
                (Some(c), _) => format!("root-farkas(mults={})", c.multipliers.len()),
                (None, Some(t)) => format!("tree-cert(leaves={})", t.num_leaves()),
                (None, None) => "NONE".to_string(),
            };
            ("INFEASIBLE", "-".to_string(), ev)
        }
        Ok(Outcome::Unbounded) => ("UNBOUNDED", "-".to_string(), "NONE".to_string()),
        Ok(Outcome::Unknown { reason }) => ("UNKNOWN", format!("{reason:?}"), "NONE".to_string()),
        Ok(o) => ("OTHER", format!("{o:?}"), "NONE".to_string()),
        Err(e) => ("ERROR", format!("{e:?}"), "NONE".to_string()),
    };
    // Price battery (a): serialize the exact witness, losslessly.
    let mut ser_bytes = 0usize;
    let mut ser_secs = 0.0f64;
    if let Ok(Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. }) = &out
    {
        let t = Instant::now();
        let mut s = String::new();
        for (j, v) in model_values.iter().enumerate() {
            use std::fmt::Write as _;
            let _ = writeln!(s, "{} {}/{}", p.col_names[j], v.numer(), v.denom());
        }
        ser_secs = t.elapsed().as_secs_f64();
        ser_bytes = s.len();
    }
    println!(
        "require_certificates={} {status} {value} {dt:.3} {nodes} evidence={evidence} \
         witness_bytes={ser_bytes} witness_ser_secs={ser_secs:.6}",
        u8::from(require)
    );
    Ok(())
}

fn ratio(v: &num_rational::BigRational) -> String {
    use num_traits::ToPrimitive as _;
    v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}"))
}
