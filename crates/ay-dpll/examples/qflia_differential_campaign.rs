// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended QF_LIA differential campaign.
//!
//! The default unit tests run bounded deterministic strata.  This executable
//! reuses the exact same generator and independent witness oracle for longer
//! campaigns without turning optional work into an ignored test:
//!
//! ```text
//! cargo run -p ay-dpll --release --example qflia_differential_campaign -- --seeds 5000
//! ```
//!
//! Z3 is used when it is available on `PATH`; pass `--no-z3` to disable that
//! cross-check or `--single-shot` to omit the incremental comparison.

use ay_dpll::Executor;

#[allow(dead_code)]
#[path = "../src/executor_tests/qflia_differential_fuzz.rs"]
mod campaign;

fn find_z3() -> Option<std::path::PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join("z3"))
        .find(|candidate| candidate.is_file())
}

fn usage() -> &'static str {
    "usage: qflia_differential_campaign [--seeds N] [--single-shot] [--no-z3]"
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut seeds = 5_000u64;
    let mut check_incremental = true;
    let mut use_z3 = true;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--seeds" => {
                let raw = args.next().ok_or_else(|| usage().to_string())?;
                seeds = raw
                    .parse()
                    .map_err(|_| format!("invalid --seeds value `{raw}`"))?;
            }
            "--single-shot" => check_incremental = false,
            "--no-z3" => use_z3 = false,
            "-h" | "--help" => {
                println!("{}", usage());
                return Ok(());
            }
            _ => return Err(format!("unknown argument `{arg}`\n{}", usage()).into()),
        }
    }
    if seeds == 0 {
        return Err("--seeds must be positive".into());
    }

    let z3 = use_z3.then(find_z3).flatten();
    eprintln!(
        "qflia differential campaign: seeds={seeds} incremental={check_incremental} z3={}",
        z3.as_ref().map_or_else(
            || "disabled/unavailable".to_string(),
            |path| path.display().to_string()
        )
    );
    let (sat, unsat, unknown) = campaign::run_campaign(seeds, z3.as_deref(), check_incremental);
    println!("completed: seeds={seeds} sat={sat} unsat={unsat} unknown={unknown}");
    Ok(())
}
