use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::Instant,
};

use anyhow::{Context, Result};
use clap::Parser;
use colored::Colorize;
use log::Level;
use std::io::Write;

#[derive(Parser)]
#[command(about = "Benchmark veripb on a directory of formula-proof instance pairs")]
struct Args {
    /// Directory containing benchmark instances (can have nested subdirs)
    benchmark_dir: PathBuf,

    /// Number of timed runs per instance
    #[arg(short, long, default_value_t = 3, value_parser = clap::value_parser!(u32).range(1..))]
    runs: u32,

    /// Path to veripb binary
    #[arg(long, default_value = env!("CARGO_BIN_EXE_veripb"))]
    binary: PathBuf,
}

fn main() -> Result<()> {
    // Cargo injects --bench when running with `cargo bench`: ignore
    let args = Args::parse_from(std::env::args().filter(|a| a != "--bench"));

    env_logger::Builder::new()
        .filter_level(log::LevelFilter::Warn)
        .format(|buf, record| {
            let label = match record.level() {
                Level::Error => "Error".red().bold(),
                Level::Warn => "Warning".yellow().bold(),
                Level::Info => "Info".cyan().bold(),
                Level::Debug | Level::Trace => "Debug".bright_black().bold(),
            };
            writeln!(buf, "{label}: {}", record.args())
        })
        .init();

    let benchmark_dir = args
        .benchmark_dir
        .canonicalize()
        .with_context(|| format!("benchmark dir not found: {}", args.benchmark_dir.display()))?;

    let mut instances = Vec::new();
    collect_instances(&benchmark_dir, &mut instances)?;
    instances.sort();

    println!("instance,run,time_seconds,exit_status,pbp_size_bytes");

    for (formula, proof) in &instances {
        let instance_name = formula.file_stem().unwrap_or_default().to_string_lossy();
        let pbp_size_bytes = fs::metadata(proof)
            .with_context(|| format!("reading metadata for {}", proof.display()))?
            .len();

        for run in 0..args.runs {
            let (elapsed, status) = time_run(&args.binary, formula, proof)
                .with_context(|| format!("failed to run {instance_name}"))?;
            println!("{instance_name},{run},{elapsed:.4},{status},{pbp_size_bytes}");
        }
    }

    Ok(())
}

fn collect_instances(dir: &Path, out: &mut Vec<(PathBuf, PathBuf)>) -> Result<()> {
    for entry in fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let path = entry?.path();
        if path.is_dir() && !path.is_symlink() {
            collect_instances(&path, out)?;
        } else if path
            .extension()
            .is_some_and(|e| e == "opb" || e == "cnf" || e == "wcnf")
        {
            let proof = path.with_extension("pbp");
            if proof.exists() {
                out.push((path, proof));
            }
        }
    }
    Ok(())
}

fn time_run(binary: &Path, formula: &Path, proof: &Path) -> Result<(f64, i32)> {
    let start = Instant::now();
    let status = Command::new(binary)
        .args([formula, proof])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .context("failed to spawn veripb")?;
    let elapsed = start.elapsed().as_secs_f64();
    let code = status.code().unwrap_or(-1);
    if !status.success() {
        if status.code().is_none() {
            log::error!("VeriPB was killed by a signal for {}", formula.display());
        } else {
            log::error!("VeriPB exited with status {code} for {}", formula.display());
        }
    }
    Ok((elapsed, code))
}
