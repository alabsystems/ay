use std::{
    fs::File,
    io::{self, BufRead},
    path::Path,
};

use ahash::{HashMap, HashMapExt};

use anyhow::{Context, Result, ensure};
use clap::Parser;
use itertools::Itertools;

#[derive(Parser)]
#[command(about = "Compare VeriPB benchmark results between two branches")]
struct Args {
    main_csv: std::path::PathBuf,
    branch_csv: std::path::PathBuf,
}

const REGRESSION_THRESHOLD: f64 = 20.0;

fn main() -> Result<()> {
    let args = Args::parse();

    let main_data = read_instance_data(&args.main_csv)?;
    let branch_data = read_instance_data(&args.branch_csv)?;

    let mut instances: Vec<&str> = main_data.keys().map(String::as_str).collect();
    instances.sort_unstable();

    struct Row {
        instance: String,
        pbp_size_bytes: u64,
        main_s: f64,
        branch_s: f64,
        percentage_change: f64,
    }

    let rows: Vec<Row> = instances
        .iter()
        .filter_map(|inst| {
            let (main_s, pbp_size_bytes) = *main_data.get(*inst)?;
            let (branch_s, _) = *branch_data.get(*inst)?;
            let percentage_change = (branch_s - main_s) / main_s * 100.0;
            Some(Row {
                instance: inst.to_string(),
                pbp_size_bytes,
                main_s,
                branch_s,
                percentage_change,
            })
        })
        .sorted_by(|a, b| {
            // sort rows in descending order according to delta
            b.percentage_change
                .partial_cmp(&a.percentage_change)
                .unwrap()
        })
        .collect();

    ensure!(
        !rows.is_empty(),
        "no matching instances found between the two CSVs"
    );

    let fmt_time = |v: f64| format!("{v:.4}");
    let fmt_proof_size = |bytes: u64| -> String {
        if bytes >= 1_000_000 {
            format!("{:.1} MB", bytes as f64 / 1_000_000.0)
        } else if bytes >= 1_000 {
            format!("{:.1} KB", bytes as f64 / 1_000.0)
        } else {
            format!("{bytes} B")
        }
    };
    let fmt_percentage_change = |p: f64| {
        let sign = if p >= 0.0 { "+" } else { "" };
        format!("{sign}{p:.2}%")
    };

    let avg_percentage_change =
        rows.iter().map(|r| r.percentage_change).sum::<f64>() / rows.len() as f64;

    let instance_width = rows
        .iter()
        .map(|r| r.instance.len())
        .max()
        .unwrap()
        .max("Instance".len());
    let pbp_size_width = rows
        .iter()
        .map(|r| fmt_proof_size(r.pbp_size_bytes).len())
        .max()
        .unwrap()
        .max("proof size".len());
    let main_width = rows
        .iter()
        .map(|r| fmt_time(r.main_s).len())
        .max()
        .unwrap()
        .max("main (s)".len());
    let branch_width = rows
        .iter()
        .map(|r| fmt_time(r.branch_s).len())
        .max()
        .unwrap()
        .max("branch (s)".len());
    let avg_cell = format!("**{}**", fmt_percentage_change(avg_percentage_change));
    let delta_width = rows
        .iter()
        .map(|r| {
            let s = fmt_percentage_change(r.percentage_change);
            if r.percentage_change >= REGRESSION_THRESHOLD {
                s.len() + " [WARN]".len()
            } else {
                s.len()
            }
        })
        .max()
        .unwrap()
        .max("Δ%".len())
        .max(avg_cell.len());

    let row = |c0: &str, c1: &str, c2: &str, c3: &str, c4: &str| {
        format!(
            "| {c0:<instance_width$} | {c1:<pbp_size_width$} | {c2:<main_width$} | {c3:<branch_width$} | {c4:<delta_width$} |"
        )
    };

    // Fill column with dashes to create header separator row
    let sep = format!(
        "| {:-<instance_width$} | {:-<pbp_size_width$} | {:-<main_width$} | {:-<branch_width$} | {:-<delta_width$} |",
        "", "", "", "", ""
    );

    println!(
        "**Average change: {}**",
        fmt_percentage_change(avg_percentage_change)
    );

    let regressions: Vec<&Row> = rows
        .iter()
        .filter(|r| r.percentage_change >= REGRESSION_THRESHOLD)
        .collect();
    if !regressions.is_empty() {
        println!("\nIndividual regressions (>={REGRESSION_THRESHOLD:.0}% slower):");
        for r in &regressions {
            println!(
                "- {}: {}",
                r.instance,
                fmt_percentage_change(r.percentage_change)
            );
        }
    }

    println!();
    println!("<details>");
    println!("<summary>Benchmark Results (Click to Expand)</summary>\n");
    println!(
        "{}",
        row("Instance", "proof size", "main (s)", "branch (s)", "Δ%")
    );
    println!("{sep}");

    for r in &rows {
        let percentage_change_str = fmt_percentage_change(r.percentage_change);
        let percentage_change_cell = if r.percentage_change >= REGRESSION_THRESHOLD {
            format!("{percentage_change_str} [WARN]")
        } else {
            percentage_change_str
        };
        println!(
            "{}",
            row(
                &r.instance,
                &fmt_proof_size(r.pbp_size_bytes),
                &fmt_time(r.main_s),
                &fmt_time(r.branch_s),
                &percentage_change_cell
            )
        );
    }

    println!("{}", row("**Average**", "", "", "", &avg_cell));
    println!("\n</details>");

    if avg_percentage_change >= REGRESSION_THRESHOLD {
        eprintln!(
            "FAIL: average regression {avg_percentage_change:.2}% >= {REGRESSION_THRESHOLD}% threshold"
        );
        std::process::exit(1);
    }

    Ok(())
}

fn read_instance_data(path: &Path) -> Result<HashMap<String, (f64, u64)>> {
    let file = File::open(path).with_context(|| format!("opening {}", path.display()))?;
    let mut times: HashMap<String, Vec<f64>> = HashMap::new();
    let mut proof_sizes: HashMap<String, u64> = HashMap::new();
    let mut first = true;

    for line in io::BufReader::new(file).lines() {
        let line = line.context("reading line")?;
        if first {
            first = false;
            continue;
        }
        if line.trim().is_empty() {
            continue;
        }

        let mut parts = line.splitn(5, ',');
        let instance = match parts.next() {
            Some(s) if !s.is_empty() => s.to_owned(),
            _ => continue,
        };
        let _run = parts.next();
        let time_str = match parts.next() {
            Some(s) if !s.is_empty() => s,
            _ => continue,
        };
        let _exit_status = parts.next();
        let pbp_size_bytes_str = match parts.next() {
            Some(s) if !s.is_empty() => s,
            _ => continue,
        };

        let time: f64 = time_str
            .parse()
            .with_context(|| format!("parsing time '{time_str}' in: {line}"))?;
        let pbp_size_bytes: u64 = pbp_size_bytes_str
            .trim()
            .parse()
            .with_context(|| format!("parsing pbp_size_bytes '{pbp_size_bytes_str}' in: {line}"))?;

        times.entry(instance.clone()).or_default().push(time);
        proof_sizes.entry(instance).or_insert(pbp_size_bytes);
    }

    Ok(times
        .into_iter()
        .map(|(k, v)| {
            let avg = v.iter().sum::<f64>() / v.len() as f64;
            let pbp_size_bytes = proof_sizes.get(&k).copied().unwrap_or(0);
            (k, (avg, pbp_size_bytes))
        })
        .collect())
}
