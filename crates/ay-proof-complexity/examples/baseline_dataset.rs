// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generate the proof-complexity baseline dataset.
//!
//! Walks the full parametric corpus (php, parity, tseitin on a handful of
//! graphs, random-k-CNF at several clause/var ratios, ordering principle),
//! runs `ProofComplexityFeatures::from_cnf` on each instance, and emits a
//! JSONL file at the development design notes.
//!
//! Run from the repo root:
//!
//! ```bash
//! cargo run --example baseline_dataset -p ay-proof-complexity --release
//! ```
//!
//! The generated JSONL is local output, not shipped benchmark evidence.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

use ay_proof_complexity::{
    ordering_principle, parity, pigeonhole, random_k_cnf, tseitin, Cnf, Graph,
    ProofComplexityFeatures,
};

#[derive(serde::Serialize)]
struct Row<'a> {
    name: String,
    family: &'a str,
    params: serde_json::Value,
    features: ProofComplexityFeatures,
}

fn write_row<W: Write>(w: &mut W, row: &Row<'_>) -> std::io::Result<()> {
    let line = serde_json::to_string(row).expect("serialize row");
    writeln!(w, "{line}")
}

fn main() -> std::io::Result<()> {
    // Resolve the output path relative to the workspace root (the parent
    // of the crate directory). `CARGO_MANIFEST_DIR` points at the crate
    // directory for `examples/`, so go up two levels.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("crate has a workspace root")
        .to_path_buf();
    let out_dir = repo_root.join("reports").join("proof-complexity-baseline");
    std::fs::create_dir_all(&out_dir)?;
    let out_path = out_dir.join("baseline.jsonl");
    let mut out = BufWriter::new(File::create(&out_path)?);

    let mut total = 0u64;

    // Pigeonhole family: PHP_k for k=3..10. k=10 encodes 11 pigeons x 10
    // holes which is still small enough to generate fast.
    for k in 3..=10usize {
        let cnf: Cnf = pigeonhole(k);
        let features = ProofComplexityFeatures::from_cnf(&cnf);
        write_row(
            &mut out,
            &Row {
                name: format!("php-k{k}"),
                family: "php",
                params: serde_json::json!({ "holes": k, "pigeons": k + 1 }),
                features,
            },
        )?;
        total += 1;
    }

    // Parity family: xor_n for n=4..20. Parity(n) has 2^(n-1) clauses so
    // we cap at 20 to keep the dataset a few MB at worst.
    for n in 4..=20usize {
        let cnf = parity(n);
        let features = ProofComplexityFeatures::from_cnf(&cnf);
        write_row(
            &mut out,
            &Row {
                name: format!("parity-n{n}"),
                family: "parity",
                params: serde_json::json!({ "n": n }),
                features,
            },
        )?;
        total += 1;
    }

    // Tseitin family: small graphs with a single odd-charge vertex.
    // Covers cycles, grids, and a small complete graph.
    let tseitin_cases: Vec<(String, Graph)> = vec![
        ("cycle-n4".into(), Graph::cycle(4)),
        ("cycle-n6".into(), Graph::cycle(6)),
        ("cycle-n8".into(), Graph::cycle(8)),
        ("cycle-n10".into(), Graph::cycle(10)),
        ("cycle-n12".into(), Graph::cycle(12)),
        ("grid-2x3".into(), Graph::grid(2, 3)),
        ("grid-3x3".into(), Graph::grid(3, 3)),
        ("grid-3x4".into(), Graph::grid(3, 4)),
        ("complete-n4".into(), Graph::complete(4)),
        ("complete-n5".into(), Graph::complete(5)),
    ];
    for (tag, graph) in tseitin_cases {
        let n = graph.num_vertices();
        let charges: Vec<bool> = (0..n).map(|i| i == 0).collect();
        let cnf = tseitin(&graph, &charges);
        let features = ProofComplexityFeatures::from_cnf(&cnf);
        write_row(
            &mut out,
            &Row {
                name: format!("tseitin-{tag}"),
                family: "tseitin",
                params: serde_json::json!({ "graph": tag, "vertices": n }),
                features,
            },
        )?;
        total += 1;
    }

    // Random k-CNF family: width 3, various (n, m) ratios around the
    // 3-SAT threshold 4.267, plus a couple of easier ratios. Seeded
    // deterministically.
    let random_cases: &[(usize, usize, usize, f64)] = &[
        // (n, m, seed, ratio_hint)
        (20, 40, 1, 2.0),
        (20, 60, 2, 3.0),
        (20, 80, 3, 4.0),
        (20, 85, 4, 4.25),
        (20, 90, 5, 4.5),
        (30, 60, 6, 2.0),
        (30, 90, 7, 3.0),
        (30, 120, 8, 4.0),
        (30, 128, 9, 4.267),
        (30, 135, 10, 4.5),
        (50, 150, 11, 3.0),
        (50, 200, 12, 4.0),
        (50, 213, 13, 4.267),
        (50, 225, 14, 4.5),
        (80, 320, 15, 4.0),
        (80, 342, 16, 4.267),
    ];
    for &(n, m, seed, ratio) in random_cases {
        let cnf = random_k_cnf(3, n, m, Some(seed as u64));
        let features = ProofComplexityFeatures::from_cnf(&cnf);
        write_row(
            &mut out,
            &Row {
                name: format!("random-3sat-n{n}-m{m}-seed{seed}"),
                family: "random-k-cnf",
                params: serde_json::json!({
                    "k": 3,
                    "n": n,
                    "m": m,
                    "seed": seed,
                    "ratio": ratio,
                }),
                features,
            },
        )?;
        total += 1;
    }

    // Ordering-principle family: OP_n for n=4..10. OP(n) has ~n^3
    // transitivity clauses so n=10 is still well under 2k clauses.
    for n in 4..=10usize {
        let cnf = ordering_principle(n);
        let features = ProofComplexityFeatures::from_cnf(&cnf);
        write_row(
            &mut out,
            &Row {
                name: format!("op-n{n}"),
                family: "ordering-principle",
                params: serde_json::json!({ "n": n }),
                features,
            },
        )?;
        total += 1;
    }

    out.flush()?;

    eprintln!("wrote {total} rows to {}", out_path.display());
    Ok(())
}
