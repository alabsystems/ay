// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! Export a read-only Fmla ledger-preview report from the Rust preview API.
//!
//! This example is diagnostic-only. It scans DIMACS inputs through
//! `FmlaGuardedEquivScout`, converts them with `FmlaLedgerPreview`, and emits
//! a stable JSON report for promotion gates. It never constructs a solver,
//! enables preprocessing transforms, or changes routing.

use ay_sat::fmla_guarded_equiv_scout::FmlaGuardedEquivScout;
use ay_sat::fmla_ledger_preview::FmlaLedgerPreview;
use ay_sat::parse_dimacs;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const SCHEMA: &str = "ay.w73-fmla-ledger-preview-export/v1";
const FMLA_PATH: &str = "benchmarks/sat/satcomp2024-sample/\
    9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz";
const CLIQUE_PATH: &str = "benchmarks/sat/satcomp2024-sample/\
    cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz";
const CIRCUIT_PATH: &str = "benchmarks/sat/satcomp2024-sample/\
    c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Role {
    FmlaTarget,
    Control,
}

#[derive(Debug, Clone, Copy)]
struct ExpectedCounts {
    transactions: usize,
    directional_witnesses: usize,
    touched_vars: usize,
    memory_bytes: usize,
}

#[derive(Debug, Clone, Copy)]
struct BenchmarkSpec {
    name: &'static str,
    path: &'static str,
    role: Role,
    expected_sha256: &'static str,
    expected: ExpectedCounts,
}

const BENCHMARKS: &[BenchmarkSpec] = &[
    BenchmarkSpec {
        name: "FmlaEquivChain_4_6_6",
        path: FMLA_PATH,
        role: Role::FmlaTarget,
        expected_sha256: "94e092124c5c13f9b4c5bf1b7f050a2e6aaac3c8e1daa894fb5b387f5074b220",
        expected: ExpectedCounts {
            transactions: 155_520,
            directional_witnesses: 311_040,
            touched_vars: 54_411,
            memory_bytes: 12_471_180,
        },
    },
    BenchmarkSpec {
        name: "clique_n2_k10",
        path: CLIQUE_PATH,
        role: Role::Control,
        expected_sha256: "61f6956ddf63cd443806094e702713b5c1263c977ad574cc74f0fe2cea684cf4",
        expected: ExpectedCounts {
            transactions: 0,
            directional_witnesses: 0,
            touched_vars: 0,
            memory_bytes: 0,
        },
    },
    BenchmarkSpec {
        name: "Circuit_multiplier22",
        path: CIRCUIT_PATH,
        role: Role::Control,
        expected_sha256: "840c1d8579db887b9e4a7b9eb051a58411f1c57aedd7a14814bd32d5e24fbcfd",
        expected: ExpectedCounts {
            transactions: 0,
            directional_witnesses: 0,
            touched_vars: 0,
            memory_bytes: 0,
        },
    },
];

#[derive(Debug)]
struct Options {
    check: bool,
    output: Option<PathBuf>,
    root: PathBuf,
}

#[derive(Debug)]
struct ExportedClass {
    transaction_class: &'static str,
    count: usize,
    touched_vars: usize,
}

#[derive(Debug)]
struct ExportedRow {
    spec: BenchmarkSpec,
    compressed_sha256: String,
    num_vars: usize,
    num_clauses: usize,
    detected_packet: bool,
    rejection: &'static str,
    guard_group_transactions: usize,
    mutex_source_clause_witnesses: usize,
    transactions: usize,
    directional_witnesses: usize,
    touched_vars: usize,
    model_reconstruction_witnesses_if_substituted: usize,
    memory_bytes: usize,
    memory_mib_x1000: usize,
    guard_vars_with_equivalences: usize,
    endpoint_vars: usize,
    onehot_width_hist: BTreeMap<usize, usize>,
    guard_fanout_hist: BTreeMap<usize, usize>,
    transaction_classes: Vec<ExportedClass>,
    fail_closed_criteria: Vec<&'static str>,
}

#[derive(Debug)]
struct CheckSummary {
    source_fingerprints_match: bool,
    fmla_counts_match: bool,
    controls_zero: bool,
    controls_fail_closed: bool,
    no_route_enabled: bool,
    errors: Vec<String>,
}

fn usage(program: &str) {
    eprintln!(
        "Usage: {program} [--check] [--output PATH] [--root REPO_ROOT]\n\
         Emits {SCHEMA} JSON from the read-only Fmla ledger preview API."
    );
}

fn parse_options(args: &[String]) -> Result<Options, String> {
    let default_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut options = Options {
        check: false,
        output: None,
        root: default_root,
    };
    let mut index = 1usize;
    while index < args.len() {
        match args[index].as_str() {
            "-h" | "--help" => {
                usage(&args[0]);
                std::process::exit(0);
            }
            "--check" => {
                options.check = true;
                index += 1;
            }
            "--output" => {
                let Some(path) = args.get(index + 1) else {
                    return Err("--output requires a path".to_string());
                };
                options.output = Some(PathBuf::from(path));
                index += 2;
            }
            "--root" => {
                let Some(path) = args.get(index + 1) else {
                    return Err("--root requires a path".to_string());
                };
                options.root = PathBuf::from(path);
                index += 2;
            }
            arg if arg.starts_with("--output=") => {
                options.output = Some(PathBuf::from(&arg["--output=".len()..]));
                index += 1;
            }
            arg if arg.starts_with("--root=") => {
                options.root = PathBuf::from(&arg["--root=".len()..]);
                index += 1;
            }
            other => {
                return Err(format!("unknown argument: {other}"));
            }
        }
    }
    Ok(options)
}

fn read_dimacs_input(root: &Path, relative_path: &str) -> Result<(Vec<u8>, String), String> {
    let path = root.join(relative_path);
    let compressed_bytes =
        fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
    if path
        .extension()
        .is_some_and(|extension| extension.eq_ignore_ascii_case("xz"))
    {
        let output = Command::new("xz")
            .arg("-dc")
            .arg("--")
            .arg(&path)
            .output()
            .map_err(|error| format!("run xz -dc for {}: {error}", path.display()))?;
        if !output.status.success() {
            return Err(format!(
                "xz -dc failed for {}: {}",
                path.display(),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let dimacs = String::from_utf8(output.stdout)
            .map_err(|error| format!("decoded DIMACS is not UTF-8: {error}"))?;
        Ok((compressed_bytes, dimacs))
    } else {
        let dimacs = String::from_utf8(compressed_bytes.clone())
            .map_err(|error| format!("DIMACS is not UTF-8: {error}"))?;
        Ok((compressed_bytes, dimacs))
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    format!("{digest:x}")
}

fn export_one(root: &Path, spec: BenchmarkSpec) -> Result<ExportedRow, String> {
    let (source_bytes, dimacs) = read_dimacs_input(root, spec.path)?;
    let formula = parse_dimacs(&dimacs).map_err(|error| format!("parse {}: {error}", spec.path))?;
    let scout = FmlaGuardedEquivScout::scan(formula.num_vars, &formula.clauses);
    let preview = FmlaLedgerPreview::from_scout(&scout);
    Ok(ExportedRow {
        spec,
        compressed_sha256: sha256_hex(&source_bytes),
        num_vars: formula.num_vars,
        num_clauses: formula.num_clauses,
        detected_packet: preview.detected_packet,
        rejection: preview.rejection.as_str(),
        guard_group_transactions: preview.source_counts.guard_group_transactions,
        mutex_source_clause_witnesses: preview.source_counts.mutex_source_clause_witnesses,
        transactions: preview.source_counts.guarded_equivalence_transactions,
        directional_witnesses: preview.source_counts.directional_ternary_clause_witnesses,
        touched_vars: preview.source_counts.touched_vars,
        model_reconstruction_witnesses_if_substituted: preview
            .source_counts
            .model_reconstruction_witnesses_if_substituted,
        memory_bytes: preview.memory_estimate.total_bytes,
        memory_mib_x1000: preview.memory_estimate.total_mib_x1000(),
        guard_vars_with_equivalences: preview.guard_vars_with_equivalences,
        endpoint_vars: preview.endpoint_vars,
        onehot_width_hist: preview.onehot_width_hist,
        guard_fanout_hist: preview.guard_fanout_hist,
        transaction_classes: preview
            .transaction_classes
            .into_iter()
            .map(|class| ExportedClass {
                transaction_class: class.transaction_class,
                count: class.count,
                touched_vars: class.touched_vars,
            })
            .collect(),
        fail_closed_criteria: preview.fail_closed_criteria,
    })
}

fn validate(rows: &[ExportedRow]) -> CheckSummary {
    let mut errors = Vec::new();
    let mut source_fingerprints_match = true;
    let mut fmla_counts_match = true;
    let mut controls_zero = true;
    let mut controls_fail_closed = true;
    let no_route_enabled = true;

    for row in rows {
        if row.compressed_sha256 != row.spec.expected_sha256 {
            source_fingerprints_match = false;
            errors.push(format!(
                "{} compressed_sha256 got {}, expected {}",
                row.spec.name, row.compressed_sha256, row.spec.expected_sha256
            ));
        }
        match row.spec.role {
            Role::FmlaTarget => {
                let expected = row.spec.expected;
                let row_matches = row.detected_packet
                    && row.rejection == "none"
                    && row.transactions == expected.transactions
                    && row.directional_witnesses == expected.directional_witnesses
                    && row.touched_vars == expected.touched_vars
                    && row.memory_bytes == expected.memory_bytes;
                if !row_matches {
                    fmla_counts_match = false;
                    errors.push(format!(
                        "{} drift: detected={} rejection={} transactions={} directional_witnesses={} touched_vars={} memory_bytes={}",
                        row.spec.name,
                        row.detected_packet,
                        row.rejection,
                        row.transactions,
                        row.directional_witnesses,
                        row.touched_vars,
                        row.memory_bytes
                    ));
                }
            }
            Role::Control => {
                let zero = !row.detected_packet
                    && row.transactions == 0
                    && row.directional_witnesses == 0
                    && row.touched_vars == 0
                    && row.model_reconstruction_witnesses_if_substituted == 0;
                if !zero {
                    controls_zero = false;
                    errors.push(format!(
                        "{} control drift: detected={} transactions={} directional_witnesses={} touched_vars={} model_witnesses={}",
                        row.spec.name,
                        row.detected_packet,
                        row.transactions,
                        row.directional_witnesses,
                        row.touched_vars,
                        row.model_reconstruction_witnesses_if_substituted
                    ));
                }
                if row.detected_packet || row.rejection == "none" {
                    controls_fail_closed = false;
                    errors.push(format!(
                        "{} control did not fail closed: detected={} rejection={}",
                        row.spec.name, row.detected_packet, row.rejection
                    ));
                }
            }
        }
    }

    CheckSummary {
        source_fingerprints_match,
        fmla_counts_match,
        controls_zero,
        controls_fail_closed,
        no_route_enabled,
        errors,
    }
}

fn row_json(row: &ExportedRow) -> Value {
    json!({
        "name": row.spec.name,
        "role": match row.spec.role {
            Role::FmlaTarget => "scoreboard-row",
            Role::Control => "control",
        },
        "path": row.spec.path,
        "compressed_sha256": row.compressed_sha256,
        "expected_compressed_sha256": row.spec.expected_sha256,
        "num_vars": row.num_vars,
        "num_clauses": row.num_clauses,
        "detected_packet": row.detected_packet,
        "rejection": row.rejection,
        "source_counts": {
            "guard_group_transactions": row.guard_group_transactions,
            "mutex_source_clause_witnesses": row.mutex_source_clause_witnesses,
            "transactions": row.transactions,
            "guarded_equivalence_transactions": row.transactions,
            "directional_witnesses": row.directional_witnesses,
            "directional_ternary_clause_witnesses": row.directional_witnesses,
            "touched_vars": row.touched_vars,
            "model_reconstruction_witnesses_if_substituted": row.model_reconstruction_witnesses_if_substituted,
        },
        "structure": {
            "guard_vars_with_equivalences": row.guard_vars_with_equivalences,
            "endpoint_vars": row.endpoint_vars,
            "onehot_width_hist": row.onehot_width_hist,
            "guard_fanout_hist": row.guard_fanout_hist,
        },
        "memory_estimate": {
            "total_bytes": row.memory_bytes,
            "total_mib_x1000": row.memory_mib_x1000,
            "total_mib": row.memory_mib_x1000 as f64 / 1000.0,
        },
        "transaction_classes": row.transaction_classes.iter().map(|class| {
            json!({
                "transaction_class": class.transaction_class,
                "count": class.count,
                "touched_vars": class.touched_vars,
            })
        }).collect::<Vec<_>>(),
        "fail_closed_criteria": row.fail_closed_criteria,
    })
}

fn report_json(rows: &[ExportedRow], checks: &CheckSummary) -> Value {
    json!({
        "schema": SCHEMA,
        "read_only": true,
        "api_source": {
            "scout": "ay_sat::fmla_guarded_equiv_scout::FmlaGuardedEquivScout::scan",
            "preview": "ay_sat::fmla_ledger_preview::FmlaLedgerPreview::from_scout",
        },
        "scoreboard_row": "FmlaEquivChain_4_6_6",
        "status": if checks.errors.is_empty() { "accepted" } else { "rejected" },
        "no_route_enabled": true,
        "transforms_enabled": false,
        "solver_invoked": false,
        "sat_comp_progress_claim": false,
        "proof_model_obligation_policy": {
            "destructive_transforms_allowed": false,
            "routing_allowed": false,
            "requires_original_dimacs_model_reconstruction_before_sat_substitution": true,
            "requires_checker_visible_unsat_proof_plan_before_clause_deletion_or_rewrite": true,
        },
        "expected_counters": {
            "transactions": 155520,
            "directional_witnesses": 311040,
            "touched_vars": 54411,
            "memory_bytes": 12471180,
        },
        "checks": {
            "source_fingerprints_match": checks.source_fingerprints_match,
            "fmla_counts_match": checks.fmla_counts_match,
            "controls_zero": checks.controls_zero,
            "controls_fail_closed": checks.controls_fail_closed,
            "no_route_enabled": checks.no_route_enabled,
            "errors": checks.errors,
        },
        "benchmarks": rows.iter().map(row_json).collect::<Vec<_>>(),
    })
}

fn write_report(report: &Value, output: Option<&Path>) -> Result<(), String> {
    let text = serde_json::to_string_pretty(report)
        .map_err(|error| format!("serialize JSON report: {error}"))?
        + "\n";
    if let Some(path) = output {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
        fs::write(path, text).map_err(|error| format!("write {}: {error}", path.display()))?;
    } else {
        print!("{text}");
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    let options = parse_options(&args)?;
    let rows = BENCHMARKS
        .iter()
        .copied()
        .map(|spec| export_one(&options.root, spec))
        .collect::<Result<Vec<_>, _>>()?;
    let checks = validate(&rows);
    let report = report_json(&rows, &checks);
    write_report(&report, options.output.as_deref())?;
    if options.check && !checks.errors.is_empty() {
        return Err(format!("FAIL-CLOSED: {}", checks.errors.join("; ")));
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
