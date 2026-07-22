// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! Export the W88 capture-only runtime ledger scaffold for FmlaEquivChain.
//!
//! The exporter exercises Rust source scanning and in-memory record emission.
//! It does not construct a solver, mutate clauses, enable a route, or emit a
//! SAT-COMP progress claim.

use ay_sat::fmla_runtime_ledger::{
    FmlaRuntimeLedger, FmlaRuntimeLedgerRecord, FmlaRuntimeLedgerStats,
    FmlaRuntimeTransactionCapture, FMLA_RUNTIME_LEDGER_SCHEMA, W83_RUNTIME_RECORD_GROUPS,
    W83_RUNTIME_REQUIRED_FIELDS,
};
use ay_sat::parse_dimacs;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const SCOREBOARD_ROW: &str = "FmlaEquivChain_4_6_6";
const ISSUE: u64 = 9489;
const FMLA_PATH: &str = "benchmarks/sat/satcomp2024-sample/\
    9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz";
const FMLA_SHA256: &str = "94e092124c5c13f9b4c5bf1b7f050a2e6aaac3c8e1daa894fb5b387f5074b220";

#[derive(Debug)]
struct Options {
    check: bool,
    output: Option<PathBuf>,
    root: PathBuf,
}

fn usage(program: &str) {
    eprintln!(
        "Usage: {program} [--check] [--output PATH] [--root REPO_ROOT]\n\
         Emits {FMLA_RUNTIME_LEDGER_SCHEMA} JSON from the W88 runtime ledger scaffold."
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
    if path.extension().is_some_and(|extension| extension == "xz") {
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

fn stats_json(stats: FmlaRuntimeLedgerStats) -> Value {
    json!({
        "capture_enabled": stats.capture_enabled,
        "records_emitted": stats.records_emitted,
        "record_groups_emitted": stats.record_groups_emitted,
        "runtime_required_fields_represented": stats.runtime_required_fields_represented,
        "duplicate_represented_fields": stats.duplicate_represented_fields,
        "witness_checker_passed": stats.witness_checker_passed,
        "witness_checker_failed": stats.witness_checker_failed,
        "model_reconstruction_ready": stats.model_reconstruction_ready,
        "proof_obligation_ready": stats.proof_obligation_ready,
        "destructive_transform_allowed": stats.destructive_transform_allowed,
        "wrong_count": stats.wrong_count,
        "invalid_count": stats.invalid_count,
    })
}

fn transaction_json(transaction: &FmlaRuntimeTransactionCapture) -> Value {
    json!({
        "transaction_id": transaction.transaction_id,
        "mutation_epoch": transaction.mutation_epoch,
        "pre_mutation_clause_epoch": transaction.pre_mutation_clause_epoch,
        "removed_original_var": transaction.removed_original_var,
        "retained_original_var": transaction.retained_original_var,
        "model_reconstruction_stack_index": transaction.model_reconstruction_stack_index,
        "guard_group": {
            "support_clause_id": transaction.guard_group.support_clause_id,
            "vars": &transaction.guard_group.vars,
            "mutex_clause_ids": &transaction.guard_group.mutex_clause_ids,
        },
        "guarded_equivalence": {
            "guard": transaction.guarded_equivalence.guard,
            "lhs": transaction.guarded_equivalence.lhs,
            "rhs": transaction.guarded_equivalence.rhs,
            "forward_clause_id": transaction.guarded_equivalence.forward_clause_id,
            "reverse_clause_id": transaction.guarded_equivalence.reverse_clause_id,
            "forward_clause_lits": &transaction.guarded_equivalence.forward_clause_lits,
            "reverse_clause_lits": &transaction.guarded_equivalence.reverse_clause_lits,
            "directional_clause_pair_complete": transaction.witness_checker_failures.is_empty(),
        },
        "replay_dependencies": {
            "guard_lhs_rhs": &transaction.replay_dependencies.guard_lhs_rhs,
            "source_clause_ids": &transaction.replay_dependencies.source_clause_ids,
        },
        "witness_checker": {
            "status": if transaction.witness_checker_failures.is_empty() { "pass" } else { "fail" },
            "failures": &transaction.witness_checker_failures,
        },
    })
}

fn records_json(records: &[FmlaRuntimeLedgerRecord]) -> Value {
    Value::Array(
        records
            .iter()
            .map(|record| {
                json!({
                    "transaction_id": record.transaction_id,
                    "record_group_id": record.record_group_id,
                    "runtime_record": record.runtime_record,
                    "gate_open": record.gate_open,
                    "fields": record.fields.iter().map(|field| {
                        json!({
                            "name": field.name,
                            "status": field.status.as_str(),
                            "detail": field.detail,
                        })
                    }).collect::<Vec<_>>(),
                })
            })
            .collect(),
    )
}

fn field_to_group_json() -> Value {
    let mut by_field = BTreeMap::new();
    for group in W83_RUNTIME_RECORD_GROUPS {
        for field in group.covered_fields {
            by_field.insert(*field, group.record_group_id);
        }
    }
    json!(by_field)
}

fn build_payload(root: &Path) -> Result<Value, String> {
    let (source_bytes, dimacs) = read_dimacs_input(root, FMLA_PATH)?;
    let compressed_sha256 = sha256_hex(&source_bytes);
    let formula = parse_dimacs(&dimacs).map_err(|error| format!("parse {FMLA_PATH}: {error}"))?;

    let mut disabled = FmlaRuntimeLedger::disabled();
    let default_capture = disabled.capture_representative_guarded_equivalence(&formula.clauses);
    debug_assert!(default_capture.is_none());

    let mut capture = FmlaRuntimeLedger::capture_only();
    capture
        .capture_representative_guarded_equivalence(&formula.clauses)
        .ok_or_else(|| {
            "capture-only ledger did not emit a representative transaction".to_string()
        })?;
    let transaction = capture
        .last_transaction()
        .ok_or_else(|| "capture-only ledger has no last transaction".to_string())?;
    let capture_stats = capture.stats();

    let mut errors = Vec::new();
    if compressed_sha256 != FMLA_SHA256 {
        errors.push(format!(
            "source sha256 {compressed_sha256} != expected {FMLA_SHA256}"
        ));
    }
    if disabled.stats().records_emitted != 0 {
        errors.push("default-off ledger emitted records".to_string());
    }
    if capture_stats.records_emitted != 6 || capture_stats.record_groups_emitted != 6 {
        errors.push(format!(
            "expected six emitted records/groups, got {}/{}",
            capture_stats.records_emitted, capture_stats.record_groups_emitted
        ));
    }
    if capture_stats.runtime_required_fields_represented != 16 {
        errors.push(format!(
            "expected 16 represented W83 fields, got {}",
            capture_stats.runtime_required_fields_represented
        ));
    }
    if capture_stats.duplicate_represented_fields != 0 {
        errors.push(format!(
            "duplicate represented fields: {}",
            capture_stats.duplicate_represented_fields
        ));
    }
    if capture_stats.witness_checker_passed != 1 || capture_stats.witness_checker_failed != 0 {
        errors.push("witness checker did not pass exactly once".to_string());
    }
    if capture_stats.model_reconstruction_ready
        || capture_stats.proof_obligation_ready
        || capture_stats.destructive_transform_allowed
    {
        errors.push("proof/model/destructive gates must remain closed".to_string());
    }
    if capture_stats.wrong_count != 0 || capture_stats.invalid_count != 0 {
        errors.push("wrong/invalid counts must stay zero".to_string());
    }

    let status = if errors.is_empty() {
        "accepted"
    } else {
        "fail-closed"
    };

    Ok(json!({
        "schema": FMLA_RUNTIME_LEDGER_SCHEMA,
        "issue": ISSUE,
        "scoreboard_row": SCOREBOARD_ROW,
        "status": status,
        "errors": errors,
        "read_only": true,
        "solver_invoked": false,
        "route_enabled": false,
        "transforms_enabled": false,
        "sat_comp_progress_claim": false,
        "source": {
            "path": FMLA_PATH,
            "compressed_sha256": compressed_sha256,
            "expected_sha256": FMLA_SHA256,
            "num_vars": formula.num_vars,
            "num_clauses": formula.num_clauses,
        },
        "default_off_probe": stats_json(disabled.stats()),
        "runtime_capture": stats_json(capture_stats),
        "w83_runtime_required_fields": W83_RUNTIME_REQUIRED_FIELDS,
        "field_to_record_group": field_to_group_json(),
        "transaction": transaction_json(transaction),
        "records": records_json(capture.records()),
    }))
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    let options = parse_options(&args)?;
    let payload = build_payload(&options.root)?;
    let rendered = serde_json::to_string_pretty(&payload)
        .map_err(|error| format!("render JSON payload: {error}"))?;
    if let Some(path) = &options.output {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
        fs::write(path, format!("{rendered}\n"))
            .map_err(|error| format!("write {}: {error}", path.display()))?;
    } else {
        println!("{rendered}");
    }

    if options.check && payload.get("status").and_then(Value::as_str) != Some("accepted") {
        return Err(format!(
            "runtime ledger scaffold rejected: {}",
            payload
                .get("errors")
                .map_or_else(|| "<missing errors>".to_string(), Value::to_string)
        ));
    }
    Ok(())
}
