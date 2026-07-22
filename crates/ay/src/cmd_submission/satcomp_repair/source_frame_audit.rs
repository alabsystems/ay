// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `source-frame-audit` subcommand + audit-only helpers (row auditing, W210
//! overlay, partial-assignment + source-hook summaries) for satcomp_repair.
//! Extracted from satcomp_repair.rs; shared `source_frame_row_has_valid_binding`
//! and the parse_source_frame_* primitives stay in the parent.

use super::*;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::Result;
use serde_json::{json, Value as JsonValue};

pub(super) fn run_source_frame_audit(opts: SourceFrameAuditOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common;
    let target_cnf = resolve_path(&root, &common.target_cnf);
    let formula = parse_dimacs_path(&target_cnf)?;
    let source_frame_rows = resolve_path(&root, &opts.source_frame_rows);
    let missing_source_rows = resolve_path(&root, &opts.missing_source_rows);
    let residual_hook_targets = resolve_path(&root, &opts.residual_hook_targets);
    let component_hook_targets = resolve_path(&root, &opts.component_hook_targets);
    let w210_overlay_enabled = opts.w210_overlay;

    let source_frame_table = read_tsv_table(&source_frame_rows)?;
    let missing_source_table = read_tsv_table(&missing_source_rows)?;
    let residual_hook_table = read_tsv_table(&residual_hook_targets)?;
    let component_hook_table = read_tsv_table(&component_hook_targets)?;
    let source_rows = parse_source_frame_rows(&source_frame_table, false)?;
    let missing_rows = parse_source_frame_rows(&missing_source_table, true)?;
    let (source_audit, direct_assignment, source_target_clauses) =
        audit_source_frame_input_rows(&formula, &source_rows, true);
    let (missing_audit, _, missing_target_clauses) =
        audit_source_frame_input_rows(&formula, &missing_rows, false);
    let source_audit = with_parse_errors(source_audit, source_rows.parse_errors);
    let missing_audit = with_parse_errors(missing_audit, missing_rows.parse_errors);
    let hook_summary = summarize_source_hook_targets(&residual_hook_table)?;
    let component_summary = summarize_component_source_hooks(&component_hook_table)?;
    let assignment_summary = summarize_partial_assignment(&formula, &direct_assignment);
    let w210_overlay = if w210_overlay_enabled {
        compute_w210_source_frame_overlay(&root, &common, &formula, &source_rows.rows)?
    } else {
        json!({
            "enabled": false,
            "note": "pass --w210-overlay to overlay accepted source-frame values onto the complete W210 assignment and rescan the original DIMACS",
        })
    };
    let source_schema_valid = source_audit.rows_rejected == 0;
    let missing_rows_present = missing_audit.rows_seen > 0;
    let complete_valid_model = assignment_summary["original_dimacs_valid_model"]
        .as_bool()
        .unwrap_or(false);
    let overlay_valid_model = w210_overlay["overlay"]["original_dimacs_valid_model"]
        .as_bool()
        .unwrap_or(false);
    let payload = json!({
        "schema": "ay.satcomp-circuit-source-frame-audit/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            git_head(&root),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI source-frame audit. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&target_cnf, &root),
            "sha256": sha256_file(&target_cnf)?,
            "num_vars": formula.num_vars,
            "num_clauses": formula.clauses.len(),
        },
        "artifacts": {
            "source_frame_rows": artifact_json(&source_frame_rows, &root)?,
            "missing_source_rows": artifact_json(&missing_source_rows, &root)?,
            "residual_hook_targets": artifact_json(&residual_hook_targets, &root)?,
            "component_hook_targets": artifact_json(&component_hook_targets, &root)?,
        },
        "allowed_source_families": ALLOWED_SOURCE_FRAME_FAMILIES,
        "source_frame_rows": {
            "header": source_frame_table.header,
            "rows_in_file": source_frame_table.rows.len(),
            "parsed_rows": source_rows.rows.len(),
            "parse_errors": source_rows.parse_errors,
            "parse_error_samples": source_rows.parse_error_samples,
            "audit": source_frame_audit_json(&source_audit),
            "family_counts": source_frame_family_counts(&source_rows.rows),
            "source_frame_row_id_samples": source_frame_row_id_samples(&source_rows.rows, 16),
            "targeted_clause_count": source_target_clauses.len(),
            "targeted_one_based_clause_ids": source_target_clauses.iter().take(64).copied().collect::<Vec<_>>(),
        },
        "diagnostic_missing_source_rows": {
            "header": missing_source_table.header,
            "rows_in_file": missing_source_table.rows.len(),
            "parsed_rows": missing_rows.rows.len(),
            "parse_errors": missing_rows.parse_errors,
            "parse_error_samples": missing_rows.parse_error_samples,
            "audit": source_frame_audit_json(&missing_audit),
            "source_frame_row_id_samples": source_frame_row_id_samples(&missing_rows.rows, 16),
            "targeted_clause_count": missing_target_clauses.len(),
            "targeted_one_based_clause_ids": missing_target_clauses.iter().take(64).copied().collect::<Vec<_>>(),
        },
        "residual_hook_targets": hook_summary,
        "component_hook_targets": component_summary,
        "direct_assignment_from_source_rows": assignment_summary,
        "w210_overlay_assignment": w210_overlay,
        "verdict": {
            "source_frame_rows_schema_valid": source_schema_valid,
            "diagnostic_missing_rows_present": missing_rows_present,
            "complete_original_dimacs_valid_model_found": complete_valid_model,
            "original_dimacs_validation_pass": complete_valid_model,
            "w210_overlay_original_dimacs_valid_model_found": overlay_valid_model,
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
            "blocker": if complete_valid_model {
                "Source-frame rows materialize a complete original-DIMACS-valid assignment, but this diagnostic still does not admit a solver route or grant SAT/model authority."
            } else if missing_rows_present {
                "Source-frame rows are a checked diagnostic surface, but diagnostic missing source rows remain and no complete original-DIMACS-valid model is materialized."
            } else {
                "Source-frame rows do not yet materialize a complete original-DIMACS-valid model."
            },
        },
    });
    write_payload(&root, &common, "source-frame-audit", &payload)
}

fn audit_source_frame_input_rows(
    formula: &RawFormula,
    rows: &SourceFrameParsedRows,
    require_source_value: bool,
) -> (SourceFrameRowAudit, Vec<Option<bool>>, BTreeSet<usize>) {
    let mut audit = SourceFrameRowAudit::default();
    let mut assignment = vec![None; formula.num_vars];
    let mut target_clauses = BTreeSet::new();
    for row in &rows.rows {
        audit.rows_seen += 1;
        let mut accepted = true;
        if !ALLOWED_SOURCE_FRAME_FAMILIES.contains(&row.source_family.as_str()) {
            audit.unsupported_family += 1;
            accepted = false;
        }
        if row.var_one_based == 0 || row.var_one_based > formula.num_vars {
            audit.var_out_of_range += 1;
            accepted = false;
        }
        if lit_var(row.lit) != row.var_one_based {
            audit.literal_var_mismatch += 1;
            accepted = false;
        }
        if row.clause_id_one_based == 0 || row.clause_id_one_based > formula.clauses.len() {
            audit.clause_out_of_range += 1;
            accepted = false;
        } else {
            target_clauses.insert(row.clause_id_one_based);
            let clause = &formula.clauses[row.clause_id_one_based - 1];
            if row.literal_index_one_based == 0 || row.literal_index_one_based > clause.len() {
                audit.literal_index_out_of_range += 1;
                accepted = false;
            } else if clause[row.literal_index_one_based - 1] != row.lit {
                audit.literal_index_mismatch += 1;
                accepted = false;
            }
            if !clause.contains(&row.lit) {
                audit.literal_missing_from_clause += 1;
                accepted = false;
            }
        }
        if row.required_value_to_satisfy_literal != (row.lit > 0) {
            audit.required_value_mismatch += 1;
            accepted = false;
        }
        let Some(source_value) = row.source_value else {
            if require_source_value {
                audit.parse_errors += 1;
            }
            audit.rows_rejected += 1;
            continue;
        };
        if source_value == row.required_value_to_satisfy_literal {
            audit.source_value_satisfies_literal += 1;
        } else {
            audit.source_value_falsifies_literal += 1;
        }
        if accepted && row.var_one_based > 0 && row.var_one_based <= formula.num_vars {
            let var = row.var_one_based - 1;
            match assignment[var] {
                None => assignment[var] = Some(source_value),
                Some(existing) if existing == source_value => {}
                Some(_) => {
                    audit.conflicts += 1;
                    accepted = false;
                }
            }
        }
        if accepted {
            audit.rows_accepted += 1;
        } else {
            audit.rows_rejected += 1;
        }
    }
    (audit, assignment, target_clauses)
}

fn with_parse_errors(mut audit: SourceFrameRowAudit, parse_errors: usize) -> SourceFrameRowAudit {
    audit.rows_seen += parse_errors;
    audit.rows_rejected += parse_errors;
    audit.parse_errors += parse_errors;
    audit
}

fn source_frame_audit_json(audit: &SourceFrameRowAudit) -> JsonValue {
    json!({
        "rows_seen": audit.rows_seen,
        "rows_accepted": audit.rows_accepted,
        "rows_rejected": audit.rows_rejected,
        "unsupported_family": audit.unsupported_family,
        "var_out_of_range": audit.var_out_of_range,
        "literal_var_mismatch": audit.literal_var_mismatch,
        "clause_out_of_range": audit.clause_out_of_range,
        "literal_index_out_of_range": audit.literal_index_out_of_range,
        "literal_index_mismatch": audit.literal_index_mismatch,
        "literal_missing_from_clause": audit.literal_missing_from_clause,
        "required_value_mismatch": audit.required_value_mismatch,
        "parse_errors": audit.parse_errors,
        "conflicts": audit.conflicts,
        "source_value_satisfies_literal": audit.source_value_satisfies_literal,
        "source_value_falsifies_literal": audit.source_value_falsifies_literal,
    })
}

fn source_frame_family_counts(rows: &[SourceFrameRow]) -> JsonValue {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.source_family.clone()).or_insert(0usize) += 1;
    }
    json!(counts)
}

fn source_frame_row_id_samples(rows: &[SourceFrameRow], limit: usize) -> Vec<String> {
    rows.iter()
        .take(limit)
        .map(|row| row.source_frame_row_id.clone())
        .collect()
}

fn summarize_partial_assignment(formula: &RawFormula, assignment: &[Option<bool>]) -> JsonValue {
    let assigned_vars = assignment.iter().filter(|value| value.is_some()).count();
    let first_missing_vars: Vec<_> = assignment
        .iter()
        .enumerate()
        .filter_map(|(idx, value)| value.is_none().then_some(idx + 1))
        .take(32)
        .collect();
    let assignment_complete =
        assignment.len() == formula.num_vars && assigned_vars == formula.num_vars;
    let residual = if assignment_complete {
        let complete: Vec<bool> = assignment.iter().map(|value| value.unwrap()).collect();
        residual_clause_ids(&formula.clauses, &complete)
    } else {
        Vec::new()
    };
    let residual_count = if assignment_complete {
        json!(residual.len())
    } else {
        JsonValue::Null
    };
    json!({
        "assignment_slots": assignment.len(),
        "assigned_vars": assigned_vars,
        "missing_source_var_count": formula.num_vars.saturating_sub(assigned_vars),
        "first_missing_source_vars": first_missing_vars,
        "assignment_complete": assignment_complete,
        "original_dimacs_clauses_checked": if assignment_complete { formula.clauses.len() } else { 0 },
        "residual_falsified_clause_count": residual_count,
        "residual_falsified_one_based_clause_ids": residual.iter().take(64).map(|idx| idx + 1).collect::<Vec<_>>(),
        "original_dimacs_valid_model": assignment_complete && residual.is_empty(),
    })
}

fn compute_w210_source_frame_overlay(
    root: &Path,
    common: &CommonOptions,
    formula: &RawFormula,
    source_rows: &[SourceFrameRow],
) -> Result<JsonValue> {
    let ledgers = ledger_paths(root, common);
    let (base_assignment, ledger_stats) = parse_w210_assignment(formula.num_vars, &ledgers)?;
    let base_residual = residual_clause_ids(&formula.clauses, &base_assignment);
    let mut overlay_assignment = base_assignment.clone();
    let mut source_values = vec![None; formula.num_vars];
    let mut rows_applied = 0usize;
    let mut rows_skipped = 0usize;
    let mut duplicate_same = 0usize;
    let mut conflicting_source_values = 0usize;
    let mut changed_vars = BTreeSet::new();
    for row in source_rows {
        if !source_frame_row_has_valid_binding(formula, row) {
            rows_skipped += 1;
            continue;
        }
        let Some(value) = row.source_value else {
            rows_skipped += 1;
            continue;
        };
        let var = row.var_one_based - 1;
        match source_values[var] {
            None => source_values[var] = Some(value),
            Some(existing) if existing == value => duplicate_same += 1,
            Some(_) => {
                conflicting_source_values += 1;
                rows_skipped += 1;
                continue;
            }
        }
        if overlay_assignment[var] != value {
            overlay_assignment[var] = value;
            changed_vars.insert(var + 1);
        }
        rows_applied += 1;
    }
    let overlay_residual = residual_clause_ids(&formula.clauses, &overlay_assignment);
    let changed_var_count = changed_vars.len();
    Ok(json!({
        "enabled": true,
        "w210_ledgers": {
            "paths": ledgers.iter().map(|path| display_path_for_report(path, root)).collect::<Vec<_>>(),
            "sha256": ledgers.iter().map(|path| sha256_file(path)).collect::<Result<Vec<_>>>()?,
            "stats": ledger_stats,
        },
        "base": {
            "residual_falsified_clause_count": base_residual.len(),
            "residual_falsified_one_based_clause_ids": base_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        },
        "overlay": {
            "source_rows_applied": rows_applied,
            "source_rows_skipped": rows_skipped,
            "duplicate_same_source_values": duplicate_same,
            "conflicting_source_values": conflicting_source_values,
            "changed_var_count": changed_var_count,
            "one_based_changed_vars": changed_vars,
            "original_dimacs_clauses_checked": formula.clauses.len(),
            "residual_falsified_clause_count": overlay_residual.len(),
            "residual_falsified_one_based_clause_ids": overlay_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
            "original_dimacs_valid_model": overlay_residual.is_empty(),
        },
        "authority": {
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
        },
    }))
}

fn summarize_source_hook_targets(table: &TsvTable) -> Result<JsonValue> {
    let mut required_literal_rows = 0usize;
    let mut diagnostic_missing_literal_rows = 0usize;
    let mut parse_errors = 0usize;
    let mut uncovered_rows = 0usize;
    let mut family_counts = BTreeMap::new();
    let mut class_counts = BTreeMap::new();
    let mut clause_ids = BTreeSet::new();
    for (idx, row) in table.rows.iter().enumerate() {
        if let Some(value) = row.get("required_literal_rows") {
            match value.parse::<usize>() {
                Ok(value) => required_literal_rows += value,
                Err(_) => parse_errors += 1,
            }
        }
        if let Some(value) = row.get("diagnostic_missing_literal_rows") {
            match value.parse::<usize>() {
                Ok(value) => diagnostic_missing_literal_rows += value,
                Err(_) => parse_errors += 1,
            }
        }
        if row
            .get("covered_by_required_family")
            .is_some_and(|value| value != "true")
        {
            uncovered_rows += 1;
        }
        if let Some(class) = row.get("source_frame_class") {
            *class_counts.entry(class.clone()).or_insert(0usize) += 1;
        }
        if let Some(families) = row.get("covered_real_source_families") {
            for family in families.split_whitespace().filter(|value| *value != ".") {
                *family_counts.entry(family.to_string()).or_insert(0usize) += 1;
            }
        }
        if !row.contains_key("clause_id") {
            parse_errors += 1;
        } else {
            match row["clause_id"].parse::<usize>() {
                Ok(value) => {
                    clause_ids.insert(value);
                }
                Err(_) => parse_errors += 1,
            }
        }
        if idx > table.rows.len() {
            unreachable!("enumerate index cannot exceed row count");
        }
    }
    let unique_clause_count = clause_ids.len();
    Ok(json!({
        "rows": table.rows.len(),
        "required_literal_rows": required_literal_rows,
        "one_based_clause_ids": clause_ids,
        "unique_clause_count": unique_clause_count,
        "diagnostic_missing_literal_rows": diagnostic_missing_literal_rows,
        "covered_by_required_family_false_rows": uncovered_rows,
        "source_frame_class_counts": class_counts,
        "covered_real_source_family_counts": family_counts,
        "parse_errors": parse_errors,
    }))
}

fn summarize_component_source_hooks(table: &TsvTable) -> Result<JsonValue> {
    let mut component_ids = BTreeSet::new();
    let mut parse_errors = 0usize;
    for row in &table.rows {
        if let Some(value) = row.get("component_id") {
            match value.parse::<usize>() {
                Ok(value) => {
                    component_ids.insert(value);
                }
                Err(_) => parse_errors += 1,
            }
        }
    }
    Ok(json!({
        "rows": table.rows.len(),
        "component_count": component_ids.len(),
        "component_ids": component_ids,
        "parse_errors": parse_errors,
    }))
}
