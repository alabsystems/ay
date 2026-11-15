// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::acceptance_inventory::r34::{
    tests::{fixture, original},
    R34Row, R34RowStatus,
};
use ay_chc::{CancellationToken, ChcExpr, ClauseBody, HornClause};

fn captured_adaptive(archive: &R34Archive, row: &capture::Row) -> String {
    let (_, body) = archive
        .text(&row.config_file)
        .unwrap()
        .split_once("\nAdaptiveConfig {")
        .unwrap();
    format!("AdaptiveConfig {{{}", body.trim_end())
}

#[test]
fn exact_false_only_config_extension_admits_all_original_configurations() {
    let archive = fixture();
    for row in &archive.capture.rows {
        let config = config(&archive, row).unwrap();
        let original = captured_adaptive(&archive, row);
        assert!(!original.contains("require_ground_unsafe_trace"));
        let current = config.to_adaptive_config();
        assert!(!current.require_ground_unsafe_trace);
        assert!(matches!(
            compare_adaptive(&current, &original),
            AdaptiveBinding::HistoricalGroundTraceFalse
        ));
        assert!(matches!(
            compare_adaptive(&current, &format!("{current:#?}")),
            AdaptiveBinding::Exact
        ));
    }
}

#[test]
fn true_ground_trace_policy_and_every_unrelated_config_change_refuse() {
    let archive = fixture();
    let row = &archive.capture.rows[0];
    let config = config(&archive, row).unwrap();
    let captured = captured_adaptive(&archive, row);
    let mut current = config.to_adaptive_config();
    current.require_ground_unsafe_trace = true;
    assert!(matches!(
        compare_adaptive(&current, &captured),
        AdaptiveBinding::Refused(_)
    ));
    current.require_ground_unsafe_trace = false;
    for (old, new) in [
        ("strict_proofs: true", "strict_proofs: false"),
        ("622.866572ms", "623ms"),
        ("65286912000", "65286912001"),
        (
            "execution_mode: AdaptiveParallel",
            "execution_mode: DeterministicSequential",
        ),
        ("max_engines: None", "max_engines: Some(1)"),
        (
            "collapse_first_nested: false",
            "collapse_first_nested: true",
        ),
        ("progress_enabled: false", "progress_enabled: true"),
        (
            "preferred_engine_order: []",
            "preferred_engine_order: [Pdr]",
        ),
    ] {
        assert!(captured.contains(old), "nonvacuous mutation: {old}");
        let changed = captured.replace(old, new);
        assert!(
            matches!(
                compare_adaptive(&current, &changed),
                AdaptiveBinding::Refused(_)
            ),
            "{old}"
        );
    }
    let unknown_field = captured.replacen(
        "AdaptiveConfig {",
        "AdaptiveConfig {\n    future_field: false,",
        1,
    );
    assert!(matches!(
        compare_adaptive(&current, &unknown_field),
        AdaptiveBinding::Refused(_)
    ));
}

#[test]
fn changed_archived_adaptive_bytes_cannot_use_an_otherwise_accepted_mapping() {
    let mut archive = fixture();
    let file = archive.capture.rows[0].config_file.clone();
    let original = archive.text(&file).unwrap();
    let changed = original.replace(
        "strict_proofs: true,",
        "strict_proofs: true,\n    require_ground_unsafe_trace: false,",
    );
    assert_ne!(changed, original);
    archive.files.insert(file, changed.into_bytes());
    assert!(config(&archive, &archive.capture.rows[0]).is_err());
}

fn captured_encode(archive: &R34Archive, row: &capture::Row) -> String {
    let (_, rest) = archive
        .text(&row.config_file)
        .unwrap()
        .split_once("EncodeConfig {")
        .unwrap();
    let (body, _) = rest.split_once("\n\n# AdaptiveConfig").unwrap();
    format!("EncodeConfig {{{}", body.trim_end())
}

#[test]
fn only_default_effort_and_frame_cap_lines_may_be_absent_from_captured_config() {
    let archive = fixture();
    assert!(!archive.capture.rows.is_empty());
    for row in &archive.capture.rows {
        let config = config(&archive, row).unwrap();
        assert!(config.effort.is_none());
        assert!(config.pdr_max_frames.is_none());
        let captured = captured_encode(&archive, row);
        let current = format!("{config:#?}");
        assert!(!captured.contains("effort"));
        assert_eq!(current.matches("\n    effort: None,").count(), 1);
        assert_eq!(current.matches("\n    pdr_max_frames: None,").count(), 1);
        assert_ne!(current, captured, "nonvacuous historical spelling");
        assert!(require_captured_encode(&config, &captured).is_ok());
        assert!(require_captured_encode(&config, &current).is_ok());
        let before_frame_cap = current.replacen("\n    pdr_max_frames: None,", "", 1);
        assert!(require_captured_encode(&config, &before_frame_cap).is_ok());
        let mut counted = config.clone();
        counted.effort = Some(1);
        assert!(require_captured_encode(&counted, &captured).is_err());
        for frames in [0, 1, 1234] {
            let capped = config.clone().with_pdr_max_frames(frames);
            assert!(require_captured_encode(&capped, &captured).is_err());
            assert!(require_captured_encode(&capped, &before_frame_cap).is_err());
        }
        let memory = config.memory_budget.unwrap();
        let (memory, other_memory) = (memory.to_string(), (memory + 1).to_string());
        for (old, new) in [
            ("strict_validation: true", "strict_validation: false"),
            ("proof_mode: None", "proof_mode: Strict"),
            ("engine: Auto", "engine: Pdr"),
            (
                "execution_mode: AdaptiveParallel",
                "execution_mode: DeterministicSequential",
            ),
            (memory.as_str(), other_memory.as_str()),
            ("\n    lemma_hints: [],", ""),
            ("\n}", "\n    effort: Some(\n        1,\n    ),\n}"),
            ("\n}", "\n    effort: None,\n    effort: None,\n}"),
            ("\n}", "\n    pdr_max_frames: Some(1),\n}"),
            (
                "\n}",
                "\n    pdr_max_frames: None,\n    pdr_max_frames: None,\n}",
            ),
        ] {
            assert!(captured.contains(old), "nonvacuous mutation: {old}");
            let changed = captured.replacen(old, new, 1);
            assert!(require_captured_encode(&config, &changed).is_err(), "{old}");
        }
    }
}

#[test]
fn complete_actual_ast_migration_rejects_unused_registry_and_clause_changes() {
    let archive = fixture();
    let source = &archive.capture.sources["static"];
    let problem = capture::parse_source(&archive, source).unwrap();
    let expected = capture::string(&source.source_problem, "normalized_input_sha256").unwrap();
    let original_normalized = problem.normalized_input();
    assert!(matches!(
        identity::compare(&problem, &original_normalized, expected, None, &mut || true).unwrap(),
        Some(identity::Comparison::Historical { .. })
    ));
    let mut registry = problem.clone();
    registry.add_datatype_def(
        "r34_extra_unused".to_owned(),
        vec![("r34_extra_ctor".to_owned(), Vec::new())],
    );
    let mut clauses = problem.clone();
    let count = clauses.clauses().len();
    clauses.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    assert_eq!(clauses.clauses().len(), count + 1);
    for changed in [registry, clauses] {
        let current = changed.normalized_input();
        assert_ne!(current, original_normalized);
        assert!(matches!(
            identity::compare(&changed, &current, expected, None, &mut || true).unwrap(),
            Some(identity::Comparison::Refused(_))
        ));
    }
}

#[test]
fn historical_prepared_bytes_and_source_metadata_are_both_still_bound() {
    for change_bytes in [false, true] {
        let mut archive = fixture();
        if change_bytes {
            let row = &archive.capture.rows[2];
            let source = &archive.capture.sources[&row.source];
            let path = format!(
                "{}/{}",
                source.base,
                capture::string(&row.row["prepared_problem"], "file").unwrap()
            );
            archive.files.get_mut(&path).unwrap().push(b' ');
        } else {
            archive
                .capture
                .sources
                .get_mut("static")
                .unwrap()
                .source_problem["normalized_input_sha256"] = "0".repeat(64).into();
        }
        let record = archive
            .inspect_row(
                R34Row::StaticErrorP22,
                &original(),
                &CancellationToken::new(),
            )
            .unwrap();
        assert!(matches!(
            record.status,
            R34RowStatus::BindingRefused { .. } | R34RowStatus::ExecutionError { .. }
        ));
        assert!(!record.promotable_for_ask_closure);
    }
}

#[test]
fn captured_static_p22_migrates_without_minting_replay_authority() {
    // Bind the actual archive without making historical machine performance a
    // correctness requirement. replay_row still enforces its original 1.907s
    // cap; a timeout cannot acquire model-validation or strict-replay authority.
    let archive = fixture();
    let original = original();
    let record = archive
        .inspect_row(R34Row::StaticErrorP22, &original, &CancellationToken::new())
        .unwrap();
    assert_eq!(record.original_timeout_ns, 1_907_606_927);
    assert_eq!(
        record.prepared_sha256,
        "f6eaacca705a4f6394e694f220e2f724ade25ce2408a1cb9040605f26d07fa3a"
    );
    let binding = record.current_binding.as_ref().unwrap();
    assert!(binding.mismatches.is_empty());
    assert_eq!(binding.migrations.len(), 4);
    assert!(
        matches!(&record.status, R34RowStatus::BoundOnly),
        "{record:?}"
    );
    assert!(!record.promotable_for_ask_closure);
    assert!(original.ticks() > 1);
}

#[test]
fn source_and_prepared_dimension_metadata_cannot_be_changed_by_migration() {
    for (source, field) in [
        (true, "predicates"),
        (true, "clauses"),
        (false, "predicates"),
        (false, "clauses"),
    ] {
        let mut archive = fixture();
        let object = if source {
            &mut archive
                .capture
                .sources
                .get_mut("static")
                .unwrap()
                .source_problem
        } else {
            &mut archive.capture.rows[2].row["prepared_problem"]
        };
        object[field] = (object[field].as_u64().unwrap() + 1).into();
        let record = archive
            .inspect_row(
                R34Row::StaticErrorP22,
                &original(),
                &CancellationToken::new(),
            )
            .unwrap();
        assert!(
            matches!(record.status, R34RowStatus::ExecutionError { reason } if reason.contains("AST dimensions changed"))
        );
        assert!(!record.promotable_for_ask_closure);
    }
}
