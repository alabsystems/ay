// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn all_four_original_rows_preserve_nanosecond_caps_and_expose_identity_migration() {
    let bundle = fixture();
    for (case, nanos) in
        R34Row::ALL
            .into_iter()
            .zip([622_866_572, 622_477_385, 1_907_606_927, 5_185_898_469])
    {
        let record = bundle
            .inspect_row(case, &original(), &CancellationToken::new())
            .unwrap();
        assert_eq!(record.original_timeout_ns, nanos);
        let binding = record.current_binding.as_ref().unwrap();
        assert_eq!(
            binding.source_schema,
            if case == R34Row::AllocErrorP28 {
                "ay.chc.normalized-input/v1"
            } else {
                "ay.chc.normalized-input/v2"
            }
        );
        assert!(binding.mismatches.is_empty());
        assert_eq!(
            binding.migrations.len(),
            if case == R34Row::AllocErrorP28 { 1 } else { 4 }
        );
        assert!(matches!(record.status, R34RowStatus::BoundOnly));
        assert_not_promotable(&record);
    }
}

#[test]
fn execution_cannot_waive_the_original_prepared_identity() {
    for case in R34Row::ALL {
        let mut bundle = fixture();
        bundle.capture.rows[case.index()].row["identity"]["content_sha256"] = "0".repeat(64).into();
        let record = bundle
            .replay_row(case, &original(), &CancellationToken::new())
            .unwrap();
        assert!(matches!(record.status, R34RowStatus::BindingRefused { .. }));
        assert_not_promotable(&record);
    }
}

#[test]
fn changed_source_bytes_are_rejected_even_when_the_smt_remains_valid() {
    let mut bundle = fixture();
    let path = format!("{}/source.smt2", bundle.capture.sources["static"].base);
    bundle
        .files
        .get_mut(&path)
        .unwrap()
        .extend_from_slice(b"\n; semantic no-op mutation\n");
    let record = bundle
        .inspect_row(
            R34Row::StaticErrorP0,
            &original(),
            &CancellationToken::new(),
        )
        .unwrap();
    assert!(
        matches!(record.status, R34RowStatus::ExecutionError { ref reason } if reason.contains("source bytes identity mismatch"))
    );
    assert!(record.current_binding.is_none());
    assert_not_promotable(&record);
}

#[test]
fn captured_encode_config_is_exact_not_replaced_by_new_defaults() {
    let mut bundle = fixture();
    let config = bundle.capture.rows[0].config_file.clone();
    let text = bundle
        .text(&config)
        .unwrap()
        .replace("strict_validation: true", "strict_validation: false");
    bundle.files.insert(config, text.into_bytes());
    assert!(bundle
        .replay_row(
            R34Row::StaticErrorP0,
            &original(),
            &CancellationToken::new()
        )
        .is_err());
}

#[test]
fn changed_query_coordinates_and_preparation_recipe_do_not_select_a_nearby_row() {
    for mutate_recipe in [false, true] {
        let mut bundle = fixture();
        if mutate_recipe {
            bundle
                .capture
                .sources
                .get_mut("static")
                .unwrap()
                .per_property_batch["row_preparation"]["expand_nullary_fail_queries"] =
                false.into();
        } else {
            bundle.capture.rows[0].row["identity"]["query_clause_index"] = 0.into();
        }
        let record = bundle
            .inspect_row(
                R34Row::StaticErrorP0,
                &original(),
                &CancellationToken::new(),
            )
            .unwrap();
        assert!(matches!(record.status, R34RowStatus::ExecutionError { .. }));
        assert_not_promotable(&record);
    }
}

#[test]
fn expired_original_deadline_skips_preparation_and_does_not_start_a_row_allowance() {
    let bundle = fixture();
    let mut guard = original();
    guard.set_deadline(Some(Instant::now()));
    for case in R34Row::ALL {
        let record = bundle
            .replay_row(case, &guard, &CancellationToken::new())
            .unwrap();
        assert!(
            matches!(record.status, R34RowStatus::ResourceRefused { ref observed } if observed == "Timeout")
        );
        assert!(record.current_binding.is_none());
        assert_not_promotable(&record);
    }
}

#[test]
fn caller_cancellation_is_preserved_without_becoming_safe_or_unsafe() {
    let bundle = fixture();
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let record = bundle
        .replay_row(R34Row::StaticErrorP22, &original(), &cancellation)
        .unwrap();
    assert!(
        matches!(record.status, R34RowStatus::ResourceRefused { ref observed } if observed == "Cancelled")
    );
    assert!(record.current_binding.is_none());
    assert_not_promotable(&record);
    assert!(cancellation.is_cancelled());
}

#[test]
fn original_shared_work_boundaries_withhold_a_completed_binding() {
    let bundle = fixture();
    let healthy = original();
    let record = bundle
        .inspect_row(R34Row::StaticErrorP0, &healthy, &CancellationToken::new())
        .unwrap();
    assert!(matches!(record.status, R34RowStatus::BoundOnly));
    let work = healthy.ticks();
    assert!(work > 1);
    for cut in work_cut_boundaries(work) {
        let mut limited = original();
        limited.set_rlimit(Some(cut));
        let record = bundle
            .inspect_row(R34Row::StaticErrorP0, &limited, &CancellationToken::new())
            .unwrap();
        assert!(
            matches!(record.status, R34RowStatus::ResourceRefused { ref observed } if observed == "WorkLimit"),
            "cut={cut}"
        );
        assert_not_promotable(&record);
        assert!(limited.ticks() <= cut);
    }
}
