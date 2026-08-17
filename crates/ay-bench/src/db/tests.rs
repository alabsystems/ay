// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn private_tempdir() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o700))
            .expect("make results-store test parent private");
    }
    dir
}

fn sample(commit: &str, bench: &str, result: &str, ms: i64, ok: i32) -> ResultRow {
    ResultRow {
        commit_hash: commit.to_string(),
        eval_name: "eval-x".to_string(),
        benchmark_path: bench.to_string(),
        result: result.to_string(),
        runtime_ms: ms,
        memory_mb: 42,
        verifier_ok: ok,
        timestamp: "2026-04-18T00:00:00Z".to_string(),
        resource_envelope: Some(
            "oom-guard-v1:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=16000".to_string(),
        ),
        benchmark_content_hash: Some("fh128:test".to_string()),
        artifact_output_dir: None,
        proof_path: None,
        proof_format: None,
        proof_exists: None,
        proof_bytes: None,
        proof_hash: None,
        proof_validation: None,
        family: None,
        clause_width_max: None,
        clause_width_mean: None,
        xor_density: None,
        cardinality_density: None,
        modularity: None,
        feature_extract_ms: None,
    }
}

#[test]
fn test_store_roundtrip() {
    let mut store = ResultsStore::open_in_memory().expect("open in-memory");
    let rows = vec![
        sample("aaa", "b1.smt2", "sat", 100, 1),
        sample("aaa", "b2.smt2", "unsat", 200, 1),
    ];
    store.upsert_rows(&rows).expect("upsert");
    let got = store
        .rows_for_commit("aaa", None)
        .expect("fetch")
        .into_iter()
        .collect::<Vec<_>>();
    assert_eq!(got.len(), 2);
    assert!(got.iter().any(|r| r.benchmark_path == "b1.smt2"));
}

#[test]
fn test_store_upsert_replaces() {
    let mut store = ResultsStore::open_in_memory().expect("open in-memory");
    store
        .upsert_rows(&[sample("c1", "a.smt2", "unknown", 5000, -1)])
        .expect("insert");
    store
        .upsert_rows(&[sample("c1", "a.smt2", "sat", 150, 1)])
        .expect("replace");
    let got = store.rows_for_commit("c1", None).expect("fetch");
    assert_eq!(got.len(), 1);
    assert_eq!(got[0].result, "sat");
    assert_eq!(got[0].runtime_ms, 150);
}

#[test]
fn test_store_filter_by_eval() {
    let mut store = ResultsStore::open_in_memory().expect("open in-memory");
    let mut row = sample("zz", "a.smt2", "sat", 10, 1);
    store.upsert_rows(&[row.clone()]).expect("insert");
    row.eval_name = "other-eval".to_string();
    row.benchmark_path = "b.smt2".to_string();
    store.upsert_rows(&[row]).expect("insert");

    let only_x = store
        .rows_for_commit("zz", Some("eval-x"))
        .expect("fetch eval-x");
    assert_eq!(only_x.len(), 1);
    assert_eq!(only_x[0].benchmark_path, "a.smt2");

    let all = store.rows_for_commit("zz", None).expect("fetch all");
    assert_eq!(all.len(), 2);
}

#[test]
fn test_default_store_path() {
    let root = Path::new("/tmp/repo");
    let p = StorePath::default_at(root);
    assert_eq!(p.as_path(), Path::new("/tmp/repo/.ay-bench/results.sqlite"));
}

#[test]
fn test_configured_store_path_resolution() {
    let root = Path::new("/tmp/repo");
    assert_eq!(
        StorePath::resolve_at(root, Some(PathBuf::from("state/results.sqlite"))).as_path(),
        Path::new("/tmp/repo/state/results.sqlite")
    );
    assert_eq!(
        StorePath::resolve_at(root, Some(PathBuf::from("/evidence/results.sqlite"))).as_path(),
        Path::new("/evidence/results.sqlite")
    );
    assert_eq!(
        StorePath::resolve_at(root, Some(PathBuf::new())).as_path(),
        Path::new("/tmp/repo/.ay-bench/results.sqlite")
    );
}

#[cfg(unix)]
#[test]
fn test_store_rejects_visible_path_replacement_after_open() {
    let dir = private_tempdir();
    let path = dir.path().join("results.sqlite");
    let displaced = dir.path().join("authenticated-results.sqlite");
    let mut store = ResultsStore::open(&path).expect("open authenticated store");
    std::fs::rename(&path, &displaced).expect("displace authenticated inode");
    let replacement = b"replacement must be preserved";
    std::fs::write(&path, replacement).expect("plant replacement");

    let error = store
        .upsert_rows(&[sample("c1", "a.smt2", "sat", 10, 1)])
        .expect_err("path replacement must fail closed");

    assert!(
        error.to_string().contains("changed identity"),
        "unexpected error: {error}"
    );
    assert_eq!(
        std::fs::read(&path).expect("read replacement"),
        replacement,
        "failed authority check must never unlink or overwrite a replacement"
    );
}

#[test]
fn test_store_initialization_failure_preserves_existing_target() {
    let dir = private_tempdir();
    let path = dir.path().join("invalid.sqlite");
    let original = b"not a sqlite database";
    std::fs::write(&path, original).expect("write invalid store");

    let error = match ResultsStore::open(&path) {
        Ok(_) => panic!("invalid store must fail"),
        Err(error) => error,
    };

    assert!(
        error
            .to_string()
            .contains("initializing bench_results schema"),
        "unexpected error: {error}"
    );
    assert_eq!(
        std::fs::read(&path).expect("read invalid store"),
        original,
        "initialization rollback must never remove an authenticated target by pathname"
    );
}

/// #8774 regression: a row with populated proof-complexity feature
/// columns must round-trip through the store unchanged, including
/// exact `f64` values and the `family` tag.
#[test]
fn test_store_roundtrip_with_features() {
    let mut row = sample("feat", "bench.cnf", "unsat", 42, 1);
    row.family = Some("php".to_string());
    row.clause_width_max = Some(3);
    row.clause_width_mean = Some(2.5);
    row.xor_density = Some(0.125);
    row.cardinality_density = Some(0.625);
    row.modularity = Some(0.875);
    row.feature_extract_ms = Some(7);

    let mut store = ResultsStore::open_in_memory().expect("open in-memory");
    store.upsert_rows(&[row.clone()]).expect("upsert");
    let got = store
        .rows_for_commit("feat", Some("eval-x"))
        .expect("fetch");
    assert_eq!(got.len(), 1);
    // `ResultRow` uses `PartialEq` (not `Eq`) because of the `f64`
    // feature columns. Exact equality works because we wrote and
    // read the same bit pattern — but to be defensive against future
    // float-coercion changes we also compare within a tight
    // tolerance below.
    assert_eq!(got[0], row);

    let got = &got[0];
    assert_eq!(got.family.as_deref(), Some("php"));
    assert_eq!(got.clause_width_max, Some(3));
    assert!((got.clause_width_mean.unwrap() - 2.5).abs() < 1e-12);
    assert!((got.xor_density.unwrap() - 0.125).abs() < 1e-12);
    assert!((got.cardinality_density.unwrap() - 0.625).abs() < 1e-12);
    assert!((got.modularity.unwrap() - 0.875).abs() < 1e-12);
    assert_eq!(got.feature_extract_ms, Some(7));
}

/// #8897 regression: SAT artifact audit metadata must survive the
/// results-store row path, including legacy rows where the fields are NULL.
#[test]
fn test_store_roundtrip_with_sat_artifact_metadata() {
    let mut row = sample("artifact", "sat.cnf", "unsat", 99, 1);
    row.artifact_output_dir = Some("/tmp/ay/artifacts".to_string());
    row.proof_path = Some("/tmp/ay/artifacts/sat.lrat".to_string());
    row.proof_format = Some("lrat".to_string());
    row.proof_exists = Some(true);
    row.proof_bytes = Some(128);
    row.proof_hash = Some("fh128:0123456789abcdef0123456789abcdef".to_string());
    row.proof_validation = Some("unchecked".to_string());
    let legacy = sample("artifact", "legacy.cnf", "sat", 50, 1);

    let mut store = ResultsStore::open_in_memory().expect("open in-memory");
    store
        .upsert_rows(&[row.clone(), legacy.clone()])
        .expect("upsert");
    let got = store
        .rows_for_commit("artifact", Some("eval-x"))
        .expect("fetch");

    assert_eq!(got.len(), 2);
    assert!(got.contains(&row));
    assert!(got.contains(&legacy));

    let legacy = got
        .iter()
        .find(|r| r.benchmark_path == "legacy.cnf")
        .expect("legacy row");
    assert_eq!(legacy.proof_path, None);
    assert_eq!(legacy.proof_exists, None);
}

/// Mixing rows with and without features on the same commit must not
/// poison the schema — the legacy columns stay populated while the
/// new columns are `NULL`.
#[test]
fn test_store_mixed_feature_and_legacy_rows() {
    let mut store = ResultsStore::open_in_memory().expect("open in-memory");
    let legacy = sample("mix", "plain.cnf", "sat", 10, 1);
    let mut featured = sample("mix", "php.cnf", "unsat", 20, 1);
    featured.family = Some("php".to_string());
    featured.xor_density = Some(0.0);
    featured.cardinality_density = Some(0.75);
    store
        .upsert_rows(&[legacy.clone(), featured.clone()])
        .expect("upsert");

    let got = store.rows_for_commit("mix", None).expect("fetch");
    assert_eq!(got.len(), 2);
    let plain = got
        .iter()
        .find(|r| r.benchmark_path == "plain.cnf")
        .expect("plain row");
    assert!(plain.family.is_none());
    assert!(plain.xor_density.is_none());
    let php = got
        .iter()
        .find(|r| r.benchmark_path == "php.cnf")
        .expect("php row");
    assert_eq!(php.family.as_deref(), Some("php"));
    assert!(php.xor_density.is_some());
}
