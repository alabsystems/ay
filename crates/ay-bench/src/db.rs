// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Persistent per-commit benchmark results store.
//!
//! Every `ay-bench run` appends rows to `.ay-bench/results.sqlite` at the repo
//! root, keyed by the current `git rev-parse HEAD`. The `ay-bench diff`
//! subcommand reads from this store to surface regressions across a commit
//! range.
//!
//! Schema:
//! ```sql
//! CREATE TABLE bench_results (
//!     commit_hash      TEXT    NOT NULL,
//!     eval_name        TEXT    NOT NULL,
//!     benchmark_path   TEXT    NOT NULL,
//!     result           TEXT    NOT NULL,
//!     runtime_ms       INTEGER NOT NULL,
//!     memory_mb        INTEGER NOT NULL,
//!     verifier_ok      INTEGER NOT NULL,
//!     timestamp        TEXT    NOT NULL,
//!     artifact_output_dir TEXT,
//!     proof_path       TEXT,
//!     proof_format     TEXT,
//!     proof_exists     INTEGER,
//!     proof_bytes      INTEGER,
//!     proof_hash       TEXT,
//!     proof_validation TEXT,
//!     resource_envelope TEXT,
//!     benchmark_content_hash TEXT,
//!     PRIMARY KEY(commit_hash, eval_name, benchmark_path)
//! );
//! ```
//!
//! `verifier_ok` encodes the three-way comparison result as an integer so that
//! `diff` can distinguish "correct" from "wrong answer" transitions:
//!   *  1 = verified / consistent with reference / expected
//!   *  0 = wrong answer (solver reported sat/unsat but reference disagreed)
//!   * -1 = unknown / not checked

use rusqlite::{params, Connection, OpenFlags};
use std::path::{Path, PathBuf};

use crate::error::{Result, WithContext};

/// A single persisted benchmark result row.
#[derive(Debug, Clone, PartialEq)]
pub struct ResultRow {
    pub commit_hash: String,
    pub eval_name: String,
    pub benchmark_path: String,
    pub result: String,
    pub runtime_ms: i64,
    pub memory_mb: i64,
    /// 1 = ok, 0 = wrong answer, -1 = unknown / not checked.
    pub verifier_ok: i32,
    pub timestamp: String,
    /// Canonical admitted execution envelope. `None` denotes a legacy row and
    /// is deliberately non-comparable with every other row.
    pub resource_envelope: Option<String>,
    /// Hash of the exact benchmark bytes solved by this row. Legacy rows with
    /// no hash are deliberately non-comparable.
    pub benchmark_content_hash: Option<String>,
    // --- #8897: optional SAT proof artifact audit metadata ---
    /// Directory where the runner planned/wrote SAT proof artifacts.
    pub artifact_output_dir: Option<String>,
    /// Planned proof artifact path passed to the solver.
    pub proof_path: Option<String>,
    /// Planned proof artifact format, e.g. `lrat` for main-track SAT.
    pub proof_format: Option<String>,
    /// Whether the planned proof path existed after the solver run.
    pub proof_exists: Option<bool>,
    /// Size of the proof artifact in bytes, if one was produced.
    pub proof_bytes: Option<i64>,
    /// Content hash of the proof artifact, if one was produced.
    pub proof_hash: Option<String>,
    /// Closed proof-checking state (`unchecked` or `not-emitted`).
    pub proof_validation: Option<String>,
    // --- #8774: optional proof-complexity features ---
    /// Structural family (e.g. `"php"`, `"tseitin"`, `"random-xor"`).
    /// `None` for ad-hoc corpora that do not tag instances by family.
    pub family: Option<String>,
    pub clause_width_max: Option<i64>,
    pub clause_width_mean: Option<f64>,
    pub xor_density: Option<f64>,
    pub cardinality_density: Option<f64>,
    pub modularity: Option<f64>,
    /// Wall-clock time spent on feature extraction, in ms. Excluded from
    /// `runtime_ms` (solver-only). `None` when `--with-features` was off.
    pub feature_extract_ms: Option<i64>,
}

/// Where to store persisted results. `Default` resolves to `<repo>/.ay-bench/results.sqlite`.
#[derive(Debug, Clone)]
pub struct StorePath(pub PathBuf);

impl StorePath {
    /// Default store path relative to the given repo root.
    #[must_use]
    pub fn default_at(repo_root: &Path) -> Self {
        Self(repo_root.join(".ay-bench").join("results.sqlite"))
    }

    /// Resolve the persistent store, honoring the continuous-runner override.
    #[must_use]
    pub fn configured_at(repo_root: &Path) -> Self {
        Self::resolve_at(
            repo_root,
            std::env::var_os("AY_BENCH_STORE_PATH").map(PathBuf::from),
        )
    }

    #[must_use]
    fn resolve_at(repo_root: &Path, configured: Option<PathBuf>) -> Self {
        match configured.filter(|path| !path.as_os_str().is_empty()) {
            Some(path) if path.is_absolute() => Self(path),
            Some(path) => Self(repo_root.join(path)),
            None => Self::default_at(repo_root),
        }
    }

    #[must_use]
    pub fn as_path(&self) -> &Path {
        &self.0
    }
}

/// Connection handle to the results store.
pub struct ResultsStore {
    conn: Connection,
    authority: Option<crate::resource::PreparedStorePath>,
}

impl ResultsStore {
    /// Open (or create) the store at the given path. Creates parent directories
    /// and initializes the schema on first use.
    pub fn open(path: &Path) -> Result<Self> {
        let mut authority = crate::resource::prepare_private_store_path(path, "results store")?;
        let resolved = authority.path().to_path_buf();
        let conn = Connection::open_with_flags(
            &resolved,
            OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_NOFOLLOW,
        )
        .with_bench_context(|| format!("opening results store {}", resolved.display()))?;
        authority.authenticate_sqlite_open()?;
        Self::init_schema(&conn)?;
        authority.verify_connection_authority()?;
        Ok(Self {
            conn,
            authority: Some(authority),
        })
    }

    /// Open a purely in-memory store (used in tests).
    pub fn open_in_memory() -> Result<Self> {
        let conn = Connection::open_in_memory().bench_context("opening in-memory results store")?;
        Self::init_schema(&conn)?;
        Ok(Self {
            conn,
            authority: None,
        })
    }

    fn verify_authority(&self) -> Result<()> {
        self.authority.as_ref().map_or(
            Ok(()),
            crate::resource::PreparedStorePath::verify_connection_authority,
        )
    }

    fn init_schema(conn: &Connection) -> Result<()> {
        conn.execute_batch(
            "CREATE TABLE IF NOT EXISTS bench_results (
                commit_hash    TEXT    NOT NULL,
                eval_name      TEXT    NOT NULL,
                benchmark_path TEXT    NOT NULL,
                result         TEXT    NOT NULL,
                runtime_ms     INTEGER NOT NULL,
                memory_mb      INTEGER NOT NULL,
                verifier_ok    INTEGER NOT NULL,
                timestamp      TEXT    NOT NULL,
                PRIMARY KEY(commit_hash, eval_name, benchmark_path)
            );
            CREATE INDEX IF NOT EXISTS idx_bench_commit ON bench_results(commit_hash);
            CREATE INDEX IF NOT EXISTS idx_bench_eval   ON bench_results(eval_name);",
        )
        .bench_context("initializing bench_results schema")?;

        // Optional audit/feature columns. `ALTER TABLE ADD COLUMN` is
        // idempotent only if we tolerate the "duplicate column" error, so we
        // swallow it per-column.
        for stmt in &[
            "ALTER TABLE bench_results ADD COLUMN family TEXT",
            "ALTER TABLE bench_results ADD COLUMN clause_width_max INTEGER",
            "ALTER TABLE bench_results ADD COLUMN clause_width_mean REAL",
            "ALTER TABLE bench_results ADD COLUMN xor_density REAL",
            "ALTER TABLE bench_results ADD COLUMN cardinality_density REAL",
            "ALTER TABLE bench_results ADD COLUMN modularity REAL",
            "ALTER TABLE bench_results ADD COLUMN feature_extract_ms INTEGER",
            "ALTER TABLE bench_results ADD COLUMN artifact_output_dir TEXT",
            "ALTER TABLE bench_results ADD COLUMN proof_path TEXT",
            "ALTER TABLE bench_results ADD COLUMN proof_format TEXT",
            "ALTER TABLE bench_results ADD COLUMN proof_exists INTEGER",
            "ALTER TABLE bench_results ADD COLUMN proof_bytes INTEGER",
            "ALTER TABLE bench_results ADD COLUMN proof_hash TEXT",
            "ALTER TABLE bench_results ADD COLUMN proof_validation TEXT",
            "ALTER TABLE bench_results ADD COLUMN resource_envelope TEXT",
            "ALTER TABLE bench_results ADD COLUMN benchmark_content_hash TEXT",
        ] {
            match conn.execute(stmt, []) {
                Ok(_) => {}
                Err(rusqlite::Error::SqliteFailure(_, Some(msg)))
                    if msg.contains("duplicate column name") => {}
                Err(e) => {
                    return Err::<(), _>(e).bench_context(format!("migration: {stmt}"));
                }
            }
        }
        Ok(())
    }

    /// Insert or replace a batch of rows atomically.
    pub fn upsert_rows(&mut self, rows: &[ResultRow]) -> Result<()> {
        self.verify_authority()?;
        let tx = self.conn.transaction().bench_context("begin tx")?;
        {
            let mut stmt = tx
                .prepare(
                    "INSERT OR REPLACE INTO bench_results
                        (commit_hash, eval_name, benchmark_path, result,
                         runtime_ms, memory_mb, verifier_ok, timestamp,
                         artifact_output_dir, proof_path, proof_format,
                         proof_exists, proof_bytes, proof_hash, proof_validation,
                         family, clause_width_max, clause_width_mean,
                         xor_density, cardinality_density, modularity,
                         feature_extract_ms, resource_envelope,
                         benchmark_content_hash)
                     VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8,
                             ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16,
                             ?17, ?18, ?19, ?20, ?21, ?22, ?23, ?24)",
                )
                .bench_context("prepare upsert")?;
            for row in rows {
                stmt.execute(params![
                    row.commit_hash,
                    row.eval_name,
                    row.benchmark_path,
                    row.result,
                    row.runtime_ms,
                    row.memory_mb,
                    row.verifier_ok,
                    row.timestamp,
                    row.artifact_output_dir,
                    row.proof_path,
                    row.proof_format,
                    row.proof_exists,
                    row.proof_bytes,
                    row.proof_hash,
                    row.proof_validation,
                    row.family,
                    row.clause_width_max,
                    row.clause_width_mean,
                    row.xor_density,
                    row.cardinality_density,
                    row.modularity,
                    row.feature_extract_ms,
                    row.resource_envelope,
                    row.benchmark_content_hash,
                ])
                .bench_context("execute upsert")?;
            }
        }
        tx.commit().bench_context("commit tx")?;
        self.verify_authority()
    }

    /// Fetch all rows for a given commit hash. Optionally filter by eval name.
    pub fn rows_for_commit(
        &self,
        commit_hash: &str,
        eval_filter: Option<&str>,
    ) -> Result<Vec<ResultRow>> {
        self.verify_authority()?;
        let mut rows = Vec::new();
        if let Some(eval) = eval_filter {
            let mut stmt = self.conn.prepare(
                "SELECT commit_hash, eval_name, benchmark_path, result,
                        runtime_ms, memory_mb, verifier_ok, timestamp,
                        artifact_output_dir, proof_path, proof_format,
                        proof_exists, proof_bytes, proof_hash, proof_validation,
                        family, clause_width_max, clause_width_mean,
                        xor_density, cardinality_density, modularity,
                        feature_extract_ms, resource_envelope,
                        benchmark_content_hash
                 FROM bench_results
                 WHERE commit_hash = ?1 AND eval_name = ?2",
            )?;
            let mapped = stmt.query_map(params![commit_hash, eval], row_from_sql)?;
            for r in mapped {
                rows.push(r?);
            }
        } else {
            let mut stmt = self.conn.prepare(
                "SELECT commit_hash, eval_name, benchmark_path, result,
                        runtime_ms, memory_mb, verifier_ok, timestamp,
                        artifact_output_dir, proof_path, proof_format,
                        proof_exists, proof_bytes, proof_hash, proof_validation,
                        family, clause_width_max, clause_width_mean,
                        xor_density, cardinality_density, modularity,
                        feature_extract_ms, resource_envelope,
                        benchmark_content_hash
                 FROM bench_results
                 WHERE commit_hash = ?1",
            )?;
            let mapped = stmt.query_map(params![commit_hash], row_from_sql)?;
            for r in mapped {
                rows.push(r?);
            }
        }
        self.verify_authority()?;
        Ok(rows)
    }

    /// Commit hashes that have stored results, newest-first by timestamp.
    pub fn known_commits(&self) -> Result<Vec<String>> {
        self.verify_authority()?;
        let mut stmt = self.conn.prepare(
            "SELECT commit_hash, MAX(timestamp) AS t
             FROM bench_results
             GROUP BY commit_hash
             ORDER BY t DESC",
        )?;
        let rows = stmt.query_map([], |r| r.get::<_, String>(0))?;
        let mut out = Vec::new();
        for r in rows {
            out.push(r?);
        }
        self.verify_authority()?;
        Ok(out)
    }
}

fn row_from_sql(r: &rusqlite::Row<'_>) -> rusqlite::Result<ResultRow> {
    Ok(ResultRow {
        commit_hash: r.get(0)?,
        eval_name: r.get(1)?,
        benchmark_path: r.get(2)?,
        result: r.get(3)?,
        runtime_ms: r.get(4)?,
        memory_mb: r.get(5)?,
        verifier_ok: r.get(6)?,
        timestamp: r.get(7)?,
        artifact_output_dir: r.get(8)?,
        proof_path: r.get(9)?,
        proof_format: r.get(10)?,
        proof_exists: r.get(11)?,
        proof_bytes: r.get(12)?,
        proof_hash: r.get(13)?,
        proof_validation: r.get(14)?,
        family: r.get(15)?,
        clause_width_max: r.get(16)?,
        clause_width_mean: r.get(17)?,
        xor_density: r.get(18)?,
        cardinality_density: r.get(19)?,
        modularity: r.get(20)?,
        feature_extract_ms: r.get(21)?,
        resource_envelope: r.get(22)?,
        benchmark_content_hash: r.get(23)?,
    })
}

/// Resolve `git rev-parse <rev>` against the given repo root. Returns `None`
/// when git is unavailable or the revision is unknown.
#[must_use]
pub fn resolve_rev(repo_root: &Path, rev: &str) -> Option<String> {
    let output = crate::resource::capture_local_output_in(
        "git",
        ["rev-parse", "--verify", "--end-of-options", rev],
        std::time::Duration::from_secs(5),
        "git revision resolution",
        Some(repo_root),
    )
    .ok()?;
    if !output.status.success() {
        return None;
    }
    let s = output.stdout.trim().to_string();
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}

/// Convenience wrapper: resolve `HEAD` against the given repo root.
#[must_use]
pub fn resolve_head(repo_root: &Path) -> Option<String> {
    resolve_rev(repo_root, "HEAD")
}

#[cfg(test)]
mod tests {
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
}
