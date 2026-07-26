// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Differential suite harvester — run reference solvers over a corpus and
//! persist `(input, expected_result, reference_runtime)` tuples as the
//! ground-truth baseline for `ay bench verify`.
//!
//! This is the first-phase implementation of issue #8711 (universal
//! differential suite). The baseline store is separate from the per-commit
//! `bench_results` store and records *reference solver* outcomes, not AY
//! outcomes:
//!
//! ```sql
//! CREATE TABLE IF NOT EXISTS baselines (
//!     corpus          TEXT    NOT NULL,
//!     benchmark_path  TEXT    NOT NULL,
//!     content_hash    TEXT    NOT NULL,
//!     solver          TEXT    NOT NULL,
//!     solver_version  TEXT    NOT NULL,
//!     answer          TEXT    NOT NULL,   -- sat | unsat | unknown | timeout | error
//!     expected        TEXT    NOT NULL,   -- sat | unsat | unknown (from file header)
//!     wall_ms         INTEGER NOT NULL,
//!     exit_code       INTEGER,
//!     timeout_s       REAL    NOT NULL,
//!     stdout_head     TEXT    NOT NULL,
//!     stderr_head     TEXT    NOT NULL,
//!     harvested_at    TEXT    NOT NULL,
//!     PRIMARY KEY(corpus, benchmark_path, solver)
//! );
//! ```
//!
//! The `expected` column captures any `(set-info :status ...)` header marker
//! or filename convention (`*/sat/*`, `*/unsat/*`) so `verify` can flag cases
//! where the reference solver itself diverged from the benchmark's declared
//! status.

use rusqlite::{params, Connection, OpenFlags};
use serde::Serialize;
use std::collections::{BTreeMap, VecDeque};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use crate::error::{BenchError, Result, WithContext};

/// Machine-readable exact enforcement tags stored in baseline rows.
pub use crate::resource::{
    ENFORCEMENT_AY_MEMORY_RSS_V1, ENFORCEMENT_AY_MEMORY_V1, ENFORCEMENT_AY_PB_MEMLIMIT_V1,
    ENFORCEMENT_RSS_WATCHDOG_V1,
};

// ===================================================================
// Baseline store
// ===================================================================

/// One persisted `(corpus, benchmark, solver)` reference result.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BaselineRow {
    pub corpus: String,
    pub benchmark_path: String,
    pub content_hash: String,
    pub solver_input_hash: String,
    pub solver: String,
    pub solver_version: String,
    /// Canonical binary identity; empty/zero values identify migrated legacy
    /// rows and make them non-comparable until re-harvested.
    pub solver_path: String,
    pub solver_sha256: String,
    pub solver_size_bytes: i64,
    pub answer: String,
    pub expected: String,
    pub expected_source: String,
    pub wall_ms: i64,
    pub exit_code: Option<i32>,
    pub timeout_s: f64,
    pub stdout_head: String,
    pub stderr_head: String,
    pub harvested_at: String,
    /// Resource envelope provenance. These values come directly from
    /// `scripts/_oom_guard.py plan` and are part of baseline comparability.
    pub resource_requested_jobs: i64,
    pub resource_jobs: i64,
    pub resource_memlimit_mb: i64,
    pub resource_nbcore: i64,
    pub resource_headroom_mb: i64,
    pub resource_enforcement: String,
    pub solver_argv_json: String,
    pub solver_env_json: String,
    pub stdout_sha256: String,
    pub stderr_sha256: String,
    pub stdout_truncated: bool,
    pub stderr_truncated: bool,
}

/// Resolved path to the baseline store (default: `<repo>/.ay-bench/baselines.sqlite`).
#[derive(Debug, Clone)]
pub struct BaselineStorePath(pub PathBuf);

impl BaselineStorePath {
    /// Default store path relative to the given repo root.
    #[must_use]
    pub fn default_at(repo_root: &Path) -> Self {
        Self(repo_root.join(".ay-bench").join("baselines.sqlite"))
    }

    #[must_use]
    pub fn as_path(&self) -> &Path {
        &self.0
    }
}

/// Connection handle to the baseline store.
pub struct BaselineStore {
    conn: Connection,
    authority: Option<crate::resource::PreparedStorePath>,
}

impl BaselineStore {
    /// Open (or create) the store, initializing the schema on first use.
    pub fn open(path: &Path) -> Result<Self> {
        let mut authority = crate::resource::prepare_private_store_path(path, "baseline store")?;
        let resolved = authority.path().to_path_buf();
        let conn = Connection::open_with_flags(
            &resolved,
            OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_NOFOLLOW,
        )
        .with_bench_context(|| format!("opening baseline store {}", resolved.display()))?;
        authority.authenticate_sqlite_open()?;
        Self::init_schema(&conn)?;
        authority.verify_connection_authority()?;
        Ok(Self {
            conn,
            authority: Some(authority),
        })
    }

    /// Open a purely in-memory baseline store (used in tests).
    pub fn open_in_memory() -> Result<Self> {
        let conn =
            Connection::open_in_memory().bench_context("opening in-memory baseline store")?;
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
            "CREATE TABLE IF NOT EXISTS baselines (
                corpus          TEXT    NOT NULL,
                benchmark_path  TEXT    NOT NULL,
                content_hash    TEXT    NOT NULL,
                solver          TEXT    NOT NULL,
                solver_version  TEXT    NOT NULL,
                solver_path     TEXT    NOT NULL DEFAULT '',
                solver_sha256   TEXT    NOT NULL DEFAULT '',
                solver_size_bytes INTEGER NOT NULL DEFAULT 0,
                answer          TEXT    NOT NULL,
                expected        TEXT    NOT NULL,
                expected_source TEXT    NOT NULL DEFAULT 'unknown',
                wall_ms         INTEGER NOT NULL,
                exit_code       INTEGER,
                timeout_s       REAL    NOT NULL,
                stdout_head     TEXT    NOT NULL,
                stderr_head     TEXT    NOT NULL,
                harvested_at    TEXT    NOT NULL,
                resource_requested_jobs INTEGER NOT NULL DEFAULT 0,
                resource_jobs   INTEGER NOT NULL DEFAULT 0,
                resource_memlimit_mb INTEGER NOT NULL DEFAULT 0,
                resource_nbcore INTEGER NOT NULL DEFAULT 0,
                resource_headroom_mb INTEGER NOT NULL DEFAULT 0,
                resource_enforcement TEXT NOT NULL DEFAULT '',
                solver_input_hash TEXT NOT NULL DEFAULT '',
                solver_argv_json TEXT NOT NULL DEFAULT '[]',
                solver_env_json TEXT NOT NULL DEFAULT '{}',
                stdout_sha256 TEXT NOT NULL DEFAULT '',
                stderr_sha256 TEXT NOT NULL DEFAULT '',
                stdout_truncated INTEGER NOT NULL DEFAULT 0,
                stderr_truncated INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY(corpus, benchmark_path, solver)
            );
            CREATE INDEX IF NOT EXISTS idx_baseline_hash   ON baselines(content_hash);
            CREATE INDEX IF NOT EXISTS idx_baseline_corpus ON baselines(corpus);",
        )
        .bench_context("initializing baselines schema")?;
        // Existing stores predate resource-envelope provenance.  Migrate them
        // in place without forcing users to delete valuable reference rows.
        ensure_column(
            conn,
            "resource_requested_jobs",
            "INTEGER NOT NULL DEFAULT 0",
        )?;
        ensure_column(conn, "solver_input_hash", "TEXT NOT NULL DEFAULT ''")?;
        ensure_column(conn, "solver_argv_json", "TEXT NOT NULL DEFAULT '[]'")?;
        ensure_column(conn, "solver_env_json", "TEXT NOT NULL DEFAULT '{}'")?;
        ensure_column(conn, "stdout_sha256", "TEXT NOT NULL DEFAULT ''")?;
        ensure_column(conn, "stderr_sha256", "TEXT NOT NULL DEFAULT ''")?;
        ensure_column(conn, "stdout_truncated", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "stderr_truncated", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_jobs", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_memlimit_mb", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_nbcore", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_headroom_mb", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_enforcement", "TEXT NOT NULL DEFAULT ''")?;
        ensure_column(conn, "solver_path", "TEXT NOT NULL DEFAULT ''")?;
        ensure_column(conn, "solver_sha256", "TEXT NOT NULL DEFAULT ''")?;
        ensure_column(conn, "solver_size_bytes", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "expected_source", "TEXT NOT NULL DEFAULT 'unknown'")?;
        Ok(())
    }

    /// Insert or replace a batch of rows atomically.
    pub fn upsert_rows(&mut self, rows: &[BaselineRow]) -> Result<()> {
        self.verify_authority()?;
        let tx = self.conn.transaction().bench_context("begin tx")?;
        insert_baseline_rows(&tx, rows)?;
        tx.commit().bench_context("commit tx")?;
        self.verify_authority()
    }

    /// Atomically replace the exact path universe for one corpus/solver
    /// campaign. Stale paths from an older campaign cannot survive this
    /// transaction and later satisfy verification coverage accidentally.
    pub fn replace_campaign(&mut self, rows: &[BaselineRow]) -> Result<()> {
        self.verify_authority()?;
        validate_uniform_campaign(rows)?;
        let corpus = &rows[0].corpus;
        let solver = &rows[0].solver;
        let tx = self.conn.transaction().bench_context("begin campaign tx")?;
        tx.execute(
            "DELETE FROM baselines WHERE corpus = ?1 AND solver = ?2",
            params![corpus, solver],
        )
        .bench_context("delete previous baseline campaign")?;
        insert_baseline_rows(&tx, rows)?;
        tx.commit().bench_context("commit campaign replacement")?;
        self.verify_authority()
    }

    /// Fetch all rows for a given corpus.
    pub fn rows_for_corpus(&self, corpus: &str) -> Result<Vec<BaselineRow>> {
        self.verify_authority()?;
        let mut stmt = self.conn.prepare(
            "SELECT corpus, benchmark_path, content_hash, solver, solver_version,
                    solver_path, solver_sha256, solver_size_bytes,
                    answer, expected, expected_source, wall_ms, exit_code, timeout_s,
                    stdout_head, stderr_head, harvested_at,
                    resource_requested_jobs, resource_jobs,
                    resource_memlimit_mb, resource_nbcore,
                    resource_headroom_mb, resource_enforcement,
                    solver_input_hash, solver_argv_json, solver_env_json,
                    stdout_sha256, stderr_sha256,
                    stdout_truncated, stderr_truncated
             FROM baselines
             WHERE corpus = ?1",
        )?;
        let mapped = stmt.query_map(params![corpus], row_from_sql)?;
        let mut rows = Vec::new();
        for r in mapped {
            rows.push(r?);
        }
        self.verify_authority()?;
        Ok(rows)
    }

    /// Distinct corpus names in the store.
    pub fn known_corpora(&self) -> Result<Vec<String>> {
        self.verify_authority()?;
        let mut stmt = self
            .conn
            .prepare("SELECT DISTINCT corpus FROM baselines ORDER BY corpus")?;
        let rows = stmt.query_map([], |r| r.get::<_, String>(0))?;
        let mut out = Vec::new();
        for r in rows {
            out.push(r?);
        }
        self.verify_authority()?;
        Ok(out)
    }
}

fn insert_baseline_rows(tx: &rusqlite::Transaction<'_>, rows: &[BaselineRow]) -> Result<()> {
    let mut stmt = tx
        .prepare(
            "INSERT OR REPLACE INTO baselines
                (corpus, benchmark_path, content_hash, solver, solver_version,
                 solver_path, solver_sha256, solver_size_bytes,
                 answer, expected, expected_source, wall_ms, exit_code, timeout_s,
                 stdout_head, stderr_head, harvested_at,
                 resource_requested_jobs, resource_jobs,
                 resource_memlimit_mb, resource_nbcore,
                 resource_headroom_mb, resource_enforcement,
                 solver_input_hash, solver_argv_json, solver_env_json,
                 stdout_sha256, stderr_sha256, stdout_truncated, stderr_truncated)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13,
                     ?14, ?15, ?16, ?17, ?18, ?19, ?20, ?21, ?22, ?23,
                     ?24, ?25, ?26, ?27, ?28, ?29, ?30)",
        )
        .bench_context("prepare baseline insert")?;
    for row in rows {
        stmt.execute(params![
            row.corpus,
            row.benchmark_path,
            row.content_hash,
            row.solver,
            row.solver_version,
            row.solver_path,
            row.solver_sha256,
            row.solver_size_bytes,
            row.answer,
            row.expected,
            row.expected_source,
            row.wall_ms,
            row.exit_code,
            row.timeout_s,
            row.stdout_head,
            row.stderr_head,
            row.harvested_at,
            row.resource_requested_jobs,
            row.resource_jobs,
            row.resource_memlimit_mb,
            row.resource_nbcore,
            row.resource_headroom_mb,
            row.resource_enforcement,
            row.solver_input_hash,
            row.solver_argv_json,
            row.solver_env_json,
            row.stdout_sha256,
            row.stderr_sha256,
            row.stdout_truncated,
            row.stderr_truncated,
        ])
        .bench_context("insert baseline row")?;
    }
    Ok(())
}

pub(crate) fn validate_uniform_campaign(rows: &[BaselineRow]) -> Result<()> {
    let Some(first) = rows.first() else {
        return Err(BenchError::msg(
            "refusing to publish an empty baseline campaign",
        ));
    };
    let mut paths = std::collections::BTreeSet::new();
    for row in rows {
        if row.corpus.trim().is_empty()
            || row.solver.trim().is_empty()
            || row.solver_version.trim().is_empty()
            || row.solver_path.trim().is_empty()
            || row.harvested_at.trim().is_empty()
        {
            return Err(BenchError::msg(
                "baseline campaign has empty corpus, solver, provenance, or timestamp fields",
            ));
        }
        if !valid_sha256(&row.content_hash)
            || !valid_sha256(&row.solver_input_hash)
            || !valid_sha256(&row.solver_sha256)
            || !valid_sha256(&row.stdout_sha256)
            || !valid_sha256(&row.stderr_sha256)
        {
            return Err(BenchError::msg(
                "baseline campaign has an invalid SHA-256 provenance field",
            ));
        }
        let argv_is_array = serde_json::from_str::<serde_json::Value>(&row.solver_argv_json)
            .is_ok_and(|value| value.is_array());
        let env_is_object = serde_json::from_str::<serde_json::Value>(&row.solver_env_json)
            .is_ok_and(|value| value.is_object());
        if !argv_is_array || !env_is_object {
            return Err(BenchError::msg(
                "baseline campaign has malformed solver argv/environment evidence",
            ));
        }
        if row.solver_size_bytes <= 0
            || row.wall_ms < 0
            || !row.timeout_s.is_finite()
            || row.timeout_s <= 0.0
            || row.resource_requested_jobs <= 0
            || row.resource_jobs <= 0
            || row.resource_jobs > row.resource_requested_jobs
            || row.resource_memlimit_mb <= 0
            || row.resource_nbcore <= 0
            || row.resource_headroom_mb < 0
        {
            return Err(BenchError::msg(
                "baseline campaign has invalid timing, size, or resource limits",
            ));
        }
        crate::resource::checked_benchmark_timeout(row.timeout_s, "baseline campaign")?;
        if !matches!(
            row.answer.as_str(),
            "sat" | "unsat" | "unknown" | "timeout" | "memout" | "error"
        ) || !matches!(row.expected.as_str(), "sat" | "unsat" | "unknown")
            || !matches!(
                row.expected_source.as_str(),
                "header" | "path" | "header+path" | "unknown"
            )
        {
            return Err(BenchError::msg(
                "baseline campaign has an invalid answer or expected-status value",
            ));
        }
        let exit_compatible = match row.answer.as_str() {
            "sat" => matches!(row.exit_code, Some(0 | 10)),
            "unsat" => matches!(row.exit_code, Some(0 | 20)),
            "unknown" => row.exit_code == Some(0),
            "timeout" | "memout" => row.exit_code.is_none(),
            "error" => true,
            _ => false,
        };
        if !exit_compatible {
            return Err(BenchError::msg(format!(
                "baseline answer {:?} is incompatible with exit code {:?}",
                row.answer, row.exit_code
            )));
        }
        if row.resource_enforcement != ENFORCEMENT_RSS_WATCHDOG_V1 {
            return Err(BenchError::msg(
                "baseline campaign does not use the recognized exact reference enforcement",
            ));
        }
        let benchmark_path = Path::new(&row.benchmark_path);
        if benchmark_path.is_absolute()
            || benchmark_path
                .components()
                .any(|component| !matches!(component, std::path::Component::Normal(_)))
            || row.benchmark_path.chars().any(char::is_control)
        {
            return Err(BenchError::msg(format!(
                "baseline campaign has a non-normal benchmark path: {:?}",
                row.benchmark_path
            )));
        }
        if row.corpus != first.corpus
            || row.solver != first.solver
            || row.solver_version != first.solver_version
            || row.solver_path != first.solver_path
            || row.solver_sha256 != first.solver_sha256
            || row.solver_size_bytes != first.solver_size_bytes
            || row.harvested_at != first.harvested_at
            || row.timeout_s.to_bits() != first.timeout_s.to_bits()
            || row.resource_requested_jobs != first.resource_requested_jobs
            || row.resource_jobs != first.resource_jobs
            || row.resource_memlimit_mb != first.resource_memlimit_mb
            || row.resource_nbcore != first.resource_nbcore
            || row.resource_headroom_mb != first.resource_headroom_mb
            || row.resource_enforcement != first.resource_enforcement
        {
            return Err(BenchError::msg(
                "baseline campaign contains mixed corpus, solver provenance, timing, or resource envelopes",
            ));
        }
        if row.benchmark_path.is_empty() || !paths.insert(&row.benchmark_path) {
            return Err(BenchError::msg(format!(
                "baseline campaign contains an empty or duplicate benchmark path: {:?}",
                row.benchmark_path
            )));
        }
    }
    Ok(())
}

fn valid_sha256(value: &str) -> bool {
    value
        .strip_prefix("sha256:")
        .is_some_and(|hex| hex.len() == 64 && hex.bytes().all(|byte| byte.is_ascii_hexdigit()))
}

fn row_from_sql(r: &rusqlite::Row<'_>) -> rusqlite::Result<BaselineRow> {
    Ok(BaselineRow {
        corpus: r.get(0)?,
        benchmark_path: r.get(1)?,
        content_hash: r.get(2)?,
        solver: r.get(3)?,
        solver_version: r.get(4)?,
        solver_path: r.get(5)?,
        solver_sha256: r.get(6)?,
        solver_size_bytes: r.get(7)?,
        answer: r.get(8)?,
        expected: r.get(9)?,
        expected_source: r.get(10)?,
        wall_ms: r.get(11)?,
        exit_code: r.get(12)?,
        timeout_s: r.get(13)?,
        stdout_head: r.get(14)?,
        stderr_head: r.get(15)?,
        harvested_at: r.get(16)?,
        resource_requested_jobs: r.get(17)?,
        resource_jobs: r.get(18)?,
        resource_memlimit_mb: r.get(19)?,
        resource_nbcore: r.get(20)?,
        resource_headroom_mb: r.get(21)?,
        resource_enforcement: r.get(22)?,
        solver_input_hash: r.get(23)?,
        solver_argv_json: r.get(24)?,
        solver_env_json: r.get(25)?,
        stdout_sha256: r.get(26)?,
        stderr_sha256: r.get(27)?,
        stdout_truncated: r.get(28)?,
        stderr_truncated: r.get(29)?,
    })
}

fn ensure_column(conn: &Connection, name: &str, declaration: &str) -> Result<()> {
    let mut stmt = conn.prepare("PRAGMA table_info(baselines)")?;
    let columns = stmt.query_map([], |row| row.get::<_, String>(1))?;
    for column in columns {
        if column? == name {
            return Ok(());
        }
    }
    // `name` and `declaration` are fixed literals from init_schema, never user
    // input. SQLite does not support bind parameters for identifiers/DDL.
    conn.execute_batch(&format!(
        "ALTER TABLE baselines ADD COLUMN {name} {declaration}"
    ))?;
    Ok(())
}

// ===================================================================
// Harvest CLI
// ===================================================================

/// Arguments for `ay bench harvest`.
#[derive(Debug, Clone)]
pub struct HarvestArgs {
    /// Name used to key these rows in the baseline store.
    /// Typically the corpus directory stem, e.g. "qfuf-neq".
    pub corpus: String,
    /// Directory containing benchmark files.
    pub benchmarks_dir: PathBuf,
    /// Reference solver binary name (looked up via `which`) or absolute path.
    pub solver: String,
    /// Wall-clock timeout per benchmark in seconds.
    pub timeout_s: f64,
    /// Parallelism; 0 = use rayon default (num CPUs).
    pub jobs: usize,
    /// Maximum number of benchmarks to harvest (0 = no limit).
    pub limit: usize,
    /// Glob-style filename extensions to include (without leading dot).
    pub extensions: Vec<String>,
    /// Override store path. `None` uses the default.
    pub store_path: Option<PathBuf>,
}

impl Default for HarvestArgs {
    fn default() -> Self {
        Self {
            corpus: "default".to_string(),
            benchmarks_dir: PathBuf::from("benchmarks"),
            solver: "z3".to_string(),
            timeout_s: 30.0,
            jobs: 0,
            limit: 0,
            extensions: vec!["smt2".to_string(), "cnf".to_string()],
            store_path: None,
        }
    }
}

/// Run the harvester. Returns the number of baseline rows written.
pub fn cmd_harvest(args: HarvestArgs) -> Result<usize> {
    crate::resource::checked_benchmark_timeout(args.timeout_s, "harvest")?;
    if args.limit > crate::resource::MAX_DISCOVERED_BENCHMARKS {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "harvest limit {} exceeds the fixed {}-benchmark discovery cap",
                args.limit,
                crate::resource::MAX_DISCOVERED_BENCHMARKS
            ),
        });
    }
    let root = crate::runner::repo_root_public();
    let requested_jobs = if args.jobs == 0 {
        std::thread::available_parallelism()
            .map(std::num::NonZeroUsize::get)
            .unwrap_or(1)
    } else {
        args.jobs.max(1)
    };
    let resources =
        crate::resource::PlannedResources::plan(&root, requested_jobs, "ay bench harvest")?;
    let resource_requested_jobs = i64::try_from(resources.plan.requested_jobs)
        .map_err(|_| BenchError::msg("requested job count does not fit baseline schema"))?;
    let resource_jobs = i64::try_from(resources.plan.jobs)
        .map_err(|_| BenchError::msg("admitted job count does not fit baseline schema"))?;
    let resource_memlimit_mb = i64::try_from(resources.plan.memlimit_mb_per_child)
        .map_err(|_| BenchError::msg("memory limit does not fit baseline schema"))?;
    let resource_nbcore = i64::try_from(resources.plan.nbcore_per_child)
        .map_err(|_| BenchError::msg("core budget does not fit baseline schema"))?;
    let resource_headroom_mb = i64::try_from(resources.plan.headroom_mb)
        .map_err(|_| BenchError::msg("memory headroom does not fit baseline schema"))?;
    let store_path = args
        .store_path
        .clone()
        .unwrap_or_else(|| BaselineStorePath::default_at(&root).as_path().to_path_buf());

    let resolved_solver =
        resolve_solver(&args.solver).ok_or_else(|| BenchError::SolverNotFound {
            name: args.solver.clone(),
        })?;
    let pinned_solver = crate::environment::PinnedSolver::capture(
        &resolved_solver,
        &resources,
        "ay bench harvest pinned solver version probe",
    )?;
    let solver_provenance = pinned_solver.provenance().clone();
    let solver_path = PathBuf::from(&solver_provenance.path);
    let solver_size_bytes = i64::try_from(solver_provenance.size_bytes)
        .map_err(|_| BenchError::msg("solver binary size does not fit baseline schema"))?;
    let solver_sha256 = solver_provenance.sha256.clone();
    let solver_name = solver_display_name(&args.solver, &solver_path);
    let solver_version = solver_provenance.version_output.clone();

    eprintln!(
        "harvest: corpus={} solver={} ({}) timeout={:.0}s store={}",
        args.corpus,
        solver_name,
        solver_version,
        args.timeout_s,
        store_path.display()
    );
    eprintln!(
        "harvest: resource plan requested_jobs={} jobs={} memory={}MiB/child NBCORE={} headroom={}MiB enforcement=_oom_guard.rss_watchdog(grace=0)+MEMLIMIT/NBCORE-env",
        resources.plan.requested_jobs,
        resources.plan.jobs,
        resources.plan.memlimit_mb_per_child,
        resources.plan.nbcore_per_child,
        resources.plan.headroom_mb,
    );

    let corpus_root = std::fs::canonicalize(&args.benchmarks_dir).with_bench_context(|| {
        format!(
            "canonicalizing corpus root {}",
            args.benchmarks_dir.display()
        )
    })?;
    let files = discover_files(&corpus_root, &args.extensions, args.limit)?;
    if files.is_empty() {
        return Err(BenchError::msg(format!(
            "no files matching extensions {:?} under {}",
            args.extensions,
            args.benchmarks_dir.display()
        )));
    }
    eprintln!("harvest: {} files to process", files.len());
    let files: Vec<(PathBuf, String)> = files
        .into_iter()
        .map(|file| {
            let benchmark_id = crate::resource::normalized_relative_id(&file, &corpus_root)?;
            Ok((file, benchmark_id))
        })
        .collect::<Result<_>>()?;

    let pool = build_thread_pool(resources.plan.jobs)?;
    let now = current_iso8601();
    let mut private_input_builder = tempfile::Builder::new();
    private_input_builder.prefix("ay-harvest-inputs-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        private_input_builder.permissions(std::fs::Permissions::from_mode(0o700));
    }
    let private_input_dir = private_input_builder
        .tempdir()
        .with_bench_context(|| "reserving private harvest input staging directory".to_string())?;

    let mut store = BaselineStore::open(&store_path)?;
    let harvest_context = HarvestContext {
        corpus: &args.corpus,
        solver_path: pinned_solver.execution_path(),
        solver_recorded_path: &solver_path,
        solver_name: &solver_name,
        solver_version: &solver_version,
        solver_sha256: &solver_sha256,
        solver_size_bytes,
        timeout_s: args.timeout_s,
        harvested_at: &now,
        private_input_dir: private_input_dir.path(),
        resources: &resources,
        resource_requested_jobs,
        resource_jobs,
        resource_memlimit_mb,
        resource_nbcore,
        resource_headroom_mb,
    };

    // Use rayon in-pool to parallelize solver runs. We collect all rows (each is
    // small), then persist in one transaction at the end for speed and atomicity.
    let rows: Vec<BaselineRow> = pool.install(|| {
        use rayon::prelude::*;
        let total = files.len();
        let counter = std::sync::atomic::AtomicUsize::new(0);
        files
            .par_iter()
            .map(|(file, benchmark_id)| {
                let r = harvest_one(file, benchmark_id, &harvest_context);
                let done = counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                if done.is_multiple_of(10) || done == total {
                    if let Ok(row) = &r {
                        eprintln!(
                            "harvest: [{done}/{total}] {} -> {} ({}ms)",
                            benchmark_id, row.answer, row.wall_ms
                        );
                    }
                }
                r
            })
            .collect::<Result<Vec<_>>>()
    })?;

    if rows.iter().any(|row| row.content_hash.is_empty()) {
        return Err(BenchError::msg(
            "failed to hash one or more benchmark inputs; refusing an unverifiable baseline",
        ));
    }
    pinned_solver.verify_source()?;

    let solved = rows
        .iter()
        .filter(|r| r.answer == "sat" || r.answer == "unsat")
        .count();
    let timeouts = rows.iter().filter(|r| r.answer == "timeout").count();
    let memouts = rows.iter().filter(|r| r.answer == "memout").count();
    let errors = rows.iter().filter(|r| r.answer == "error").count();
    let wrong = rows
        .iter()
        .filter(|row| {
            matches!(row.answer.as_str(), "sat" | "unsat")
                && matches!(row.expected.as_str(), "sat" | "unsat")
                && row.answer != row.expected
        })
        .count();
    if wrong > 0 {
        return Err(BenchError::msg(format!(
            "reference solver contradicted {wrong} declared benchmark status(es); refusing to poison the baseline store"
        )));
    }
    store.replace_campaign(&rows)?;
    let invalid = errors;
    eprintln!(
        "harvest: wrote {} rows  (solved={} timeout={} memout={} error={} wrong={} invalid={})",
        rows.len(),
        solved,
        timeouts,
        memouts,
        errors,
        wrong,
        invalid,
    );
    Ok(rows.len())
}

fn build_thread_pool(jobs: usize) -> Result<rayon::ThreadPool> {
    let mut builder = rayon::ThreadPoolBuilder::new();
    if jobs > 0 {
        builder = builder.num_threads(jobs);
    }
    builder
        .build()
        .map_err(|e| BenchError::ThreadPool(e.to_string()))
}

struct HarvestContext<'a> {
    corpus: &'a str,
    solver_path: &'a Path,
    solver_recorded_path: &'a Path,
    solver_name: &'a str,
    solver_version: &'a str,
    solver_sha256: &'a str,
    solver_size_bytes: i64,
    timeout_s: f64,
    harvested_at: &'a str,
    private_input_dir: &'a Path,
    resources: &'a crate::resource::PlannedResources,
    resource_requested_jobs: i64,
    resource_jobs: i64,
    resource_memlimit_mb: i64,
    resource_nbcore: i64,
    resource_headroom_mb: i64,
}

fn harvest_one(
    file: &Path,
    benchmark_id: &str,
    context: &HarvestContext<'_>,
) -> Result<BaselineRow> {
    let prepared = crate::native::prepare_benchmark(
        file,
        benchmark_id,
        context.private_input_dir,
        context.resources,
        context.timeout_s,
    )?;
    let expected = read_expected_for_id(&prepared.solver_path, benchmark_id)?;

    let outcome = run_solver(
        context.solver_path,
        &prepared.solver_path,
        context.timeout_s,
        context.resources,
    );

    Ok(BaselineRow {
        corpus: context.corpus.to_string(),
        benchmark_path: benchmark_id.to_string(),
        content_hash: prepared.content_hash,
        solver_input_hash: prepared.solver_input_hash,
        solver: context.solver_name.to_string(),
        solver_version: context.solver_version.to_string(),
        solver_path: context.solver_recorded_path.display().to_string(),
        solver_sha256: context.solver_sha256.to_string(),
        solver_size_bytes: context.solver_size_bytes,
        answer: outcome.answer,
        expected: expected
            .value
            .clone()
            .unwrap_or_else(|| "unknown".to_string()),
        expected_source: expected.source.to_string(),
        wall_ms: outcome.wall_ms,
        exit_code: outcome.exit_code,
        timeout_s: context.timeout_s,
        stdout_head: outcome.stdout_head,
        stderr_head: outcome.stderr_head,
        harvested_at: context.harvested_at.to_string(),
        resource_requested_jobs: context.resource_requested_jobs,
        resource_jobs: context.resource_jobs,
        resource_memlimit_mb: context.resource_memlimit_mb,
        resource_nbcore: context.resource_nbcore,
        resource_headroom_mb: context.resource_headroom_mb,
        resource_enforcement: ENFORCEMENT_RSS_WATCHDOG_V1.to_string(),
        solver_argv_json: serde_json::to_string(&outcome.solver_argv)?,
        solver_env_json: serde_json::to_string(&outcome.solver_env)?,
        stdout_sha256: outcome.stdout_sha256,
        stderr_sha256: outcome.stderr_sha256,
        stdout_truncated: outcome.stdout_truncated,
        stderr_truncated: outcome.stderr_truncated,
    })
}

struct SolverOutcome {
    answer: String,
    wall_ms: i64,
    exit_code: Option<i32>,
    stdout_head: String,
    stderr_head: String,
    solver_argv: Vec<String>,
    solver_env: BTreeMap<String, String>,
    stdout_sha256: String,
    stderr_sha256: String,
    stdout_truncated: bool,
    stderr_truncated: bool,
}

impl SolverOutcome {
    fn harness_error(error: impl Into<String>) -> Self {
        Self {
            answer: "error".to_string(),
            wall_ms: 0,
            exit_code: None,
            stdout_head: String::new(),
            stderr_head: error.into(),
            solver_argv: Vec::new(),
            solver_env: BTreeMap::new(),
            stdout_sha256:
                "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
                    .to_string(),
            stderr_sha256:
                "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
                    .to_string(),
            stdout_truncated: false,
            stderr_truncated: false,
        }
    }
}

const CAPTURE_HEAD_BYTES: usize = 512 * 1024;
const CAPTURE_TAIL_BYTES: usize = 512 * 1024;
const CAPTURE_LIMIT_BYTES: usize = CAPTURE_HEAD_BYTES + CAPTURE_TAIL_BYTES;

#[derive(Default)]
struct CapturedPipe {
    text: String,
    truncated: bool,
    read_failed: bool,
    sha256: String,
}

impl CapturedPipe {
    fn incomplete(&self) -> bool {
        self.truncated || self.read_failed
    }

    fn missing() -> Self {
        Self {
            read_failed: true,
            ..Self::default()
        }
    }
}

struct PipeCapture {
    receiver: mpsc::Receiver<CapturedPipe>,
}

impl PipeCapture {
    /// Drain a solver pipe concurrently while retaining a bounded head/tail.
    /// Waiting for process exit before reading can deadlock on a full pipe;
    /// retaining unlimited diagnostics lets a noisy solver OOM the harness.
    fn start<R>(mut reader: R) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            use sha2::{Digest as _, Sha256};

            let mut head = Vec::with_capacity(CAPTURE_HEAD_BYTES);
            let mut tail: VecDeque<Vec<u8>> = VecDeque::new();
            let mut tail_len = 0usize;
            let mut total_len = 0usize;
            let mut read_failed = false;
            let mut hasher = Sha256::new();
            let mut chunk = [0u8; 8192];
            loop {
                let read = match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => read,
                    Err(_) => {
                        read_failed = true;
                        break;
                    }
                };
                hasher.update(&chunk[..read]);
                total_len = total_len.saturating_add(read);
                let head_read = read.min(CAPTURE_HEAD_BYTES.saturating_sub(head.len()));
                head.extend_from_slice(&chunk[..head_read]);
                if head_read < read {
                    let trailing = chunk[head_read..read].to_vec();
                    tail_len += trailing.len();
                    tail.push_back(trailing);
                    while tail_len > CAPTURE_TAIL_BYTES {
                        let excess = tail_len - CAPTURE_TAIL_BYTES;
                        let Some(front) = tail.front_mut() else {
                            break;
                        };
                        let remove = excess.min(front.len());
                        front.drain(..remove);
                        tail_len -= remove;
                        if front.is_empty() {
                            tail.pop_front();
                        }
                    }
                }
            }
            if !tail.is_empty() {
                if total_len > CAPTURE_LIMIT_BYTES {
                    head.extend_from_slice(b"\n[... output truncated ...]\n");
                }
                for bytes in tail {
                    head.extend_from_slice(&bytes);
                }
            }
            let _ = sender.send(CapturedPipe {
                text: String::from_utf8_lossy(&head).into_owned(),
                truncated: total_len > CAPTURE_LIMIT_BYTES,
                read_failed,
                sha256: format!("sha256:{:x}", hasher.finalize()),
            });
        });
        Self { receiver }
    }

    fn finish(self) -> CapturedPipe {
        self.receiver
            .recv_timeout(Duration::from_secs(2))
            .unwrap_or(CapturedPipe {
                read_failed: true,
                ..CapturedPipe::default()
            })
    }
}

fn run_solver(
    solver: &Path,
    benchmark: &Path,
    timeout_s: f64,
    resources: &crate::resource::PlannedResources,
) -> SolverOutcome {
    let timeout = match crate::resource::checked_benchmark_timeout(timeout_s, "harvest child") {
        Ok(timeout) => timeout,
        Err(error) => return SolverOutcome::harness_error(error.to_string()),
    };
    let start = Instant::now();

    // Per-solver argument customization. For z3 we pass `-T:<seconds>` so the
    // solver self-terminates quickly; for Golem we use the input's exact
    // declared logic with the CHC spacer engine. SAT solvers
    // (CaDiCaL, Kissat) accept their own wall-clock timeout flags in seconds
    // and run in quiet mode to keep `stdout_head` focused on the
    // `s SATISFIABLE` / `s UNSATISFIABLE` line. Alternate SMT solvers
    // (Bitwuzla, CVC5) take millisecond timeouts. `Other` solvers run with no
    // extra flags and rely on the external wall-clock timeout.
    let solver_file = solver
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    let kind = SolverKind::detect(solver_file);

    let timeout_sec_u64 = timeout.as_secs().max(1);
    let timeout_ms_u64 = u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX);

    let mut args = Vec::<String>::new();
    // These variables are enforced by ay-pb and are harmless advisory
    // provenance for external solvers; the zero-grace RSS watchdog remains
    // the exact memory enforcement for every child.
    match kind {
        SolverKind::Z3 => {
            args.push(format!("-T:{}", timeout_sec_u64));
        }
        SolverKind::Golem => {
            let logic = match read_smt_metadata(benchmark) {
                Ok(metadata) => match metadata.logic {
                    Some(logic) => logic,
                    None => {
                        return SolverOutcome::harness_error(format!(
                            "Golem input has no explicit set-logic: {}",
                            benchmark.display()
                        ))
                    }
                },
                Err(error) => return SolverOutcome::harness_error(error.to_string()),
            };
            args.extend([
                "-l".to_string(),
                logic,
                "-e".to_string(),
                "spacer".to_string(),
            ]);
        }
        SolverKind::CaDiCaL => {
            args.extend([
                "-q".to_string(),
                "-t".to_string(),
                timeout_sec_u64.to_string(),
            ]);
        }
        SolverKind::Kissat => {
            args.extend(["-q".to_string(), format!("--time={timeout_sec_u64}")]);
        }
        SolverKind::Bitwuzla => {
            args.extend(["-t".to_string(), timeout_ms_u64.to_string()]);
        }
        SolverKind::Cvc5 => {
            args.push(format!("--tlimit={timeout_ms_u64}"));
        }
        SolverKind::Other => {}
    }
    args.push(benchmark.display().to_string());
    let mut solver_argv = Vec::with_capacity(args.len() + 1);
    solver_argv.push(solver.display().to_string());
    solver_argv.extend(args.iter().cloned());
    let mut solver_env = BTreeMap::new();
    solver_env.insert("LC_ALL".to_string(), "C".to_string());
    solver_env.insert("TZ".to_string(), "UTC".to_string());
    solver_env.insert(
        "PATH".to_string(),
        std::env::var("PATH").unwrap_or_else(|_| "/usr/local/bin:/usr/bin:/bin".to_string()),
    );
    solver_env.insert(
        "MEMLIMIT".to_string(),
        resources.plan.memlimit_mb_per_child.to_string(),
    );
    solver_env.insert(
        "NBCORE".to_string(),
        resources.plan.nbcore_per_child.to_string(),
    );
    let mut cmd = resources.external_command(solver);
    cmd.args(&args);
    cmd.env_clear();
    cmd.envs(&solver_env);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());
    let (mut child, watchdog) = match resources.spawn_external_child(&mut cmd, "ay bench harvest") {
        Ok(guarded) => guarded,
        Err(e) => {
            let mut outcome = SolverOutcome::harness_error(format!("spawn failed: {e}"));
            outcome.solver_argv = solver_argv;
            outcome.solver_env = solver_env;
            return outcome;
        }
    };
    let stdout_capture = child.stdout.take().map(PipeCapture::start);
    let stderr_capture = child.stderr.take().map(PipeCapture::start);
    let outcome =
        crate::resource::wait_for_guarded_child(&mut child, watchdog, timeout, "ay bench harvest");
    let elapsed_ms = start.elapsed().as_millis().min(i64::MAX as u128) as i64;
    let stdout = stdout_capture
        .map(PipeCapture::finish)
        .unwrap_or_else(CapturedPipe::missing);
    let mut stderr = stderr_capture
        .map(PipeCapture::finish)
        .unwrap_or_else(CapturedPipe::missing);
    let capture_incomplete = stdout.incomplete() || stderr.incomplete();
    let (answer, exit_code) = match outcome {
        Err(error) => {
            append_diagnostic(
                &mut stderr.text,
                &format!("RSS watchdog or child wait failure: {error}"),
            );
            ("error", None)
        }
        Ok(outcome) if outcome.memout => ("memout", None),
        Ok(outcome) if outcome.timed_out => ("timeout", None),
        Ok(_) if capture_incomplete => ("error", None),
        Ok(outcome) => match outcome.status {
            Some(status) => (
                parse_reference_verdict(&stdout.text, &stderr.text, status.code()),
                status.code(),
            ),
            None => {
                append_diagnostic(&mut stderr.text, "solver was not reaped");
                ("error", None)
            }
        },
    };
    if capture_incomplete {
        append_diagnostic(
            &mut stderr.text,
            "solver output capture was truncated or unreadable",
        );
    }
    SolverOutcome {
        answer: answer.to_string(),
        wall_ms: elapsed_ms,
        exit_code,
        stdout_head: truncate(&stdout.text, 512),
        stderr_head: truncate_head_tail(&stderr.text, 512),
        solver_argv,
        solver_env,
        stdout_sha256: stdout.sha256,
        stderr_sha256: stderr.sha256,
        stdout_truncated: stdout.truncated,
        stderr_truncated: stderr.truncated,
    }
}

fn append_diagnostic(text: &mut String, diagnostic: &str) {
    if !text.is_empty() {
        text.push('\n');
    }
    text.push_str(diagnostic);
}

/// Classification of a reference solver binary. Used to tailor the per-invocation
/// argument list:
///
/// | Kind     | Timeout flag                  | Notes                          |
/// |----------|-------------------------------|--------------------------------|
/// | Z3       | `-T:<seconds>`                | SMT/CHC                        |
/// | Golem    | `-l QF_LIA -e spacer`         | CHC; no timeout flag used      |
/// | CaDiCaL  | `-q -t <seconds>`             | SAT (DIMACS); quiet mode       |
/// | Kissat   | `-q --time=<seconds>`         | SAT (DIMACS); quiet mode       |
/// | Bitwuzla | `-t <milliseconds>`           | BV/SMT                         |
/// | Cvc5     | `--tlimit=<milliseconds>`     | SMT                            |
/// | Other    | (none)                        | rely on external wall-clock    |
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolverKind {
    Z3,
    Golem,
    CaDiCaL,
    Kissat,
    Bitwuzla,
    Cvc5,
    Other,
}

impl SolverKind {
    /// Identify a solver from its binary filename (e.g. "z3", "golem",
    /// "cadical", "kissat", "bitwuzla", "cvc5"). Matching is
    /// ASCII-case-insensitive.
    pub(crate) fn detect(file_name: &str) -> Self {
        if file_name.eq_ignore_ascii_case("z3") {
            Self::Z3
        } else if file_name.eq_ignore_ascii_case("golem") {
            Self::Golem
        } else if file_name.eq_ignore_ascii_case("cadical") {
            Self::CaDiCaL
        } else if file_name.eq_ignore_ascii_case("kissat") {
            Self::Kissat
        } else if file_name.eq_ignore_ascii_case("bitwuzla") {
            Self::Bitwuzla
        } else if file_name.eq_ignore_ascii_case("cvc5") {
            Self::Cvc5
        } else {
            Self::Other
        }
    }
}

fn parse_reference_verdict(stdout: &str, stderr: &str, exit_code: Option<i32>) -> &'static str {
    crate::resource::strict_solver_verdict(stdout, stderr, exit_code)
}

// ===================================================================
// Expected-verdict extraction
// ===================================================================

#[derive(Debug, Clone, Default)]
pub(crate) struct SmtMetadata {
    pub status: Option<String>,
    pub logic: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct ExpectedLabel {
    pub value: Option<String>,
    pub source: &'static str,
}

/// Parse metadata from the entire pinned input with constant parent memory.
/// This avoids treating an arbitrary 256 KiB prefix boundary as EOF while
/// still rejecting conflicting declarations anywhere in the file.
pub(crate) fn read_smt_metadata(path: &Path) -> Result<SmtMetadata> {
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let mut file = options
        .open(path)
        .with_bench_context(|| format!("opening SMT-LIB metadata source {}", path.display()))?;
    let metadata = file.metadata()?;
    if !metadata.file_type().is_file() {
        return Err(BenchError::msg(format!(
            "SMT-LIB metadata source is not a regular file: {}",
            path.display()
        )));
    }
    if metadata.len() > crate::resource::MAX_DECOMPRESSED_BYTES {
        return Err(BenchError::msg(format!(
            "SMT-LIB metadata source exceeds the fixed {}-byte input cap: {}",
            crate::resource::MAX_DECOMPRESSED_BYTES,
            path.display()
        )));
    }
    scan_smtlib_metadata(&mut file)
        .with_bench_context(|| format!("scanning SMT-LIB metadata in {}", path.display()))
}

pub(crate) fn read_expected_for_id(path: &Path, benchmark_id: &str) -> Result<ExpectedLabel> {
    let header = if base_extension(benchmark_id).eq_ignore_ascii_case("smt2") {
        read_smt_metadata(path)?.status
    } else {
        None
    };
    let path_label = expected_from_relative_id(benchmark_id)?;
    if header.is_some() && path_label.is_some() && header != path_label {
        return Err(BenchError::msg(format!(
            "benchmark expected-status conflict between SMT-LIB header {:?} and corpus-relative path {:?}: {benchmark_id}",
            header, path_label
        )));
    }
    let (value, source) = match (header, path_label) {
        (Some(value), Some(_)) => (Some(value), "header+path"),
        (Some(value), None) => (Some(value), "header"),
        (None, Some(value)) => (Some(value), "path"),
        (None, None) => (None, "unknown"),
    };
    Ok(ExpectedLabel { value, source })
}

/// Compatibility helper used by callers that have no corpus root. Production
/// harvest/native paths use `read_expected_for_id` with a strict relative ID.
pub fn read_expected(path: &Path) -> Result<Option<String>> {
    let id = path.to_str().ok_or_else(|| {
        BenchError::msg(format!(
            "benchmark path is not valid UTF-8: {}",
            path.display()
        ))
    })?;
    Ok(read_expected_for_id(path, id)?.value)
}

fn expected_from_relative_id(benchmark_id: &str) -> Result<Option<String>> {
    let mut observed: Option<&'static str> = None;
    for component in benchmark_id.split('/') {
        let candidate = if component.eq_ignore_ascii_case("sat") {
            Some("sat")
        } else if component.eq_ignore_ascii_case("unsat") {
            Some("unsat")
        } else {
            None
        };
        if let Some(candidate) = candidate {
            if observed.is_some_and(|previous| previous != candidate) {
                return Err(BenchError::msg(format!(
                    "conflicting sat/unsat components in corpus-relative benchmark path: {benchmark_id}"
                )));
            }
            observed = Some(candidate);
        }
    }
    Ok(observed.map(str::to_string))
}

fn base_extension(path: &str) -> &str {
    let lower = path.to_ascii_lowercase();
    let without_compression = [".xz", ".gz", ".bz2"]
        .iter()
        .find(|suffix| lower.ends_with(**suffix))
        .map_or(path, |suffix| &path[..path.len() - suffix.len()]);
    without_compression
        .rsplit_once('.')
        .map_or("", |(_, ext)| ext)
}

fn scan_smtlib_metadata(reader: &mut impl Read) -> Result<SmtMetadata> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum State {
        Normal,
        Comment,
        String,
        StringQuote,
        Quoted,
    }

    fn push_token(
        command: &mut Vec<String>,
        token: &mut Vec<u8>,
        oversized: &mut bool,
    ) -> Result<()> {
        if token.is_empty() && !*oversized {
            return Ok(());
        }
        if command.len() < 4 {
            if *oversized {
                command.push("<oversized-symbol>".to_string());
            } else {
                command.push(String::from_utf8(std::mem::take(token)).map_err(|_| {
                    BenchError::msg("SMT-LIB top-level command contains invalid UTF-8")
                })?);
            }
        }
        token.clear();
        *oversized = false;
        Ok(())
    }

    fn observe(current: &mut Option<String>, value: &str, label: &str) -> Result<()> {
        if current.as_deref().is_some_and(|previous| previous != value) {
            return Err(BenchError::msg(format!(
                "conflicting SMT-LIB {label} declarations"
            )));
        }
        *current = Some(value.to_string());
        Ok(())
    }

    fn finish_command(command: &[String], metadata: &mut SmtMetadata) -> Result<()> {
        if command.first().is_some_and(|value| value == "set-info")
            && command.get(1).is_some_and(|value| value == ":status")
        {
            if command.len() != 3 || !matches!(command[2].as_str(), "sat" | "unsat" | "unknown") {
                return Err(BenchError::msg(
                    "invalid SMT-LIB (set-info :status ...) declaration",
                ));
            }
            observe(&mut metadata.status, &command[2], ":status")?;
        } else if command.first().is_some_and(|value| value == "set-logic") {
            if command.len() != 2
                || command[1].starts_with('<')
                || command[1].chars().any(char::is_whitespace)
            {
                return Err(BenchError::msg(
                    "invalid SMT-LIB (set-logic ...) declaration",
                ));
            }
            observe(&mut metadata.logic, &command[1], "set-logic")?;
        }
        Ok(())
    }

    let mut state = State::Normal;
    let mut depth = 0_usize;
    let mut command = Vec::<String>::new();
    let mut token = Vec::<u8>::new();
    let mut token_oversized = false;
    let mut metadata = SmtMetadata::default();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        let mut index = 0_usize;
        while index < read {
            let byte = buffer[index];
            match state {
                State::Comment => {
                    if byte == b'\n' {
                        state = State::Normal;
                    }
                    index += 1;
                }
                State::String => {
                    if byte == b'"' {
                        state = State::StringQuote;
                    }
                    index += 1;
                }
                State::StringQuote => {
                    if byte == b'"' {
                        state = State::String;
                        index += 1;
                    } else {
                        state = State::Normal;
                    }
                }
                State::Quoted => {
                    if byte == b'|' {
                        state = State::Normal;
                    }
                    index += 1;
                }
                State::Normal => match byte {
                    b';' => {
                        if depth == 1 {
                            push_token(&mut command, &mut token, &mut token_oversized)?;
                        }
                        state = State::Comment;
                        index += 1;
                    }
                    b'"' | b'|' => {
                        if depth == 1 {
                            push_token(&mut command, &mut token, &mut token_oversized)?;
                            if command.len() < 4 {
                                command.push("<non-symbol>".to_string());
                            }
                        }
                        state = if byte == b'"' {
                            State::String
                        } else {
                            State::Quoted
                        };
                        index += 1;
                    }
                    b'(' => {
                        if depth == 1 {
                            push_token(&mut command, &mut token, &mut token_oversized)?;
                        }
                        if depth == 0 {
                            command.clear();
                        }
                        depth = depth
                            .checked_add(1)
                            .ok_or_else(|| BenchError::msg("SMT-LIB nesting depth overflow"))?;
                        index += 1;
                    }
                    b')' => {
                        if depth == 0 {
                            return Err(BenchError::msg(
                                "unmatched ')' while scanning SMT-LIB metadata",
                            ));
                        }
                        if depth == 1 {
                            push_token(&mut command, &mut token, &mut token_oversized)?;
                            finish_command(&command, &mut metadata)?;
                        }
                        depth -= 1;
                        index += 1;
                    }
                    byte if byte.is_ascii_whitespace() => {
                        if depth == 1 {
                            push_token(&mut command, &mut token, &mut token_oversized)?;
                        }
                        index += 1;
                    }
                    _ => {
                        if depth == 1 && command.len() < 4 {
                            if token.len() < 4096 {
                                token.push(byte);
                            } else {
                                token_oversized = true;
                            }
                        }
                        index += 1;
                    }
                },
            }
        }
    }
    if state == State::StringQuote {
        state = State::Normal;
    }
    if matches!(state, State::String | State::Quoted) || depth != 0 {
        return Err(BenchError::msg(
            "unterminated string, quoted symbol, or command while scanning SMT-LIB metadata",
        ));
    }
    Ok(metadata)
}

// ===================================================================
// File discovery / hashing
// ===================================================================

fn discover_files(root: &Path, extensions: &[String], limit: usize) -> Result<Vec<PathBuf>> {
    let retained_limit = if limit == 0 {
        crate::resource::MAX_DISCOVERED_BENCHMARKS
    } else {
        limit
    };
    if retained_limit > crate::resource::MAX_DISCOVERED_BENCHMARKS {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "discovery limit {retained_limit} exceeds the fixed {}-benchmark cap",
                crate::resource::MAX_DISCOVERED_BENCHMARKS
            ),
        });
    }
    let mut retained = std::collections::BinaryHeap::new();
    collect_files_with_limits(
        root,
        extensions,
        &mut retained,
        retained_limit,
        crate::resource::MAX_CORPUS_TRAVERSAL_ENTRIES,
        crate::resource::MAX_CORPUS_PENDING_DIRECTORIES,
        crate::resource::MAX_DISCOVERED_BENCHMARKS,
    )
    .with_bench_context(|| format!("walking {}", root.display()))?;
    let mut out = retained.into_vec();
    out.sort();
    Ok(out)
}

fn collect_files_with_limits(
    dir: &Path,
    extensions: &[String],
    retained: &mut std::collections::BinaryHeap<PathBuf>,
    retained_limit: usize,
    max_entries: usize,
    max_pending_directories: usize,
    max_benchmarks: usize,
) -> Result<()> {
    if retained_limit == 0 {
        return Err(BenchError::msg(
            "corpus discovery retention limit must be positive",
        ));
    }
    let root_type = std::fs::symlink_metadata(dir)?.file_type();
    if root_type.is_file() {
        if matches_extension(dir, extensions) {
            if max_benchmarks == 0 {
                return Err(BenchError::msg(
                    "corpus contains more than the fixed 0-benchmark cap",
                ));
            }
            retained.push(dir.to_path_buf());
        }
        return Ok(());
    }
    if !root_type.is_dir() {
        return Ok(());
    }
    let mut pending = vec![dir.to_path_buf()];
    let mut visited_entries = 0_usize;
    let mut matched_benchmarks = 0_usize;
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(directory)? {
            let entry = entry?;
            visited_entries = visited_entries
                .checked_add(1)
                .ok_or_else(|| BenchError::msg("corpus traversal entry count overflow"))?;
            if visited_entries > max_entries {
                return Err(BenchError::msg(format!(
                    "corpus traversal exceeds the fixed {max_entries}-entry cap"
                )));
            }
            let path = entry.path();
            let file_type = entry.file_type()?;
            if file_type.is_dir() {
                if pending.len() >= max_pending_directories {
                    return Err(BenchError::msg(format!(
                        "corpus traversal exceeds the fixed {max_pending_directories}-pending-directory cap"
                    )));
                }
                pending.push(path);
            } else if file_type.is_file() && matches_extension(&path, extensions) {
                matched_benchmarks = matched_benchmarks
                    .checked_add(1)
                    .ok_or_else(|| BenchError::msg("discovered benchmark count overflow"))?;
                if matched_benchmarks > max_benchmarks {
                    return Err(BenchError::msg(format!(
                        "corpus contains more than the fixed {max_benchmarks}-benchmark cap"
                    )));
                }
                if retained.len() < retained_limit {
                    retained.push(path);
                } else if retained.peek().is_some_and(|largest| path < *largest) {
                    retained.pop();
                    retained.push(path);
                }
            }
        }
    }
    Ok(())
}

fn matches_extension(path: &Path, extensions: &[String]) -> bool {
    let Some(name) = path.file_name().and_then(|value| value.to_str()) else {
        return false;
    };
    let lower = name.to_ascii_lowercase();
    let base = [".xz", ".gz", ".bz2"]
        .iter()
        .find_map(|suffix| lower.strip_suffix(suffix))
        .unwrap_or(&lower);
    let Some((_, ext)) = base.rsplit_once('.') else {
        return false;
    };
    extensions.iter().any(|e| e.eq_ignore_ascii_case(ext))
}

/// Content-hash a file with a toolchain-independent digest.
///
/// These values persist across compiler upgrades and are compared with native
/// benchmark results, so `std::hash::DefaultHasher` is unsuitable: its
/// algorithm is explicitly not a stable storage format.
#[cfg(test)]
fn hash_file(path: &Path) -> Result<String> {
    use sha2::{Digest as _, Sha256};
    use std::io::Read as _;

    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let mut file = options
        .open(path)
        .with_bench_context(|| format!("opening {}", path.display()))?;
    if !file.metadata()?.file_type().is_file() {
        return Err(BenchError::msg(format!(
            "refusing to hash non-regular file {}",
            path.display()
        )));
    }
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 8192];
    loop {
        let read = file
            .read(&mut buffer)
            .with_bench_context(|| format!("reading {}", path.display()))?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

// ===================================================================
// Solver binary resolution
// ===================================================================

fn resolve_solver(name_or_path: &str) -> Option<PathBuf> {
    let p = Path::new(name_or_path);
    if p.is_absolute() || name_or_path.contains('/') {
        if p.exists() {
            return Some(p.to_path_buf());
        }
        return None;
    }
    let path = std::env::var_os("PATH")?;
    for directory in std::env::split_paths(&path) {
        let candidate = directory.join(name_or_path);
        let Ok(metadata) = std::fs::metadata(&candidate) else {
            continue;
        };
        if !metadata.is_file() {
            continue;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            if metadata.permissions().mode() & 0o111 == 0 {
                continue;
            }
        }
        return Some(candidate);
    }
    None
}

fn solver_display_name(requested: &str, resolved: &Path) -> String {
    // Prefer the `requested` name (usually `z3`, `cadical`, `cvc5`) over the
    // absolute path so downstream tools can key by short name.
    let name = Path::new(requested)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(requested);
    if !name.is_empty() {
        name.to_string()
    } else {
        resolved
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("solver")
            .to_string()
    }
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_string()
    } else {
        // Be careful with UTF-8 boundaries.
        let cut = (0..=max)
            .rev()
            .find(|index| s.is_char_boundary(*index))
            .unwrap_or(0);
        s[..cut].to_string()
    }
}

fn truncate_head_tail(s: &str, max: usize) -> String {
    if s.len() <= max || max < 2 {
        return truncate(s, max);
    }
    const MARKER: &str = "\n[... truncated ...]\n";
    if max <= MARKER.len() {
        return truncate(s, max);
    }
    let content_budget = max - MARKER.len();
    let head_budget = content_budget / 2;
    let tail_budget = content_budget - head_budget;
    let head_end = (0..=head_budget)
        .rev()
        .find(|index| s.is_char_boundary(*index))
        .unwrap_or(0);
    let tail_start = (s.len().saturating_sub(tail_budget)..s.len())
        .find(|index| s.is_char_boundary(*index))
        .unwrap_or(s.len());
    format!("{}{MARKER}{}", &s[..head_end], &s[tail_start..])
}

fn current_iso8601() -> String {
    // Minimal timestamp — seconds since UNIX epoch as a string. We avoid
    // pulling in `chrono` or `time` for this one field. `ay-bench diff` uses
    // the same string-based comparison for `timestamp` in its store.
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    format!("unix:{secs}")
}

// ===================================================================
// Verify CLI
// ===================================================================

/// Arguments for `ay bench verify`.
#[derive(Debug, Clone)]
pub struct VerifyArgs {
    /// Corpus name in the baseline store (e.g. "qfuf-neq").
    pub corpus: String,
    /// AY results JSON file produced by `ay bench run ... -o results.json`.
    pub results_file: PathBuf,
    /// Reference solver to compare against (matches `baselines.solver`).
    pub reference_solver: String,
    /// Override baseline store path.
    pub baseline_store: Option<PathBuf>,
    /// Emit JSON report to stdout.
    pub json: bool,
}

/// Output classification for one benchmark.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum VerifyClass {
    /// Both solvers agreed on `sat`/`unsat`.
    Match,
    /// AY said `sat`/`unsat` but the reference solver said the opposite.
    /// This is a potential soundness bug.
    SoundBug,
    /// AY returned `unknown`/`timeout`/`error` but the reference solved it.
    Incomplete,
    /// Reference returned `unknown`/`timeout`/`error` but AY solved it.
    /// AY is ahead here, but worth recording.
    ReferenceUnknown,
    /// Neither solver produced a definite answer.
    BothUnknown,
    /// No baseline row for this benchmark.
    NoBaseline,
    /// Both rows exist, but their admitted RAM/CPU envelopes differ or one
    /// side lacks envelope provenance.
    NonComparable,
}

impl VerifyClass {
    fn as_str(self) -> &'static str {
        match self {
            VerifyClass::Match => "match",
            VerifyClass::SoundBug => "sound_bug",
            VerifyClass::Incomplete => "incomplete",
            VerifyClass::ReferenceUnknown => "reference_unknown",
            VerifyClass::BothUnknown => "both_unknown",
            VerifyClass::NoBaseline => "no_baseline",
            VerifyClass::NonComparable => "non_comparable",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct VerifyEntry {
    pub benchmark_path: String,
    pub ay_answer: String,
    pub reference_answer: Option<String>,
    pub expected: Option<String>,
    pub ay_wall_ms: i64,
    pub reference_wall_ms: Option<i64>,
    pub classification: String,
    pub ay_resource_envelope: Option<String>,
    pub baseline_resource_envelope: Option<String>,
    pub ay_content_hash: Option<String>,
    pub baseline_content_hash: Option<String>,
    pub non_comparable_reason: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct VerifyReport {
    pub corpus: String,
    pub reference_solver: String,
    pub total: usize,
    pub matches: usize,
    pub sound_bugs: usize,
    pub incomplete: usize,
    pub reference_unknown: usize,
    pub both_unknown: usize,
    pub no_baseline: usize,
    pub non_comparable: usize,
    pub ay_resource_envelope: Option<String>,
    pub entries: Vec<VerifyEntry>,
}

impl VerifyReport {
    /// `true` iff any entry classified as a potential soundness bug.
    #[must_use]
    pub fn has_sound_bugs(&self) -> bool {
        self.sound_bugs > 0
    }

    /// Non-comparable evidence is also a failing verification outcome: callers
    /// must not report success when resource envelopes differ.
    #[must_use]
    pub fn has_failures(&self) -> bool {
        self.has_sound_bugs() || self.no_baseline > 0 || self.non_comparable > 0
    }
}

/// Classify a single (ay_answer, ref_answer) pair.
#[must_use]
pub fn classify_pair(ay_answer: &str, reference_answer: Option<&str>) -> VerifyClass {
    let ay = ay_answer.trim().to_ascii_lowercase();
    let Some(ra) = reference_answer else {
        return VerifyClass::NoBaseline;
    };
    let r = ra.trim().to_ascii_lowercase();
    let ay_def = ay == "sat" || ay == "unsat";
    let r_def = r == "sat" || r == "unsat";
    match (ay_def, r_def) {
        (true, true) => {
            if ay == r {
                VerifyClass::Match
            } else {
                VerifyClass::SoundBug
            }
        }
        (false, true) => VerifyClass::Incomplete,
        (true, false) => VerifyClass::ReferenceUnknown,
        (false, false) => VerifyClass::BothUnknown,
    }
}

/// Run the verify subcommand, producing a report and returning it.
///
/// The caller (CLI layer) is responsible for printing and mapping
/// `report.has_sound_bugs()` to a non-zero exit code.
pub fn cmd_verify(args: VerifyArgs) -> Result<VerifyReport> {
    let root = crate::runner::repo_root_public();
    let store_path = args
        .baseline_store
        .clone()
        .unwrap_or_else(|| BaselineStorePath::default_at(&root).as_path().to_path_buf());
    if !store_path.exists() {
        return Err(BenchError::msg(format!(
            "no baseline store at {} — run `ay bench harvest` first",
            store_path.display()
        )));
    }

    let store = BaselineStore::open(&store_path)?;
    let rows = store.rows_for_corpus(&args.corpus)?;
    if rows.is_empty() {
        return Err(BenchError::msg(format!(
            "no baseline rows for corpus '{}' in {}",
            args.corpus,
            store_path.display()
        )));
    }

    // Build an exact lookup by normalized corpus-relative identifier. Basename
    // aliases are deliberately forbidden: two directories can legally contain
    // the same filename and must never share verdict authority.
    let selected = rows
        .into_iter()
        .filter(|row| row.solver == args.reference_solver)
        .collect::<Vec<_>>();
    if selected.is_empty() {
        return Err(BenchError::msg(format!(
            "corpus '{}' has no rows for solver '{}'",
            args.corpus, args.reference_solver
        )));
    }
    validate_uniform_campaign(&selected)?;
    let mut by_path: std::collections::BTreeMap<String, &BaselineRow> =
        std::collections::BTreeMap::new();
    for r in &selected {
        if r.benchmark_path.trim().is_empty()
            || !is_stable_sha256(&r.content_hash)
            || r.solver_path.trim().is_empty()
            || !is_stable_sha256(&r.solver_sha256)
            || r.solver_size_bytes <= 0
        {
            return Err(BenchError::msg(format!(
                "baseline row lacks stable benchmark/solver provenance: {}",
                r.benchmark_path
            )));
        }
        if by_path.insert(r.benchmark_path.clone(), r).is_some() {
            return Err(BenchError::msg(format!(
                "duplicate baseline benchmark path: {}",
                r.benchmark_path
            )));
        }
    }

    // Load AY results JSON (produced by `ay bench run -o ...`).
    let text = crate::resource::read_bounded_text(
        &args.results_file,
        256 * 1024 * 1024,
        "native benchmark results",
    )?;
    let doc: serde_json::Value = serde_json::from_str(&text)
        .with_bench_context(|| format!("parsing JSON in {}", args.results_file.display()))?;
    let ay_resource_plan = doc
        .pointer("/settings/resource_plan")
        .cloned()
        .and_then(|value| serde_json::from_value::<crate::resource::ResourcePlan>(value).ok());
    let ay_resource_enforcement = doc
        .pointer("/settings/resource_enforcement")
        .and_then(serde_json::Value::as_str);
    let ay_timeout_sec = doc
        .pointer("/settings/timeout_sec")
        .and_then(serde_json::Value::as_f64);
    let ay_resource_envelope = ay_resource_plan
        .as_ref()
        .zip(ay_resource_enforcement)
        .zip(ay_timeout_sec)
        .and_then(|((plan, enforcement), timeout_sec)| {
            crate::resource::effective_execution_envelope(plan, enforcement, timeout_sec).ok()
        });

    let items = extract_result_items(&doc).with_bench_context(|| {
        format!(
            "could not find a results array in {}",
            args.results_file.display()
        )
    })?;
    if items.is_empty() {
        return Err(BenchError::msg(
            "native benchmark results contain no items; refusing vacuous verification",
        ));
    }

    let mut entries = Vec::with_capacity(items.len());
    let mut counts = [0usize; 7];
    let mut seen_item_ids = std::collections::BTreeSet::new();
    let mut matched_baselines = std::collections::BTreeSet::new();
    for item in items {
        if !seen_item_ids.insert(item.file.clone()) {
            return Err(BenchError::msg(format!(
                "duplicate native result item identifier: {}",
                item.file
            )));
        }
        let ay_answer = item.result.trim().to_ascii_lowercase();
        let ay_wall_ms = (item.time_sec * 1000.0).round() as i64;
        let base = by_path.get(&item.file).copied();
        if let Some(base) = base {
            matched_baselines.insert(base.benchmark_path.clone());
        }
        let ref_answer = base.map(|b| b.answer.clone());
        let ref_wall_ms = base.map(|b| b.wall_ms);
        let expected = base.map(|b| b.expected.clone());
        let baseline_resource_envelope = base.and_then(baseline_execution_envelope);
        let baseline_content_hash = base.map(|row| row.content_hash.clone());
        let resources_match = base.is_none()
            || (ay_resource_envelope.is_some()
                && ay_resource_envelope == baseline_resource_envelope);
        let content_matches = base.is_none()
            || matches!(
                (&item.benchmark_content_hash, &baseline_content_hash),
                (Some(ay), Some(baseline)) if !ay.is_empty() && ay == baseline
            );
        let non_comparable_reason = match (base.is_some(), resources_match, content_matches) {
            (true, false, false) => Some("resource envelope and benchmark content differ"),
            (true, false, true) => Some("resource envelope differs"),
            (true, true, false) => Some("benchmark content differs or is missing"),
            _ => None,
        };
        let class = if non_comparable_reason.is_some() {
            VerifyClass::NonComparable
        } else {
            classify_pair(&ay_answer, ref_answer.as_deref())
        };
        match class {
            VerifyClass::Match => counts[0] += 1,
            VerifyClass::SoundBug => counts[1] += 1,
            VerifyClass::Incomplete => counts[2] += 1,
            VerifyClass::ReferenceUnknown => counts[3] += 1,
            VerifyClass::BothUnknown => counts[4] += 1,
            VerifyClass::NoBaseline => counts[5] += 1,
            VerifyClass::NonComparable => counts[6] += 1,
        }
        entries.push(VerifyEntry {
            benchmark_path: item.file,
            ay_answer,
            reference_answer: ref_answer,
            expected,
            ay_wall_ms,
            reference_wall_ms: ref_wall_ms,
            classification: class.as_str().to_string(),
            ay_resource_envelope: ay_resource_envelope.clone(),
            baseline_resource_envelope,
            ay_content_hash: item.benchmark_content_hash,
            baseline_content_hash,
            non_comparable_reason: non_comparable_reason.map(str::to_string),
        });
    }

    let unmatched_results = entries
        .iter()
        .filter(|entry| entry.reference_answer.is_none())
        .map(|entry| entry.benchmark_path.clone())
        .collect::<Vec<_>>();
    let omitted_baselines = by_path
        .keys()
        .filter(|path| !matched_baselines.contains(*path))
        .cloned()
        .collect::<Vec<_>>();
    if !unmatched_results.is_empty() || !omitted_baselines.is_empty() {
        return Err(BenchError::msg(format!(
            "results do not exactly cover the baseline corpus: unmatched_results={unmatched_results:?} omitted_baselines={omitted_baselines:?}"
        )));
    }

    Ok(VerifyReport {
        corpus: args.corpus.clone(),
        reference_solver: args.reference_solver.clone(),
        total: entries.len(),
        matches: counts[0],
        sound_bugs: counts[1],
        incomplete: counts[2],
        reference_unknown: counts[3],
        both_unknown: counts[4],
        no_baseline: counts[5],
        non_comparable: counts[6],
        ay_resource_envelope,
        entries,
    })
}

fn baseline_execution_envelope(row: &BaselineRow) -> Option<String> {
    if row.resource_jobs <= 0
        || row.resource_memlimit_mb <= 0
        || row.resource_nbcore <= 0
        || row.resource_headroom_mb < 0
    {
        return None;
    }
    let plan = crate::resource::ResourcePlan {
        requested_jobs: usize::try_from(row.resource_requested_jobs).ok()?,
        jobs: usize::try_from(row.resource_jobs).ok()?,
        memlimit_mb_per_child: usize::try_from(row.resource_memlimit_mb).ok()?,
        nbcore_per_child: usize::try_from(row.resource_nbcore).ok()?,
        headroom_mb: usize::try_from(row.resource_headroom_mb).ok()?,
        planner: "persisted-baseline".to_string(),
    };
    crate::resource::effective_execution_envelope(&plan, &row.resource_enforcement, row.timeout_s)
        .ok()
}

fn is_stable_sha256(value: &str) -> bool {
    let Some(digest) = value.trim().strip_prefix("sha256:") else {
        return false;
    };
    digest.len() == 64 && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
}

/// Extracted subset of a AY `results.json` row that we need for verification.
#[derive(Debug)]
struct VerifyResultItem {
    file: String,
    result: String,
    time_sec: f64,
    benchmark_content_hash: Option<String>,
}

fn extract_result_items(doc: &serde_json::Value) -> Result<Vec<VerifyResultItem>> {
    // `ay-bench` / `ay bench run` writes `items: [...]` with entries
    // `{file, result, time_sec, ...}`. `ay-bench score` consumes the same
    // shape. Accept either a bare array or an object with "items".
    let arr = if let Some(items) = doc.get("items").and_then(|v| v.as_array()) {
        items
    } else if let Some(items) = doc.as_array() {
        items
    } else {
        return Err(BenchError::MissingJsonField {
            field: "top-level `items` array".to_string(),
        });
    };

    let mut out = Vec::with_capacity(arr.len());
    for v in arr {
        let file = v
            .get("file")
            .and_then(|x| x.as_str())
            .ok_or_else(|| BenchError::MissingJsonField {
                field: "result item.`file`".to_string(),
            })?
            .to_string();
        let result = v
            .get("result")
            .and_then(|x| x.as_str())
            .ok_or_else(|| BenchError::MissingJsonField {
                field: "result item.`result`".to_string(),
            })?
            .to_string();
        let time_sec = v
            .get("time_sec")
            .and_then(|x| x.as_f64())
            .filter(|value| value.is_finite() && *value >= 0.0)
            .ok_or_else(|| BenchError::MissingJsonField {
                field: "result item finite non-negative `time_sec`".to_string(),
            })?;
        let benchmark_content_hash = v
            .get("benchmark_content_hash")
            .and_then(|value| value.as_str())
            .map(str::to_string);
        if !benchmark_content_hash
            .as_deref()
            .is_some_and(is_stable_sha256)
        {
            return Err(BenchError::msg(format!(
                "result item {file:?} lacks a stable sha256 benchmark content hash"
            )));
        }
        out.push(VerifyResultItem {
            file,
            result,
            time_sec,
            benchmark_content_hash,
        });
    }
    Ok(out)
}

/// Render a verify report as a human-readable table.
#[must_use]
pub fn render_verify_table(report: &VerifyReport) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "== Verify ({} vs {}): {} benchmarks ==\n",
        report.corpus, report.reference_solver, report.total
    ));
    s.push_str(&format!(
        "  match            : {}\n  sound_bug        : {}\n  incomplete       : {}\n  reference_unknown: {}\n  both_unknown     : {}\n  no_baseline      : {}\n  non_comparable   : {}\n",
        report.matches,
        report.sound_bugs,
        report.incomplete,
        report.reference_unknown,
        report.both_unknown,
        report.no_baseline,
        report.non_comparable,
    ));
    for entry in report
        .entries
        .iter()
        .filter(|entry| entry.classification == "non_comparable")
    {
        s.push_str(&format!(
            "  NON-COMPARABLE {} : {} (resources ay={} baseline={}; content ay={} baseline={})\n",
            entry.benchmark_path,
            entry
                .non_comparable_reason
                .as_deref()
                .unwrap_or("unknown reason"),
            entry.ay_resource_envelope.as_deref().unwrap_or("<missing>"),
            entry
                .baseline_resource_envelope
                .as_deref()
                .unwrap_or("<missing>"),
            entry.ay_content_hash.as_deref().unwrap_or("<missing>"),
            entry
                .baseline_content_hash
                .as_deref()
                .unwrap_or("<missing>"),
        ));
    }
    let bugs: Vec<&VerifyEntry> = report
        .entries
        .iter()
        .filter(|e| e.classification == "sound_bug")
        .collect();
    if !bugs.is_empty() {
        s.push_str("\nSOUND BUGS (ay disagrees with reference):\n");
        for e in bugs {
            s.push_str(&format!(
                "  {} : ay={} reference={} expected={}\n",
                e.benchmark_path,
                e.ay_answer,
                e.reference_answer.as_deref().unwrap_or("?"),
                e.expected.as_deref().unwrap_or("?"),
            ));
        }
    }
    s
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn private_tempdir() -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o700))
                .expect("secure tempdir");
        }
        dir
    }

    fn sample(
        corpus: &str,
        bench: &str,
        solver: &str,
        answer: &str,
        expected: &str,
        ms: i64,
    ) -> BaselineRow {
        BaselineRow {
            corpus: corpus.to_string(),
            benchmark_path: bench.to_string(),
            content_hash: "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                .to_string(),
            solver_input_hash:
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                    .to_string(),
            solver: solver.to_string(),
            solver_version: "v1".to_string(),
            solver_path: format!("/usr/bin/{solver}"),
            solver_sha256:
                "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
                    .to_string(),
            solver_size_bytes: 1234,
            answer: answer.to_string(),
            expected: expected.to_string(),
            expected_source: "path".to_string(),
            wall_ms: ms,
            exit_code: Some(0),
            timeout_s: 30.0,
            stdout_head: String::new(),
            stderr_head: String::new(),
            harvested_at: "unix:1".to_string(),
            resource_requested_jobs: 1,
            resource_jobs: 1,
            resource_memlimit_mb: 1024,
            resource_nbcore: 1,
            resource_headroom_mb: 16000,
            resource_enforcement: ENFORCEMENT_RSS_WATCHDOG_V1.to_string(),
            solver_argv_json: format!(r#"["/usr/bin/{solver}","case"]"#),
            solver_env_json: r#"{"LC_ALL":"C"}"#.to_string(),
            stdout_sha256:
                "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
                    .to_string(),
            stderr_sha256:
                "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
                    .to_string(),
            stdout_truncated: false,
            stderr_truncated: false,
        }
    }

    #[test]
    fn pipe_capture_is_bounded_and_marks_trailing_verdict_incomplete() {
        let mut input = vec![b'x'; CAPTURE_LIMIT_BYTES + 4096];
        input.extend_from_slice(b"\nsat\n");
        let capture = PipeCapture::start(std::io::Cursor::new(input));
        let output = capture.finish();
        assert!(output.text.len() <= CAPTURE_LIMIT_BYTES + 64);
        assert!(output.incomplete());
        assert!(
            output.text.ends_with("\nsat\n"),
            "{}",
            &output.text[output.text.len() - 32..]
        );
    }

    #[test]
    fn benchmark_hash_uses_stable_sha256_storage_format() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("input.smt2");
        std::fs::write(&path, b"abc").expect("write input");
        assert_eq!(
            hash_file(&path).expect("hash input"),
            "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn discovery_retains_deterministic_smallest_paths_with_bounded_memory() {
        let dir = tempfile::tempdir().expect("tempdir");
        for name in ["z.smt2", "b.smt2", "a.smt2", "m.smt2"] {
            std::fs::write(dir.path().join(name), "(check-sat)\n").expect("benchmark");
        }
        let mut retained = std::collections::BinaryHeap::new();
        collect_files_with_limits(
            dir.path(),
            &["smt2".to_string()],
            &mut retained,
            2,
            100,
            100,
            100,
        )
        .expect("bounded discovery");
        let mut names: Vec<String> = retained
            .into_vec()
            .into_iter()
            .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        names.sort();
        assert_eq!(names, ["a.smt2", "b.smt2"]);
    }

    #[test]
    fn discovery_rejects_total_benchmark_count_overflow_even_with_small_limit() {
        let dir = tempfile::tempdir().expect("tempdir");
        for name in ["a.smt2", "b.smt2", "c.smt2"] {
            std::fs::write(dir.path().join(name), "(check-sat)\n").expect("benchmark");
        }
        let mut retained = std::collections::BinaryHeap::new();
        let error = collect_files_with_limits(
            dir.path(),
            &["smt2".to_string()],
            &mut retained,
            1,
            100,
            100,
            2,
        )
        .expect_err("discovery must enforce the total benchmark cap");
        assert!(error.to_string().contains("2-benchmark cap"));
        assert_eq!(retained.len(), 1);
    }

    #[test]
    fn test_baseline_roundtrip() {
        let mut store = BaselineStore::open_in_memory().expect("open");
        let rows = vec![
            sample("c1", "a.smt2", "z3", "sat", "sat", 100),
            sample("c1", "b.smt2", "z3", "unsat", "unsat", 200),
        ];
        store.upsert_rows(&rows).expect("upsert");
        let got = store.rows_for_corpus("c1").expect("fetch");
        assert_eq!(got.len(), 2);
        assert!(got.iter().any(|r| r.benchmark_path == "a.smt2"));
    }

    #[test]
    fn test_baseline_upsert_replaces() {
        let mut store = BaselineStore::open_in_memory().expect("open");
        store
            .upsert_rows(&[sample("c1", "a.smt2", "z3", "unknown", "unknown", 5000)])
            .expect("first");
        store
            .upsert_rows(&[sample("c1", "a.smt2", "z3", "sat", "sat", 120)])
            .expect("second");
        let got = store.rows_for_corpus("c1").expect("fetch");
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].answer, "sat");
        assert_eq!(got[0].wall_ms, 120);
    }

    #[test]
    fn test_existing_baseline_store_migrates_resource_columns() {
        let dir = private_tempdir();
        let path = dir.path().join("legacy.sqlite");
        let conn = Connection::open(&path).expect("open legacy db");
        conn.execute_batch(
            "CREATE TABLE baselines (
                corpus TEXT NOT NULL, benchmark_path TEXT NOT NULL,
                content_hash TEXT NOT NULL, solver TEXT NOT NULL,
                solver_version TEXT NOT NULL, answer TEXT NOT NULL,
                expected TEXT NOT NULL, wall_ms INTEGER NOT NULL,
                exit_code INTEGER, timeout_s REAL NOT NULL,
                stdout_head TEXT NOT NULL, stderr_head TEXT NOT NULL,
                harvested_at TEXT NOT NULL,
                PRIMARY KEY(corpus, benchmark_path, solver)
            );",
        )
        .expect("create legacy schema");
        drop(conn);

        let mut store = BaselineStore::open(&path).expect("migrate store");
        let row = sample("c1", "a.smt2", "z3", "sat", "sat", 10);
        store
            .upsert_rows(std::slice::from_ref(&row))
            .expect("upsert");
        let got = store.rows_for_corpus("c1").expect("read");
        assert_eq!(got, vec![row]);
    }

    #[cfg(unix)]
    #[test]
    fn baseline_store_rejects_visible_path_replacement_after_open() {
        let dir = private_tempdir();
        let path = dir.path().join("baselines.sqlite");
        let displaced = dir.path().join("authenticated-baselines.sqlite");
        let store = BaselineStore::open(&path).expect("open authenticated store");
        std::fs::rename(&path, &displaced).expect("displace authenticated inode");
        let replacement = b"replacement must be preserved";
        std::fs::write(&path, replacement).expect("plant replacement");

        let error = store
            .known_corpora()
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

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn test_run_solver_drains_large_output_without_pipe_deadlock() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().expect("tempdir");
        let solver = dir.path().join("noisy-solver");
        std::fs::write(
            &solver,
            "#!/usr/bin/env python3\nimport sys\nsys.stderr.write('x' * (2 * 1024 * 1024))\nprint('sat')\n",
        )
        .expect("write solver");
        let mut permissions = std::fs::metadata(&solver).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&solver, permissions).expect("chmod solver");
        let benchmark = dir.path().join("case.smt2");
        std::fs::write(&benchmark, "(check-sat)\n").expect("write benchmark");
        let root = crate::runner::repo_root_public();
        let resources = crate::resource::PlannedResources::for_test(&root, 4096);

        let outcome = run_solver(&solver, &benchmark, 5.0, &resources);
        assert_eq!(outcome.answer, "error");
        assert!(outcome.stderr_head.contains("truncated"));
        assert!(outcome.stderr_head.len() <= 520);
        assert!(outcome.wall_ms < 5_000);
    }

    #[test]
    fn test_classify_pair_match() {
        assert_eq!(classify_pair("sat", Some("sat")), VerifyClass::Match);
        assert_eq!(classify_pair("unsat", Some("unsat")), VerifyClass::Match);
    }

    #[test]
    fn test_classify_pair_sound_bug() {
        assert_eq!(classify_pair("sat", Some("unsat")), VerifyClass::SoundBug);
        assert_eq!(classify_pair("unsat", Some("sat")), VerifyClass::SoundBug);
    }

    #[test]
    fn test_classify_pair_incomplete() {
        assert_eq!(
            classify_pair("unknown", Some("sat")),
            VerifyClass::Incomplete
        );
        assert_eq!(
            classify_pair("timeout", Some("unsat")),
            VerifyClass::Incomplete
        );
    }

    #[test]
    fn test_classify_pair_reference_unknown() {
        assert_eq!(
            classify_pair("sat", Some("unknown")),
            VerifyClass::ReferenceUnknown
        );
        assert_eq!(
            classify_pair("unsat", Some("timeout")),
            VerifyClass::ReferenceUnknown
        );
    }

    #[test]
    fn test_classify_pair_both_unknown() {
        assert_eq!(
            classify_pair("unknown", Some("timeout")),
            VerifyClass::BothUnknown
        );
    }

    #[test]
    fn test_classify_pair_no_baseline() {
        assert_eq!(classify_pair("sat", None), VerifyClass::NoBaseline);
    }

    #[test]
    fn test_read_expected_from_header() {
        let dir = tempfile::tempdir().expect("tmpdir");
        let p = dir.path().join("f.smt2");
        std::fs::write(
            &p,
            "(set-info :smt-lib-version 2.6)\n(set-info :status unsat)\n(check-sat)\n",
        )
        .expect("write");
        assert_eq!(read_expected(&p).unwrap().as_deref(), Some("unsat"));
    }

    #[test]
    fn test_read_expected_fallback_sat_dir() {
        let dir = tempfile::tempdir().expect("tmpdir");
        let sat_dir = dir.path().join("sat");
        std::fs::create_dir_all(&sat_dir).expect("mkdir");
        let p = sat_dir.join("no-header.smt2");
        std::fs::write(&p, "(check-sat)\n").expect("write");
        assert_eq!(read_expected(&p).unwrap().as_deref(), Some("sat"));
    }

    #[test]
    fn strict_expected_id_ignores_absolute_parent_labels_and_rejects_conflicts() {
        let dir = tempfile::tempdir().expect("tmpdir");
        let sat_dir = dir.path().join("sat");
        std::fs::create_dir_all(&sat_dir).expect("mkdir");
        let neutral = sat_dir.join("neutral.smt2");
        std::fs::write(&neutral, "(check-sat)\n").expect("write");
        let label = read_expected_for_id(&neutral, "neutral/case.smt2").expect("label");
        assert_eq!(label.value, None);
        assert_eq!(label.source, "unknown");

        let conflict = sat_dir.join("conflict.smt2");
        std::fs::write(&conflict, "(set-info :status unsat)\n(check-sat)\n").expect("write");
        let error = read_expected_for_id(&conflict, "sat/conflict.smt2")
            .expect_err("header/path conflict must fail");
        assert!(error.to_string().contains("expected-status conflict"));
        assert!(expected_from_relative_id("sat/unsat/case.smt2").is_err());
    }

    #[test]
    fn smt_metadata_scanner_handles_boundaries_comments_and_doubled_quotes() {
        let dir = tempfile::tempdir().expect("tmpdir");
        let path = dir.path().join("metadata.smt2");
        let padding = " ".repeat(64 * 1024 - 7);
        std::fs::write(
            &path,
            format!(
                "; fake (set-info :status sat)\n{padding}(set-logic QF_LIA)\n(set-info :source \"quoted \"\" status unsat\")\n(set-info :status unsat)\n"
            ),
        )
        .expect("write");
        let metadata = read_smt_metadata(&path).expect("metadata");
        assert_eq!(metadata.logic.as_deref(), Some("QF_LIA"));
        assert_eq!(metadata.status.as_deref(), Some("unsat"));

        std::fs::write(&path, "(set-info :status sat)\n(set-info :status unsat)\n")
            .expect("rewrite");
        assert!(read_smt_metadata(&path).is_err());
    }

    #[test]
    fn test_matches_extension() {
        let exts = vec!["smt2".to_string(), "cnf".to_string()];
        assert!(matches_extension(Path::new("a/b.smt2"), &exts));
        assert!(matches_extension(Path::new("a/b.SMT2"), &exts));
        assert!(matches_extension(Path::new("a/b.SMT2.GZ"), &exts));
        assert!(!matches_extension(Path::new("a/b.txt"), &exts));
    }

    #[test]
    fn test_parse_reference_verdict() {
        assert_eq!(parse_reference_verdict("sat\n", "", Some(0)), "sat");
        assert_eq!(parse_reference_verdict("unsat\n", "", Some(0)), "unsat");
        assert_eq!(parse_reference_verdict("unknown\n", "", Some(0)), "unknown");
        // CaDiCaL-style exit code encoding
        assert_eq!(parse_reference_verdict("", "", Some(10)), "sat");
        assert_eq!(parse_reference_verdict("", "", Some(20)), "unsat");
        assert_eq!(parse_reference_verdict("sat\n", "", Some(1)), "error");
        assert_eq!(
            parse_reference_verdict("sat\nunsat\n", "", Some(0)),
            "error"
        );
        assert_eq!(
            parse_reference_verdict("sat\n", "fatal: crash\n", Some(0)),
            "error"
        );
    }

    #[test]
    fn test_solver_kind_detect_z3() {
        assert_eq!(SolverKind::detect("z3"), SolverKind::Z3);
        assert_eq!(SolverKind::detect("Z3"), SolverKind::Z3);
    }

    #[test]
    fn test_solver_kind_detect_golem() {
        assert_eq!(SolverKind::detect("golem"), SolverKind::Golem);
        assert_eq!(SolverKind::detect("Golem"), SolverKind::Golem);
    }

    #[test]
    fn test_solver_kind_detect_cadical() {
        assert_eq!(SolverKind::detect("cadical"), SolverKind::CaDiCaL);
        assert_eq!(SolverKind::detect("CaDiCaL"), SolverKind::CaDiCaL);
        assert_eq!(SolverKind::detect("CADICAL"), SolverKind::CaDiCaL);
    }

    #[test]
    fn test_solver_kind_detect_kissat() {
        assert_eq!(SolverKind::detect("kissat"), SolverKind::Kissat);
        assert_eq!(SolverKind::detect("Kissat"), SolverKind::Kissat);
    }

    #[test]
    fn test_solver_kind_detect_bitwuzla() {
        assert_eq!(SolverKind::detect("bitwuzla"), SolverKind::Bitwuzla);
        assert_eq!(SolverKind::detect("Bitwuzla"), SolverKind::Bitwuzla);
    }

    #[test]
    fn test_solver_kind_detect_cvc5() {
        assert_eq!(SolverKind::detect("cvc5"), SolverKind::Cvc5);
        assert_eq!(SolverKind::detect("CVC5"), SolverKind::Cvc5);
    }

    #[test]
    fn test_solver_kind_detect_other() {
        // Names that don't match any known solver fall back to `Other`, which
        // means "no special args" — the harvester will rely on the external
        // wall-clock timeout loop. Examples: proprietary solvers we cannot
        // ship special-casing for, minor forks, renamed binaries.
        assert_eq!(SolverKind::detect("mathsat"), SolverKind::Other);
        assert_eq!(SolverKind::detect("yices-smt2"), SolverKind::Other);
        assert_eq!(SolverKind::detect("minisat"), SolverKind::Other);
        assert_eq!(SolverKind::detect(""), SolverKind::Other);
    }

    #[test]
    fn test_parse_reference_verdict_golem_stdout() {
        // Golem emits `sat` / `unsat` / `unknown` on stdout (CHC semantics:
        // sat = safe / unsat = unsafe). The shared parser handles them directly.
        assert_eq!(parse_reference_verdict("sat\n", "", Some(0)), "sat");
        assert_eq!(parse_reference_verdict("unsat\n", "", Some(0)), "unsat");
        // Golem unknown on memory/timeout; with stdout empty and a non-zero
        // exit code we classify as error.
        assert_eq!(parse_reference_verdict("", "", Some(1)), "error");
    }

    #[test]
    fn test_verify_report_has_sound_bugs() {
        let r = VerifyReport {
            corpus: "x".into(),
            reference_solver: "z3".into(),
            total: 1,
            matches: 0,
            sound_bugs: 1,
            incomplete: 0,
            reference_unknown: 0,
            both_unknown: 0,
            no_baseline: 0,
            non_comparable: 0,
            ay_resource_envelope: None,
            entries: vec![],
        };
        assert!(r.has_sound_bugs());
    }

    #[test]
    fn test_truncate() {
        assert_eq!(truncate("hello", 100), "hello");
        assert_eq!(truncate("abcdefghij", 3), "abc");
        assert_eq!(truncate("éé", 3), "é");
        assert!(truncate("éé", 3).len() <= 3);
    }

    /// Basename fallback is ambiguous across corpus directories. Persistent
    /// verification must require the exact normalized corpus-relative ID.
    #[test]
    fn test_verify_rejects_basename_only_results_for_path_qualified_baseline() {
        let dir = private_tempdir();
        let store_path = dir.path().join("baselines.sqlite");
        {
            let mut store = BaselineStore::open(&store_path).expect("open store");
            store
                .upsert_rows(&[
                    // Path-qualified benchmark_path, as harvest stores it.
                    sample(
                        "corp",
                        "benchmarks/chc/2025/extra-small-lia/foo.smt2",
                        "golem",
                        "sat",
                        "sat",
                        100,
                    ),
                    sample(
                        "corp",
                        "benchmarks/chc/2025/extra-small-lia/bar.smt2",
                        "golem",
                        "unsat",
                        "unsat",
                        200,
                    ),
                ])
                .expect("upsert");
        }

        // Results.json with bare-basename `file` fields, as `ay bench run` emits.
        let results_path = dir.path().join("results.json");
        std::fs::write(
            &results_path,
            r#"{"settings":{"timeout_sec":30.0,"resource_enforcement":"ay-resource-v1:rss-watchdog-zero-grace","resource_plan":{"requested_jobs":1,"jobs":1,"memlimit_mb_per_child":1024,"nbcore_per_child":1,"headroom_mb":16000,"planner":"test"}},"items":[
                {"file":"foo.smt2","result":"sat","time_sec":0.1,"benchmark_content_hash":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"},
                {"file":"bar.smt2","result":"unsat","time_sec":0.2,"benchmark_content_hash":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}
            ]}"#,
        )
        .expect("write results");

        let error = cmd_verify(VerifyArgs {
            corpus: "corp".into(),
            results_file: results_path,
            reference_solver: "golem".into(),
            baseline_store: Some(store_path),
            json: true,
        })
        .expect_err("basename-only evidence must not alias path-qualified baselines");
        assert!(error.to_string().contains("do not exactly cover"));
    }

    #[test]
    fn test_verify_rejects_legacy_results_without_stable_hash() {
        let dir = private_tempdir();
        let store_path = dir.path().join("baselines.sqlite");
        let mut store = BaselineStore::open(&store_path).expect("open store");
        store
            .upsert_rows(&[sample("corp", "foo.smt2", "z3", "sat", "sat", 10)])
            .expect("upsert");
        drop(store);
        let results_path = dir.path().join("results.json");
        std::fs::write(
            &results_path,
            r#"{"items":[{"file":"foo.smt2","result":"unsat","time_sec":0.01}]}"#,
        )
        .expect("write results");
        let error = cmd_verify(VerifyArgs {
            corpus: "corp".into(),
            results_file: results_path,
            reference_solver: "z3".into(),
            baseline_store: Some(store_path),
            json: true,
        })
        .expect_err("legacy evidence must fail closed");
        assert!(error.to_string().contains("stable sha256"));
    }
}
