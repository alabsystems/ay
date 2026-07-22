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
use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use crate::error::{BenchError, Result, WithContext};

// ===================================================================
// Baseline store
// ===================================================================

/// One persisted `(corpus, benchmark, solver)` reference result.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BaselineRow {
    pub corpus: String,
    pub benchmark_path: String,
    pub content_hash: String,
    pub solver: String,
    pub solver_version: String,
    pub answer: String,
    pub expected: String,
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
}

impl BaselineStore {
    /// Open (or create) the store, initializing the schema on first use.
    pub fn open(path: &Path) -> Result<Self> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).with_bench_context(|| {
                format!("creating baseline store directory {}", parent.display())
            })?;
        }
        let conn = Connection::open_with_flags(
            path,
            OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE,
        )
        .with_bench_context(|| format!("opening baseline store {}", path.display()))?;
        Self::init_schema(&conn)?;
        Ok(Self { conn })
    }

    /// Open a purely in-memory baseline store (used in tests).
    pub fn open_in_memory() -> Result<Self> {
        let conn =
            Connection::open_in_memory().bench_context("opening in-memory baseline store")?;
        Self::init_schema(&conn)?;
        Ok(Self { conn })
    }

    fn init_schema(conn: &Connection) -> Result<()> {
        conn.execute_batch(
            "CREATE TABLE IF NOT EXISTS baselines (
                corpus          TEXT    NOT NULL,
                benchmark_path  TEXT    NOT NULL,
                content_hash    TEXT    NOT NULL,
                solver          TEXT    NOT NULL,
                solver_version  TEXT    NOT NULL,
                answer          TEXT    NOT NULL,
                expected        TEXT    NOT NULL,
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
        ensure_column(conn, "resource_jobs", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_memlimit_mb", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_nbcore", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_headroom_mb", "INTEGER NOT NULL DEFAULT 0")?;
        ensure_column(conn, "resource_enforcement", "TEXT NOT NULL DEFAULT ''")?;
        Ok(())
    }

    /// Insert or replace a batch of rows atomically.
    pub fn upsert_rows(&mut self, rows: &[BaselineRow]) -> Result<()> {
        let tx = self.conn.transaction().bench_context("begin tx")?;
        {
            let mut stmt = tx
                .prepare(
                    "INSERT OR REPLACE INTO baselines
                        (corpus, benchmark_path, content_hash, solver, solver_version,
                         answer, expected, wall_ms, exit_code, timeout_s,
                         stdout_head, stderr_head, harvested_at,
                         resource_requested_jobs, resource_jobs,
                         resource_memlimit_mb, resource_nbcore,
                         resource_headroom_mb, resource_enforcement)
                     VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13,
                             ?14, ?15, ?16, ?17, ?18, ?19)",
                )
                .bench_context("prepare upsert")?;
            for row in rows {
                stmt.execute(params![
                    row.corpus,
                    row.benchmark_path,
                    row.content_hash,
                    row.solver,
                    row.solver_version,
                    row.answer,
                    row.expected,
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
                ])
                .bench_context("execute upsert")?;
            }
        }
        tx.commit().bench_context("commit tx")?;
        Ok(())
    }

    /// Fetch all rows for a given corpus.
    pub fn rows_for_corpus(&self, corpus: &str) -> Result<Vec<BaselineRow>> {
        let mut stmt = self.conn.prepare(
            "SELECT corpus, benchmark_path, content_hash, solver, solver_version,
                    answer, expected, wall_ms, exit_code, timeout_s,
                    stdout_head, stderr_head, harvested_at,
                    resource_requested_jobs, resource_jobs,
                    resource_memlimit_mb, resource_nbcore,
                    resource_headroom_mb, resource_enforcement
             FROM baselines
             WHERE corpus = ?1",
        )?;
        let mapped = stmt.query_map(params![corpus], row_from_sql)?;
        let mut rows = Vec::new();
        for r in mapped {
            rows.push(r?);
        }
        Ok(rows)
    }

    /// Distinct corpus names in the store.
    pub fn known_corpora(&self) -> Result<Vec<String>> {
        let mut stmt = self
            .conn
            .prepare("SELECT DISTINCT corpus FROM baselines ORDER BY corpus")?;
        let rows = stmt.query_map([], |r| r.get::<_, String>(0))?;
        let mut out = Vec::new();
        for r in rows {
            out.push(r?);
        }
        Ok(out)
    }
}

fn row_from_sql(r: &rusqlite::Row<'_>) -> rusqlite::Result<BaselineRow> {
    Ok(BaselineRow {
        corpus: r.get(0)?,
        benchmark_path: r.get(1)?,
        content_hash: r.get(2)?,
        solver: r.get(3)?,
        solver_version: r.get(4)?,
        answer: r.get(5)?,
        expected: r.get(6)?,
        wall_ms: r.get(7)?,
        exit_code: r.get(8)?,
        timeout_s: r.get(9)?,
        stdout_head: r.get(10)?,
        stderr_head: r.get(11)?,
        harvested_at: r.get(12)?,
        resource_requested_jobs: r.get(13)?,
        resource_jobs: r.get(14)?,
        resource_memlimit_mb: r.get(15)?,
        resource_nbcore: r.get(16)?,
        resource_headroom_mb: r.get(17)?,
        resource_enforcement: r.get(18)?,
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
    if !args.timeout_s.is_finite() || args.timeout_s <= 0.0 {
        return Err(BenchError::InvalidArgs {
            reason: "--timeout must be finite and positive".to_string(),
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
    let store_path = args
        .store_path
        .clone()
        .unwrap_or_else(|| BaselineStorePath::default_at(&root).as_path().to_path_buf());

    let solver_path = resolve_solver(&args.solver).ok_or_else(|| BenchError::SolverNotFound {
        name: args.solver.clone(),
    })?;
    let solver_name = solver_display_name(&args.solver, &solver_path);
    let solver_version = probe_solver_version(&solver_path);

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

    let mut files = discover_files(&args.benchmarks_dir, &args.extensions)?;
    files.sort();
    if args.limit > 0 && files.len() > args.limit {
        files.truncate(args.limit);
    }
    if files.is_empty() {
        return Err(BenchError::msg(format!(
            "no files matching extensions {:?} under {}",
            args.extensions,
            args.benchmarks_dir.display()
        )));
    }
    eprintln!("harvest: {} files to process", files.len());

    let pool = build_thread_pool(resources.plan.jobs)?;
    let now = current_iso8601();

    let mut store = BaselineStore::open(&store_path)?;
    let harvest_context = HarvestContext {
        corpus: &args.corpus,
        solver_path: &solver_path,
        solver_name: &solver_name,
        solver_version: &solver_version,
        timeout_s: args.timeout_s,
        harvested_at: &now,
        resources: &resources,
    };

    // Use rayon in-pool to parallelize solver runs. We collect all rows (each is
    // small), then persist in one transaction at the end for speed and atomicity.
    let rows: Vec<BaselineRow> = pool.install(|| {
        use rayon::prelude::*;
        let total = files.len();
        let counter = std::sync::atomic::AtomicUsize::new(0);
        files
            .par_iter()
            .map(|file| {
                let r = harvest_one(file, &harvest_context);
                let done = counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                if done.is_multiple_of(10) || done == total {
                    eprintln!(
                        "harvest: [{done}/{total}] {} -> {} ({}ms)",
                        display_relative(file, &args.benchmarks_dir),
                        r.answer,
                        r.wall_ms
                    );
                }
                r
            })
            .collect()
    });

    if rows.iter().any(|row| row.content_hash.is_empty()) {
        return Err(BenchError::msg(
            "failed to hash one or more benchmark inputs; refusing an unverifiable baseline",
        ));
    }

    store.upsert_rows(&rows)?;
    let solved = rows
        .iter()
        .filter(|r| r.answer == "sat" || r.answer == "unsat")
        .count();
    let timeouts = rows.iter().filter(|r| r.answer == "timeout").count();
    let memouts = rows.iter().filter(|r| r.answer == "memout").count();
    let errors = rows.iter().filter(|r| r.answer == "error").count();
    eprintln!(
        "harvest: wrote {} rows  (solved={} timeout={} memout={} error={})",
        rows.len(),
        solved,
        timeouts,
        memouts,
        errors
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
    solver_name: &'a str,
    solver_version: &'a str,
    timeout_s: f64,
    harvested_at: &'a str,
    resources: &'a crate::resource::PlannedResources,
}

fn harvest_one(file: &Path, context: &HarvestContext<'_>) -> BaselineRow {
    let expected = read_expected(file).unwrap_or_else(|| "unknown".to_string());
    let content_hash = hash_file(file).unwrap_or_default();

    let outcome = run_solver(
        context.solver_path,
        file,
        context.timeout_s,
        context.resources,
    );

    BaselineRow {
        corpus: context.corpus.to_string(),
        benchmark_path: file.to_string_lossy().to_string(),
        content_hash,
        solver: context.solver_name.to_string(),
        solver_version: context.solver_version.to_string(),
        answer: outcome.answer,
        expected,
        wall_ms: outcome.wall_ms,
        exit_code: outcome.exit_code,
        timeout_s: context.timeout_s,
        stdout_head: outcome.stdout_head,
        stderr_head: outcome.stderr_head,
        harvested_at: context.harvested_at.to_string(),
        resource_requested_jobs: context.resources.plan.requested_jobs as i64,
        resource_jobs: context.resources.plan.jobs as i64,
        resource_memlimit_mb: context.resources.plan.memlimit_mb_per_child as i64,
        resource_nbcore: context.resources.plan.nbcore_per_child as i64,
        resource_headroom_mb: context.resources.plan.headroom_mb as i64,
        resource_enforcement:
            "_oom_guard.rss_watchdog(grace=0); MEMLIMIT/NBCORE environment applied".to_string(),
    }
}

struct SolverOutcome {
    answer: String,
    wall_ms: i64,
    exit_code: Option<i32>,
    stdout_head: String,
    stderr_head: String,
}

const CAPTURE_LIMIT_BYTES: usize = 1024 * 1024;
const CAPTURE_HEAD_BYTES: usize = CAPTURE_LIMIT_BYTES / 2;

struct PipeCapture {
    receiver: mpsc::Receiver<String>,
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
            let mut head = Vec::with_capacity(CAPTURE_HEAD_BYTES);
            let mut tail = VecDeque::with_capacity(CAPTURE_LIMIT_BYTES - CAPTURE_HEAD_BYTES);
            let tail_cap = CAPTURE_LIMIT_BYTES - CAPTURE_HEAD_BYTES;
            let mut total = 0usize;
            let mut chunk = [0u8; 8192];
            loop {
                match reader.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(read) => {
                        total = total.saturating_add(read);
                        let head_read = read.min(CAPTURE_HEAD_BYTES.saturating_sub(head.len()));
                        head.extend_from_slice(&chunk[..head_read]);
                        for byte in &chunk[head_read..read] {
                            if tail.len() == tail_cap {
                                tail.pop_front();
                            }
                            tail.push_back(*byte);
                        }
                    }
                }
            }
            if !tail.is_empty() {
                if total > CAPTURE_LIMIT_BYTES {
                    head.extend_from_slice(b"\n[... output truncated ...]\n");
                }
                head.extend(tail);
            }
            let _ = sender.send(String::from_utf8_lossy(&head).into_owned());
        });
        Self { receiver }
    }

    fn finish(self) -> String {
        self.receiver
            .recv_timeout(Duration::from_secs(2))
            .unwrap_or_default()
    }
}

#[cfg(unix)]
fn isolate_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    command.process_group(0);
}

#[cfg(not(unix))]
fn isolate_process_group(_command: &mut Command) {}

fn terminate_process_group(child: &mut Child) {
    #[cfg(unix)]
    {
        if let Ok(pid) = i32::try_from(child.id()) {
            let pgid = nix::unistd::Pid::from_raw(pid);
            let _ = nix::sys::signal::killpg(pgid, nix::sys::signal::Signal::SIGKILL);
        }
    }
    #[cfg(not(unix))]
    {
        let _ = child.kill();
    }
    let _ = child.wait();
}

fn finish_armed_watchdog(watchdog: &mut Option<crate::resource::RssWatchdog>) -> Result<bool> {
    watchdog
        .take()
        .map_or(Ok(false), crate::resource::RssWatchdog::finish)
}

fn run_solver(
    solver: &Path,
    benchmark: &Path,
    timeout_s: f64,
    resources: &crate::resource::PlannedResources,
) -> SolverOutcome {
    let timeout = Duration::from_secs_f64(timeout_s);
    let start = Instant::now();

    // Per-solver argument customization. For z3 we pass `-T:<seconds>` so the
    // solver self-terminates quickly; for Golem we default to the CHC spacer
    // engine with QF_LIA logic (Golem 0.9.0 does not auto-detect the logic
    // reliably and requires `-l <logic>` for CHC-COMP inputs). SAT solvers
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

    let timeout_sec_u64 = timeout_s.max(1.0) as u64;
    let timeout_ms_u64 = (timeout_s.max(1.0) * 1000.0) as u64;

    let mut cmd = Command::new(solver);
    // These variables are enforced by ay-pb and are harmless advisory
    // provenance for external solvers; the zero-grace RSS watchdog remains
    // the exact memory enforcement for every child.
    cmd.env("MEMLIMIT", resources.plan.memlimit_mb_per_child.to_string());
    cmd.env("NBCORE", resources.plan.nbcore_per_child.to_string());
    match kind {
        SolverKind::Z3 => {
            cmd.arg(format!("-T:{}", timeout_sec_u64));
        }
        SolverKind::Golem => {
            cmd.arg("-l").arg("QF_LIA");
            cmd.arg("-e").arg("spacer");
        }
        SolverKind::CaDiCaL => {
            cmd.arg("-q");
            cmd.arg("-t").arg(format!("{}", timeout_sec_u64));
        }
        SolverKind::Kissat => {
            cmd.arg("-q");
            cmd.arg(format!("--time={}", timeout_sec_u64));
        }
        SolverKind::Bitwuzla => {
            cmd.arg("-t").arg(format!("{}", timeout_ms_u64));
        }
        SolverKind::Cvc5 => {
            cmd.arg(format!("--tlimit={}", timeout_ms_u64));
        }
        SolverKind::Other => {}
    }
    cmd.arg(benchmark);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());
    isolate_process_group(&mut cmd);

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return SolverOutcome {
                answer: "error".to_string(),
                wall_ms: 0,
                exit_code: None,
                stdout_head: String::new(),
                stderr_head: format!("spawn failed: {e}"),
            };
        }
    };
    let stdout_capture = child.stdout.take().map(PipeCapture::start);
    let stderr_capture = child.stderr.take().map(PipeCapture::start);
    let watchdog = match resources.watch_external_child(&child, "ay bench harvest") {
        Ok(watchdog) => watchdog,
        Err(error) => {
            terminate_process_group(&mut child);
            return SolverOutcome {
                answer: "error".to_string(),
                wall_ms: start.elapsed().as_millis().min(i64::MAX as u128) as i64,
                exit_code: None,
                stdout_head: stdout_capture.map(PipeCapture::finish).unwrap_or_default(),
                stderr_head: format!("failed to arm RSS watchdog: {error}"),
            };
        }
    };
    let mut watchdog = Some(watchdog);

    let poll_interval = Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed_ms = start.elapsed().as_millis().min(i64::MAX as u128) as i64;
                // The top-level solver may leave descendants holding pipes.
                // Reap its whole isolated group before joining pipe drains.
                terminate_process_group(&mut child);
                let stdout = stdout_capture.map(PipeCapture::finish).unwrap_or_default();
                let mut stderr = stderr_capture.map(PipeCapture::finish).unwrap_or_default();
                let answer = match finish_armed_watchdog(&mut watchdog) {
                    Ok(true) => "memout",
                    Ok(false) => parse_reference_verdict(&stdout, status.code()),
                    Err(error) => {
                        if !stderr.is_empty() {
                            stderr.push('\n');
                        }
                        stderr.push_str(&format!("RSS watchdog failure: {error}"));
                        "error"
                    }
                };
                return SolverOutcome {
                    answer: answer.to_string(),
                    wall_ms: elapsed_ms,
                    exit_code: status.code(),
                    stdout_head: truncate(&stdout, 512),
                    stderr_head: truncate(&stderr, 512),
                };
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    terminate_process_group(&mut child);
                    let stdout = stdout_capture.map(PipeCapture::finish).unwrap_or_default();
                    let mut stderr = stderr_capture.map(PipeCapture::finish).unwrap_or_default();
                    let answer = match finish_armed_watchdog(&mut watchdog) {
                        Ok(true) => "memout",
                        Ok(false) => "timeout",
                        Err(error) => {
                            if !stderr.is_empty() {
                                stderr.push('\n');
                            }
                            stderr.push_str(&format!("RSS watchdog failure: {error}"));
                            "error"
                        }
                    };
                    return SolverOutcome {
                        answer: answer.to_string(),
                        wall_ms: (timeout_s * 1000.0) as i64,
                        exit_code: None,
                        stdout_head: truncate(&stdout, 512),
                        stderr_head: truncate(&stderr, 512),
                    };
                }
                std::thread::sleep(poll_interval);
            }
            Err(e) => {
                terminate_process_group(&mut child);
                let stdout = stdout_capture.map(PipeCapture::finish).unwrap_or_default();
                let mut stderr = stderr_capture.map(PipeCapture::finish).unwrap_or_default();
                let memout = match finish_armed_watchdog(&mut watchdog) {
                    Ok(memout) => memout,
                    Err(error) => {
                        if !stderr.is_empty() {
                            stderr.push('\n');
                        }
                        stderr.push_str(&format!("RSS watchdog failure: {error}"));
                        false
                    }
                };
                if !stderr.is_empty() {
                    stderr.push('\n');
                }
                stderr.push_str(&format!("wait failed: {e}"));
                return SolverOutcome {
                    answer: if memout { "memout" } else { "error" }.to_string(),
                    wall_ms: start.elapsed().as_millis().min(i64::MAX as u128) as i64,
                    exit_code: None,
                    stdout_head: truncate(&stdout, 512),
                    stderr_head: truncate(&stderr, 512),
                };
            }
        }
    }
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

fn parse_reference_verdict(stdout: &str, exit_code: Option<i32>) -> &'static str {
    for line in stdout.lines() {
        let lower = line.trim().to_ascii_lowercase();
        match lower.as_str() {
            "sat" | "s satisfiable" | "satisfiable" => return "sat",
            "unsat" | "s unsatisfiable" | "unsatisfiable" => return "unsat",
            "unknown" | "s unknown" | "timeout" => return "unknown",
            _ => {}
        }
    }
    match exit_code {
        Some(10) => "sat",
        Some(20) => "unsat",
        Some(0) => "unknown",
        _ => "error",
    }
}

// ===================================================================
// Expected-verdict extraction
// ===================================================================

/// Parse `(set-info :status sat|unsat|unknown)` from the first ~100 lines.
/// Falls back to filename conventions (`*/sat/*`, `*/unsat/*`).
pub fn read_expected(path: &Path) -> Option<String> {
    if let Ok(f) = std::fs::File::open(path) {
        use std::io::{BufRead, BufReader};
        let reader = BufReader::new(f);
        for (i, line) in reader.lines().enumerate() {
            if i > 200 {
                break;
            }
            let Ok(line) = line else { break };
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("(set-info :status") {
                let rest = rest.trim().trim_end_matches(')').trim();
                if rest.starts_with("sat") {
                    return Some("sat".to_string());
                }
                if rest.starts_with("unsat") {
                    return Some("unsat".to_string());
                }
                if rest.starts_with("unknown") {
                    return Some("unknown".to_string());
                }
            }
        }
    }

    // Filename conventions: */sat/* or */unsat/*
    for comp in path.iter() {
        let s = comp.to_string_lossy().to_ascii_lowercase();
        if s == "sat" {
            return Some("sat".to_string());
        }
        if s == "unsat" {
            return Some("unsat".to_string());
        }
    }
    None
}

// ===================================================================
// File discovery / hashing
// ===================================================================

fn discover_files(root: &Path, extensions: &[String]) -> Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    collect_files(root, extensions, &mut out)
        .with_bench_context(|| format!("walking {}", root.display()))?;
    Ok(out)
}

fn collect_files(dir: &Path, extensions: &[String], out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if dir.is_file() {
        if matches_extension(dir, extensions) {
            out.push(dir.to_path_buf());
        }
        return Ok(());
    }
    if !dir.is_dir() {
        return Ok(());
    }
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let ft = entry.file_type()?;
        if ft.is_dir() {
            collect_files(&path, extensions, out)?;
        } else if ft.is_file() && matches_extension(&path, extensions) {
            out.push(path);
        }
    }
    Ok(())
}

fn matches_extension(path: &Path, extensions: &[String]) -> bool {
    let Some(ext) = path.extension().and_then(|e| e.to_str()) else {
        return false;
    };
    extensions.iter().any(|e| e.eq_ignore_ascii_case(ext))
}

/// Content-hash a file with a small-block xxhash-style fallback.
///
/// We avoid pulling in `sha2` here to keep the dependency surface tight —
/// the hash is used purely as a cross-corpus dedup key inside our own store,
/// not for adversarial uses.
fn hash_file(path: &Path) -> Result<String> {
    use std::hash::Hasher as _;
    use std::io::Read as _;
    let mut file =
        std::fs::File::open(path).with_bench_context(|| format!("opening {}", path.display()))?;
    let mut h = foldhash_64_hasher();
    let mut h2 = foldhash_64_hasher_seeded(0x9E37_79B9_7F4A_7C15);
    // Keep the chunking identical to native artifact hashing so the internal
    // `fh128` representation is stable across benchmark/report producers.
    let mut buffer = [0u8; 8192];
    loop {
        let read = file
            .read(&mut buffer)
            .with_bench_context(|| format!("reading {}", path.display()))?;
        if read == 0 {
            break;
        }
        h.write(&buffer[..read]);
        h2.write(&buffer[..read]);
    }
    Ok(format!("fh128:{:016x}{:016x}", h.finish(), h2.finish()))
}

fn foldhash_64_hasher() -> std::collections::hash_map::DefaultHasher {
    std::collections::hash_map::DefaultHasher::new()
}

fn foldhash_64_hasher_seeded(seed: u64) -> std::collections::hash_map::DefaultHasher {
    use std::hash::Hasher as _;
    let mut h = std::collections::hash_map::DefaultHasher::new();
    h.write_u64(seed);
    h
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
    let output = Command::new("which").arg(name_or_path).output().ok()?;
    if !output.status.success() {
        return None;
    }
    let s = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if s.is_empty() {
        None
    } else {
        Some(PathBuf::from(s))
    }
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

fn probe_solver_version(solver: &Path) -> String {
    // Try common version flags; return the full trimmed output so multi-line
    // structured build stamps are preserved in reports.
    for flag in ["--version", "-version"] {
        if let Ok(out) = Command::new(solver).arg(flag).output() {
            let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !s.is_empty() {
                return s;
            }
        }
    }
    "unknown".to_string()
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_string()
    } else {
        // Be careful with UTF-8 boundaries.
        let cut = s
            .char_indices()
            .take_while(|(i, _)| *i <= max)
            .last()
            .map(|(i, c)| i + c.len_utf8())
            .unwrap_or(0);
        s[..cut].to_string()
    }
}

fn display_relative(file: &Path, base: &Path) -> String {
    file.strip_prefix(base)
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_else(|_| file.to_string_lossy().to_string())
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
        self.has_sound_bugs() || self.non_comparable > 0
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

    // Build lookup by benchmark_path filtered to our reference solver.
    //
    // The baseline stores `benchmark_path` as harvested (the `--dir`-relative or
    // absolute path that `ay bench harvest` walked, e.g.
    // `benchmarks/chc-comp/2025/extra-small-lia/foo.smt2`). A AY results.json
    // item's `file` field, however, is the *bare* basename (`foo.smt2`). To make
    // the two reconcile regardless of how the baseline was harvested (absolute,
    // relative, or already-bare path), we index each baseline row under BOTH its
    // full stored path and its basename. Basenames are required to be unique
    // within the (corpus, solver) slice; a collision would make a bare-name
    // lookup ambiguous, so we drop the basename alias in that case and fall back
    // to full-path matching only (never silently pick a wrong row).
    let mut by_path: std::collections::BTreeMap<String, &BaselineRow> =
        std::collections::BTreeMap::new();
    let mut basename_index: std::collections::BTreeMap<String, &BaselineRow> =
        std::collections::BTreeMap::new();
    let mut ambiguous_basenames: std::collections::BTreeSet<String> =
        std::collections::BTreeSet::new();
    for r in &rows {
        if r.solver != args.reference_solver {
            continue;
        }
        by_path.insert(r.benchmark_path.clone(), r);
        if let Some(base) = Path::new(&r.benchmark_path)
            .file_name()
            .and_then(|s| s.to_str())
        {
            let base = base.to_string();
            if basename_index.insert(base.clone(), r).is_some() {
                // Two baseline rows share a basename: ambiguous, don't alias.
                ambiguous_basenames.insert(base);
            }
        }
    }
    for amb in &ambiguous_basenames {
        basename_index.remove(amb);
    }
    if by_path.is_empty() {
        return Err(BenchError::msg(format!(
            "corpus '{}' has no rows for solver '{}'",
            args.corpus, args.reference_solver
        )));
    }

    // Load AY results JSON (produced by `ay bench run -o ...`).
    let text = std::fs::read_to_string(&args.results_file)
        .with_bench_context(|| format!("reading {}", args.results_file.display()))?;
    let doc: serde_json::Value = serde_json::from_str(&text)
        .with_bench_context(|| format!("parsing JSON in {}", args.results_file.display()))?;
    let ay_resource_plan = doc
        .pointer("/settings/resource_plan")
        .cloned()
        .and_then(|value| serde_json::from_value::<crate::resource::ResourcePlan>(value).ok());
    let ay_resource_envelope = ay_resource_plan
        .as_ref()
        .map(crate::resource::ResourcePlan::execution_envelope);

    let items = extract_result_items(&doc).with_bench_context(|| {
        format!(
            "could not find a results array in {}",
            args.results_file.display()
        )
    })?;

    let mut entries = Vec::with_capacity(items.len());
    let mut counts = [0usize; 7];
    for item in items {
        let ay_answer = item.result.trim().to_ascii_lowercase();
        let ay_wall_ms = (item.time_sec * 1000.0).round() as i64;
        // Match the results.json item to a baseline row. Prefer an exact
        // full-path hit; otherwise fall back to a (unique) basename match so a
        // bare-filename `file` field reconciles with a path-qualified baseline.
        let base = by_path.get(&item.file).copied().or_else(|| {
            let item_base = Path::new(&item.file)
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or(item.file.as_str());
            basename_index.get(item_base).copied()
        });
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
    Some(format!(
        "oom-guard-v1:jobs={};memlimit_mb={};nbcore={};headroom_mb={}",
        row.resource_jobs, row.resource_memlimit_mb, row.resource_nbcore, row.resource_headroom_mb
    ))
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
        let time_sec = v.get("time_sec").and_then(|x| x.as_f64()).unwrap_or(0.0);
        let benchmark_content_hash = v
            .get("benchmark_content_hash")
            .and_then(|value| value.as_str())
            .map(str::to_string);
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
            content_hash: "fh128:deadbeef".to_string(),
            solver: solver.to_string(),
            solver_version: "v1".to_string(),
            answer: answer.to_string(),
            expected: expected.to_string(),
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
            resource_enforcement: "test".to_string(),
        }
    }

    #[test]
    fn pipe_capture_is_bounded_and_preserves_trailing_verdict() {
        let mut input = vec![b'x'; CAPTURE_LIMIT_BYTES + 4096];
        input.extend_from_slice(b"\nsat\n");
        let capture = PipeCapture::start(std::io::Cursor::new(input));
        let output = capture.finish();
        assert!(output.len() <= CAPTURE_LIMIT_BYTES + 64);
        assert!(
            output.ends_with("\nsat\n"),
            "{}",
            &output[output.len() - 32..]
        );
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
        let dir = tempfile::tempdir().expect("tempdir");
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
        assert_eq!(outcome.answer, "sat");
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
        assert_eq!(read_expected(&p).as_deref(), Some("unsat"));
    }

    #[test]
    fn test_read_expected_fallback_sat_dir() {
        let dir = tempfile::tempdir().expect("tmpdir");
        let sat_dir = dir.path().join("sat");
        std::fs::create_dir_all(&sat_dir).expect("mkdir");
        let p = sat_dir.join("no-header.smt2");
        std::fs::write(&p, "(check-sat)\n").expect("write");
        assert_eq!(read_expected(&p).as_deref(), Some("sat"));
    }

    #[test]
    fn test_matches_extension() {
        let exts = vec!["smt2".to_string(), "cnf".to_string()];
        assert!(matches_extension(Path::new("a/b.smt2"), &exts));
        assert!(matches_extension(Path::new("a/b.SMT2"), &exts));
        assert!(!matches_extension(Path::new("a/b.txt"), &exts));
    }

    #[test]
    fn test_parse_reference_verdict() {
        assert_eq!(parse_reference_verdict("sat\n", Some(0)), "sat");
        assert_eq!(parse_reference_verdict("unsat\n", Some(0)), "unsat");
        assert_eq!(parse_reference_verdict("unknown\n", Some(0)), "unknown");
        // CaDiCaL-style exit code encoding
        assert_eq!(parse_reference_verdict("", Some(10)), "sat");
        assert_eq!(parse_reference_verdict("", Some(20)), "unsat");
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
        assert_eq!(parse_reference_verdict("sat\n", Some(0)), "sat");
        assert_eq!(parse_reference_verdict("unsat\n", Some(0)), "unsat");
        // Golem unknown on memory/timeout; with stdout empty and a non-zero
        // exit code we classify as error.
        assert_eq!(parse_reference_verdict("", Some(1)), "error");
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
        assert!(truncate("abcdefghij", 3).len() <= 5);
    }

    /// Regression: `ay bench run` writes the bare basename in each results.json
    /// item's `file` field, but `ay bench harvest` stores the (dir-qualified)
    /// path it walked in `benchmark_path`. `cmd_verify` must reconcile the two
    /// by basename so a path-qualified baseline still matches bare-name results
    /// (otherwise everything is misclassified as `no_baseline`).
    #[test]
    fn test_verify_matches_basename_against_path_qualified_baseline() {
        let dir = tempfile::tempdir().expect("tmpdir");
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
            r#"{"settings":{"resource_plan":{"requested_jobs":1,"jobs":1,"memlimit_mb_per_child":1024,"nbcore_per_child":1,"headroom_mb":16000,"planner":"test"}},"items":[
                {"file":"foo.smt2","result":"sat","time_sec":0.1,"benchmark_content_hash":"fh128:deadbeef"},
                {"file":"bar.smt2","result":"unsat","time_sec":0.2,"benchmark_content_hash":"fh128:deadbeef"}
            ]}"#,
        )
        .expect("write results");

        let report = cmd_verify(VerifyArgs {
            corpus: "corp".into(),
            results_file: results_path,
            reference_solver: "golem".into(),
            baseline_store: Some(store_path),
            json: true,
        })
        .expect("verify");

        assert_eq!(report.total, 2);
        assert_eq!(report.matches, 2, "both bare names should match");
        assert_eq!(report.no_baseline, 0, "no item should be unmatched");
        assert_eq!(report.non_comparable, 0);
        assert_eq!(report.sound_bugs, 0);
    }

    #[test]
    fn test_verify_marks_legacy_results_without_envelope_non_comparable() {
        let dir = tempfile::tempdir().expect("tmpdir");
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
        let report = cmd_verify(VerifyArgs {
            corpus: "corp".into(),
            results_file: results_path,
            reference_solver: "z3".into(),
            baseline_store: Some(store_path),
            json: true,
        })
        .expect("verify");
        assert_eq!(report.non_comparable, 1);
        assert_eq!(report.sound_bugs, 0);
        assert!(report.has_failures());
    }
}
