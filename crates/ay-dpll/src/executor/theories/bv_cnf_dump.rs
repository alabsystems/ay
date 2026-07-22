// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Faithful, per-check DIMACS export for bit-vector certificate consumers.
//!
//! A dump is a certificate input, not a best-effort debug trace.  Every
//! top-level `check-sat` owns a serialized export transaction, clears the
//! preceding artifact, and accepts only a file installed by that transaction's
//! canonical writer.  Nested checks run normally but cannot clear or overwrite
//! their owner's artifact.  Missing, stale, concurrent, or unwritable output is
//! an execution error, so no verdict can authorize the wrong certificate input.

use std::cell::RefCell;
use std::fs::File;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard, TryLockError};

use ay_core::{CnfClause, TermId, TermStore};
use ay_sat::Literal as SatLiteral;
use sha2::{Digest, Sha256};

use crate::executor_types::{ExecutorError, Result};

static BV_CNF_DUMP_FILE_ID: AtomicU64 = AtomicU64::new(0);
static BV_CNF_DUMP_GENERATION: AtomicU64 = AtomicU64::new(1);
static BV_CNF_DUMP_LOCK: Mutex<()> = Mutex::new(());

#[derive(Default)]
struct ThreadTransactionState {
    depth: usize,
    suppression_depth: usize,
    generation: u64,
    written_artifact: Option<(u64, ArtifactSeal)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ArtifactSeal {
    len: u64,
    sha256: [u8; 32],
}

thread_local! {
    static THREAD_TRANSACTION: RefCell<ThreadTransactionState> =
        RefCell::new(ThreadTransactionState::default());
}

/// Scoped suppression for semantic validation re-solves that are subordinate
/// to an already-completed user decision.
///
/// This is thread-local deliberately: suppressing one thread must never allow
/// an independent concurrent caller to return a verdict without its requested
/// artifact.
pub(in crate::executor) struct InternalExportSuppression;

impl Drop for InternalExportSuppression {
    fn drop(&mut self) {
        THREAD_TRANSACTION.with(|state| {
            let mut state = state.borrow_mut();
            state.suppression_depth = state
                .suppression_depth
                .checked_sub(1)
                .expect("BV CNF export suppression depth underflow");
        });
    }
}

/// Disable BV CNF export for nested semantic validation on this thread.
pub(in crate::executor) fn suppress_internal_export() -> InternalExportSuppression {
    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        state.suppression_depth = state
            .suppression_depth
            .checked_add(1)
            .expect("BV CNF export suppression depth overflow");
    });
    InternalExportSuppression
}

/// RAII ownership of one check's export transaction.
///
/// An unfinished top-level transaction removes its destination on drop.  This
/// also covers solver errors and unwinding panics after a partial solve.
pub(in crate::executor) struct CheckTransaction {
    active: bool,
    owner: bool,
    generation: u64,
    completed: bool,
    _cross_process_lock: Option<CrossProcessLock>,
    _process_lock: Option<MutexGuard<'static, ()>>,
}

impl CheckTransaction {
    fn disabled() -> Self {
        Self {
            active: false,
            owner: false,
            generation: 0,
            completed: true,
            _cross_process_lock: None,
            _process_lock: None,
        }
    }
}

struct CrossProcessLock {
    _path: PathBuf,
    _file: File,
}

impl Drop for CrossProcessLock {
    fn drop(&mut self) {
        // Release eagerly instead of relying only on descriptor close. This is
        // observably important to a same-process successor on platforms where
        // an immediately preceding failed nonblocking acquisition can delay
        // close-based lock release.
        let _ = self._file.unlock();
    }
}

fn cross_process_lock_path(path: &str) -> Result<PathBuf> {
    let target = Path::new(path);
    let file_name = target.file_name().ok_or_else(|| {
        ExecutorError::ArtifactExport(format!("BV CNF dump path '{path}' has no file name"))
    })?;
    let parent = target
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    Ok(parent.join(format!(".{}.ay-bv-cnf.lock", file_name.to_string_lossy())))
}

fn acquire_cross_process_lock(path: &str, generation: u64) -> Result<CrossProcessLock> {
    let lock_path = cross_process_lock_path(path)?;
    let mut file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        // Lock file: existing contents (a stale generation stamp) must survive
        // until the lock is held, so explicitly do NOT truncate on open.
        .truncate(false)
        .open(&lock_path)
        .map_err(|error| {
            export_error(
                path,
                "acquire cross-process export lock for",
                format!("{}: {error}", lock_path.display()),
            )
        })?;
    file.try_lock().map_err(|error| {
        export_error(
            path,
            "acquire cross-process export lock for",
            format!("{}: {error}", lock_path.display()),
        )
    })?;
    file.set_len(0)
        .and_then(|()| writeln!(file, "pid={} generation={generation}", std::process::id()))
        .and_then(|()| file.sync_all())
        .map_err(|error| export_error(path, "initialize cross-process export lock for", error))?;
    Ok(CrossProcessLock {
        _path: lock_path,
        _file: file,
    })
}

impl Drop for CheckTransaction {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        THREAD_TRANSACTION.with(|state| {
            let mut state = state.borrow_mut();
            debug_assert!(state.depth > 0, "BV CNF transaction depth underflow");
            state.depth = state.depth.saturating_sub(1);
            if self.owner {
                debug_assert_eq!(
                    state.depth, 0,
                    "top-level BV CNF owner dropped while nested"
                );
                debug_assert_eq!(state.generation, self.generation);
                if !self.completed {
                    if let (Some(path), Some((generation, expected_seal))) =
                        (configured_path(), state.written_artifact)
                    {
                        let current_is_owned = seal_file(Path::new(path))
                            .is_ok_and(|actual_seal| actual_seal == expected_seal)
                            || artifact_has_generation(path, generation).unwrap_or(false);
                        if current_is_owned {
                            let _ = std::fs::remove_file(path);
                        }
                    }
                }
                state.generation = 0;
                state.written_artifact = None;
            }
        });
        // `_process_lock` is released after the transaction state is cleared.
    }
}

fn configured_path() -> Option<&'static str> {
    ay_core::trace_config().dump_bv_cnf_path.as_deref()
}

/// The configured single-invocation BV DRAT proof path, if any.
fn configured_drat_path() -> Option<&'static str> {
    ay_core::trace_config().bv_drat_path.as_deref()
}

/// Whether a BV CNF artifact was requested for this process.
pub(in crate::executor) fn requested() -> bool {
    configured_path().is_some()
        && THREAD_TRANSACTION.with(|state| state.borrow().suppression_depth == 0)
}

/// Whether the current solve is the top-level owner that may emit the artifact.
///
/// Nested model-completion/cross-check solves intentionally see `false`: their
/// formula is not the user's decision query and must not replace its CNF.
pub(in crate::executor) fn enabled() -> bool {
    requested()
        && THREAD_TRANSACTION.with(|state| {
            let state = state.borrow();
            state.depth == 1 && state.generation != 0
        })
}

/// The DRAT proof target `(path, binary)` for the current top-level BV export,
/// or `None` when no DRAT was requested or this is not the owning check.
///
/// Coupled to the CNF-export owner gate ([`enabled`]): a DRAT is only ever
/// emitted from the same top-level, non-suppressed check that owns the CNF
/// artifact, so a nested model-completion or cross-check solve can never write
/// a proof. `bv_drat_path` is itself only populated by the CLI when
/// `--dump-bv-cnf` is set, so the CNF export's fail-closed pure-QF_BV gate is
/// the single point that keeps a DRAT from being emitted for a non-bit-blastable
/// logic.
pub(in crate::executor) fn bv_drat_target() -> Option<(&'static str, bool)> {
    if !enabled() {
        return None;
    }
    let config = ay_core::trace_config();
    config
        .bv_drat_path
        .as_deref()
        .map(|path| (path, config.bv_drat_binary))
}

/// Write the one-line empty-clause DRAT for a trivial-false conjunction.
///
/// The companion CNF is the bare empty clause (`p cnf 0 1` / `0`), which is
/// already UNSAT; the `0` proof line makes the empty-clause derivation explicit
/// so drat-trim reports `s VERIFIED`.
fn install_trivial_false_drat(drat_path: &str) -> Result<()> {
    let mut file = File::create(drat_path)
        .map_err(|error| export_error(drat_path, "create trivial-false DRAT for", error))?;
    file.write_all(b"0\n")
        .and_then(|()| file.flush())
        .map_err(|error| export_error(drat_path, "write trivial-false DRAT for", error))
}

/// Finalize the single-invocation BV DRAT proof.
///
/// On UNSAT the live proof stream (already terminated by the empty clause the
/// SAT solver emits when it declares UNSAT) is flushed and its writer's I/O
/// health is checked: a truncated proof aborts the check rather than leaving an
/// uncheckable certificate. On SAT/Unknown the scratch DRAT is removed so no
/// verdict is ever accompanied by a non-refuting "proof".
pub(in crate::executor) fn finish_bv_drat(
    proof: Option<ay_sat::ProofOutput>,
    path: &str,
    unsat: bool,
) -> Result<()> {
    if unsat {
        let mut proof = proof.ok_or_else(|| {
            export_error(
                path,
                "finalize DRAT proof for",
                "the SAT solver retained no proof writer",
            )
        })?;
        proof
            .flush()
            .map_err(|error| export_error(path, "flush DRAT proof for", error))?;
        if proof.has_io_error() {
            return Err(export_error(
                path,
                "write DRAT proof for",
                "the proof stream reported an I/O error and may be truncated",
            ));
        }
        // Dropping the writer closes the file with all buffered bytes flushed.
        drop(proof);
    } else {
        drop(proof);
        match std::fs::remove_file(path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(export_error(
                    path,
                    "remove the non-UNSAT DRAT scratch file for",
                    error,
                ))
            }
        }
    }
    Ok(())
}

fn export_error(path: &str, action: &str, error: impl std::fmt::Display) -> ExecutorError {
    ExecutorError::ArtifactExport(format!(
        "cannot {action} BV CNF dump target '{path}': {error}"
    ))
}

/// Begin one certificate-export transaction.
///
/// Top-level transactions use a process-wide `try_lock`: independent solvers
/// targeting the singleton configured path are rejected instead of racing (or
/// deadlocking a parallel parent waiting for its worker).  Reentrant checks on
/// the owner thread are tracked as nested and do not touch the artifact.
pub(in crate::executor) fn prepare_for_check() -> Result<CheckTransaction> {
    if !requested() {
        return Ok(CheckTransaction::disabled());
    }
    let Some(path) = configured_path() else {
        return Ok(CheckTransaction::disabled());
    };

    if let Some(generation) = THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        if state.depth == 0 {
            None
        } else {
            state.depth += 1;
            Some(state.generation)
        }
    }) {
        return Ok(CheckTransaction {
            active: true,
            owner: false,
            generation,
            completed: true,
            _cross_process_lock: None,
            _process_lock: None,
        });
    }

    let process_lock = match BV_CNF_DUMP_LOCK.try_lock() {
        Ok(guard) => guard,
        Err(TryLockError::WouldBlock) => {
            return Err(ExecutorError::ArtifactExport(
                "concurrent BV CNF export is unsupported for the single configured target"
                    .to_string(),
            ));
        }
        Err(TryLockError::Poisoned(error)) => {
            return Err(ExecutorError::ArtifactExport(format!(
                "BV CNF export transaction lock is poisoned: {error}"
            )));
        }
    };

    let generation = BV_CNF_DUMP_GENERATION
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |generation| {
            generation.checked_add(1)
        })
        .map_err(|_| {
            ExecutorError::ArtifactExport(
                "BV CNF export generation counter exhausted the u64 domain".to_string(),
            )
        })?;
    let cross_process_lock = acquire_cross_process_lock(path, generation)?;

    match std::fs::remove_file(path) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(export_error(path, "clear", error)),
    }

    // Clear any stale DRAT companion so a prior run's proof can never be mistaken
    // for this check's certificate. The DRAT is (re)written only on this check's
    // own UNSAT; a SAT/Unknown verdict must leave no proof file behind.
    if let Some(drat_path) = configured_drat_path() {
        match std::fs::remove_file(drat_path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(export_error(drat_path, "clear DRAT companion", error)),
        }
    }

    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        debug_assert_eq!(state.depth, 0);
        state.depth = 1;
        state.generation = generation;
        state.written_artifact = None;
    });
    Ok(CheckTransaction {
        active: true,
        owner: true,
        generation,
        completed: false,
        _cross_process_lock: Some(cross_process_lock),
        _process_lock: Some(process_lock),
    })
}

/// Install a file through a same-directory temporary.
///
/// On Unix the file is synced, renamed over the destination atomically, and
/// the parent directory is synced so the rename is durable.  Rust's Windows
/// rename API cannot replace an existing file atomically; the per-check clear
/// and fail-closed transaction still prevent a stale artifact there.
fn seal_file(path: &Path) -> io::Result<ArtifactSeal> {
    let mut file = File::open(path)?;
    let len = file.metadata()?.len();
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 16 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(ArtifactSeal {
        len,
        sha256: hasher.finalize().into(),
    })
}

fn atomic_write<F>(path: &str, write_contents: F) -> io::Result<ArtifactSeal>
where
    F: FnOnce(&mut BufWriter<File>) -> io::Result<()>,
{
    let target = Path::new(path);
    let file_name = target.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "BV CNF dump path has no file name",
        )
    })?;
    let parent = target
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));

    let mut temporary_file = None;
    for _ in 0..128 {
        let id = BV_CNF_DUMP_FILE_ID.fetch_add(1, Ordering::Relaxed);
        let candidate = parent.join(format!(
            ".{}.ay-bv-cnf-{}-{id}.tmp",
            file_name.to_string_lossy(),
            std::process::id()
        ));
        match std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&candidate)
        {
            Ok(file) => {
                temporary_file = Some((candidate, file));
                break;
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    let (temporary, file) = temporary_file.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::AlreadyExists,
            "exhausted 128 unique BV CNF temporary-file attempts",
        )
    })?;

    let result = (|| {
        let mut writer = BufWriter::new(file);
        write_contents(&mut writer)?;
        writer.flush()?;
        writer.get_ref().sync_all()?;
        drop(writer);
        let seal = seal_file(&temporary)?;

        #[cfg(windows)]
        if target.exists() {
            std::fs::remove_file(target)?;
        }

        std::fs::rename(&temporary, target)?;
        #[cfg(unix)]
        File::open(parent)?.sync_all()?;
        Ok(seal)
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result
}

fn install<F>(path: &str, write_contents: F) -> Result<ArtifactSeal>
where
    F: FnOnce(&mut BufWriter<File>) -> io::Result<()>,
{
    match atomic_write(path, write_contents) {
        Ok(seal) => Ok(seal),
        Err(error) => {
            let _ = std::fs::remove_file(path);
            Err(export_error(path, "write", error))
        }
    }
}

fn current_generation() -> Result<u64> {
    THREAD_TRANSACTION
        .with(|state| {
            let state = state.borrow();
            (state.depth == 1 && state.generation != 0).then_some(state.generation)
        })
        .ok_or_else(|| {
            ExecutorError::ArtifactExport(
                "BV CNF writer was invoked without a top-level export transaction".to_string(),
            )
        })
}

fn mark_written(generation: u64, seal: ArtifactSeal) {
    THREAD_TRANSACTION.with(|state| {
        let mut state = state.borrow_mut();
        debug_assert_eq!(state.generation, generation);
        debug_assert_eq!(state.depth, 1);
        state.written_artifact = Some((generation, seal));
    });
}

fn generation_marker(generation: u64) -> String {
    format!(
        "c ay export pid {} generation {generation}",
        std::process::id()
    )
}

fn sat_literal_to_dimacs(literal: SatLiteral) -> Result<i32> {
    let zero_based = literal.variable().id();
    let one_based = zero_based.checked_add(1).ok_or_else(|| {
        ExecutorError::ArtifactExport(format!(
            "SAT variable {zero_based} overflows DIMACS one-based numbering"
        ))
    })?;
    let variable = i32::try_from(one_based).map_err(|_| {
        ExecutorError::ArtifactExport(format!(
            "SAT variable {zero_based} exceeds the DIMACS i32 domain"
        ))
    })?;
    Ok(if literal.is_positive() {
        variable
    } else {
        -variable
    })
}

fn assumption_literals_to_dimacs(assumptions: &[SatLiteral], total_vars: u32) -> Result<Vec<i32>> {
    let literals = assumptions
        .iter()
        .copied()
        .map(sat_literal_to_dimacs)
        .collect::<Result<Vec<_>>>()?;
    if let Some(&literal) = literals
        .iter()
        .find(|literal| literal.unsigned_abs() > total_vars)
    {
        return Err(ExecutorError::ArtifactExport(format!(
            "assumption literal {literal} lies outside declared variable range 1..={total_vars}"
        )));
    }
    Ok(literals)
}

/// Export the exact conjunction solved for one pure QF_BV decision query.
///
/// `clauses` is the fully assembled eager bit-blast.  `assumptions` are
/// materialized as unit clauses because `solve_with_assumptions(assumptions)`
/// is satisfiability-equivalent to solving that augmented clause set.  Delayed
/// internalization and the persistent incremental route are disabled while
/// export is enabled, so no post-write semantic refinement can be omitted.
pub(in crate::executor) fn write_formula(
    clauses: &[CnfClause],
    total_vars: u32,
    assumptions: &[SatLiteral],
) -> Result<()> {
    if !enabled() {
        return Ok(());
    }
    let path = configured_path().expect("enabled export has configured path");
    let generation = current_generation()?;
    if total_vars > i32::MAX as u32 {
        return Err(ExecutorError::ArtifactExport(format!(
            "BV CNF has {total_vars} variables, exceeding the DIMACS i32 domain"
        )));
    }
    let assumption_literals = assumption_literals_to_dimacs(assumptions, total_vars)?;
    let clause_count = clauses
        .len()
        .checked_add(assumption_literals.len())
        .ok_or_else(|| {
            ExecutorError::ArtifactExport(
                "BV CNF clause count overflows the platform usize domain".to_string(),
            )
        })?;

    let seal = install(path, |writer| {
        writeln!(writer, "{}", generation_marker(generation))?;
        writeln!(writer, "c ay bit-blasted QF_BV CNF (--dump-bv-cnf)")?;
        writeln!(
            writer,
            "c complete eager encoding of the current check-sat query"
        )?;
        writeln!(writer, "p cnf {total_vars} {clause_count}")?;
        for clause in clauses {
            for &literal in clause.literals() {
                if literal == 0 || literal.unsigned_abs() > total_vars {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "CNF literal {literal} lies outside declared variable range 1..={total_vars}"
                        ),
                    ));
                }
                write!(writer, "{literal} ")?;
            }
            writeln!(writer, "0")?;
        }
        for literal in &assumption_literals {
            writeln!(writer, "{literal} 0")?;
        }
        Ok(())
    })?;
    mark_written(generation, seal);
    tracing::info!(
        path,
        generation,
        vars = total_vars,
        clauses = clause_count,
        assumption_units = assumptions.len(),
        "faithful bit-blasted BV DIMACS written"
    );
    Ok(())
}

/// Return the value of a conjunction made only from literal `true`/`false`
/// roots, or `None` for any non-literal formula.
pub(in crate::executor) fn trivial_conjunction(
    terms: &TermStore,
    roots: &[TermId],
) -> Option<bool> {
    if roots.iter().any(|&root| root == terms.false_term()) {
        Some(false)
    } else if roots.iter().all(|&root| root == terms.true_term()) {
        Some(true)
    } else {
        None
    }
}

fn artifact_has_generation(path: &str, generation: u64) -> Result<bool> {
    let file = match File::open(path) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(export_error(path, "inspect", error)),
    };
    let mut prefix = String::new();
    BufReader::new(file)
        .take(256)
        .read_to_string(&mut prefix)
        .map_err(|error| export_error(path, "inspect", error))?;
    Ok(prefix
        .lines()
        .next()
        .is_some_and(|line| line == generation_marker(generation)))
}

fn install_trivial(path: &str, generation: u64, value: bool) -> Result<()> {
    let seal = install(path, |writer| {
        writeln!(writer, "{}", generation_marker(generation))?;
        if value {
            writeln!(writer, "c ay canonical true CNF (--dump-bv-cnf)")?;
            writeln!(writer, "p cnf 0 0")?;
        } else {
            writeln!(writer, "c ay canonical false CNF (--dump-bv-cnf)")?;
            writeln!(writer, "p cnf 0 1")?;
            writeln!(writer, "0")?;
        }
        Ok(())
    })?;
    mark_written(generation, seal);
    Ok(())
}

/// Complete one decision query's export transaction.
///
/// Literal `true`/`false` formulas can terminate before theory dispatch and get
/// canonical CNFs.  Non-literal early simplifications never synthesize a file
/// from the solver verdict: they must have gone through the faithful writer or
/// the check fails before its verdict is returned.
pub(in crate::executor) fn finish_check(
    mut transaction: CheckTransaction,
    terms: &TermStore,
    roots: &[TermId],
) -> Result<()> {
    if !transaction.active {
        transaction.completed = true;
        return Ok(());
    }
    if !transaction.owner {
        transaction.completed = true;
        return Ok(());
    }

    let path = configured_path().expect("active export transaction has configured path");
    let generation = transaction.generation;
    let mut written = THREAD_TRANSACTION.with(|state| {
        let state = state.borrow();
        (state.depth == 1 && state.generation == generation)
            .then_some(state.written_artifact)
            .flatten()
            .and_then(|(written_generation, seal)| {
                (written_generation == generation).then_some(seal)
            })
    });
    if written.is_none() {
        if let Some(value) = trivial_conjunction(terms, roots) {
            install_trivial(path, generation, value)?;
            // A trivial-false conjunction is decided before bit-blasting, so the
            // SAT solver (and its live DRAT stream) never ran. Its canonical CNF
            // is the bare empty clause, so a one-line empty-clause DRAT is a
            // complete drat-trim-checkable refutation of it. A trivial-true
            // conjunction is SAT and gets no proof.
            if !value {
                if let Some(drat_path) = bv_drat_target().map(|(path, _)| path) {
                    install_trivial_false_drat(drat_path)?;
                }
            }
            written = THREAD_TRANSACTION.with(|state| {
                state
                    .borrow()
                    .written_artifact
                    .and_then(|(written_generation, seal)| {
                        (written_generation == generation).then_some(seal)
                    })
            });
        } else {
            return Err(ExecutorError::ArtifactExport(format!(
                "BV CNF export generation {generation} produced no artifact for the current check at '{path}'"
            )));
        }
    }

    if !artifact_has_generation(path, generation)? {
        return Err(ExecutorError::ArtifactExport(format!(
            "BV CNF artifact at '{path}' was not produced by current export generation {generation}"
        )));
    }
    let expected_seal = written.ok_or_else(|| {
        ExecutorError::ArtifactExport(format!(
            "BV CNF export generation {generation} did not record an artifact seal for '{path}'"
        ))
    })?;
    let actual_seal = seal_file(Path::new(path))
        .map_err(|error| export_error(path, "verify sealed contents of", error))?;
    if actual_seal != expected_seal {
        return Err(ExecutorError::ArtifactExport(format!(
            "BV CNF artifact at '{path}' changed after generation {generation} installed it (expected {} bytes, found {} bytes; SHA-256 content seal differs)",
            expected_seal.len,
            actual_seal.len
        )));
    }
    transaction.completed = true;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_sat::Variable as SatVariable;

    #[test]
    fn dimacs_conversion_rejects_unrepresentable_variable() {
        let literal = SatLiteral::positive(SatVariable::new(i32::MAX as u32));
        assert!(matches!(
            sat_literal_to_dimacs(literal),
            Err(ExecutorError::ArtifactExport(_))
        ));
    }

    #[test]
    fn assumption_must_fit_declared_header_range() {
        let literal = SatLiteral::positive(SatVariable::new(3));
        assert!(matches!(
            assumption_literals_to_dimacs(&[literal], 3),
            Err(ExecutorError::ArtifactExport(_))
        ));
        assert_eq!(assumption_literals_to_dimacs(&[literal], 4).unwrap(), [4]);
    }

    #[test]
    fn stale_lock_file_is_reusable_but_live_lock_is_exclusive() {
        static TEST_ID: AtomicU64 = AtomicU64::new(0);
        let id = TEST_ID.fetch_add(1, Ordering::Relaxed);
        let target = std::env::temp_dir().join(format!(
            "ay-bv-cnf-lock-test-{}-{id}.cnf",
            std::process::id()
        ));
        let path = target.to_str().expect("temporary path is UTF-8");
        let lock_path = cross_process_lock_path(path).expect("derive lock path");
        std::fs::write(&lock_path, "stale marker without an OS lock\n")
            .expect("precreate stale lock file");

        let first = acquire_cross_process_lock(path, 11).expect("first lock acquisition");
        assert!(matches!(
            acquire_cross_process_lock(path, 12),
            Err(ExecutorError::ArtifactExport(_))
        ));
        drop(first);
        let second = acquire_cross_process_lock(path, 13).expect("lock released on drop");
        drop(second);
        let _ = std::fs::remove_file(target);
        let _ = std::fs::remove_file(lock_path);
    }
}
