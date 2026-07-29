// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test utilities for ay-sat integration tests.
//!
//! This module is included via `mod common;` in integration test files.
//! Items must be `pub` for use by the importing test, but the compiler
//! warns because integration tests are leaf crates with no downstream users.

#![allow(unreachable_pub, dead_code, unused_imports)]

use ay_sat::{Literal, Solver, Variable};
pub use ay_test_support::{
    assert_workspace_source_identity, ay_version_has_source_identity, build_ay_cli,
    build_ay_drat_checker, build_ay_lrat_checker, build_workspace_binary, cargo_binary_path,
    isolated_cargo_target_dir, isolated_cargo_target_dir_for_outer, source_bound_target_name,
    source_identity_from_parts, workspace_source_identity, BuiltWorkspaceBinary, SourceBinding,
    WorkspaceBinarySpec, AY_CHECKER_TARGET_NAME, AY_CLI_TARGET_NAME,
};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Sender};
use std::sync::{Arc, OnceLock};
use std::thread::JoinHandle;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Cancellation-aware wall-clock deadline for an interruptible SAT solve.
///
/// A timeout thread that only sleeps and is then joined charges the full
/// deadline even when the solve finishes immediately. This helper lets normal
/// completion cancel the deadline thread while still setting the solver's
/// interrupt flag when the deadline expires. Dropping it also cancels and
/// joins the thread, so early returns and panics cannot leak a sleeping thread.
pub struct SolverInterruptTimer {
    interrupted: Arc<AtomicBool>,
    cancel: Option<Sender<()>>,
    handle: Option<JoinHandle<()>>,
}

impl SolverInterruptTimer {
    pub fn start(solver: &mut Solver, timeout: Duration) -> Self {
        let interrupted = Arc::new(AtomicBool::new(false));
        solver.set_interrupt(interrupted.clone());

        let (cancel, cancelled) = channel();
        let deadline_interrupt = interrupted.clone();
        let handle = std::thread::spawn(move || {
            if matches!(
                cancelled.recv_timeout(timeout),
                Err(std::sync::mpsc::RecvTimeoutError::Timeout)
            ) {
                deadline_interrupt.store(true, Ordering::Relaxed);
            }
        });

        Self {
            interrupted,
            cancel: Some(cancel),
            handle: Some(handle),
        }
    }

    pub fn is_interrupted(&self) -> bool {
        self.interrupted.load(Ordering::Relaxed)
    }

    pub fn cancel_and_join(mut self) {
        self.finish();
    }

    fn finish(&mut self) {
        if let Some(cancel) = self.cancel.take() {
            let _ = cancel.send(());
        }
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

impl Drop for SolverInterruptTimer {
    fn drop(&mut self) {
        self.finish();
    }
}

/// Result of running an external SAT solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleResult {
    Sat,
    Unsat,
    Unknown,
    Unavailable,
}

/// Workspace root (two levels above `CARGO_MANIFEST_DIR` for ay-sat).
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

/// Plan the exact-source checker target while avoiding an outer Cargo lock.
pub fn workspace_checker_target_dir_for_outer(
    workspace: &Path,
    source_identity: &str,
    outer_exe: Option<&Path>,
) -> PathBuf {
    let target_name = source_bound_target_name(AY_CHECKER_TARGET_NAME, source_identity);
    isolated_cargo_target_dir_for_outer(workspace, &target_name, outer_exe)
}

/// Return an immutable exact-source, provenance-checked `ay-lrat-check` binary.
pub fn require_ay_lrat_check() -> &'static BuiltWorkspaceBinary {
    static AY_LRAT_CHECK: OnceLock<BuiltWorkspaceBinary> = OnceLock::new();
    AY_LRAT_CHECK.get_or_init(|| build_ay_lrat_checker(&workspace_root()))
}

/// Return an immutable exact-source, provenance-checked `ay-drat-check` binary.
pub fn require_ay_drat_check() -> &'static BuiltWorkspaceBinary {
    static AY_DRAT_CHECK: OnceLock<BuiltWorkspaceBinary> = OnceLock::new();
    AY_DRAT_CHECK.get_or_init(|| build_ay_drat_checker(&workspace_root()))
}

fn missing_optional_benchmark_message(path: &Path) -> String {
    format!(
        "Optional external benchmark corpus file missing: {} \
         (place a CreuSAT benchmark checkout under reference/creusat to run it)",
        path.display()
    )
}

/// Load a benchmark file from an explicitly optional external corpus.
///
/// Runs skip benchmark-dependent tests loudly when the fixture is
/// unavailable. The `reference/creusat` corpus is an optional external
/// checkout that is not shipped with (or initializable from) this
/// repository, so its absence must not hard-fail CI.
/// Supports `.xz` compressed files via the `xz` command.
pub fn load_optional_benchmark(path: impl AsRef<Path>) -> Option<String> {
    let path = path.as_ref();
    if !path.exists() {
        let message = missing_optional_benchmark_message(path);
        eprintln!("SKIP (loud): benchmark-dependent test: {message}");
        return None;
    }
    Some(read_benchmark_file(path))
}

/// Read a benchmark file, decompressing `.xz` files via the `xz` command.
fn read_benchmark_file(path: &Path) -> String {
    if path.extension().is_some_and(|ext| ext == "xz") {
        let output = Command::new("xz")
            .arg("-d")
            .arg("-k")
            .arg("-c")
            .arg(path)
            .output()
            .unwrap_or_else(|e| panic!("Failed to run xz on {}: {e}", path.display()));
        assert!(
            output.status.success(),
            "xz failed for {}: status={:?}, stderr={}",
            path.display(),
            output.status.code(),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout)
            .unwrap_or_else(|e| panic!("decompressed CNF is not UTF-8 for {}: {e}", path.display()))
    } else {
        std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("Failed to read benchmark {}: {e}", path.display()))
    }
}

/// Load a benchmark file from a path relative to the workspace root.
/// Supports `.xz` compressed files via the `xz` command.
///
/// If the exact path does not exist but a `.xz`-compressed variant does,
/// the compressed file is transparently decompressed (#8116). This handles
/// repositories where benchmarks are stored compressed to save space.
pub fn load_repo_benchmark(relative_path: &str) -> String {
    let path = workspace_root().join(relative_path);
    if path.exists() {
        return read_benchmark_file(&path);
    }
    // Try .xz fallback: benchmarks may be stored compressed.
    let xz_path = workspace_root().join(format!("{relative_path}.xz"));
    if xz_path.exists() {
        return read_benchmark_file(&xz_path);
    }
    panic!("benchmark not found: {} (also tried .xz)", path.display());
}

/// Load an explicitly optional repo-relative corpus file, returning `None` if
/// it (and its `.xz` variant) is absent. Tracked required fixtures must use
/// [`load_repo_benchmark`] and fail rather than calling this helper.
pub fn load_optional_repo_benchmark(relative_path: &str) -> Option<String> {
    let path = workspace_root().join(relative_path);
    if path.exists() {
        return Some(read_benchmark_file(&path));
    }
    let xz_path = workspace_root().join(format!("{relative_path}.xz"));
    if xz_path.exists() {
        return Some(read_benchmark_file(&xz_path));
    }
    let message = missing_optional_benchmark_message(&path);
    assert!(std::env::var_os("CI").is_none(), "{message}");
    eprintln!("Skipping benchmark-dependent test: {message}");
    None
}

/// Load the barrel6 benchmark fixture used by external DRAT/LRAT tests.
///
/// The fixture is vendored under `tests/data/` to keep proof validation tests
/// deterministic across zones and CI checkouts.
pub fn load_barrel6_cnf() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("data")
        .join("cmu-bmc-barrel6.cnf");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("Failed to read barrel6 fixture {}: {e}", path.display()))
}

/// Run CaDiCaL on a DIMACS CNF file and return the result.
///
/// Returns `OracleResult::Unavailable` if the CaDiCaL binary is not found.
/// Returns `OracleResult::Unknown` on timeout or other solver failures.
pub fn cadical_oracle(cnf_path: &str) -> OracleResult {
    let cadical_path = workspace_root().join("reference/cadical/build/cadical");

    if !cadical_path.exists() {
        return OracleResult::Unavailable;
    }

    let output = Command::new(&cadical_path)
        .arg("-q")
        .arg(cnf_path)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .output();

    match output {
        Ok(result) => match result.status.code() {
            Some(10) => OracleResult::Sat,
            Some(20) => OracleResult::Unsat,
            _ => OracleResult::Unknown,
        },
        Err(_) => OracleResult::Unavailable,
    }
}

/// Disable all inprocessing features on a solver.
///
/// This is the canonical list of all inprocessing features. When adding a new
/// inprocessing feature to the solver, add its disable call here too.
pub fn disable_all_inprocessing(solver: &mut Solver) {
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_backbone_enabled(false);
    solver.set_cce_enabled(false);
}

/// Assert that a model satisfies all clauses, with per-clause failure detail.
pub fn assert_model_satisfies(original_clauses: &[Vec<Literal>], model: &[bool], label: &str) {
    for (ci, clause) in original_clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|lit| {
            let var_idx = lit.variable().index();
            if var_idx >= model.len() {
                return false;
            }
            if lit.is_positive() {
                model[var_idx]
            } else {
                !model[var_idx]
            }
        });
        assert!(
            satisfied,
            "[{label}]: SAT model violates clause {ci}: {clause:?}"
        );
    }
}

/// Check that a model satisfies all clauses (returns bool instead of panicking).
pub fn verify_model(clauses: &[Vec<Literal>], model: &[bool]) -> bool {
    for clause in clauses {
        let satisfied = clause.iter().any(|lit| {
            let var_idx = lit.variable().index();
            let var_value = model.get(var_idx).copied().unwrap_or(false);
            if lit.is_positive() {
                var_value
            } else {
                !var_value
            }
        });
        if !satisfied {
            return false;
        }
    }
    true
}

/// Path to the barrel6 benchmark (UNSAT, ~60s in release mode).
pub const BARREL6_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/cmu-bmc-barrel6.cnf"
);

/// Read barrel6 CNF, returning None with a diagnostic message when the file
/// is absent (e.g. `reference/creusat` submodule not initialized).
pub fn read_barrel6() -> Option<String> {
    match std::fs::read_to_string(BARREL6_PATH) {
        Ok(cnf) => Some(cnf),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "SKIP: barrel6 benchmark not found at {BARREL6_PATH}\n\
                 Fix: git submodule update --init reference/creusat"
            );
            None
        }
        Err(e) => panic!("failed to read barrel6: {e}"),
    }
}

pub const MANOL_PIPE_C9_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/manol-pipe-c9.cnf"
);

pub fn read_manol_pipe_c9() -> Option<String> {
    match std::fs::read_to_string(MANOL_PIPE_C9_PATH) {
        Ok(cnf) => Some(cnf),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "SKIP: manol-pipe-c9 benchmark not found at {MANOL_PIPE_C9_PATH}\n\
                 Fix: git submodule update --init reference/creusat"
            );
            None
        }
        Err(e) => panic!("failed to read manol-pipe-c9: {e}"),
    }
}

/// PHP(3,2): 3 pigeons, 2 holes — used for lightweight cross-validation.
pub const PHP32_DIMACS: &str = "\
p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0
";

/// Smaller UNSAT formula (PHP 4,3) for debug-mode proof tests.
pub const PHP43_DIMACS: &str = "\
p cnf 12 22
1 2 3 0
4 5 6 0
7 8 9 0
10 11 12 0
-1 -4 0
-1 -7 0
-1 -10 0
-4 -7 0
-4 -10 0
-7 -10 0
-2 -5 0
-2 -8 0
-2 -11 0
-5 -8 0
-5 -11 0
-8 -11 0
-3 -6 0
-3 -9 0
-3 -12 0
-6 -9 0
-6 -12 0
-9 -12 0
";

static DRAT_TRIM_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();

/// Find a drat-trim binary that can actually verify proofs.
pub fn find_drat_trim() -> Option<PathBuf> {
    DRAT_TRIM_PATH.get_or_init(find_drat_trim_uncached).clone()
}

fn find_drat_trim_uncached() -> Option<PathBuf> {
    if let Ok(output) = Command::new("which").arg("drat-trim").output() {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_owned();
            if !path.is_empty() {
                let path = PathBuf::from(path);
                if drat_trim_candidate_verified(&path) {
                    return Some(path);
                }
            }
        }
    }
    for candidate in [
        "/tmp/drat-trim/drat-trim",
        "/usr/local/bin/drat-trim",
        "/opt/homebrew/bin/drat-trim",
    ] {
        let path = PathBuf::from(candidate);
        if drat_trim_candidate_verified(&path) {
            return Some(path);
        }
    }
    // Also check workspace bin/
    let workspace_bin = workspace_root().join("bin/drat-trim");
    if drat_trim_candidate_verified(&workspace_bin) {
        return Some(workspace_bin);
    }
    None
}

fn drat_trim_candidate_verified(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }

    let cnf_path = write_temp_file("drat_trim_probe_cnf", b"p cnf 1 2\n1 0\n-1 0\n", "cnf");
    let proof_path = write_temp_file("drat_trim_probe_proof", b"0\n", "drat");

    let output = Command::new(path).arg(&cnf_path).arg(&proof_path).output();

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    match output {
        Ok(output) => {
            output.status.success()
                && String::from_utf8_lossy(&output.stdout).contains("s VERIFIED")
        }
        Err(_) => false,
    }
}

/// Find the lrat-check binary from the drat-trim suite.
pub fn find_lrat_check() -> Option<PathBuf> {
    let candidates = [
        "/tmp/drat-trim/lrat-check",
        "/usr/local/bin/lrat-check",
        "/opt/homebrew/bin/lrat-check",
    ];
    for path in candidates {
        if Path::new(path).is_file() {
            return Some(PathBuf::from(path));
        }
    }
    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let candidate = dir.join("lrat-check");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn sanitize_label(label: &str) -> String {
    label
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn write_temp_file(label: &str, content: &[u8], extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before unix epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "ay_test_{}_{nanos}_{}.{extension}",
        sanitize_label(label),
        std::process::id(),
    ));
    std::fs::write(&path, content)
        .unwrap_or_else(|e| panic!("write {} failed: {e}", path.display()));
    path
}

/// Verify a DRAT proof using drat-trim. Skips gracefully outside CI if
/// drat-trim is not found.
pub fn verify_drat_proof(cnf_dimacs: &str, proof_bytes: &[u8], test_name: &str) {
    let proof_text = String::from_utf8_lossy(proof_bytes);
    assert!(
        proof_text.ends_with("0\n"),
        "{test_name}: proof must end with empty clause"
    );

    let Some(drat_trim) = find_drat_trim() else {
        assert!(
            std::env::var_os("CI").is_none(),
            "drat-trim is required in CI"
        );
        eprintln!("drat-trim not found, skipping external verification for {test_name}");
        return;
    };

    let cnf_path = write_temp_file(
        &format!("drat_cnf_{test_name}"),
        cnf_dimacs.as_bytes(),
        "cnf",
    );
    let proof_path = write_temp_file(&format!("drat_proof_{test_name}"), proof_bytes, "drat");

    let output = Command::new(drat_trim)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("execute drat-trim");

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // drat-trim: exit 0 + "s VERIFIED" = verified.
    // MUST use both exit code AND exact prefix "s VERIFIED" to avoid false
    // positives: "s NOT VERIFIED" contains "VERIFIED" as a substring (#4273).
    let verified = output.status.success() && stdout.contains("s VERIFIED");
    assert!(
        verified,
        "{test_name}: drat-trim verification FAILED\nstatus: {:?}\nstdout: {}\nstderr: {}",
        output.status.code(),
        stdout.trim(),
        stderr.trim(),
    );
}

/// Generate random test clauses for inprocessing and correctness tests.
pub fn generate_test_clauses(num_vars: u32, num_clauses: usize, seed: u64) -> Vec<Vec<Literal>> {
    let mut clauses = Vec::new();

    // Simple LCG for deterministic pseudo-randomness
    let mut state = seed;
    let lcg_next = |s: &mut u64| {
        *s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
        *s
    };

    for _ in 0..num_clauses {
        let clause_len = (lcg_next(&mut state) % 3 + 2) as usize; // 2-4 literals
        let mut clause = Vec::with_capacity(clause_len);
        for _ in 0..clause_len {
            let var = (lcg_next(&mut state) % u64::from(num_vars)) as u32;
            let positive = lcg_next(&mut state) % 2 == 0;
            let lit = if positive {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            clause.push(lit);
        }
        clauses.push(clause);
    }

    clauses
}

/// Convert solver clauses to DIMACS CNF format for drat-trim.
pub fn clauses_to_dimacs(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut dimacs = format!("p cnf {} {}\n", num_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
            let var = lit.variable().index() as i64 + 1;
            let signed = if lit.is_positive() { var } else { -var };
            dimacs.push_str(&format!("{signed} "));
        }
        dimacs.push_str("0\n");
    }
    dimacs
}

/// Stress formula: use barrel6 in release, PHP(4,3) in debug.
///
/// Shared across DRAT/LRAT proof tests to keep a single definition.
pub fn stress_formula_dimacs() -> String {
    if cfg!(debug_assertions) {
        PHP43_DIMACS.to_owned()
    } else {
        read_barrel6().unwrap_or_else(|| PHP43_DIMACS.to_owned())
    }
}

/// Check that a benchmark file exists; skip gracefully if missing.
pub fn require_benchmark(path: &str) -> bool {
    if Path::new(path).exists() {
        return true;
    }
    eprintln!(
        "Skipping test: benchmark file missing: {path}\n\
         Expected fixture root: reference/creusat/tests/mfleury/SAT-2009-preprocessed"
    );
    false
}
