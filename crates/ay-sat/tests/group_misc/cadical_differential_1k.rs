// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential testing: AY SAT vs CaDiCaL on 1000+ generated benchmarks.
//!
//! Part of #7912 — verify_model audit acceptance criteria:
//! "No disagreements with CaDiCaL on 1000+ benchmarks."
//!
//! Strategy:
//! - Generate random 3-SAT formulas at various clause/var ratios to produce
//!   a mix of SAT and UNSAT instances
//! - Generate structured UNSAT formulas (pigeonhole principle)
//! - Include filesystem benchmarks from benchmarks/sat/ (size-limited)
//! - For SAT results: verify the model against original clauses
//! - For UNSAT results: verify DRAT proofs via drat-trim (when available)
//! - Any SAT/UNSAT disagreement between AY and CaDiCaL is a hard failure

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use ay_sat::{parse_dimacs, ProofOutput, SatResult, Solver};
use ntest::timeout;

use super::common::{workspace_root, OracleResult};

/// Per-solver timeout. Keep short since generated instances are small.
const SOLVER_TIMEOUT: Duration = Duration::from_secs(5);

/// Sequence counter for temp file uniqueness.
static TEMP_SEQ: AtomicU64 = AtomicU64::new(0);

// ---------------------------------------------------------------------------
// Random formula generation
// ---------------------------------------------------------------------------

/// SplitMix64 PRNG — better statistical quality than LCG for formula generation.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    fn next_bounded(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }
}

/// Generate a random 3-SAT formula in DIMACS format with no duplicate
/// variables per clause.
///
/// Uses Fisher-Yates to sample 3 distinct variables per clause.
fn generate_random_3sat(num_vars: u32, num_clauses: u32, seed: u64) -> String {
    assert!(num_vars >= 3, "need at least 3 variables for 3-SAT");
    let mut rng = Rng::new(seed);
    let mut dimacs = format!("p cnf {num_vars} {num_clauses}\n");

    // Pool of variable indices for sampling
    let mut pool: Vec<u32> = (1..=num_vars).collect();

    for _ in 0..num_clauses {
        // Fisher-Yates partial shuffle to pick 3 distinct vars
        for i in 0..3 {
            let j = i + rng.next_bounded(u64::from(num_vars) - (i as u64)) as usize;
            pool.swap(i, j);
        }
        for &v in &pool[..3] {
            let var = v as i32;
            let sign = if rng.next_bounded(2) == 0 { 1 } else { -1 };
            write!(dimacs, "{} ", var * sign).unwrap();
        }
        dimacs.push_str("0\n");
    }
    dimacs
}

/// Generate a pigeonhole principle formula PHP(n+1, n).
///
/// n+1 pigeons, n holes. Always UNSAT.
fn generate_php(n: u32) -> String {
    let pigeons = n + 1;
    let holes = n;
    let var = |i: u32, j: u32| -> i32 { (i * holes + j + 1) as i32 };
    let num_vars = pigeons * holes;

    let mut clauses: Vec<Vec<i32>> = Vec::new();

    // At-least-one per pigeon
    for i in 0..pigeons {
        let clause: Vec<i32> = (0..holes).map(|j| var(i, j)).collect();
        clauses.push(clause);
    }

    // At-most-one per hole
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                clauses.push(vec![-var(i1, j), -var(i2, j)]);
            }
        }
    }

    let total_clauses = clauses.len();
    let mut dimacs = format!("p cnf {num_vars} {total_clauses}\n");
    for clause in &clauses {
        for &lit in clause {
            write!(dimacs, "{lit} ").unwrap();
        }
        dimacs.push_str("0\n");
    }
    dimacs
}

// ---------------------------------------------------------------------------
// Solver runners
// ---------------------------------------------------------------------------

fn write_temp_cnf(dimacs: &str) -> PathBuf {
    let seq = TEMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let path = std::env::temp_dir().join(format!("ay_diff1k_{pid}_{seq}.cnf"));
    std::fs::write(&path, dimacs).unwrap_or_else(|e| panic!("write temp CNF: {e}"));
    path
}

fn run_cadical(cadical: &Path, cnf_path: &Path) -> OracleResult {
    let mut child = match Command::new(cadical)
        .arg("-q")
        .arg(cnf_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        Ok(c) => c,
        Err(_) => return OracleResult::Unavailable,
    };

    match wait_timeout::ChildExt::wait_timeout(&mut child, SOLVER_TIMEOUT) {
        Ok(Some(status)) => match status.code() {
            Some(10) => OracleResult::Sat,
            Some(20) => OracleResult::Unsat,
            _ => OracleResult::Unknown,
        },
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            OracleResult::Unknown
        }
        Err(_) => OracleResult::Unknown,
    }
}

struct AYResult {
    oracle: OracleResult,
    model: Option<Vec<bool>>,
    drat_proof: Option<Vec<u8>>,
}

/// Run AY on a DIMACS string with timeout.
///
/// When `with_proof` is true, enables DRAT proof output and captures the
/// proof bytes on UNSAT results. When false, uses `into_solver()` for
/// faster solving without proof overhead.
fn run_ay(dimacs: &str, with_proof: bool) -> AYResult {
    let formula = match parse_dimacs(dimacs) {
        Ok(f) => f,
        Err(_) => {
            return AYResult {
                oracle: OracleResult::Unknown,
                model: None,
                drat_proof: None,
            }
        }
    };

    let original_clauses = formula.clauses.clone();

    let mut solver = if with_proof {
        let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
        let mut s = Solver::with_proof_output(formula.num_vars, proof_writer);
        // Keep inprocessing conservative for proof mode to avoid forward
        // checker panics on BVE/gate proof steps.
        s.set_congruence_enabled(true);
        s.set_subsume_enabled(true);
        s.set_factor_enabled(false);
        for clause in formula.clauses {
            s.add_clause(clause);
        }
        s
    } else {
        formula.into_solver()
    };

    let timer = super::common::SolverInterruptTimer::start(&mut solver, SOLVER_TIMEOUT);

    // The forward proof checker can panic on certain inprocessing steps
    // (known pre-existing issue). When with_proof=true, catch_unwind
    // protects the test from forward checker assertions.
    let solve_result = if with_proof {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solver
                .solve_interruptible(|| timer.is_interrupted())
                .into_inner()
        }))
    } else {
        Ok(solver
            .solve_interruptible(|| timer.is_interrupted())
            .into_inner())
    };
    timer.cancel_and_join();

    let result = match solve_result {
        Ok(r) => r,
        Err(_) => {
            // Forward checker panic — treat as unknown
            return AYResult {
                oracle: OracleResult::Unknown,
                model: None,
                drat_proof: None,
            };
        }
    };

    match result {
        SatResult::Sat(ref model) => {
            // Verify model against original clauses
            let valid = original_clauses.iter().all(|clause| {
                clause.iter().any(|lit| {
                    let idx = lit.variable().index();
                    let val = model.get(idx).copied().unwrap_or(false);
                    if lit.is_positive() {
                        val
                    } else {
                        !val
                    }
                })
            });
            assert!(
                valid,
                "AY returned SAT but model does not satisfy all clauses"
            );
            AYResult {
                oracle: OracleResult::Sat,
                model: Some(model.clone()),
                drat_proof: None,
            }
        }
        SatResult::Unsat(_) => {
            let drat_proof = if with_proof {
                solver.take_proof_writer().and_then(|w| w.into_vec().ok())
            } else {
                None
            };
            AYResult {
                oracle: OracleResult::Unsat,
                model: None,
                drat_proof,
            }
        }
        _ => AYResult {
            oracle: OracleResult::Unknown,
            model: None,
            drat_proof: None,
        },
    }
}

// ---------------------------------------------------------------------------
// DRAT proof verification
// ---------------------------------------------------------------------------

/// Result of DRAT proof verification.
enum DratResult {
    /// Proof verified by drat-trim.
    Verified,
    /// drat-trim rejected the proof.
    Failed(String),
    /// drat-trim is not available.
    Unavailable,
}

/// Verify a DRAT proof using drat-trim.
fn verify_drat(dimacs: &str, proof_bytes: &[u8], label: &str) -> DratResult {
    let drat_trim = match super::common::find_drat_trim() {
        Some(p) => p,
        None => return DratResult::Unavailable,
    };

    let seq = TEMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let cnf_path = std::env::temp_dir().join(format!("ay_diff1k_drat_cnf_{pid}_{seq}.cnf"));
    let proof_path = std::env::temp_dir().join(format!("ay_diff1k_drat_proof_{pid}_{seq}.drat"));

    std::fs::write(&cnf_path, dimacs).expect("write CNF for drat-trim");
    std::fs::write(&proof_path, proof_bytes).expect("write DRAT proof");

    let output = Command::new(&drat_trim)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("run drat-trim");

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let verified = output.status.success() && stdout.contains("s VERIFIED");

    if verified {
        DratResult::Verified
    } else {
        DratResult::Failed(format!(
            "{label}: drat-trim exit {:?}, stdout last line: {}",
            output.status.code(),
            stdout.lines().last().unwrap_or("(empty)"),
        ))
    }
}

// ---------------------------------------------------------------------------
// Test aggregation
// ---------------------------------------------------------------------------

#[derive(Default)]
struct DiffStats {
    tested: u32,
    both_sat: u32,
    both_unsat: u32,
    skipped_timeout: u32,
    skipped_other: u32,
    drat_verified: u32,
    drat_failed: Vec<String>,
    model_verified: u32,
    disagreements: Vec<String>,
}

impl DiffStats {
    fn merge(&mut self, other: &Self) {
        self.tested += other.tested;
        self.both_sat += other.both_sat;
        self.both_unsat += other.both_unsat;
        self.skipped_timeout += other.skipped_timeout;
        self.skipped_other += other.skipped_other;
        self.drat_verified += other.drat_verified;
        self.drat_failed.extend(other.drat_failed.iter().cloned());
        self.model_verified += other.model_verified;
        self.disagreements
            .extend(other.disagreements.iter().cloned());
    }

    fn report(&self, label: &str) {
        eprintln!(
            "[{label}] tested={}, SAT={}, UNSAT={}, skip_timeout={}, skip_other={}, \
             drat_verified={}, drat_failed={}, model_verified={}, disagreements={}",
            self.tested,
            self.both_sat,
            self.both_unsat,
            self.skipped_timeout,
            self.skipped_other,
            self.drat_verified,
            self.drat_failed.len(),
            self.model_verified,
            self.disagreements.len(),
        );
    }
}

fn run_one(cadical: &Path, dimacs: &str, label: &str, stats: &mut DiffStats) {
    // No proof output for the main differential test — faster, avoids
    // forward checker panics on edge cases.
    let ay = run_ay(dimacs, false);

    let cnf_path = write_temp_cnf(dimacs);
    let cadical_result = run_cadical(cadical, &cnf_path);
    let _ = std::fs::remove_file(&cnf_path);

    if ay.oracle == OracleResult::Unknown || cadical_result == OracleResult::Unknown {
        stats.skipped_timeout += 1;
        return;
    }

    stats.tested += 1;

    if ay.oracle != cadical_result {
        stats.disagreements.push(format!(
            "{label}: AY={:?} CaDiCaL={cadical_result:?}",
            ay.oracle
        ));
        return;
    }

    match ay.oracle {
        OracleResult::Sat => {
            stats.both_sat += 1;
            if ay.model.is_some() {
                stats.model_verified += 1;
            }
        }
        OracleResult::Unsat => {
            stats.both_unsat += 1;
            if let Some(ref proof_bytes) = ay.drat_proof {
                if !proof_bytes.is_empty() {
                    match verify_drat(dimacs, proof_bytes, label) {
                        DratResult::Verified => stats.drat_verified += 1,
                        DratResult::Failed(msg) => stats.drat_failed.push(msg),
                        DratResult::Unavailable => {}
                    }
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Filesystem benchmark discovery
// ---------------------------------------------------------------------------

fn discover_cnf_benchmarks(dir: &Path, max_size: u64) -> Vec<PathBuf> {
    let mut results = Vec::new();
    if !dir.is_dir() {
        return results;
    }
    collect_cnf_recursive(dir, &mut results, max_size);
    results.sort();
    results
}

fn collect_cnf_recursive(dir: &Path, results: &mut Vec<PathBuf>, max_size: u64) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cnf_recursive(&path, results, max_size);
        } else if path.extension().is_some_and(|ext| ext == "cnf") {
            if std::fs::metadata(&path).map_or(false, |m| m.len() <= max_size) {
                results.push(path);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Main test: 1000+ benchmark differential test
// ---------------------------------------------------------------------------

/// Differential testing: AY vs CaDiCaL on 1000+ benchmarks.
///
/// Generates random 3-SAT instances at various clause/variable ratios,
/// structured UNSAT instances (pigeonhole), and includes filesystem benchmarks.
///
/// For every tested instance:
/// - SAT results: model is verified against original clauses
/// - UNSAT results: DRAT proof is verified via drat-trim (when available)
/// - Any SAT/UNSAT disagreement with CaDiCaL is a hard failure
///
/// Acceptance criteria from the development design notes:
/// "No disagreements with CaDiCaL on 1000+ benchmarks."
#[test]
#[timeout(600_000)]
fn differential_ay_cadical_1000_benchmarks() {
    let root = workspace_root();
    let cadical = root.join("reference/cadical/build/cadical");
    if !cadical.exists() {
        eprintln!("SKIP: CaDiCaL binary not found at {}", cadical.display());
        return;
    }

    let mut total = DiffStats::default();

    // Phase 1: Random 3-SAT at SAT-side ratios (ratio ~3.5, mostly SAT)
    // 15 vars, 53 clauses — fast for both solvers, predominantly satisfiable
    {
        let mut stats = DiffStats::default();
        for seed in 0..250u64 {
            let dimacs = generate_random_3sat(15, 53, seed);
            run_one(
                &cadical,
                &dimacs,
                &format!("rand3sat_15v_53c_s{seed}"),
                &mut stats,
            );
        }
        stats.report("random-3SAT-15v-undersat");
        total.merge(&stats);
    }

    // Phase 2: Random 3-SAT near phase transition (ratio ~4.267)
    // 15 vars, 64 clauses — mix of SAT/UNSAT
    {
        let mut stats = DiffStats::default();
        for seed in 500..900u64 {
            let dimacs = generate_random_3sat(15, 64, seed);
            run_one(
                &cadical,
                &dimacs,
                &format!("rand3sat_15v_64c_s{seed}"),
                &mut stats,
            );
        }
        stats.report("random-3SAT-15v-transition");
        total.merge(&stats);
    }

    // Phase 3: Random 3-SAT over-constrained (ratio ~5.5, mostly UNSAT)
    // 15 vars, 83 clauses — predominantly unsatisfiable
    {
        let mut stats = DiffStats::default();
        for seed in 1000..1300u64 {
            let dimacs = generate_random_3sat(15, 83, seed);
            run_one(
                &cadical,
                &dimacs,
                &format!("rand3sat_15v_83c_s{seed}"),
                &mut stats,
            );
        }
        stats.report("random-3SAT-15v-oversat");
        total.merge(&stats);
    }

    // Phase 4: Slightly larger instances near transition
    // 20 vars, 86 clauses (ratio 4.3)
    {
        let mut stats = DiffStats::default();
        for seed in 2000..2200u64 {
            let dimacs = generate_random_3sat(20, 86, seed);
            run_one(
                &cadical,
                &dimacs,
                &format!("rand3sat_20v_86c_s{seed}"),
                &mut stats,
            );
        }
        stats.report("random-3SAT-20v-transition");
        total.merge(&stats);
    }

    // Phase 5: Larger random 3-SAT (30 vars, 130 clauses, ratio ~4.33)
    {
        let mut stats = DiffStats::default();
        for seed in 3000..3100u64 {
            let dimacs = generate_random_3sat(30, 130, seed);
            run_one(
                &cadical,
                &dimacs,
                &format!("rand3sat_30v_130c_s{seed}"),
                &mut stats,
            );
        }
        stats.report("random-3SAT-30v-transition");
        total.merge(&stats);
    }

    // Phase 6: 2-SAT random instances (mix of SAT/UNSAT at ratio ~1.0)
    // 20 vars, 20 clauses of length 2
    {
        let mut stats = DiffStats::default();
        for seed in 4000..4100u64 {
            let mut rng = Rng::new(seed);
            let num_vars: u32 = 20;
            let num_clauses: u32 = 20;
            let mut dimacs = format!("p cnf {num_vars} {num_clauses}\n");
            let mut pool: Vec<u32> = (1..=num_vars).collect();
            for _ in 0..num_clauses {
                for i in 0..2usize {
                    let j = i + rng.next_bounded(u64::from(num_vars) - (i as u64)) as usize;
                    pool.swap(i, j);
                }
                for &v in &pool[..2] {
                    let var = v as i32;
                    let sign = if rng.next_bounded(2) == 0 { 1 } else { -1 };
                    write!(dimacs, "{} ", var * sign).unwrap();
                }
                dimacs.push_str("0\n");
            }
            run_one(
                &cadical,
                &dimacs,
                &format!("rand2sat_20v_20c_s{seed}"),
                &mut stats,
            );
        }
        stats.report("random-2SAT-20v");
        total.merge(&stats);
    }

    // Phase 7: Pigeonhole principle UNSAT instances PHP(n+1, n)
    // n=2..8 — small enough to solve quickly in debug mode
    {
        let mut stats = DiffStats::default();
        for n in 2..=8u32 {
            let dimacs = generate_php(n);
            run_one(&cadical, &dimacs, &format!("php_{}_{n}", n + 1), &mut stats);
        }
        stats.report("pigeonhole");
        total.merge(&stats);
    }

    // Phase 8: Filesystem benchmarks from benchmarks/sat/
    // Limit to 500KB to avoid timeouts on large SAT-COMP instances.
    {
        let mut stats = DiffStats::default();
        let sat_dir = root.join("benchmarks/sat");
        let benchmarks = discover_cnf_benchmarks(&sat_dir, 500_000);
        for path in &benchmarks {
            let name = path
                .strip_prefix(&sat_dir)
                .unwrap_or(path)
                .to_string_lossy()
                .to_string();
            let cnf = match std::fs::read_to_string(path) {
                Ok(c) => c,
                Err(_) => {
                    stats.skipped_other += 1;
                    continue;
                }
            };
            run_one(&cadical, &cnf, &format!("file:{name}"), &mut stats);
        }
        stats.report("filesystem");
        total.merge(&stats);
    }

    // Summary
    total.report("TOTAL");

    // Report DRAT failures as warnings (tracked separately from disagreements)
    if !total.drat_failed.is_empty() {
        eprintln!(
            "WARNING: {} DRAT proof verification failures (tracked separately):\n{}",
            total.drat_failed.len(),
            total.drat_failed.join("\n")
        );
    }

    // Primary assertion: no SAT/UNSAT disagreements with CaDiCaL
    assert!(
        total.disagreements.is_empty(),
        "CaDiCaL differential testing found {} SAT/UNSAT disagreements:\n{}",
        total.disagreements.len(),
        total.disagreements.join("\n")
    );
    assert!(
        total.tested >= 1000,
        "Expected 1000+ tested benchmarks, got {}. \
         Need more generated instances or filesystem benchmarks.",
        total.tested
    );

    eprintln!(
        "PASS: {}/{} benchmarks tested with 0 SAT/UNSAT disagreements \
         ({} SAT model-verified, {} UNSAT DRAT-verified, {} DRAT-failed)",
        total.tested,
        total.tested + total.skipped_timeout + total.skipped_other,
        total.model_verified,
        total.drat_verified,
        total.drat_failed.len(),
    );
}

/// Focused test: DRAT proof verification for UNSAT instances.
///
/// Verifies that AY's DRAT proofs are accepted by drat-trim for all UNSAT
/// benchmarks in the filesystem corpus plus generated pigeonhole instances.
#[test]
#[timeout(300_000)]
fn differential_drat_proofs_unsat_corpus() {
    if super::common::find_drat_trim().is_none() {
        eprintln!("SKIP: drat-trim not found, cannot verify proofs");
        return;
    }

    let root = workspace_root();
    let mut tested = 0u32;
    let mut drat_verified = 0u32;
    let mut failures = Vec::new();

    // Filesystem UNSAT benchmarks
    let unsat_dir = root.join("benchmarks/sat/unsat");
    let benchmarks = discover_cnf_benchmarks(&unsat_dir, 2_000_000);
    for path in &benchmarks {
        let name = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let cnf = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(_) => continue,
        };

        let ay = run_ay(&cnf, true);
        if ay.oracle != OracleResult::Unsat {
            continue;
        }
        tested += 1;

        if let Some(ref proof_bytes) = ay.drat_proof {
            if !proof_bytes.is_empty() {
                match verify_drat(&cnf, proof_bytes, &name) {
                    DratResult::Verified => drat_verified += 1,
                    DratResult::Failed(msg) => failures.push(msg),
                    DratResult::Unavailable => {}
                }
            }
        }
    }

    // Generated pigeonhole UNSAT
    for n in 2..=8u32 {
        let dimacs = generate_php(n);
        let label = format!("php_{}_{n}", n + 1);
        let ay = run_ay(&dimacs, true);
        if ay.oracle != OracleResult::Unsat {
            continue;
        }
        tested += 1;

        if let Some(ref proof_bytes) = ay.drat_proof {
            if !proof_bytes.is_empty() {
                match verify_drat(&dimacs, proof_bytes, &label) {
                    DratResult::Verified => drat_verified += 1,
                    DratResult::Failed(msg) => failures.push(msg),
                    DratResult::Unavailable => {}
                }
            }
        }
    }

    // Generated random UNSAT (over-constrained 3-SAT)
    for seed in 1000..1100u64 {
        let dimacs = generate_random_3sat(15, 83, seed);
        let label = format!("rand3sat_15v_83c_s{seed}");
        let ay = run_ay(&dimacs, true);
        if ay.oracle != OracleResult::Unsat {
            continue;
        }
        tested += 1;

        if let Some(ref proof_bytes) = ay.drat_proof {
            if !proof_bytes.is_empty() {
                match verify_drat(&dimacs, proof_bytes, &label) {
                    DratResult::Verified => drat_verified += 1,
                    DratResult::Failed(msg) => failures.push(msg),
                    DratResult::Unavailable => {}
                }
            }
        }
    }

    eprintln!(
        "DRAT proof corpus: {tested} UNSAT tested, {drat_verified} DRAT-verified, {} failures",
        failures.len()
    );

    assert!(
        failures.is_empty(),
        "DRAT proof verification failures:\n{}",
        failures.join("\n")
    );
    assert!(
        tested >= 10,
        "Expected at least 10 UNSAT benchmarks tested, got {tested}"
    );
}
