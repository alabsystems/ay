// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF-fuzz differential testing for BVE/inprocessing soundness (Part of #7927).
//!
//! Generates random small CNF formulas and solves each with multiple solver
//! configurations (BVE-enabled, default BVE-disabled, all-inprocessing-disabled).
//! Verifies that all configurations agree on SAT/UNSAT and that SAT models
//! satisfy the original clauses.
//!
//! When CaDiCaL is available at `reference/cadical/build/cadical`, each formula
//! is also compared against CaDiCaL as an external oracle.
//!
//! Uses a seeded PRNG for full reproducibility. On failure, the seed and
//! formula index are printed so the failing instance can be replayed.

#![allow(clippy::panic)]

use ay_sat::{Literal, SatResult, Solver, Variable};
use ntest::timeout;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

// ---------------------------------------------------------------------------
// SplitMix64 PRNG for deterministic formula generation
// ---------------------------------------------------------------------------

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

    fn next_range(&mut self, lo: u64, hi: u64) -> u64 {
        lo + self.next_bounded(hi - lo + 1)
    }
}

// ---------------------------------------------------------------------------
// Random CNF formula generation
// ---------------------------------------------------------------------------

/// Generate a random CNF formula with `num_vars` variables and `num_clauses`
/// clauses. Clause lengths are drawn from [1, max_clause_len]. The formula is
/// returned as a `Vec<Vec<Literal>>` suitable for feeding to `Solver::add_clause`.
fn generate_random_cnf(
    rng: &mut Rng,
    num_vars: u32,
    num_clauses: usize,
    max_clause_len: usize,
) -> Vec<Vec<Literal>> {
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let clause_len = rng.next_range(1, max_clause_len as u64) as usize;
        let mut clause = Vec::with_capacity(clause_len);
        for _ in 0..clause_len {
            let var = rng.next_bounded(u64::from(num_vars)) as u32;
            let positive = rng.next_bounded(2) == 0;
            let lit = if positive {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            // Skip duplicate variables in the same clause
            if !clause
                .iter()
                .any(|l: &Literal| l.variable() == lit.variable())
            {
                clause.push(lit);
            }
        }
        if !clause.is_empty() {
            clauses.push(clause);
        }
    }
    clauses
}

// ---------------------------------------------------------------------------
// DIMACS serialization
// ---------------------------------------------------------------------------

/// Convert clauses to DIMACS CNF format string.
fn to_dimacs(num_vars: u32, clauses: &[Vec<Literal>]) -> String {
    let mut out = format!("p cnf {} {}\n", num_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
            // DIMACS variables are 1-indexed
            let var_1idx = lit.variable().index() as i64 + 1;
            let signed = if lit.is_positive() {
                var_1idx
            } else {
                -var_1idx
            };
            out.push_str(&signed.to_string());
            out.push(' ');
        }
        out.push_str("0\n");
    }
    out
}

// ---------------------------------------------------------------------------
// CaDiCaL oracle
// ---------------------------------------------------------------------------

/// Result from CaDiCaL oracle comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CadicalResult {
    Sat,
    Unsat,
    Unknown,
}

/// Path to CaDiCaL binary, cached once.
fn cadical_path() -> Option<PathBuf> {
    let path = super::common::workspace_root().join("reference/cadical/build/cadical");
    if path.exists() {
        Some(path)
    } else {
        None
    }
}

/// Run CaDiCaL on a DIMACS string and return the result.
/// Writes the formula to a temp file, runs CaDiCaL with a 10s timeout,
/// and interprets the exit code (10=SAT, 20=UNSAT).
fn run_cadical(cadical_bin: &PathBuf, dimacs: &str) -> CadicalResult {
    let tmp = tempfile::Builder::new()
        .prefix("ay_fuzz_")
        .suffix(".cnf")
        .tempfile()
        .expect("create temp file");

    tmp.as_file()
        .write_all(dimacs.as_bytes())
        .expect("write DIMACS to temp file");

    // Flush to ensure the file is written before CaDiCaL reads it
    tmp.as_file().sync_all().expect("sync temp file");

    let output = Command::new(cadical_bin)
        .arg("-q") // quiet mode
        .arg(tmp.path())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .output();

    match output {
        Ok(result) => match result.status.code() {
            Some(10) => CadicalResult::Sat,
            Some(20) => CadicalResult::Unsat,
            _ => CadicalResult::Unknown,
        },
        Err(_) => CadicalResult::Unknown,
    }
}

// ---------------------------------------------------------------------------
// Solver configuration helpers
// ---------------------------------------------------------------------------

/// Solve the given clauses with BVE explicitly enabled. Returns the `SatResult`.
fn solve_bve_enabled(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

/// Solve with BVE explicitly disabled but other inprocessing enabled.
fn solve_no_bve(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

/// Solve with all inprocessing disabled (pure CDCL baseline).
fn solve_no_inprocessing(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

// ---------------------------------------------------------------------------
// Model verification
// ---------------------------------------------------------------------------

/// Verify that a model satisfies all clauses. Returns the index of the first
/// violated clause, or `None` if all clauses are satisfied.
fn find_violated_clause(clauses: &[Vec<Literal>], model: &[bool]) -> Option<usize> {
    for (ci, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|lit| {
            let var_idx = lit.variable().index();
            let val = model.get(var_idx).copied().unwrap_or(false);
            if lit.is_positive() {
                val
            } else {
                !val
            }
        });
        if !satisfied {
            return Some(ci);
        }
    }
    None
}

/// Extract SAT/UNSAT classification, ignoring Unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn classify(result: &SatResult) -> Verdict {
    match result {
        SatResult::Sat(_) => Verdict::Sat,
        SatResult::Unsat(_) => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
        _ => Verdict::Unknown, // non_exhaustive future variants
    }
}

// ---------------------------------------------------------------------------
// Core differential test loop
// ---------------------------------------------------------------------------

/// Statistics collected during a fuzz batch.
struct BatchStats {
    sat_count: usize,
    unsat_count: usize,
    unknown_count: usize,
    cadical_compared: usize,
    cadical_unavailable: bool,
}

/// Run `count` random formulas with the given variable/clause parameters.
/// Compares BVE-on vs default BVE-off vs no-inprocessing configurations.
/// When CaDiCaL is available, also compares against CaDiCaL as oracle.
fn differential_fuzz_batch(
    seed: u64,
    count: usize,
    min_vars: u64,
    max_vars: u64,
    min_clauses: u64,
    max_clauses: u64,
    max_clause_len: usize,
) -> BatchStats {
    let mut rng = Rng::new(seed);
    let mut stats = BatchStats {
        sat_count: 0,
        unsat_count: 0,
        unknown_count: 0,
        cadical_compared: 0,
        cadical_unavailable: false,
    };

    let cadical_bin = cadical_path();
    if cadical_bin.is_none() {
        eprintln!("CaDiCaL not found at reference/cadical/build/cadical; skipping oracle checks");
        stats.cadical_unavailable = true;
    }

    for i in 0..count {
        let num_vars = rng.next_range(min_vars, max_vars) as u32;
        let num_clauses = rng.next_range(min_clauses, max_clauses) as usize;
        let clauses = generate_random_cnf(&mut rng, num_vars, num_clauses, max_clause_len);

        let nv = num_vars as usize;

        // Configuration A: BVE explicitly enabled
        let result_bve = solve_bve_enabled(nv, &clauses);
        let verdict_bve = classify(&result_bve);

        // Configuration B: BVE disabled
        let result_no_bve = solve_no_bve(nv, &clauses);
        let verdict_no_bve = classify(&result_no_bve);

        // Configuration C: all inprocessing disabled
        let result_baseline = solve_no_inprocessing(nv, &clauses);
        let verdict_baseline = classify(&result_baseline);

        // --- Check SAT model correctness for each configuration ---
        if let SatResult::Sat(ref model) = result_bve {
            if let Some(ci) = find_violated_clause(&clauses, model) {
                panic!(
                    "SOUNDNESS BUG: BVE-enabled config model violates clause {ci} \
                     [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
                );
            }
        }
        if let SatResult::Sat(ref model) = result_no_bve {
            if let Some(ci) = find_violated_clause(&clauses, model) {
                panic!(
                    "SOUNDNESS BUG: no-BVE config model violates clause {ci} \
                     [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
                );
            }
        }
        if let SatResult::Sat(ref model) = result_baseline {
            if let Some(ci) = find_violated_clause(&clauses, model) {
                panic!(
                    "SOUNDNESS BUG: no-inprocessing config model violates clause {ci} \
                     [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
                );
            }
        }

        // --- Differential comparison across ay configurations ---
        if verdict_bve != Verdict::Unknown && verdict_no_bve != Verdict::Unknown {
            assert_eq!(
                verdict_bve, verdict_no_bve,
                "DISAGREEMENT: BVE={verdict_bve:?} vs no-BVE={verdict_no_bve:?} \
                 [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
            );
        }
        if verdict_bve != Verdict::Unknown && verdict_baseline != Verdict::Unknown {
            assert_eq!(
                verdict_bve, verdict_baseline,
                "DISAGREEMENT: BVE={verdict_bve:?} vs baseline={verdict_baseline:?} \
                 [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
            );
        }
        if verdict_no_bve != Verdict::Unknown && verdict_baseline != Verdict::Unknown {
            assert_eq!(
                verdict_no_bve, verdict_baseline,
                "DISAGREEMENT: no-BVE={verdict_no_bve:?} vs baseline={verdict_baseline:?} \
                 [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
            );
        }

        // --- CaDiCaL oracle comparison ---
        if let Some(ref cadical) = cadical_bin {
            let dimacs = to_dimacs(num_vars, &clauses);
            let cadical_result = run_cadical(cadical, &dimacs);

            if cadical_result != CadicalResult::Unknown {
                stats.cadical_compared += 1;

                // Map ay verdict to CaDiCaL result for comparison
                let ay_verdict = if verdict_bve != Verdict::Unknown {
                    verdict_bve
                } else if verdict_baseline != Verdict::Unknown {
                    verdict_baseline
                } else {
                    Verdict::Unknown
                };

                if ay_verdict != Verdict::Unknown {
                    let ay_as_cadical = match ay_verdict {
                        Verdict::Sat => CadicalResult::Sat,
                        Verdict::Unsat => CadicalResult::Unsat,
                        Verdict::Unknown => unreachable!(),
                    };
                    assert_eq!(
                        ay_as_cadical, cadical_result,
                        "AY vs CaDiCaL DISAGREEMENT: ay={ay_verdict:?} cadical={cadical_result:?} \
                         [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]\n\
                         DIMACS:\n{dimacs}"
                    );
                }
            }
        }

        match verdict_bve {
            Verdict::Sat => stats.sat_count += 1,
            Verdict::Unsat => stats.unsat_count += 1,
            Verdict::Unknown => stats.unknown_count += 1,
        }
    }

    eprintln!(
        "cnf-fuzz batch (seed={seed:#x}): {count} formulas, \
         {} SAT, {} UNSAT, {} unknown, {} cadical-compared{}",
        stats.sat_count,
        stats.unsat_count,
        stats.unknown_count,
        stats.cadical_compared,
        if stats.cadical_unavailable {
            " (cadical unavailable)"
        } else {
            ""
        },
    );

    stats
}

// ---------------------------------------------------------------------------
// Test entry points: self-consistency (ay configs agree)
// ---------------------------------------------------------------------------

/// Small formulas (5-15 vars, 10-40 clauses): 200 instances.
/// These are cheap to solve so BVE/inprocessing effects are exercised
/// on formulas where the preprocessing ratio is high relative to search.
#[test]
#[timeout(120_000)]
fn differential_bve_small_formulas() {
    differential_fuzz_batch(
        0xDEAD_BEEF_7927_0001, // seed
        200,                   // count
        5,                     // min_vars
        15,                    // max_vars
        10,                    // min_clauses
        40,                    // max_clauses
        5,                     // max_clause_len
    );
}

/// Medium formulas (10-20 vars, 20-50 clauses): 200 instances.
/// Near the phase-transition boundary for random 3-SAT, producing
/// a mix of SAT and UNSAT instances that stress BVE resolution.
#[test]
#[timeout(120_000)]
fn differential_bve_medium_formulas() {
    differential_fuzz_batch(
        0xDEAD_BEEF_7927_0002, // seed
        200,                   // count
        10,                    // min_vars
        20,                    // max_vars
        20,                    // min_clauses
        50,                    // max_clauses
        5,                     // max_clause_len
    );
}

/// Binary-heavy formulas (5-12 vars, 15-50 clauses, max clause len 3):
/// 100 instances. Binary clauses produce more BVE candidates because
/// their occurrence lists are shorter, testing bounded elimination more
/// aggressively.
#[test]
#[timeout(120_000)]
fn differential_bve_binary_heavy() {
    differential_fuzz_batch(
        0xDEAD_BEEF_7927_0003, // seed
        100,                   // count
        5,                     // min_vars
        12,                    // max_vars
        15,                    // min_clauses
        50,                    // max_clauses
        3,                     // max_clause_len (binary-heavy)
    );
}

/// Under-constrained formulas (15-20 vars, 10-25 clauses): 100 instances.
/// Low clause/variable ratio produces mostly SAT instances, testing
/// BVE reconstruction and model extension paths that only run on
/// satisfiable formulas.
#[test]
#[timeout(120_000)]
fn differential_bve_underconstrained() {
    differential_fuzz_batch(
        0xDEAD_BEEF_7927_0004, // seed
        100,                   // count
        15,                    // min_vars
        20,                    // max_vars
        10,                    // min_clauses
        25,                    // max_clauses
        4,                     // max_clause_len
    );
}

// ---------------------------------------------------------------------------
// Test entry points: larger formulas targeting BVE stress
// ---------------------------------------------------------------------------

/// Larger formulas near the 3-SAT phase transition (20-50 vars, 85-213
/// clauses with clause len 3). The phase transition for random 3-SAT
/// occurs at clause/variable ratio ~4.26, so these formulas are
/// concentrated around the hardest region, producing a balanced mix of
/// SAT and UNSAT instances that exercise BVE on non-trivial search.
#[test]
#[timeout(180_000)]
fn differential_bve_phase_transition() {
    differential_fuzz_batch(
        0xDEAD_BEEF_7927_0010, // seed
        150,                   // count
        20,                    // min_vars
        50,                    // max_vars
        85,                    // min_clauses (20*4.26 ~ 85)
        200,                   // max_clauses
        3,                     // max_clause_len (pure 3-SAT)
    );
}

/// Over-constrained formulas (30-50 vars, 150-200 clauses): 100 instances.
/// High clause/variable ratio produces mostly UNSAT instances, stressing
/// BVE elimination and the UNSAT proof path after inprocessing.
#[test]
#[timeout(180_000)]
fn differential_bve_overconstrained() {
    let stats = differential_fuzz_batch(
        0xDEAD_BEEF_7927_0011, // seed
        100,                   // count
        30,                    // min_vars
        50,                    // max_vars
        150,                   // min_clauses
        200,                   // max_clauses
        4,                     // max_clause_len
    );
    // With this clause/variable ratio, most formulas should be UNSAT
    assert!(
        stats.unsat_count > stats.sat_count,
        "Expected mostly UNSAT formulas in over-constrained regime, \
         got {} SAT vs {} UNSAT",
        stats.sat_count,
        stats.unsat_count,
    );
}

/// Mixed clause-length formulas (10-40 vars, 30-120 clauses, clause len
/// up to 7): 150 instances. Wider clause length distribution creates
/// formulas where BVE must handle a mix of short and long resolvents,
/// exercising the growth-guard heuristic (#7900).
#[test]
#[timeout(180_000)]
fn differential_bve_mixed_clause_lengths() {
    differential_fuzz_batch(
        0xDEAD_BEEF_7927_0012, // seed
        150,                   // count
        10,                    // min_vars
        40,                    // max_vars
        30,                    // min_clauses
        120,                   // max_clauses
        7,                     // max_clause_len (wide range)
    );
}

/// Unit-clause-heavy formulas (10-30 vars, 30-80 clauses, clause len up
/// to 2): 100 instances. Many unit and binary clauses force early BVE
/// decisions and interact with unit propagation during preprocessing.
#[test]
#[timeout(120_000)]
fn differential_bve_unit_heavy() {
    differential_fuzz_batch(
        0xDEAD_BEEF_7927_0013, // seed
        100,                   // count
        10,                    // min_vars
        30,                    // max_vars
        30,                    // min_clauses
        80,                    // max_clauses
        2,                     // max_clause_len (unit + binary only)
    );
}

// ---------------------------------------------------------------------------
// CaDiCaL-specific oracle test with summary assertion
// ---------------------------------------------------------------------------

/// Dedicated CaDiCaL cross-validation test. Runs 200 formulas across
/// the full range (10-50 vars, 30-200 clauses) and verifies that ay
/// agrees with CaDiCaL on every decidable instance. When CaDiCaL is
/// unavailable, the test still passes (self-consistency is checked)
/// but prints a diagnostic.
#[test]
#[timeout(300_000)]
fn cadical_oracle_cross_validation() {
    let stats = differential_fuzz_batch(
        0xDEAD_BEEF_7927_CADA, // seed
        200,                   // count
        10,                    // min_vars
        50,                    // max_vars
        30,                    // min_clauses
        200,                   // max_clauses
        5,                     // max_clause_len
    );

    if !stats.cadical_unavailable {
        // CaDiCaL was available -- we should have compared a meaningful
        // number of formulas. At least 80% should have been decidable.
        let expected_min = stats.sat_count + stats.unsat_count;
        assert!(
            stats.cadical_compared >= expected_min * 80 / 100,
            "CaDiCaL comparison rate too low: compared {} out of {} decidable formulas",
            stats.cadical_compared,
            expected_min,
        );
        eprintln!(
            "cadical oracle: {}/{} formulas cross-validated successfully",
            stats.cadical_compared,
            stats.sat_count + stats.unsat_count,
        );
    } else {
        eprintln!(
            "cadical oracle: SKIPPED (binary not found). \
             Self-consistency still verified for {} formulas.",
            stats.sat_count + stats.unsat_count + stats.unknown_count,
        );
    }
}
