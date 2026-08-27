// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF fuzz differential testing for inprocessing soundness (Part of #7927).
//!
//! Generates random small 3-SAT CNF formulas near the phase transition
//! (clause/variable ratio ~4.26) and checks that AY produces consistent
//! SAT/UNSAT results across different inprocessing configurations. Any
//! disagreement between "all inprocessing enabled" and "all inprocessing
//! disabled" (or individual technique toggles) indicates a soundness bug.
//!
//! When the result is SAT, the model is verified against the original clauses.

use super::common::{disable_all_inprocessing, verify_model, workspace_root};
use ay_sat::{Literal, SatResult, Solver, Variable};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// Simple 64-bit LCG PRNG for deterministic, reproducible test generation.
/// Constants from Knuth's MMIX (period 2^64).
struct Lcg {
    state: u64,
}

impl Lcg {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.state
    }

    /// Uniform random in [0, bound).
    fn next_usize(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }

    /// Uniform random in [lo, hi] (inclusive).
    fn next_range(&mut self, lo: usize, hi: usize) -> usize {
        lo + self.next_usize(hi - lo + 1)
    }
}

/// Generate a random 3-SAT formula near the phase transition.
///
/// Parameters:
/// - `num_vars`: number of variables (10-50 typical)
/// - `ratio`: clause/variable ratio (4.26 for phase transition)
/// - `rng`: seeded PRNG
///
/// Returns the number of variables and the clause list.
fn generate_random_3sat(num_vars: usize, ratio: f64, rng: &mut Lcg) -> (usize, Vec<Vec<Literal>>) {
    let num_clauses = (num_vars as f64 * ratio).round() as usize;
    let mut clauses = Vec::with_capacity(num_clauses);

    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(3);
        for _ in 0..3 {
            let var = rng.next_usize(num_vars) as u32;
            let positive = rng.next_u64().is_multiple_of(2);
            let lit = if positive {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            clause.push(lit);
        }
        clauses.push(clause);
    }

    (num_vars, clauses)
}

/// Solve a formula with a specific solver configuration.
///
/// Returns the SatResult. If SAT, the model is verified against the original
/// clauses and the test panics on model violation.
fn solve_with_config(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    configure: impl FnOnce(&mut Solver),
    label: &str,
) -> SatResult {
    let mut solver = Solver::new(num_vars);
    configure(&mut solver);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();

    // If SAT, verify the model against original clauses.
    if let SatResult::Sat(ref model) = result {
        assert!(
            verify_model(clauses, model),
            "[{label}] SAT model does not satisfy original clauses"
        );
    }

    result
}

/// Result classification for comparison (ignores model content).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl Verdict {
    fn from_result(r: &SatResult) -> Self {
        match r {
            SatResult::Sat(_) => Self::Sat,
            SatResult::Unsat(_) => Self::Unsat,
            SatResult::Unknown => Self::Unknown,
            _ => Self::Unknown,
        }
    }
}

impl std::fmt::Display for Verdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat => write!(f, "SAT"),
            Self::Unsat => write!(f, "UNSAT"),
            Self::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

/// Enable all inprocessing techniques (matches DIMACS binary configuration).
fn enable_all_inprocessing(solver: &mut Solver) {
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_vivify_enabled(true);
    solver.set_subsume_enabled(true);
    solver.set_probe_enabled(true);
    solver.set_bce_enabled(true);
    solver.set_condition_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_factor_enabled(true);
    solver.set_transred_enabled(true);
    solver.set_htr_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_backbone_enabled(true);
    solver.set_cce_enabled(true);
}

// =============================================================================
// DIMACS serialization and failing formula persistence
// =============================================================================

/// Convert internal clause representation to DIMACS CNF format.
fn to_dimacs(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut out = format!("p cnf {} {}\n", num_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
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

/// Save a failing formula to a temp file for post-mortem debugging.
/// Returns the path of the saved file.
fn save_failing_formula(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    seed: u64,
    index: usize,
) -> PathBuf {
    let dimacs = to_dimacs(num_vars, clauses);
    let path = std::env::temp_dir().join(format!("ay_fuzz_fail_{label}_{seed:#x}_{index}.cnf"));
    std::fs::write(&path, &dimacs)
        .unwrap_or_else(|e| panic!("failed to save failing formula to {}: {e}", path.display()));
    eprintln!("Failing formula saved to: {}", path.display());
    path
}

// =============================================================================
// External oracle comparison (CaDiCaL / Kissat)
// =============================================================================

/// Result from an external SAT solver oracle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OracleVerdict {
    Sat,
    Unsat,
    Unknown,
}

/// Find the CaDiCaL binary if available.
fn find_cadical() -> Option<PathBuf> {
    let path = workspace_root().join("reference/cadical/build/cadical");
    if path.exists() {
        Some(path)
    } else {
        None
    }
}

/// Find the Kissat binary if available.
fn find_kissat() -> Option<PathBuf> {
    let path = workspace_root().join("reference/kissat/build/kissat");
    if path.exists() {
        return Some(path);
    }
    let alt = workspace_root().join("reference/ae-kissat-mab/build/kissat");
    if alt.exists() {
        Some(alt)
    } else {
        None
    }
}

/// Run an external solver on a DIMACS string and return SAT/UNSAT/Unknown.
/// Exit code 10 = SAT, 20 = UNSAT (standard DIMACS convention).
fn run_oracle(binary: &PathBuf, dimacs: &str) -> OracleVerdict {
    let tmp = tempfile::Builder::new()
        .prefix("ay_diff_oracle_")
        .suffix(".cnf")
        .tempfile()
        .expect("create temp file for oracle");
    tmp.as_file()
        .write_all(dimacs.as_bytes())
        .expect("write DIMACS to temp file");
    tmp.as_file().sync_all().expect("sync temp file");

    let output = Command::new(binary)
        .arg("-q")
        .arg(tmp.path())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .output();

    match output {
        Ok(result) => match result.status.code() {
            Some(10) => OracleVerdict::Sat,
            Some(20) => OracleVerdict::Unsat,
            _ => OracleVerdict::Unknown,
        },
        Err(_) => OracleVerdict::Unknown,
    }
}

/// Run the core differential fuzz loop comparing two configurations.
///
/// `config_a` and `config_b` are applied to fresh solvers for each formula.
/// Returns the number of formulas tested and any disagreements found.
///
/// On disagreement, the failing formula is saved to a temp file in DIMACS
/// format for post-mortem debugging.
fn fuzz_differential(
    seed_base: u64,
    count: usize,
    config_a: impl Fn(&mut Solver) + Copy,
    config_b: impl Fn(&mut Solver) + Copy,
    label_a: &str,
    label_b: &str,
) -> (usize, Vec<String>) {
    let mut rng = Lcg::new(seed_base);
    let mut tested = 0;
    let mut disagreements = Vec::new();

    for i in 0..count {
        let num_vars = rng.next_range(10, 50);
        let (nv, clauses) = generate_random_3sat(num_vars, 4.26, &mut rng);

        let result_a = solve_with_config(nv, &clauses, config_a, label_a);
        let result_b = solve_with_config(nv, &clauses, config_b, label_b);

        let verdict_a = Verdict::from_result(&result_a);
        let verdict_b = Verdict::from_result(&result_b);

        // Skip comparisons where either side returned Unknown.
        if verdict_a == Verdict::Unknown || verdict_b == Verdict::Unknown {
            continue;
        }

        tested += 1;

        if verdict_a != verdict_b {
            let saved = save_failing_formula(nv, &clauses, label_a, seed_base, i);
            disagreements.push(format!(
                "formula #{i} (seed_base={seed_base:#x}, nv={nv}, nc={}): {label_a}={verdict_a}, {label_b}={verdict_b}\n  saved: {}",
                clauses.len(),
                saved.display(),
            ));
        }
    }

    (tested, disagreements)
}

// =============================================================================
// Main differential test: all inprocessing ON vs OFF
// =============================================================================

/// Fuzz 500 random 3-SAT formulas: all inprocessing enabled vs all disabled.
///
/// This is the primary soundness gate. Any disagreement means an inprocessing
/// technique is unsound (changes the satisfiability of the formula).
#[test]
fn fuzz_all_inprocessing_vs_none() {
    let (tested, disagreements) = fuzz_differential(
        0xDEAD_BEEF_CAFE_F00D,
        500,
        enable_all_inprocessing,
        disable_all_inprocessing,
        "all-inproc",
        "no-inproc",
    );

    eprintln!(
        "fuzz_all_inprocessing_vs_none: {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "Inprocessing soundness failures:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 100,
        "Expected at least 100 formulas tested, got {tested}"
    );
}

// =============================================================================
// Per-technique toggle tests: one technique ON (rest off) vs all off
// =============================================================================

/// Helper: enable exactly one technique on top of "all disabled".
macro_rules! fuzz_single_technique {
    ($test_name:ident, $setter:ident, $label:literal, $seed:expr) => {
        #[test]
        fn $test_name() {
            let (tested, disagreements) = fuzz_differential(
                $seed,
                500,
                |s| {
                    disable_all_inprocessing(s);
                    s.$setter(true);
                },
                |s| disable_all_inprocessing(s),
                $label,
                "no-inproc",
            );

            eprintln!(
                "{}: {tested} tested, {} disagreements",
                stringify!($test_name),
                disagreements.len()
            );
            assert!(
                disagreements.is_empty(),
                "{} soundness failures:\n{}",
                $label,
                disagreements.join("\n")
            );
            assert!(
                tested >= 100,
                "Expected at least 100 formulas tested, got {tested}"
            );
        }
    };
}

fuzz_single_technique!(
    fuzz_bve_only,
    set_bve_enabled,
    "bve-only",
    0x1111_1111_1111_1111
);
fuzz_single_technique!(
    fuzz_vivify_only,
    set_vivify_enabled,
    "vivify-only",
    0x2222_2222_2222_2222
);
fuzz_single_technique!(
    fuzz_subsume_only,
    set_subsume_enabled,
    "subsume-only",
    0x3333_3333_3333_3333
);
fuzz_single_technique!(
    fuzz_probe_only,
    set_probe_enabled,
    "probe-only",
    0x4444_4444_4444_4444
);
fuzz_single_technique!(
    fuzz_bce_only,
    set_bce_enabled,
    "bce-only",
    0x5555_5555_5555_5555
);
fuzz_single_technique!(
    fuzz_condition_only,
    set_condition_enabled,
    "condition-only",
    0x6666_6666_6666_6666
);
fuzz_single_technique!(
    fuzz_decompose_only,
    set_decompose_enabled,
    "decompose-only",
    0x7777_7777_7777_7777
);
fuzz_single_technique!(
    fuzz_factor_only,
    set_factor_enabled,
    "factor-only",
    0x8888_8888_8888_8888
);
fuzz_single_technique!(
    fuzz_transred_only,
    set_transred_enabled,
    "transred-only",
    0x9999_9999_9999_9999
);
fuzz_single_technique!(
    fuzz_htr_only,
    set_htr_enabled,
    "htr-only",
    0xAAAA_AAAA_AAAA_AAAA
);
fuzz_single_technique!(
    fuzz_gate_only,
    set_gate_enabled,
    "gate-only",
    0xBBBB_BBBB_BBBB_BBBB
);
fuzz_single_technique!(
    fuzz_congruence_only,
    set_congruence_enabled,
    "congruence-only",
    0xCCCC_CCCC_CCCC_CCCC
);
fuzz_single_technique!(
    fuzz_sweep_only,
    set_sweep_enabled,
    "sweep-only",
    0xDDDD_DDDD_DDDD_DDDD
);
fuzz_single_technique!(
    fuzz_backbone_only,
    set_backbone_enabled,
    "backbone-only",
    0xEEEE_EEEE_EEEE_EEEE
);
fuzz_single_technique!(
    fuzz_cce_only,
    set_cce_enabled,
    "cce-only",
    0xFFFF_FFFF_FFFF_FFFF
);

// =============================================================================
// Technique-pair interaction tests
// =============================================================================

/// BVE + probe interaction: these two techniques most commonly interact
/// (BVE eliminates variables, probe discovers implications on remaining vars).
#[test]
fn fuzz_bve_plus_probe() {
    let (tested, disagreements) = fuzz_differential(
        0xABCD_EF01_2345_6789,
        500,
        |s| {
            disable_all_inprocessing(s);
            s.set_bve_enabled(true);
            s.set_probe_enabled(true);
        },
        disable_all_inprocessing,
        "bve+probe",
        "no-inproc",
    );

    eprintln!(
        "fuzz_bve_plus_probe: {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "BVE+probe interaction soundness failures:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 100,
        "Expected at least 100 formulas tested, got {tested}"
    );
}

/// BVE + vivify interaction: vivification strengthens clauses that BVE then
/// uses for resolution, so incorrect strengthening can produce unsound BVE.
#[test]
fn fuzz_bve_plus_vivify() {
    let (tested, disagreements) = fuzz_differential(
        0xFEDC_BA98_7654_3210,
        500,
        |s| {
            disable_all_inprocessing(s);
            s.set_bve_enabled(true);
            s.set_vivify_enabled(true);
        },
        disable_all_inprocessing,
        "bve+vivify",
        "no-inproc",
    );

    eprintln!(
        "fuzz_bve_plus_vivify: {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "BVE+vivify interaction soundness failures:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 100,
        "Expected at least 100 formulas tested, got {tested}"
    );
}

/// Congruence + sweep interaction: both discover equivalences, and sweep
/// relies on congruence-class information, making interactions subtle.
#[test]
fn fuzz_congruence_plus_sweep() {
    let (tested, disagreements) = fuzz_differential(
        0x0123_4567_89AB_CDEF,
        500,
        |s| {
            disable_all_inprocessing(s);
            s.set_congruence_enabled(true);
            s.set_sweep_enabled(true);
            s.set_gate_enabled(true); // gate extraction feeds congruence/sweep
        },
        disable_all_inprocessing,
        "congruence+sweep+gate",
        "no-inproc",
    );

    eprintln!(
        "fuzz_congruence_plus_sweep: {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "Congruence+sweep+gate interaction soundness failures:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 100,
        "Expected at least 100 formulas tested, got {tested}"
    );
}

/// BCE + subsume interaction: BCE removes blocked clauses, subsumption
/// removes subsumed clauses. Together they may expose reconstruction bugs.
#[test]
fn fuzz_bce_plus_subsume() {
    let (tested, disagreements) = fuzz_differential(
        0xCAFE_BABE_DEAD_BEEF,
        500,
        |s| {
            disable_all_inprocessing(s);
            s.set_bce_enabled(true);
            s.set_subsume_enabled(true);
        },
        disable_all_inprocessing,
        "bce+subsume",
        "no-inproc",
    );

    eprintln!(
        "fuzz_bce_plus_subsume: {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "BCE+subsume interaction soundness failures:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 100,
        "Expected at least 100 formulas tested, got {tested}"
    );
}

// =============================================================================
// Variable-size stress test: larger formulas
// =============================================================================

/// Fuzz with larger formulas (50-100 variables) to exercise inprocessing
/// on problems where techniques are more likely to trigger multiple rounds.
#[test]
fn fuzz_larger_formulas_all_vs_none() {
    let mut rng = Lcg::new(0xBAD_C0DE_600D_F00D);
    let mut tested = 0;
    let mut disagreements = Vec::new();

    for i in 0..200 {
        let num_vars = rng.next_range(50, 100);
        let (nv, clauses) = generate_random_3sat(num_vars, 4.26, &mut rng);

        let result_all = solve_with_config(nv, &clauses, enable_all_inprocessing, "all");
        let result_none = solve_with_config(nv, &clauses, disable_all_inprocessing, "none");

        let v_all = Verdict::from_result(&result_all);
        let v_none = Verdict::from_result(&result_none);

        if v_all == Verdict::Unknown || v_none == Verdict::Unknown {
            continue;
        }

        tested += 1;

        if v_all != v_none {
            let saved = save_failing_formula(nv, &clauses, "larger", 0xBAD_C0DE_600D_F00D, i);
            disagreements.push(format!(
                "formula #{i} (nv={nv}, nc={}): all={v_all}, none={v_none}\n  saved: {}",
                clauses.len(),
                saved.display(),
            ));
        }
    }

    eprintln!(
        "fuzz_larger_formulas: {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "Larger formula inprocessing soundness failures:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 50,
        "Expected at least 50 formulas tested, got {tested}"
    );
}

// =============================================================================
// Consistency across multiple seeds
// =============================================================================

/// Run the same formula through all-inprocessing multiple times to check
/// determinism (same seed, same config should give same result).
#[test]
fn fuzz_determinism_check() {
    let mut rng = Lcg::new(0xDEAD_FACE_BEAD_CAFE);
    let mut tested = 0;

    for _ in 0..200 {
        let num_vars = rng.next_range(10, 40);
        let (nv, clauses) = generate_random_3sat(num_vars, 4.26, &mut rng);

        let result1 = solve_with_config(nv, &clauses, enable_all_inprocessing, "run1");
        let result2 = solve_with_config(nv, &clauses, enable_all_inprocessing, "run2");

        let v1 = Verdict::from_result(&result1);
        let v2 = Verdict::from_result(&result2);

        // Skip Unknown (non-deterministic timeouts).
        if v1 == Verdict::Unknown || v2 == Verdict::Unknown {
            continue;
        }

        tested += 1;
        assert_eq!(
            v1, v2,
            "Non-determinism detected: run1={v1}, run2={v2} on formula with {nv} vars"
        );
    }

    eprintln!("fuzz_determinism_check: {tested} formulas verified deterministic");
    assert!(
        tested >= 50,
        "Expected at least 50 formulas tested, got {tested}"
    );
}

// =============================================================================
// External oracle: CaDiCaL cross-validation on random formulas
// =============================================================================

/// Compare AY (all inprocessing) against CaDiCaL on 500 random 3-SAT formulas.
///
/// When CaDiCaL is unavailable, the test passes with a diagnostic message.
/// This is the primary cross-solver soundness gate for the fuzz harness.
#[test]
fn fuzz_cadical_oracle_500() {
    let cadical = match find_cadical() {
        Some(path) => path,
        None => {
            eprintln!("fuzz_cadical_oracle_500: SKIP (CaDiCaL not found)");
            return;
        }
    };

    let mut rng = Lcg::new(0xCAD1_CA10_0AC1_E000);
    let mut tested = 0;
    let mut disagreements = Vec::new();

    for i in 0..500 {
        let num_vars = rng.next_range(10, 50);
        let (nv, clauses) = generate_random_3sat(num_vars, 4.26, &mut rng);

        // AY with all inprocessing
        let ay_result = solve_with_config(nv, &clauses, enable_all_inprocessing, "ay-all");
        let ay_verdict = Verdict::from_result(&ay_result);
        if ay_verdict == Verdict::Unknown {
            continue;
        }

        // CaDiCaL oracle
        let dimacs = to_dimacs(nv, &clauses);
        let cadical_verdict = run_oracle(&cadical, &dimacs);
        if cadical_verdict == OracleVerdict::Unknown {
            continue;
        }

        tested += 1;

        let ay_as_oracle = match ay_verdict {
            Verdict::Sat => OracleVerdict::Sat,
            Verdict::Unsat => OracleVerdict::Unsat,
            Verdict::Unknown => unreachable!(),
        };

        if ay_as_oracle != cadical_verdict {
            let saved =
                save_failing_formula(nv, &clauses, "cadical_oracle", 0xCAD1_CA10_0AC1_E000, i);
            disagreements.push(format!(
                "formula #{i} (nv={nv}, nc={}): ay={ay_verdict}, cadical={cadical_verdict:?}\n  saved: {}",
                clauses.len(),
                saved.display(),
            ));
        }
    }

    eprintln!(
        "fuzz_cadical_oracle_500: {tested} cross-validated, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "AY vs CaDiCaL oracle disagreements:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 200,
        "Expected at least 200 formulas cross-validated, got {tested}"
    );
}

// =============================================================================
// External oracle: Kissat cross-validation on random formulas
// =============================================================================

/// Compare AY (all inprocessing) against Kissat on 500 random 3-SAT formulas.
///
/// When Kissat is unavailable, the test passes with a diagnostic message.
/// Provides a second independent oracle (different solver, different bugs).
#[test]
fn fuzz_kissat_oracle_500() {
    let kissat = match find_kissat() {
        Some(path) => path,
        None => {
            eprintln!("fuzz_kissat_oracle_500: SKIP (Kissat not found)");
            return;
        }
    };

    let mut rng = Lcg::new(0x6155_A700_DEAD_BEEF);
    let mut tested = 0;
    let mut disagreements = Vec::new();

    for i in 0..500 {
        let num_vars = rng.next_range(10, 50);
        let (nv, clauses) = generate_random_3sat(num_vars, 4.26, &mut rng);

        // AY with all inprocessing
        let ay_result = solve_with_config(nv, &clauses, enable_all_inprocessing, "ay-all");
        let ay_verdict = Verdict::from_result(&ay_result);
        if ay_verdict == Verdict::Unknown {
            continue;
        }

        // Kissat oracle
        let dimacs = to_dimacs(nv, &clauses);
        let kissat_verdict = run_oracle(&kissat, &dimacs);
        if kissat_verdict == OracleVerdict::Unknown {
            continue;
        }

        tested += 1;

        let ay_as_oracle = match ay_verdict {
            Verdict::Sat => OracleVerdict::Sat,
            Verdict::Unsat => OracleVerdict::Unsat,
            Verdict::Unknown => unreachable!(),
        };

        if ay_as_oracle != kissat_verdict {
            let saved =
                save_failing_formula(nv, &clauses, "kissat_oracle", 0x6155_A700_DEAD_BEEF, i);
            disagreements.push(format!(
                "formula #{i} (nv={nv}, nc={}): ay={ay_verdict}, kissat={kissat_verdict:?}\n  saved: {}",
                clauses.len(),
                saved.display(),
            ));
        }
    }

    eprintln!(
        "fuzz_kissat_oracle_500: {tested} cross-validated, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "AY vs Kissat oracle disagreements:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 200,
        "Expected at least 200 formulas cross-validated, got {tested}"
    );
}

// =============================================================================
// Relevancy frontier (#relevancy-frontier-incremental)
// =============================================================================

/// Deterministic xorshift 3-SAT generator for the relevancy arm.
///
/// `generate_random_3sat` above draws from an LCG through `% n` and
/// `is_multiple_of(2)` — the two places an LCG is weakest — so its low bits are
/// nearly periodic and its clause polarities strictly alternate. The formulas
/// that come out are structurally easy: a 12-formula sweep at 180-260 variables
/// and ratio 4.4 finished in 0.83 s having never reached a single clause-DB
/// reduction, let alone the arena compaction this arm needs. Xorshift plus a
/// distinct-variable rejection gives genuine phase-transition 3-SAT at the same
/// sizes, which refutes in tens of thousands of conflicts.
fn generate_hard_3sat(num_vars: usize, num_clauses: usize, seed: u64) -> Vec<Vec<Literal>> {
    let mut state = seed | 1;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let mut clause: Vec<Literal> = Vec::with_capacity(3);
        while clause.len() < 3 {
            let v = Variable::new((next() % num_vars as u64) as u32);
            if clause.iter().any(|l| l.variable() == v) {
                continue;
            }
            clause.push(if next().is_multiple_of(2) {
                Literal::positive(v)
            } else {
                Literal::negative(v)
            });
        }
        clauses.push(clause);
    }
    clauses
}

/// Fuzz the INCREMENTAL relevancy frontier against unrestricted branching, on
/// formulas large enough that the clause DB actually MUTATES under it.
///
/// The rest of this file leaves `relevancy_branching` off, so nothing here used
/// to touch `solver/relevancy_frontier.rs` at all — running the fuzz group with
/// `--features relevancy-frontier-invariants` asserted nothing. This arm turns
/// the frontier on HARD (engaged on every decision, skipping the wander
/// trip-wire) so both of its exactness pins fire: the query-time set-equality
/// check, and the post-unassignment-fold check that is the only one able to see
/// a fold over a clause DB that moved (`reduce_db` deletions, `replace`
/// strengthening, and `compact_arena_locality`, which rewrites the arena
/// SHORTER with every offset moved).
///
/// Sizing is the point, and so is the generator (see `generate_hard_3sat`):
/// 180-250 variables at ratio 4.35 refutes in tens of thousands of conflicts,
/// which is what it takes to reach the first clause-DB reduction and the arena
/// compaction that follows it. The test asserts that at least one formula in
/// the sweep actually compacted, so it cannot quietly stop covering that class.
///
/// Relevancy gates DECISIONS only, so it can never flip SAT<->UNSAT; it may
/// legitimately return `unknown` (the empty-frontier SAT signal is re-verified
/// by the always-on model gate), so only a FLIPPED verdict is a failure.
#[test]
fn fuzz_relevancy_frontier_vs_unrestricted() {
    let mut tested = 0;
    let mut unknowns = 0;
    let mut compactions = 0u64;
    let mut relevancy_decisions = 0u64;
    let mut conflicts = 0u64;
    let mut disagreements = Vec::new();

    for i in 0..8u64 {
        let nv = 180 + 10 * i as usize;
        let clauses = generate_hard_3sat(nv, (nv as f64 * 4.35) as usize, 0x5EED_0000 + i);

        let mut solver = Solver::new(nv);
        solver.set_relevancy_branching(true);
        solver.set_relevancy_hard(true);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }
        let result_rel = solver.solve().into_inner();
        if let SatResult::Sat(ref model) = result_rel {
            assert!(
                verify_model(&clauses, model),
                "[relevancy] SAT model does not satisfy original clauses (formula #{i}, nv={nv})"
            );
        }
        compactions += solver.num_arena_compactions();
        relevancy_decisions += solver.relevancy_decisions();
        conflicts += solver.num_conflicts();

        let result_plain = solve_with_config(nv, &clauses, |_| {}, "unrestricted");

        let v_rel = Verdict::from_result(&result_rel);
        let v_plain = Verdict::from_result(&result_plain);

        if v_plain == Verdict::Unknown {
            continue;
        }
        if v_rel == Verdict::Unknown {
            // Allowed: relevancy can degrade to unknown, never to a wrong verdict.
            unknowns += 1;
            continue;
        }

        tested += 1;
        if v_rel != v_plain {
            let saved = save_failing_formula(nv, &clauses, "relevancy", 0x5EED_0000, i as usize);
            disagreements.push(format!(
                "formula #{i} (nv={nv}, nc={}): relevancy={v_rel}, unrestricted={v_plain}\n  saved: {}",
                clauses.len(),
                saved.display(),
            ));
        }
    }

    eprintln!(
        "fuzz_relevancy_frontier_vs_unrestricted: {tested} tested, {unknowns} relevancy-unknown, \
         {conflicts} conflicts, {compactions} arena compactions, {relevancy_decisions} relevancy \
         decisions, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "Relevancy frontier soundness failures:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 4,
        "Expected at least 8 comparable formulas, got {tested}"
    );
    assert!(
        relevancy_decisions > 0,
        "the relevancy frontier never engaged, so nothing was folded"
    );
    assert!(
        compactions > 0,
        "no formula in this sweep compacted the arena, so it no longer covers the \
         fold-over-a-moved-formula class this arm exists for"
    );
}
