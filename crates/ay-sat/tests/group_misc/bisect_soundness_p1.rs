// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Bisection tests for P1 soundness bugs #4719 (false UNSAT) and #4720 (false SAT).
//
// Strategy: "exclude one technique at a time" — start from the default profile,
// explicitly opt into the suspect transforms where needed, then disable a
// single technique. If the bug disappears when technique X is disabled, X is
// the culprit (or a necessary participant).

use ay_sat::{parse_dimacs, SatResult, Solver};
use ntest::timeout;
use std::path::PathBuf;
use std::sync::LazyLock;
use std::time::{Duration, Instant};

fn repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.parent().unwrap().parent().unwrap().to_path_buf()
}

fn load_benchmark_uncached(filename: &str) -> Option<String> {
    let root = repo_root();
    let path = root
        .join("benchmarks/sat/satcomp2024-sample")
        .join(filename);
    if !path.exists() {
        eprintln!("Benchmark not found: {}", path.display());
        return None;
    }
    Some(std::fs::read_to_string(&path).unwrap())
}

const ECAREV: &str = "cd361d33986dccd7f2d86016d6c35241-ecarev-110-4099-22-30-7.cnf";
const MP1: &str = "0876c518e5653369e20fb1ee0bb8db40-mp1-klieber2017s-0500-023-t12.cnf";

// Cache 16MB ecarev and mp1 benchmarks: loaded once across all 35 tests.
// Saves ~34 redundant 16MB file reads (18 ecarev + 17 mp1 calls → 1 each).
static ECAREV_CNF: LazyLock<Option<String>> = LazyLock::new(|| load_benchmark_uncached(ECAREV));
static MP1_CNF: LazyLock<Option<String>> = LazyLock::new(|| load_benchmark_uncached(MP1));

fn load_benchmark(filename: &str) -> Option<&'static str> {
    match filename {
        ECAREV => ECAREV_CNF.as_deref(),
        MP1 => MP1_CNF.as_deref(),
        _ => panic!("unexpected benchmark: {filename}"),
    }
}

/// All techniques explicitly enabled in DIMACS mode for bisection.
const ALL_DIMACS_TECHNIQUES: &[&str] = &[
    "vivify",
    "subsume",
    "probe",
    "bve",
    "bce",
    "condition",
    "decompose",
    "factor",
    "transred",
    "htr",
    "gate",
    "congruence",
    "sweep",
    "backbone",
];

/// Create a solver with all bisection techniques explicitly enabled, then
/// disable specific techniques.
fn make_solver_excluding(cnf: &str, exclude: &[&str]) -> Solver {
    let formula = parse_dimacs(cnf).expect("parse");
    let mut solver: Solver = Solver::new(formula.num_vars);

    // Opt into every technique covered by this bisection matrix.
    solver.set_bve_enabled(true);
    solver.set_bce_enabled(true);
    solver.set_condition_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_congruence_enabled(true);

    // Selectively disable excluded techniques.
    for name in exclude {
        match *name {
            "vivify" => solver.set_vivify_enabled(false),
            "subsume" => solver.set_subsume_enabled(false),
            "probe" => solver.set_probe_enabled(false),
            "bve" => solver.set_bve_enabled(false),
            "bce" => solver.set_bce_enabled(false),
            "condition" => solver.set_condition_enabled(false),
            "decompose" => solver.set_decompose_enabled(false),
            "factor" => solver.set_factor_enabled(false),
            "transred" => solver.set_transred_enabled(false),
            "htr" => solver.set_htr_enabled(false),
            "gate" => solver.set_gate_enabled(false),
            "congruence" => solver.set_congruence_enabled(false),
            "sweep" => solver.set_sweep_enabled(false),
            "backbone" => solver.set_backbone_enabled(false),
            other => panic!("Unknown technique: {other}"),
        }
    }

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    solver
}

/// Solve with a wall-clock time limit. Returns the result or Unknown on timeout.
/// Uses both `set_interrupt` (checked during preprocessing/inprocessing) and
/// `solve_interruptible` (checked every 100 conflicts in the CDCL main loop).
fn solve_with_timeout(solver: &mut Solver, timeout: Duration) -> SatResult {
    let start = Instant::now();
    let timer = super::common::SolverInterruptTimer::start(solver, timeout);

    let result = solver
        .solve_interruptible(|| timer.is_interrupted())
        .into_inner();
    timer.cancel_and_join();
    let elapsed = start.elapsed();
    eprintln!("  solve completed in {elapsed:.1?}");
    result
}

// ==================== #4719: ecarev false UNSAT (FIXED) ====================
//
// CaDiCaL: SAT (exit 10) in ~102s.
// AY (before fix): UNSAT in ~2.8s — confirmed false UNSAT.
// AY (after 30dae80d9 HBR reason fix): no false UNSAT, but times out.
//
// Root cause: HBR reason/parent mismatch in probing (probe_reason lifecycle).
// Fix: unconditional probe_reason assignment in propagation.rs (30dae80d9).
//
// Bisection tests below disable one technique at a time to verify the
// soundness fix holds across all inprocessing configurations.

/// Soundness regression test: ay must NOT return false UNSAT on ecarev.
/// CaDiCaL confirms this formula is SAT. AY previously returned false UNSAT
/// in ~2.8s (bug #4719). After the HBR reason coherence fix (30dae80d9),
/// ay no longer returns false UNSAT. It may return SAT, Unknown, or timeout.
///
/// Note: 180s ntest timeout because preprocessing on this 16MB benchmark
/// does not check the interrupt flag (#5936), so the 5s solve timeout is
/// not respected until preprocessing completes (~60-90s in debug mode).
#[test]
#[timeout(180_000)]
fn ecarev_no_false_unsat() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &[]);
    let result = solve_with_timeout(&mut solver, Duration::from_secs(5));
    report_ecarev("all-enabled", &result);
}

/// Soundness regression: verify no false UNSAT with each technique excluded.
/// 180s ntest timeout: preprocessing ignores interrupt flag (#5936).

#[test]
#[timeout(180_000)]
fn ecarev_exclude_vivify() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["vivify"]);
    report_ecarev(
        "exclude-vivify",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_subsume() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["subsume"]);
    report_ecarev(
        "exclude-subsume",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_probe() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["probe"]);
    report_ecarev(
        "exclude-probe",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_bce() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["bce"]);
    report_ecarev(
        "exclude-bce",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_condition() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["condition"]);
    report_ecarev(
        "exclude-condition",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_decompose() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["decompose"]);
    report_ecarev(
        "exclude-decompose",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_factor() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["factor"]);
    report_ecarev(
        "exclude-factor",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_transred() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["transred"]);
    report_ecarev(
        "exclude-transred",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_htr() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["htr"]);
    report_ecarev(
        "exclude-htr",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_gate() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["gate"]);
    report_ecarev(
        "exclude-gate",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_congruence() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["congruence"]);
    report_ecarev(
        "exclude-congruence",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn ecarev_exclude_sweep() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["sweep"]);
    report_ecarev(
        "exclude-sweep",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

/// Exclude ALL inprocessing — if UNSAT with no inprocessing, bug is in core CDCL.
#[test]
#[timeout(60_000)]
fn ecarev_exclude_all_inprocessing() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, ALL_DIMACS_TECHNIQUES);
    report_ecarev(
        "exclude-ALL",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

fn report_ecarev(label: &str, result: &SatResult) {
    let tag = match result {
        SatResult::Sat(_) => "SAT (correct!)",
        SatResult::Unsat(_) => "UNSAT (regression!)",
        SatResult::Unknown => "Unknown/timeout",
        #[allow(unreachable_patterns)]
        _ => "other",
    };
    eprintln!("ecarev {label}: {tag}");
    // Soundness assertion: ecarev is SAT per CaDiCaL. AY must not return false UNSAT.
    assert!(
        !matches!(result, SatResult::Unsat(_)),
        "ecarev {label}: returned false UNSAT — #4719 regression!",
    );
}

// ==================== #4720: mp1 invalid SAT model (FAIL-CLOSED) ====================
//
// CaDiCaL: SAT (exit 10). AY: previously SAT with invalid model (panic at
// solve.rs model verification). After fail-closed fix (76f554158), ay now
// returns Unknown when model verification fails. Root cause (BVE
// reconstruction) is still open.

/// Soundness regression test: ay must not return SAT with an invalid model on mp1.
/// CaDiCaL confirms this formula is SAT. AY previously returned SAT with an
/// invalid model (bug #4720). After the fail-closed fix (76f554158), ay returns
/// Unknown when model verification fails. If SAT is returned, the model must be valid.
#[test]
#[timeout(60_000)]
fn mp1_no_invalid_sat_model() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &[]);
    let result = solve_with_timeout(&mut solver, Duration::from_secs(5));
    report_mp1("all-default", cnf, &result);
}

/// Soundness regression: verify no false UNSAT or invalid model with each technique excluded.

#[test]
#[timeout(60_000)]
fn mp1_exclude_vivify() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["vivify"]);
    report_mp1(
        "exclude-vivify",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_subsume() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["subsume"]);
    report_mp1(
        "exclude-subsume",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_probe() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["probe"]);
    report_mp1(
        "exclude-probe",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_bce() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["bce"]);
    report_mp1(
        "exclude-bce",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_condition() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["condition"]);
    report_mp1(
        "exclude-condition",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_decompose() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["decompose"]);
    report_mp1(
        "exclude-decompose",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_factor() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["factor"]);
    report_mp1(
        "exclude-factor",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_transred() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["transred"]);
    report_mp1(
        "exclude-transred",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_htr() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["htr"]);
    report_mp1(
        "exclude-htr",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_gate() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["gate"]);
    report_mp1(
        "exclude-gate",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_congruence() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["congruence"]);
    report_mp1(
        "exclude-congruence",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_sweep() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, &["sweep"]);
    report_mp1(
        "exclude-sweep",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

#[test]
#[timeout(60_000)]
fn mp1_exclude_all_inprocessing() {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let mut solver = make_solver_excluding(cnf, ALL_DIMACS_TECHNIQUES);
    report_mp1(
        "exclude-ALL",
        cnf,
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

fn report_mp1(label: &str, cnf: &str, result: &SatResult) {
    match result {
        SatResult::Sat(model) => {
            let violation = find_first_violation(cnf, model);
            if let Some(ci) = violation {
                panic!("mp1 {label}: SAT with BAD MODEL (violation at clause {ci}) — #4720 regression!");
            }
            eprintln!("mp1 {label}: SAT (model valid!)");
        }
        SatResult::Unsat(_) => {
            panic!("mp1 {label}: returned UNSAT — CaDiCaL says SAT, this is a false UNSAT!");
        }
        SatResult::Unknown => eprintln!("mp1 {label}: Unknown/timeout (fail-closed, expected)"),
        #[allow(unreachable_patterns)]
        _ => eprintln!("mp1 {label}: other"),
    }
}

/// Find the first clause violated by the model. Returns None if model is valid.
fn find_first_violation(cnf: &str, model: &[bool]) -> Option<usize> {
    let formula = parse_dimacs(cnf).expect("parse");
    for (ci, clause) in formula.clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|&lit| {
            let var = lit.variable().index();
            if var >= model.len() {
                return false;
            }
            let val = model[var];
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

// ==================== #4719 Phase 2: Probe sub-bisection ====================
//
// Probe is implicated in the ecarev false UNSAT. Bisect further:
// - Probe with HBR disabled: isolates failed-literal-only derivation
// - Probe with HBR enabled: includes hyper-binary resolution during BCP

/// Create a solver with the default profile plus the suspect BVE/congruence pair.
fn make_solver_probe_hbr_control(cnf: &str, hbr_enabled: bool) -> Solver {
    let formula = parse_dimacs(cnf).expect("parse");
    let mut solver: Solver = Solver::new(formula.num_vars);
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_hbr_enabled(hbr_enabled);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    solver
}

/// Probe enabled, HBR disabled: soundness check.
/// 180s ntest timeout: preprocessing ignores interrupt flag (#5936).
#[test]
#[timeout(180_000)]
fn ecarev_probe_without_hbr() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_probe_hbr_control(cnf, false);
    report_ecarev(
        "probe-no-hbr",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

/// Probe enabled, HBR enabled: soundness check.
/// 180s ntest timeout: preprocessing ignores interrupt flag (#5936).
#[test]
#[timeout(180_000)]
fn ecarev_probe_with_hbr() {
    let Some(cnf) = load_benchmark(ECAREV) else {
        return;
    };
    let mut solver = make_solver_probe_hbr_control(cnf, true);
    report_ecarev(
        "probe-with-hbr",
        &solve_with_timeout(&mut solver, Duration::from_secs(5)),
    );
}

// ==================== #4720 Phase 2: mp1 safe bisection ====================
//
// After fail-closed fix (76f554158), mp1 no longer panics — it returns Unknown.
// catch_unwind is kept as a safety net in case of regressions.

fn run_mp1_safe(label: &str, exclude: &[&str]) {
    let Some(cnf) = load_benchmark(MP1) else {
        return;
    };
    let exclude_owned: Vec<String> = exclude.iter().map(ToString::to_string).collect();

    let result = std::panic::catch_unwind(move || {
        let exclude_refs: Vec<&str> = exclude_owned.iter().map(String::as_str).collect();
        let mut solver = make_solver_excluding(cnf, &exclude_refs);
        solve_with_timeout(&mut solver, Duration::from_secs(5))
    });

    match result {
        Ok(sat_result) => report_mp1(label, cnf, &sat_result),
        Err(e) => panic!("mp1 {label}: PANIC ({e:?}) — fail-closed fix regression!"),
    }
}

#[test]
#[timeout(60_000)]
fn mp1_safe_all_default() {
    run_mp1_safe("safe-all-default", &[]);
}

#[test]
#[timeout(60_000)]
fn mp1_safe_exclude_bve() {
    run_mp1_safe("safe-exclude-bve", &["bve"]);
}

#[test]
#[timeout(60_000)]
fn mp1_safe_exclude_congruence() {
    run_mp1_safe("safe-exclude-congruence", &["congruence"]);
}

#[test]
#[timeout(60_000)]
fn mp1_safe_exclude_bve_and_congruence() {
    run_mp1_safe("safe-exclude-bve-congruence", &["bve", "congruence"]);
}

#[test]
#[timeout(60_000)]
fn mp1_safe_exclude_all_inprocessing() {
    run_mp1_safe("safe-exclude-ALL", ALL_DIMACS_TECHNIQUES);
}
