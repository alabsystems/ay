// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Shared types, constants, and helper functions for soundness gate tests.

use super::test_common;
use ay_drat_check::checker::DratChecker;
use ay_sat::{parse_dimacs, InprocessingFeatureProfile, Literal, ProofOutput, SatResult, Solver};
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

pub(crate) const BENCHMARK_DIR: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/"
);

/// Vendored benchmark data directory (checked into the repo).
const VENDORED_DATA_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

/// Gate benchmarks: small (248 vars, 3729 clauses), medium (936 vars, 7902 clauses).
/// These must complete in debug mode within 60s even with all inprocessing disabled.
pub(crate) const GATE_BENCHMARKS: &[&str] = &["cmu-bmc-barrel6.cnf", "cmu-bmc-longmult15.cnf"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct OracleBenchmark {
    pub(crate) name: &'static str,
    pub(crate) rel_path: &'static str,
    /// Re-run DRAT inside the full oracle matrix only for cheap UNSAT formulas.
    /// Larger proofs stay covered by the dedicated per-feature proof tests above.
    pub(crate) matrix_drat: bool,
}

pub(crate) const ORACLE_SAT_BENCHMARKS: &[OracleBenchmark] = &[
    // Industrial / crypto SAT-COMP sample.
    OracleBenchmark {
        name: "simon-r16-1",
        rel_path:
            "benchmarks/sat/satcomp2024-sample/08ccc34df5d8eb9e9d45278af3dc093d-simon-r16-1.sanitized.cnf.xz",
        matrix_drat: false,
    },
    // Historical wrong-UNSAT family for decompose / sweep regressions (#3466, #6999).
    OracleBenchmark {
        name: "AProVE09-13",
        rel_path: "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/sat/AProVE09-13.cnf",
        matrix_drat: false,
    },
    // Independent SAT family from the same decompose regression cluster (#3466).
    OracleBenchmark {
        name: "q_query_3_l37_lambda",
        rel_path:
            "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/sat/q_query_3_l37_lambda.cnf",
        matrix_drat: false,
    },
    // Random 3-SAT regression target (#3913).
    OracleBenchmark {
        name: "uf200-01",
        rel_path: "reference/creusat/tests/satlib/UF200.860.100/uf200-01.cnf",
        matrix_drat: false,
    },
    // Larger random 3-SAT SATLIB case to cover threshold-style formulas.
    OracleBenchmark {
        name: "uf250-02",
        rel_path: "reference/creusat/tests/satlib/UF250.1065.100/uf250-02.cnf",
        matrix_drat: false,
    },
];

pub(crate) const ORACLE_UNSAT_BENCHMARKS: &[OracleBenchmark] = &[
    // BMC baseline used throughout the SAT soundness gate.
    OracleBenchmark {
        name: "cmu-bmc-barrel6",
        rel_path:
            "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/cmu-bmc-barrel6.cnf",
        matrix_drat: true,
    },
    // Historical reconstruction / model-validation regression target.
    // #7913: enabled matrix_drat for expanded DRAT coverage.
    OracleBenchmark {
        name: "minor032",
        rel_path: "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/minor032.cnf",
        matrix_drat: true,
    },
    // Historical structured UNSAT soundness benchmark.
    // #7913: enabled matrix_drat for expanded DRAT coverage.
    OracleBenchmark {
        name: "manol-pipe-c9",
        rel_path:
            "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/manol-pipe-c9.cnf",
        matrix_drat: true,
    },
    // Tiny combinatorial UNSAT with cheap proofs.
    OracleBenchmark {
        name: "php_4_3",
        rel_path: "benchmarks/sat/unsat/php_4_3.cnf",
        matrix_drat: true,
    },
    // Second tiny combinatorial family to avoid overfitting to pigeonhole only.
    OracleBenchmark {
        name: "ramsey_r3_3_6",
        rel_path: "benchmarks/sat/unsat/ramsey_r3_3_6.cnf",
        matrix_drat: true,
    },
    // Medium BMC formula (936 vars, 7902 clauses). Same family as barrel6 but
    // larger — catches bugs that only trigger with more variables. Already a
    // GATE_BENCHMARK; adding to oracle matrix for CaDiCaL cross-validation.
    // #7913: enabled matrix_drat for expanded DRAT coverage.
    OracleBenchmark {
        name: "cmu-bmc-longmult15",
        rel_path:
            "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/cmu-bmc-longmult15.cnf",
        matrix_drat: true,
    },
    // Random 3-SAT unsatisfiable at the phase transition (250 vars, 1065 clauses).
    // Pairs with uf250-02 on the SAT side to cover both polarities of random formulas.
    OracleBenchmark {
        name: "uuf250-01",
        rel_path: "reference/creusat/tests/satlib/UUF250.1065.100/uuf250-01.cnf",
        matrix_drat: true,
    },
];

pub(crate) use super::test_common::{
    assert_model_satisfies, load_repo_benchmark, verify_drat_proof,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OracleResult {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GateFeature {
    Vivify,
    Subsume,
    Probe,
    Shrink,
    Bve,
    Bce,
    Transred,
    Htr,
    Condition,
    Congruence,
    Sweep,
    Decompose,
    Factor,
    Backbone,
}

impl GateFeature {
    pub(crate) const ALL: [Self; 14] = [
        Self::Vivify,
        Self::Subsume,
        Self::Probe,
        Self::Shrink,
        Self::Bve,
        Self::Bce,
        Self::Transred,
        Self::Htr,
        Self::Condition,
        Self::Congruence,
        Self::Sweep,
        Self::Decompose,
        Self::Factor,
        Self::Backbone,
    ];

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Vivify => "vivify",
            Self::Subsume => "subsume",
            Self::Probe => "probe",
            Self::Shrink => "shrink",
            Self::Bve => "bve",
            Self::Bce => "bce",
            Self::Transred => "transred",
            Self::Htr => "htr",
            Self::Condition => "conditioning",
            Self::Congruence => "congruence",
            Self::Sweep => "sweep",
            Self::Decompose => "decompose",
            Self::Factor => "factor",
            Self::Backbone => "backbone",
        }
    }

    /// Whether this technique's DRAT proof emission has been verified by drat-trim.
    /// Decompose and congruence are excluded until proof-mode rewrite/model
    /// reconstruction is safe. Sweep is excluded: kitten can't produce DRAT
    /// proof steps, and rebuild-per-probe (#7037) makes sweep-only+DRAT too
    /// slow for barrel6.
    pub(crate) fn drat_verified(self) -> bool {
        !matches!(self, Self::Congruence | Self::Decompose | Self::Sweep)
    }

    pub(crate) fn enable(self, solver: &mut Solver) {
        match self {
            Self::Vivify => solver.set_vivify_enabled(true),
            Self::Subsume => solver.set_subsume_enabled(true),
            Self::Probe => solver.set_probe_enabled(true),
            Self::Shrink => solver.set_shrink_enabled(true),
            Self::Bve => solver.set_bve_enabled(true),
            Self::Bce => solver.set_bce_enabled(true),
            Self::Transred => solver.set_transred_enabled(true),
            Self::Htr => solver.set_htr_enabled(true),
            Self::Condition => solver.set_condition_enabled(true),
            Self::Congruence => {
                solver.set_congruence_enabled(true);
            }
            Self::Sweep => solver.set_sweep_enabled(true),
            Self::Decompose => solver.set_decompose_enabled(true),
            Self::Factor => solver.set_factor_enabled(true),
            Self::Backbone => solver.set_backbone_enabled(true),
        }
    }

    fn profile_flag(self, profile: &InprocessingFeatureProfile) -> bool {
        match self {
            Self::Vivify => profile.vivify,
            Self::Subsume => profile.subsume,
            Self::Probe => profile.probe,
            Self::Shrink => profile.shrink,
            Self::Bve => profile.bve,
            Self::Bce => profile.bce,
            Self::Transred => profile.transred,
            Self::Htr => profile.htr,
            Self::Condition => profile.condition,
            Self::Congruence => profile.congruence,
            Self::Sweep => profile.sweep,
            Self::Decompose => profile.decompose,
            Self::Factor => profile.factor,
            Self::Backbone => profile.backbone,
        }
    }
}

fn assert_base_profile(profile: InprocessingFeatureProfile, context: &str) {
    assert!(
        profile.preprocess,
        "SOUNDNESS GATE [{context}]: preprocess must remain enabled"
    );
    assert!(
        profile.walk,
        "SOUNDNESS GATE [{context}]: walk must remain enabled"
    );
    assert!(
        profile.warmup,
        "SOUNDNESS GATE [{context}]: warmup must remain enabled"
    );
    assert!(
        !profile.hbr,
        "SOUNDNESS GATE [{context}]: hbr must be disabled in isolation mode"
    );
}

fn assert_isolation_profile(
    profile: InprocessingFeatureProfile,
    enabled: GateFeature,
    context: &str,
) {
    assert_base_profile(profile, context);
    for feature in GateFeature::ALL {
        let should_be_enabled = feature == enabled;
        assert_eq!(
            feature.profile_flag(&profile),
            should_be_enabled,
            "SOUNDNESS GATE [{context}]: feature '{}' expected enabled={should_be_enabled}",
            feature.label(),
        );
    }
}

pub(crate) fn try_cadical_binary() -> Option<PathBuf> {
    let path = test_common::workspace_root().join("reference/cadical/build/cadical");
    if path.exists() {
        Some(path)
    } else {
        eprintln!(
            "CaDiCaL binary not found at {}. Build with: cd reference/cadical && ./configure && make",
            path.display()
        );
        None
    }
}

pub(crate) fn cadical_binary() -> PathBuf {
    try_cadical_binary().expect("CaDiCaL binary required for this test")
}

fn write_temp_cnf(label: &str, cnf: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before unix epoch")
        .as_nanos();
    let sanitized = label
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect::<String>();
    let path = std::env::temp_dir().join(format!(
        "ay_soundness_gate_{sanitized}_{}_{}.cnf",
        std::process::id(),
        nanos
    ));
    std::fs::write(&path, cnf).unwrap_or_else(|e| panic!("write {} failed: {e}", path.display()));
    path
}

fn parse_cadical_status(stdout: &str) -> OracleResult {
    if stdout.lines().any(|line| line.trim() == "s SATISFIABLE") {
        OracleResult::Sat
    } else if stdout.lines().any(|line| line.trim() == "s UNSATISFIABLE") {
        OracleResult::Unsat
    } else {
        OracleResult::Unknown
    }
}

pub(crate) fn run_cadical_oracle(cnf_dimacs: &str, label: &str) -> OracleResult {
    let cnf_path = write_temp_cnf(&format!("oracle_{label}"), cnf_dimacs);
    let output = Command::new(cadical_binary())
        .arg(&cnf_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to run cadical on {}: {e}", cnf_path.display()));
    let _ = std::fs::remove_file(&cnf_path);
    parse_cadical_status(&String::from_utf8_lossy(&output.stdout))
}

pub(crate) fn sat_result_kind(result: &SatResult) -> OracleResult {
    match result {
        SatResult::Sat(_) => OracleResult::Sat,
        SatResult::Unsat(_) => OracleResult::Unsat,
        SatResult::Unknown => OracleResult::Unknown,
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

pub(crate) fn disable_all_inprocessing(solver: &mut Solver) {
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
    solver.set_hbr_enabled(false);
    solver.set_backbone_enabled(false);
    assert_base_profile(
        solver.inprocessing_feature_profile(),
        "disable-all-inprocessing",
    );
}

/// Create a solver with ALL inprocessing disabled.
/// The caller then enables exactly one feature to test it in isolation.
pub(crate) fn solver_all_disabled(content: &str) -> (Solver, Vec<Vec<Literal>>) {
    let formula = parse_dimacs(content).expect("parse");
    let original_clauses = formula.clauses.clone();
    let num_vars = formula.num_vars;
    let mut solver = Solver::new(num_vars);

    // Disable all inprocessing features.
    disable_all_inprocessing(&mut solver);

    // Keep core search infrastructure enabled (these are not inprocessing):
    // glucose restarts, chronological backtracking, walk, warmup, rephase, preprocess

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    (solver, original_clauses)
}

/// Verify that the solver produces the correct UNSAT result.
/// If SAT is returned, verify the model against original clauses and panic.
pub(crate) fn verify_unsat(solver: &mut Solver, original_clauses: &[Vec<Literal>], label: &str) {
    let result = solver.solve().into_inner();
    match result {
        SatResult::Unsat(_) => {} // Expected
        SatResult::Sat(model) => {
            assert_model_satisfies(original_clauses, &model, label);
            panic!(
                "SOUNDNESS GATE [{label}]: returned SAT with valid model on known-UNSAT instance"
            );
        }
        SatResult::Unknown => {
            panic!("SOUNDNESS GATE [{label}]: returned Unknown on known-UNSAT instance");
        }
        _ => unreachable!(),
    }
}

/// Try to read a benchmark from the reference directory, falling back to
/// vendored data under `tests/data/`.
fn read_benchmark_from_any_source(name: &str) -> Result<String, String> {
    let primary = format!("{BENCHMARK_DIR}{name}");
    if let Ok(content) = std::fs::read_to_string(&primary) {
        return Ok(content);
    }
    let vendored = format!("{VENDORED_DATA_DIR}{name}");
    if let Ok(content) = std::fs::read_to_string(&vendored) {
        return Ok(content);
    }
    Err(format!(
        "benchmark {name} not found at {primary} or {vendored}"
    ))
}

pub(crate) fn load_benchmark(name: &str) -> String {
    read_benchmark_from_any_source(name).unwrap_or_else(|msg| panic!("Missing benchmark: {msg}"))
}

/// Load a benchmark file, returning `None` if the fixture is absent.
///
/// Use this for tests that depend on optional benchmark fixtures (e.g.,
/// `longmult15.cnf` which may be missing in shallow checkouts or zone
/// branches). The caller should return early with an explanatory message
/// rather than panic on a missing fixture.
pub(crate) fn try_load_benchmark(name: &str) -> Option<String> {
    match read_benchmark_from_any_source(name) {
        Ok(content) => Some(content),
        Err(msg) => {
            eprintln!("SOUNDNESS GATE: skipping — {msg}");
            None
        }
    }
}

pub(crate) fn solve_feature_isolation(
    feature: GateFeature,
    cnf_dimacs: &str,
) -> (SatResult, Vec<Vec<Literal>>, usize) {
    let formula = parse_dimacs(cnf_dimacs).expect("parse");
    let num_vars = formula.num_vars;
    let original_clauses = formula.clauses.clone();

    let mut solver = Solver::new(num_vars);
    disable_all_inprocessing(&mut solver);
    feature.enable(&mut solver);
    assert_isolation_profile(
        solver.inprocessing_feature_profile(),
        feature,
        "solve-feature-isolation",
    );
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    (solver.solve().into_inner(), original_clauses, num_vars)
}

pub(crate) fn verify_unsat_with_drat(feature: GateFeature, cnf_dimacs: &str, label: &str) {
    let formula = parse_dimacs(cnf_dimacs).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    disable_all_inprocessing(&mut solver);
    feature.enable(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "SOUNDNESS GATE [{label}]: proof-mode run must be UNSAT to verify DRAT"
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    verify_drat_proof(
        cnf_dimacs,
        &writer.into_vec().expect("proof writer flush"),
        label,
    );
}

/// Verify a DRAT proof using ay-drat-check in-process (always available, no external binary).
///
/// This uses the native Rust DRAT checker rather than the external drat-trim binary.
/// The native checker is always available as a crate dependency, making these tests
/// hermetic and runnable without installing drat-trim.
pub(crate) fn verify_drat_proof_native(cnf_dimacs: &str, proof_bytes: &[u8], label: &str) {
    let proof_text = String::from_utf8_lossy(proof_bytes);
    assert!(
        proof_text.ends_with("0\n"),
        "SOUNDNESS GATE [{label}]: proof must end with empty clause"
    );

    // Parse CNF using ay-drat-check's parser (shared ay-proof-common types).
    let cnf = ay_drat_check::cnf_parser::parse_cnf(cnf_dimacs.as_bytes())
        .unwrap_or_else(|e| panic!("SOUNDNESS GATE [{label}]: CNF parse failed: {e}"));

    // Parse DRAT proof.
    let steps = ay_drat_check::drat_parser::parse_drat(proof_bytes)
        .unwrap_or_else(|e| panic!("SOUNDNESS GATE [{label}]: DRAT parse failed: {e}"));

    // Run the forward checker with RAT support enabled.
    let mut checker = DratChecker::new(cnf.num_vars, true);
    checker.verify(&cnf.clauses, &steps).unwrap_or_else(|e| {
        let stats = checker.stats();
        panic!(
            "SOUNDNESS GATE [{label}]: native DRAT verification FAILED: {e}\n\
                 stats: original={} additions={} deletions={} checks={} failures={}",
            stats.original, stats.additions, stats.deletions, stats.checks, stats.failures,
        )
    });
}

/// Verify an UNSAT result with native DRAT proof checking (ay-drat-check, in-process).
///
/// Creates a solver with proof output enabled, solves with the given feature
/// in isolation, extracts the DRAT proof, and verifies it using the native
/// Rust checker. This is the in-process counterpart to `verify_unsat_with_drat`
/// which uses the external drat-trim binary.
pub(crate) fn verify_unsat_with_native_drat(feature: GateFeature, cnf_dimacs: &str, label: &str) {
    let formula = parse_dimacs(cnf_dimacs).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    disable_all_inprocessing(&mut solver);
    feature.enable(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "SOUNDNESS GATE [{label}]: proof-mode run must be UNSAT to verify native DRAT"
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    verify_drat_proof_native(cnf_dimacs, &proof_bytes, label);
}

/// Verify that a full-stack solver (all defaults) produces a valid DRAT proof
/// for the given UNSAT formula. Uses native ay-drat-check (in-process).
pub(crate) fn verify_full_stack_unsat_with_native_drat(cnf_dimacs: &str, label: &str) {
    let formula = parse_dimacs(cnf_dimacs).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "SOUNDNESS GATE [{label}]: full-stack proof-mode run must be UNSAT to verify DRAT"
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    verify_drat_proof_native(cnf_dimacs, &proof_bytes, label);
}

/// Verify an UNSAT result with native DRAT checking for a pair of features.
///
/// Like `verify_unsat_with_native_drat` but enables two features instead of one.
/// Used by pairwise interaction gate tests.
pub(crate) fn verify_pairwise_unsat_with_native_drat(
    feature_a: GateFeature,
    feature_b: GateFeature,
    cnf_dimacs: &str,
    label: &str,
) {
    // Skip if either feature doesn't have verified DRAT emission.
    if !feature_a.drat_verified() || !feature_b.drat_verified() {
        return;
    }
    let formula = parse_dimacs(cnf_dimacs).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    disable_all_inprocessing(&mut solver);
    feature_a.enable(&mut solver);
    feature_b.enable(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "SOUNDNESS GATE [{label}]: proof-mode run must be UNSAT to verify native DRAT"
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    verify_drat_proof_native(cnf_dimacs, &proof_bytes, label);
}

/// Verify an UNSAT result with native DRAT checking for a triple of features.
///
/// Like `verify_pairwise_unsat_with_native_drat` but enables three features.
/// Used by triple interaction gate tests (#3479).
pub(crate) fn verify_triple_unsat_with_native_drat(
    feature_a: GateFeature,
    feature_b: GateFeature,
    feature_c: GateFeature,
    cnf_dimacs: &str,
    label: &str,
) {
    // Skip if any feature doesn't have verified DRAT emission.
    if !feature_a.drat_verified() || !feature_b.drat_verified() || !feature_c.drat_verified() {
        return;
    }
    let formula = parse_dimacs(cnf_dimacs).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    disable_all_inprocessing(&mut solver);
    feature_a.enable(&mut solver);
    feature_b.enable(&mut solver);
    feature_c.enable(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "SOUNDNESS GATE [{label}]: proof-mode run must be UNSAT to verify native DRAT"
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    verify_drat_proof_native(cnf_dimacs, &proof_bytes, label);
}
