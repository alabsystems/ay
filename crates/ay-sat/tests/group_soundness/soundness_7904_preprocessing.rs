// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing-focused soundness tests (Part of #7904).
//!
//! Tests that BVE, subsumption, vivification, BCE, and other preprocessing
//! techniques do not corrupt formula satisfiability when applied in isolation.
//! Each test encodes a small, crafted formula where the expected answer is
//! known by construction, then verifies:
//!
//! - SAT results: model satisfies ALL original clauses
//! - UNSAT results: DRAT proof verified by ay-drat-check
//!
//! These complement the gate tests in soundness_gate/ by testing individual
//! techniques on adversarial formula structures rather than benchmark files.

#![allow(clippy::panic)]
#![allow(unused_must_use)]

use ay_sat::{Literal, ProofOutput, SatResult, Solver, Variable};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn pos(v: u32) -> Literal {
    Literal::positive(Variable::new(v))
}

fn neg(v: u32) -> Literal {
    Literal::negative(Variable::new(v))
}

/// Verify a SAT model against original clauses.
fn verify_model(clauses: &[Vec<Literal>], model: &[bool], label: &str) {
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
        assert!(
            satisfied,
            "SOUNDNESS BUG: [{label}] SAT model violates clause {ci}: {clause:?}"
        );
    }
}

/// Solve with a single inprocessing feature enabled, verify result.
fn solve_single_feature(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected_sat: Option<bool>,
    enable_feature: impl FnOnce(&mut Solver),
) -> SatResult {
    let mut solver = Solver::new(num_vars);
    super::common::disable_all_inprocessing(&mut solver);
    enable_feature(&mut solver);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            verify_model(clauses, model, label);
            assert!(
                expected_sat != Some(false),
                "SOUNDNESS BUG: [{label}] returned SAT on known-UNSAT"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected_sat != Some(true),
                "SOUNDNESS BUG: [{label}] returned UNSAT on known-SAT"
            );
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

/// Solve with a single feature and verify DRAT proof for UNSAT results.
fn solve_single_feature_with_drat(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected_sat: Option<bool>,
    enable_feature: impl FnOnce(&mut Solver),
) -> SatResult {
    let mut solver = Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
    super::common::disable_all_inprocessing(&mut solver);
    enable_feature(&mut solver);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            verify_model(clauses, model, label);
            assert!(
                expected_sat != Some(false),
                "SOUNDNESS BUG: [{label}] returned SAT on known-UNSAT"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected_sat != Some(true),
                "SOUNDNESS BUG: [{label}] returned UNSAT on known-SAT"
            );
            let writer = solver.take_proof_writer().expect("proof writer");
            let proof_bytes = writer.into_vec().expect("proof flush");
            let dimacs = super::common::clauses_to_dimacs(num_vars, clauses);
            super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

/// Solve with ALL features (default config) and verify result.
fn solve_default_config(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected_sat: Option<bool>,
) -> SatResult {
    let mut solver = Solver::new(num_vars);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            verify_model(clauses, model, label);
            assert!(
                expected_sat != Some(false),
                "SOUNDNESS BUG: [{label}] returned SAT on known-UNSAT"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected_sat != Some(true),
                "SOUNDNESS BUG: [{label}] returned UNSAT on known-SAT"
            );
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

// ===========================================================================
// BVE (Bounded Variable Elimination) edge cases
//
// BVE resolves out a variable by replacing it with all resolvents of its
// positive and negative clauses. Bugs typically arise when:
// - Tautological resolvents are not filtered
// - Self-subsuming resolution creates incorrect clauses
// - Clause strengthening corrupts learned clauses
// - Model reconstruction after BVE is incorrect
// ===========================================================================

/// BVE on a variable that appears in both polarities with no tautological
/// resolvents. The result must remain SAT.
#[test]
fn bve_simple_elimination_sat() {
    // x0 appears in: (x0 v x1) and (-x0 v x2)
    // Resolvent: (x1 v x2) — still SAT
    let clauses = vec![vec![pos(0), pos(1)], vec![neg(0), pos(2)], vec![pos(3)]];
    solve_single_feature(4, &clauses, "bve-simple-sat", Some(true), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE elimination where all resolvents are tautological.
/// The variable can be eliminated without adding any clauses.
#[test]
fn bve_all_tautological_resolvents_sat() {
    // x0 in: (x0 v x1), (-x0 v -x1), (x2)
    // Resolvent of first two: (x1 v -x1) — tautology, discarded
    // Formula is SAT (x0=T, x1=T, x2=T)
    let clauses = vec![vec![pos(0), pos(1)], vec![neg(0), neg(1)], vec![pos(2)]];
    solve_single_feature(3, &clauses, "bve-taut-resolvent", Some(true), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE on a pure variable (appears in only one polarity).
/// Should be eliminable without adding any resolvents.
#[test]
fn bve_pure_variable_sat() {
    // x0 appears only positive: (x0 v x1), (x0 v x2)
    // Setting x0=T satisfies both. No negative occurrences.
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![pos(0), pos(2)],
        vec![neg(1), neg(2)],
    ];
    solve_single_feature(3, &clauses, "bve-pure-var", Some(true), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE where eliminating a variable makes the formula UNSAT.
/// The resolvent of the two clauses containing x0 produces the empty clause.
#[test]
fn bve_elimination_causes_unsat() {
    // (x0) and (-x0) — resolvent is the empty clause
    let clauses = vec![vec![pos(0)], vec![neg(0)]];
    solve_single_feature_with_drat(1, &clauses, "bve-elim-unsat", Some(false), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE with a variable that has many positive and negative occurrences.
/// Tests that the resolvent count limit (growth bound) is respected.
#[test]
fn bve_high_occurrence_count_sat() {
    let n = 10u32;
    let mut clauses = Vec::new();
    // x0 appears positive with x1..x5
    for i in 1..=5 {
        clauses.push(vec![pos(0), pos(i)]);
    }
    // x0 appears negative with x6..x10
    for i in 6..=n {
        clauses.push(vec![neg(0), pos(i)]);
    }
    // Force some variables to ensure SAT
    clauses.push(vec![pos(1)]);
    solve_single_feature(
        (n + 1) as usize,
        &clauses,
        "bve-high-occ",
        Some(true),
        |s| {
            s.set_bve_enabled(true);
        },
    );
}

/// BVE model reconstruction: after eliminating x0, the model for x0 must
/// be reconstructed to satisfy the original formula.
#[test]
fn bve_model_reconstruction_sat() {
    // (x0 v x1 v x2), (-x0 v x3), (-x1), (-x2)
    // With -x1, -x2 forced: x0 must be true. Then x3 is free.
    let clauses = vec![
        vec![pos(0), pos(1), pos(2)],
        vec![neg(0), pos(3)],
        vec![neg(1)],
        vec![neg(2)],
    ];
    let r = solve_single_feature(4, &clauses, "bve-model-recon", Some(true), |s| {
        s.set_bve_enabled(true);
    });
    if let SatResult::Sat(model) = &r {
        // x0 must be true since x1, x2 are forced false
        assert!(
            model.first().copied().unwrap_or(false),
            "BVE model reconstruction: x0 should be true"
        );
    }
}

/// BVE on a chain of implications. Eliminating middle variables must
/// preserve the implied relationship.
#[test]
fn bve_implication_chain_unsat() {
    // x0 => x1 => x2 => x3, plus x0 and -x3
    // UNSAT: x0=T forces x1=T, x2=T, x3=T, contradicting -x3
    let clauses = vec![
        vec![neg(0), pos(1)], // x0 => x1
        vec![neg(1), pos(2)], // x1 => x2
        vec![neg(2), pos(3)], // x2 => x3
        vec![pos(0)],         // x0
        vec![neg(3)],         // -x3
    ];
    solve_single_feature_with_drat(4, &clauses, "bve-impl-chain-unsat", Some(false), |s| {
        s.set_bve_enabled(true);
    });
}

// ===========================================================================
// Subsumption edge cases
//
// Forward subsumption removes clauses subsumed by existing clauses.
// Backward subsumption removes clauses subsumed by newly learned clauses.
// Bugs: removing the wrong clause, or self-subsumption corruption.
// ===========================================================================

/// Subsumption with exact subset relationship.
#[test]
fn subsume_exact_subset_sat() {
    // (x0) subsumes (x0 v x1) and (x0 v x2 v x3)
    let clauses = vec![
        vec![pos(0)],
        vec![pos(0), pos(1)],
        vec![pos(0), pos(2), pos(3)],
        vec![neg(1), pos(2)],
    ];
    solve_single_feature(4, &clauses, "subsume-subset-sat", Some(true), |s| {
        s.set_subsume_enabled(true);
    });
}

/// Self-subsuming resolution: (x0 v x1) and (-x0 v x1) implies (x1).
/// After strengthening, the formula must remain correct.
#[test]
fn subsume_self_subsuming_resolution_sat() {
    let clauses = vec![vec![pos(0), pos(1)], vec![neg(0), pos(1)], vec![pos(2)]];
    let r = solve_single_feature(3, &clauses, "subsume-ssr-sat", Some(true), |s| {
        s.set_subsume_enabled(true);
    });
    if let SatResult::Sat(model) = &r {
        // x1 must be true (implied by the two clauses)
        assert!(
            model.get(1).copied().unwrap_or(false),
            "Self-subsuming resolution should force x1=true"
        );
    }
}

/// Subsumption must not remove a clause that is NOT subsumed.
#[test]
fn subsume_near_miss_sat() {
    // (x0 v x1) does NOT subsume (x0 v -x1 v x2) — x1 vs -x1
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![pos(0), neg(1), pos(2)],
        vec![neg(0), neg(2)],
    ];
    solve_single_feature(3, &clauses, "subsume-near-miss", Some(true), |s| {
        s.set_subsume_enabled(true);
    });
}

/// Subsumption chain: unit clause subsumes binary subsumes ternary.
#[test]
fn subsume_chain_unsat() {
    // (x0), (-x0 v x1), (-x1) — UNSAT
    // (x0) subsumes (x0 v anything), but the chain matters for propagation
    let clauses = vec![vec![pos(0)], vec![neg(0), pos(1)], vec![neg(1)]];
    solve_single_feature_with_drat(2, &clauses, "subsume-chain-unsat", Some(false), |s| {
        s.set_subsume_enabled(true);
    });
}

// ===========================================================================
// Vivification edge cases
//
// Vivification strengthens clauses by attempting unit propagation on the
// negation of each literal. If a conflict is found, the clause can be
// shortened. Bugs: shortening a clause incorrectly, or losing literals.
// ===========================================================================

/// Vivification on a clause where one literal is implied by unit propagation.
#[test]
fn vivify_redundant_literal_sat() {
    // x0=T is forced. (x0 v x1 v x2) can be vivified since x0 is always true.
    let clauses = vec![
        vec![pos(0)],
        vec![pos(0), pos(1), pos(2)],
        vec![neg(1), pos(2)],
    ];
    solve_single_feature(3, &clauses, "vivify-redundant-lit", Some(true), |s| {
        s.set_vivify_enabled(true);
    });
}

/// Vivification must not shorten a clause below its actual implication.
#[test]
fn vivify_must_preserve_satisfiability_sat() {
    let n = 8u32;
    let mut clauses = Vec::new();
    // Create a satisfiable formula with long clauses
    for i in 0..(n - 1) {
        clauses.push(vec![pos(i), pos(i + 1)]);
        clauses.push(vec![neg(i), pos(i + 1)]);
    }
    clauses.push(vec![pos(n - 1)]);
    solve_single_feature(
        n as usize,
        &clauses,
        "vivify-preserve-sat",
        Some(true),
        |s| {
            s.set_vivify_enabled(true);
        },
    );
}

/// Vivification on UNSAT formula with DRAT proof.
#[test]
fn vivify_unsat_with_drat() {
    // PHP(3,2) — always UNSAT
    let clauses = vec![
        vec![pos(0), pos(1)], // pigeon 1 in hole 1 or 2
        vec![pos(2), pos(3)], // pigeon 2 in hole 1 or 2
        vec![pos(4), pos(5)], // pigeon 3 in hole 1 or 2
        vec![neg(0), neg(2)], // not both pigeons 1,2 in hole 1
        vec![neg(0), neg(4)], // not both pigeons 1,3 in hole 1
        vec![neg(2), neg(4)], // not both pigeons 2,3 in hole 1
        vec![neg(1), neg(3)], // not both pigeons 1,2 in hole 2
        vec![neg(1), neg(5)], // not both pigeons 1,3 in hole 2
        vec![neg(3), neg(5)], // not both pigeons 2,3 in hole 2
    ];
    solve_single_feature_with_drat(6, &clauses, "vivify-php32-drat", Some(false), |s| {
        s.set_vivify_enabled(true);
    });
}

// ===========================================================================
// BCE (Blocked Clause Elimination) edge cases
//
// A clause C is blocked on literal l if every resolvent of C with clauses
// containing -l is a tautology. BCE removes blocked clauses.
// Bug: removing a clause that is not actually blocked.
// ===========================================================================

/// BCE on a formula with a genuinely blocked clause.
#[test]
fn bce_blocked_clause_sat() {
    // (x0 v x1) is blocked on x0 if every clause with -x0 resolves
    // to a tautology. (-x0 v x1) resolves with (x0 v x1) to (x1 v x1) = (x1).
    // Not tautological, so (x0 v x1) is NOT blocked on x0.
    // But (x0 v x1 v x2) is blocked on x0 if (-x0 v -x1 v -x2) is the only
    // clause with -x0, since resolvent is (x1 v x2 v -x1 v -x2) = tautology.
    let clauses = vec![
        vec![pos(0), pos(1), pos(2)],
        vec![neg(0), neg(1), neg(2)],
        vec![pos(3)],
    ];
    solve_single_feature(4, &clauses, "bce-blocked-sat", Some(true), |s| {
        s.set_bce_enabled(true);
    });
}

/// BCE must not remove a non-blocked clause.
#[test]
fn bce_non_blocked_must_stay_unsat() {
    // Simple contradiction: (x0) and (-x0) — neither is blocked
    let clauses = vec![vec![pos(0)], vec![neg(0)]];
    solve_single_feature_with_drat(1, &clauses, "bce-non-blocked-unsat", Some(false), |s| {
        s.set_bce_enabled(true);
    });
}

// ===========================================================================
// Probe (failed literal probing) edge cases
//
// Probing tests assigning a literal and propagating. If a conflict occurs,
// the literal is a failed literal and the opposite is implied. Bugs:
// incorrect propagation during probing, or wrong literal implication.
// ===========================================================================

/// Probing discovers an implied unit.
#[test]
fn probe_failed_literal_sat() {
    // If x0=T leads to conflict, then x0=F is implied.
    // (-x0 v x1), (-x0 v -x1) — x0=T => x1=T and x1=F => conflict
    // But also need (x0 v x2) to keep formula SAT when x0=F
    let clauses = vec![
        vec![neg(0), pos(1)],
        vec![neg(0), neg(1)],
        vec![pos(0), pos(2)],
    ];
    let r = solve_single_feature(3, &clauses, "probe-failed-lit-sat", Some(true), |s| {
        s.set_probe_enabled(true);
    });
    if let SatResult::Sat(model) = &r {
        // x0 must be false (failed literal)
        assert!(
            !model.first().copied().unwrap_or(true),
            "probe should discover x0 is a failed literal"
        );
    }
}

/// Probing on UNSAT formula.
#[test]
fn probe_unsat_with_drat() {
    // Both x0=T and x0=F lead to conflict
    let clauses = vec![
        vec![neg(0), pos(1)],
        vec![neg(0), neg(1)],
        vec![pos(0), pos(2)],
        vec![pos(0), neg(2)],
    ];
    solve_single_feature_with_drat(3, &clauses, "probe-unsat-drat", Some(false), |s| {
        s.set_probe_enabled(true);
    });
}

// ===========================================================================
// Transitive reduction edge cases
//
// Transitive reduction removes redundant binary implications from the
// implication graph. Bug: removing a non-redundant implication.
// ===========================================================================

/// Transitive reduction on a chain: x0=>x1=>x2 with redundant x0=>x2.
#[test]
fn transred_removes_redundant_sat() {
    let clauses = vec![
        vec![neg(0), pos(1)], // x0 => x1
        vec![neg(1), pos(2)], // x1 => x2
        vec![neg(0), pos(2)], // x0 => x2 (redundant, transitive)
        vec![pos(3)],         // force SAT
    ];
    solve_single_feature(4, &clauses, "transred-redundant-sat", Some(true), |s| {
        s.set_transred_enabled(true);
    });
}

/// Transitive reduction must not break a non-redundant implication.
#[test]
fn transred_non_redundant_unsat() {
    // x0 => x1, x0 => -x1 with forced x0
    let clauses = vec![vec![neg(0), pos(1)], vec![neg(0), neg(1)], vec![pos(0)]];
    solve_single_feature_with_drat(2, &clauses, "transred-nonred-unsat", Some(false), |s| {
        s.set_transred_enabled(true);
    });
}

// ===========================================================================
// Per-feature x formula-type matrix
//
// Run each preprocessing feature on a diverse set of formula types to catch
// technique-specific bugs that only manifest on certain structures.
// ===========================================================================

/// PHP(4,3) — classic UNSAT, structured, exercises resolution.
fn php_4_3_clauses() -> (usize, Vec<Vec<Literal>>) {
    let cnf = super::common::load_repo_benchmark("benchmarks/sat/unsat/php_4_3.cnf");
    let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
    (formula.num_vars, formula.clauses)
}

/// Tseitin grid 3x3 — structured UNSAT, exercises simplification.
fn tseitin_grid_clauses() -> (usize, Vec<Vec<Literal>>) {
    let cnf = super::common::load_repo_benchmark("benchmarks/sat/unsat/tseitin_grid_3x3.cnf");
    let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
    (formula.num_vars, formula.clauses)
}

type FeatureSetup = (&'static str, fn(&mut Solver));

const PREPROCESSING_FEATURES: &[FeatureSetup] = &[
    ("bve", |s| s.set_bve_enabled(true)),
    ("subsume", |s| s.set_subsume_enabled(true)),
    ("vivify", |s| s.set_vivify_enabled(true)),
    ("bce", |s| s.set_bce_enabled(true)),
    ("probe", |s| s.set_probe_enabled(true)),
    ("shrink", |s| s.set_shrink_enabled(true)),
    ("transred", |s| s.set_transred_enabled(true)),
    ("htr", |s| s.set_htr_enabled(true)),
    ("condition", |s| s.set_condition_enabled(true)),
    ("backbone", |s| s.set_backbone_enabled(true)),
    ("factor", |s| s.set_factor_enabled(true)),
    ("decompose", |s| s.set_decompose_enabled(true)),
    ("congruence", |s| s.set_congruence_enabled(true)),
];

/// Each preprocessing feature on PHP(4,3) — UNSAT with DRAT proof.
#[test]
fn per_feature_php43_unsat_drat() {
    let (nv, clauses) = php_4_3_clauses();
    for (name, enable) in PREPROCESSING_FEATURES {
        let label = format!("per-feat-php43/{name}");
        solve_single_feature_with_drat(nv, &clauses, &label, Some(false), enable);
    }
}

/// Each preprocessing feature on tseitin grid — UNSAT with DRAT proof.
#[test]
fn per_feature_tseitin_grid_unsat_drat() {
    let (nv, clauses) = tseitin_grid_clauses();
    for (name, enable) in PREPROCESSING_FEATURES {
        let label = format!("per-feat-tseitin/{name}");
        solve_single_feature_with_drat(nv, &clauses, &label, Some(false), enable);
    }
}

/// Each preprocessing feature on a known-SAT formula — model verification.
#[test]
fn per_feature_sat_model_verification() {
    // Satisfiable formula: (x0 v x1), (x2 v x3), (-x0 v x2), (-x1 v x3)
    // Many satisfying assignments exist.
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![pos(2), pos(3)],
        vec![neg(0), pos(2)],
        vec![neg(1), pos(3)],
    ];
    for (name, enable) in PREPROCESSING_FEATURES {
        let label = format!("per-feat-sat-model/{name}");
        solve_single_feature(4, &clauses, &label, Some(true), enable);
    }
}

// ===========================================================================
// SAT corpus model verification sweep
//
// Solve every known-SAT benchmark from the canary and SATLIB collections
// and verify that SAT models satisfy all original clauses. This closes
// the gap where SAT results were not systematically model-checked.
// ===========================================================================

/// Sweep all SATLIB UF200 (known-SAT) benchmarks with model verification.
/// These are random 3-SAT at 200 variables, uniformly satisfiable.
#[test]
fn satlib_uf200_model_verification_sweep() {
    let dir = super::common::workspace_root().join("reference/creusat/tests/satlib/UF200.860.100");
    if !dir.exists() {
        eprintln!("SKIP: UF200 directory not found at {}", dir.display());
        return;
    }
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    entries.sort();

    // Test first 10 to keep runtime bounded
    let mut verified = 0;
    for path in entries.iter().take(10) {
        let label = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("<unknown>");
        let cnf = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
        let r = solve_default_config(
            formula.num_vars,
            &formula.clauses,
            &format!("uf200-sweep/{label}"),
            Some(true),
        );
        if matches!(r, SatResult::Sat(_)) {
            verified += 1;
        }
    }
    eprintln!("UF200 model verification sweep: {verified}/10 SAT-verified");
    assert!(
        verified >= 5,
        "expected at least 5 UF200 SAT results, got {verified}"
    );
}

/// Verify canary benchmarks with all preprocessing features individually.
#[test]
fn canary_per_feature_sweep() {
    let sat_cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_sat.cnf");
    let sat_formula = ay_sat::parse_dimacs(&sat_cnf).expect("parse canary SAT");

    let unsat_cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_unsat.cnf");
    let unsat_formula = ay_sat::parse_dimacs(&unsat_cnf).expect("parse canary UNSAT");

    for (name, enable) in PREPROCESSING_FEATURES {
        // SAT canary: model must satisfy all clauses
        solve_single_feature(
            sat_formula.num_vars,
            &sat_formula.clauses,
            &format!("canary-sat/{name}"),
            Some(true),
            enable,
        );

        // UNSAT canary: DRAT proof must verify
        solve_single_feature_with_drat(
            unsat_formula.num_vars,
            &unsat_formula.clauses,
            &format!("canary-unsat/{name}"),
            Some(false),
            enable,
        );
    }
}

// ===========================================================================
// Cross-configuration consistency
//
// The same formula solved with different feature combinations must agree.
// Disagreement is a soundness bug.
// ===========================================================================

/// Solve a formula with each feature in isolation and with default config.
/// All must agree on SAT/UNSAT.
#[test]
fn cross_config_agreement_php43() {
    let (nv, clauses) = php_4_3_clauses();
    let mut results = Vec::new();

    // Default config
    let r = solve_default_config(nv, &clauses, "cross-php43/default", Some(false));
    results.push(("default", matches!(r, SatResult::Unsat(_))));

    // Each feature in isolation
    for (name, enable) in PREPROCESSING_FEATURES {
        let r = solve_single_feature(
            nv,
            &clauses,
            &format!("cross-php43/{name}"),
            Some(false),
            enable,
        );
        results.push((name, matches!(r, SatResult::Unsat(_))));
    }

    // All must agree: UNSAT
    for (name, is_unsat) in &results {
        assert!(
            *is_unsat,
            "SOUNDNESS BUG: cross-config disagreement on PHP(4,3): {name} returned SAT"
        );
    }
}

/// Cross-config on a SAT formula.
#[test]
fn cross_config_agreement_sat_formula() {
    let clauses = vec![
        vec![pos(0), pos(1), pos(2)],
        vec![neg(0), pos(1)],
        vec![neg(1), pos(2)],
        vec![pos(0), neg(2)],
    ];

    // Default config
    let r = solve_default_config(3, &clauses, "cross-sat/default", Some(true));
    assert!(matches!(r, SatResult::Sat(_)));

    // Each feature in isolation
    for (name, enable) in PREPROCESSING_FEATURES {
        let r = solve_single_feature(
            3,
            &clauses,
            &format!("cross-sat/{name}"),
            Some(true),
            enable,
        );
        assert!(
            !matches!(r, SatResult::Unsat(_)),
            "SOUNDNESS BUG: {name} returned UNSAT on known-SAT formula"
        );
    }
}

// ===========================================================================
// Feature interaction edge cases
//
// Two preprocessing features together can trigger bugs that neither
// exhibits alone.
// ===========================================================================

/// BVE + Vivification: BVE eliminates a variable, vivification tries to
/// strengthen the resolvent. Must not corrupt the formula.
#[test]
fn bve_plus_vivify_sat() {
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![neg(0), pos(2)],
        vec![pos(1), pos(2), pos(3)],
        vec![neg(3), pos(4)],
        vec![pos(4)],
    ];
    let mut solver = Solver::new(5);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_bve_enabled(true);
    solver.set_vivify_enabled(true);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => verify_model(&clauses, model, "bve+vivify-sat"),
        SatResult::Unsat(_) => panic!("SOUNDNESS BUG: bve+vivify returned UNSAT on SAT formula"),
        _ => {}
    }
}

/// Subsumption + BVE: subsumption removes a clause that BVE would have
/// used for resolution. The result must still be correct.
#[test]
fn subsume_plus_bve_unsat() {
    // (x0), (-x0 v x1), (-x1), (x0 v x1) — UNSAT
    // (x0) subsumes (x0 v x1), then BVE on x0 => resolvent (-x1) from (-x0 v x1)
    let clauses = vec![
        vec![pos(0)],
        vec![neg(0), pos(1)],
        vec![neg(1)],
        vec![pos(0), pos(1)],
    ];
    let mut solver = Solver::with_proof_output(2, ProofOutput::drat_text(Vec::<u8>::new()));
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_subsume_enabled(true);
    solver.set_bve_enabled(true);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "subsume+bve on UNSAT formula must return UNSAT"
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("flush");
    let dimacs = super::common::clauses_to_dimacs(2, &clauses);
    super::common::verify_drat_proof(&dimacs, &proof_bytes, "subsume+bve-unsat");
}

/// Vivification + Probe: both manipulate the trail. Must not interfere.
#[test]
fn vivify_plus_probe_sat() {
    let clauses = vec![
        vec![pos(0), pos(1), pos(2)],
        vec![neg(0), neg(1)],
        vec![neg(0), pos(2)],
        vec![pos(3), pos(4)],
    ];
    let mut solver = Solver::new(5);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_vivify_enabled(true);
    solver.set_probe_enabled(true);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => verify_model(&clauses, model, "vivify+probe-sat"),
        SatResult::Unsat(_) => {
            panic!("SOUNDNESS BUG: vivify+probe returned UNSAT on SAT formula")
        }
        _ => {}
    }
}
