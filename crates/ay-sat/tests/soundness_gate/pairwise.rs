// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pairwise interaction gates and comprehensive oracle tests.
//!
//! Tests that pairs of inprocessing features together don't cause
//! unsoundness, plus full-stack and CaDiCaL oracle comparison tests.

use ay_sat::{parse_dimacs, ProofOutput, SatResult, Solver};
use ntest::timeout;

use super::common::{
    assert_model_satisfies, disable_all_inprocessing, load_benchmark, run_cadical_oracle,
    sat_result_kind, solve_feature_isolation, solver_all_disabled, try_cadical_binary,
    try_load_benchmark, verify_drat_proof_native, verify_full_stack_unsat_with_native_drat,
    verify_pairwise_unsat_with_native_drat, verify_triple_unsat_with_native_drat, verify_unsat,
    verify_unsat_with_drat, verify_unsat_with_native_drat, GateFeature, OracleResult,
    GATE_BENCHMARKS, ORACLE_SAT_BENCHMARKS, ORACLE_UNSAT_BENCHMARKS,
};
use super::test_common;

// ============================================================================
// Pairwise interaction gates for currently-enabled features
// Tests that two features together don't cause unsoundness.
// ============================================================================

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_vivify_plus_subsume() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_vivify_enabled(true);
    solver.set_subsume_enabled(true);
    verify_unsat(&mut solver, &clauses, "vivify+subsume/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_probe_plus_transred() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_probe_enabled(true);
    solver.set_transred_enabled(true);
    verify_unsat(&mut solver, &clauses, "probe+transred/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_shrink_plus_probe() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_shrink_enabled(true);
    solver.set_probe_enabled(true);
    verify_unsat(&mut solver, &clauses, "shrink+probe/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_shrink_plus_vivify() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_shrink_enabled(true);
    solver.set_vivify_enabled(true);
    verify_unsat(&mut solver, &clauses, "shrink+vivify/longmult15");
}

#[test]
#[timeout(120_000)]
fn gate_shrink_plus_bve() {
    // Keep this interaction gate cheap: long structured UNSAT benchmarks can
    // exceed the timeout with BVE enabled (#3501), which turns this into a
    // timeout flake rather than a soundness check.
    //
    // The formula below is UNSAT and still drives conflict analysis, so both
    // shrink and BVE stay wired through the same solve path.
    let content = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n".to_string();
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_shrink_enabled(true);
    solver.set_bve_enabled(true);
    verify_unsat(&mut solver, &clauses, "shrink+bve/tiny-xor-unsat");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bve_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "bve+congruence/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_htr_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_htr_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "htr+congruence/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bve_plus_bce() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bve_enabled(true);
    solver.set_bce_enabled(true);
    verify_unsat(&mut solver, &clauses, "bve+bce/longmult15");
}

// ============================================================================
// Additional pairwise interaction gates (Part of #3479)
//
// High-risk pairs identified by feature interaction analysis:
// - Pairs involving congruence: congruence uses equivalence merging which
//   interacts with many techniques that modify clause/variable structure.
// - Pairs involving decompose: decompose splits SCC components, techniques
//   referencing cross-component structures may break.
// - Pairs involving sweep: sweep uses kitten probing for equivalences,
//   combining with other simplification can cause stale references.
// ============================================================================

/// congruence + sweep: both use equivalence merging. Congruence discovers
/// equivalences via syntactic gate analysis; sweep discovers them via
/// semantic probing. Combined, they must not double-merge or create
/// stale equivalence edges.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_congruence_plus_sweep() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_congruence_enabled(true);
    solver.set_sweep_enabled(true);
    verify_unsat(&mut solver, &clauses, "congruence+sweep/longmult15");
}

/// decompose + probe: decompose splits into SCC components; probe
/// references the implication graph which may span components.
/// Combined, probing must not reference stale cross-component edges.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_decompose_plus_probe() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_decompose_enabled(true);
    solver.set_probe_enabled(true);
    verify_unsat(&mut solver, &clauses, "decompose+probe/longmult15");
}

/// bve + transred: BVE changes clause structure by resolution; transred
/// depends on the binary implication graph which BVE may modify.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bve_plus_transred() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bve_enabled(true);
    solver.set_transred_enabled(true);
    verify_unsat(&mut solver, &clauses, "bve+transred/longmult15");
}

/// probe + congruence: probing discovers implied units and equivalences;
/// congruence merges variables based on gate structure. Probing may
/// invalidate congruence's variable availability assumptions.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_probe_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_probe_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "probe+congruence/longmult15");
}

/// sweep + vivify: sweep discovers equivalences via kitten probing;
/// vivification strengthens clauses by propagation. Combined, vivification
/// may shorten clauses that sweep depends on for its COI.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_sweep_plus_vivify() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_sweep_enabled(true);
    solver.set_vivify_enabled(true);
    verify_unsat(&mut solver, &clauses, "sweep+vivify/longmult15");
}

/// bce + congruence: BCE removes blocked clauses; congruence assumes
/// clause structure for gate extraction. Removing a blocked clause
/// may invalidate a gate that congruence depends on.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bce_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bce_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "bce+congruence/longmult15");
}

/// factor + bve: factoring merges duplicate literals and strengthens
/// clauses; BVE depends on occurrence counts and clause lengths for
/// elimination decisions. Factor changing clause sizes can alter BVE
/// cost estimates.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_factor_plus_bve() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_factor_enabled(true);
    solver.set_bve_enabled(true);
    verify_unsat(&mut solver, &clauses, "factor+bve/longmult15");
}

/// subsume + congruence: subsumption removes subsumed clauses; congruence
/// uses clause structure for gate analysis. Removing a subsumed clause
/// may change the gate pattern congruence depends on.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_subsume_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_subsume_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "subsume+congruence/longmult15");
}

/// factor + congruence: factoring changes clause structure; congruence
/// depends on clause patterns for gate extraction. This pair tests
/// that factored clauses still produce correct congruence analysis.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_factor_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_factor_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "factor+congruence/longmult15");
}

/// decompose + congruence: decompose splits SCC components; congruence
/// merges equivalences. This tests that component splitting does not
/// produce stale congruence edges spanning separated components.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_decompose_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_decompose_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "decompose+congruence/longmult15");
}

/// condition + congruence: conditioning (GBCE) adds conditional
/// binary clauses; congruence uses clause patterns for gate analysis.
/// GBCE-generated clauses may create new gate patterns for congruence.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_condition_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_condition_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "condition+congruence/longmult15");
}

/// backbone + probe: backbone detection and failed literal probing both
/// manipulate the assignment trail. Combined, they must not interfere
/// with each other's trail assumptions.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_backbone_plus_probe() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_backbone_enabled(true);
    solver.set_probe_enabled(true);
    verify_unsat(&mut solver, &clauses, "backbone+probe/longmult15");
}

// ============================================================================
// Triple interaction gates (Part of #3479)
//
// Three features together can trigger bugs that no pair exhibits.
// These test the highest-risk triples where all three techniques
// interact with shared data structures.
// ============================================================================

/// bve + congruence + sweep: BVE eliminates variables, congruence merges
/// equivalences via gates, sweep discovers equivalences via probing.
/// All three modify the variable/clause universe. This is the highest-risk
/// triple because each technique can invalidate another's invariants.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bve_congruence_sweep() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_sweep_enabled(true);
    verify_unsat(&mut solver, &clauses, "bve+congruence+sweep/longmult15");
}

/// bve + subsume + vivify: BVE eliminates variables, subsumption removes
/// subsumed clauses, vivification strengthens clauses. All three modify
/// clause structure and interact through occurrence lists.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bve_subsume_vivify() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bve_enabled(true);
    solver.set_subsume_enabled(true);
    solver.set_vivify_enabled(true);
    verify_unsat(&mut solver, &clauses, "bve+subsume+vivify/longmult15");
}

/// probe + congruence + decompose: probing discovers units, congruence
/// merges gates, decompose splits components. All three interact with
/// the implication graph and variable equivalence tracking.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_probe_congruence_decompose() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_probe_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    verify_unsat(
        &mut solver,
        &clauses,
        "probe+congruence+decompose/longmult15",
    );
}

// ============================================================================
// HTR isolation + DRAT proof verification (#3971)
// After the collect_level0_garbage() fix, HTR must produce correct results
// and valid DRAT proofs on all gate benchmarks.
// ============================================================================

#[test]
#[timeout(120_000)]
fn gate_htr_isolation() {
    for name in GATE_BENCHMARKS {
        let Some(content) = try_load_benchmark(name) else {
            continue;
        };
        let (mut solver, clauses) = solver_all_disabled(&content);
        solver.set_htr_enabled(true);
        verify_unsat(&mut solver, &clauses, &format!("htr-isolation/{name}"));
    }
}

#[test]
#[timeout(120_000)]
fn gate_htr_drat_proof_verification() {
    // Use only barrel6 (the smaller gate benchmark) for proof-mode DRAT
    // verification. longmult15 + DRAT + HTR exceeds 300s in debug mode,
    // turning this into a timeout flake rather than a soundness check
    // (same pattern as gate_shrink_plus_bve / #3501). HTR isolation
    // already covers both benchmarks without proof overhead.
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_unsat_with_drat(GateFeature::Htr, &content, "htr-drat/barrel6");
}

/// DRAT proof verification for techniques previously excluded by proof_compatible() (#4447).
/// Each technique is a separate test to avoid cumulative timeout in debug mode.
/// Uses barrel6 (248 vars), same benchmark as gate_htr_drat_proof_verification.
#[test]
#[timeout(120_000)]
fn gate_condition_drat_proof_verification() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_unsat_with_drat(
        GateFeature::Condition,
        &content,
        "conditioning-drat/barrel6",
    );
}

/// Congruence is DRAT-open since 2026-07-10 (registry `Congruence { drat:
/// true }`, wf_ff5991a1: complementary-contradiction-edge skip + vivify
/// garbage-husk exclusion; externally verified via dpr-trim + cake_lpr on
/// congruence-active UNSAT runs; kill-switch AY_AB_DRAT_SUBST=0). The
/// request must be honored and the emitted proof must still verify —
/// barrel6 is the instance whose FINALIZE_SAT_FAIL motivated the old clamp.
#[test]
#[timeout(300_000)]
fn gate_congruence_drat_request_is_honored_barrel6() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    let formula = parse_dimacs(&content).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    disable_all_inprocessing(&mut solver);
    solver.set_congruence_enabled(true);
    assert!(
        solver.inprocessing_feature_profile().congruence,
        "DRAT proof mode must honor congruence requests (registry drat=true \
         since 2026-07-10; kill-switch AY_AB_DRAT_SUBST=0)"
    );
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "barrel6 must be UNSAT");
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    verify_drat_proof_native(&content, &proof_bytes, "congruence-drat-honored/barrel6");
}

// Sweep DRAT test removed (#7037): kitten can't produce DRAT proof steps,
// and rebuild-per-probe makes sweep-only + DRAT too slow for barrel6.
// Sweep correctness is verified by the #6999 feature isolation tests and
// the full pairwise oracle comparison below.

/// Decompose is DRAT-open since 2026-07-09 (registry `Decompose { drat: true }`,
/// externally verified via dpr-trim + cake_lpr; kill-switch AY_AB_DRAT_SUBST=0).
/// The request must be honored and the emitted proof must still verify.
#[test]
#[timeout(120_000)]
fn gate_decompose_drat_request_is_honored() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    let formula = parse_dimacs(&content).expect("parse");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    disable_all_inprocessing(&mut solver);
    solver.set_decompose_enabled(true);
    assert!(
        solver.inprocessing_feature_profile().decompose,
        "DRAT proof mode must honor decompose requests (registry drat=true \
         since 2026-07-09; kill-switch AY_AB_DRAT_SUBST=0)"
    );
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "barrel6 must be UNSAT");
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    verify_drat_proof_native(&content, &proof_bytes, "decompose-drat-honored/barrel6");
}

/// HTR oracle: verify AY+HTR agrees with CaDiCaL on SAT/UNSAT benchmarks.
/// Catches wrong-UNSAT on SAT instances (the original #3873 failure mode).
#[test]
#[timeout(300_000)]
fn gate_htr_oracle_comparison() {
    if try_cadical_binary().is_none() {
        eprintln!("SKIP: CaDiCaL binary not available for oracle comparison");
        return;
    }
    for benchmark in ORACLE_SAT_BENCHMARKS {
        let path = test_common::workspace_root().join(benchmark.rel_path);
        let Some(cnf) = test_common::load_optional_benchmark(&path) else {
            continue;
        };
        let oracle = run_cadical_oracle(&cnf, &format!("htr_sat_{}", benchmark.name));
        assert_eq!(
            oracle,
            OracleResult::Sat,
            "oracle baseline SAT for {}",
            benchmark.name
        );
        let (result, clauses, _) = solve_feature_isolation(GateFeature::Htr, &cnf);
        let actual = sat_result_kind(&result);
        assert_eq!(
            actual, oracle,
            "SOUNDNESS GATE [htr/{}]: AY+HTR vs CaDiCaL mismatch on SAT benchmark",
            benchmark.name
        );
        if let SatResult::Sat(model) = &result {
            assert_model_satisfies(&clauses, model, &format!("htr-oracle/{}", benchmark.name));
        }
    }

    for benchmark in ORACLE_UNSAT_BENCHMARKS {
        let path = test_common::workspace_root().join(benchmark.rel_path);
        let Some(cnf) = test_common::load_optional_benchmark(&path) else {
            continue;
        };
        let oracle = run_cadical_oracle(&cnf, &format!("htr_unsat_{}", benchmark.name));
        assert_eq!(
            oracle,
            OracleResult::Unsat,
            "oracle baseline UNSAT for {}",
            benchmark.name
        );
        let (result, _, _) = solve_feature_isolation(GateFeature::Htr, &cnf);
        let actual = sat_result_kind(&result);
        assert_eq!(
            actual, oracle,
            "SOUNDNESS GATE [htr/{}]: AY+HTR vs CaDiCaL mismatch on UNSAT benchmark",
            benchmark.name
        );
    }
}

// ============================================================================
// Full-stack gate: all currently-enabled features together
// This is what into_solver() produces in DIMACS mode.
// ============================================================================

// All default DIMACS features on 2 benchmarks.
#[test]
#[timeout(300_000)]
fn gate_all_enabled_features() {
    for name in GATE_BENCHMARKS {
        let Some(content) = try_load_benchmark(name) else {
            continue;
        };
        let formula = parse_dimacs(&content).expect("parse");
        let original_clauses = formula.clauses.clone();
        let mut solver = formula.into_solver();
        verify_unsat(
            &mut solver,
            &original_clauses,
            &format!("all-enabled/{name}"),
        );
    }
}

// ============================================================================
// Full-stack DRAT proof verification with default proof-safe features (#7913)
// Complements gate_all_enabled_features above by also verifying the DRAT proof.
// Uses barrel6 (248 vars) to keep proof-mode overhead within timeout.
// ============================================================================

#[test]
#[timeout(300_000)]
fn gate_all_enabled_features_drat_barrel6() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_full_stack_unsat_with_native_drat(&content, "all-enabled-drat/barrel6");
}

// ============================================================================
// Oracle comparison: AY vs CaDiCaL on expanded SAT/UNSAT coverage.
// DRAT stays in the UNSAT matrix only for the cheap subset; larger proof traces
// are covered by the focused per-feature DRAT tests above.
// ============================================================================

type OracleCase = (super::common::OracleBenchmark, String, OracleResult);

fn load_sat_oracle_cases() -> Vec<OracleCase> {
    ORACLE_SAT_BENCHMARKS
        .iter()
        .filter_map(|benchmark| {
            let path = test_common::workspace_root().join(benchmark.rel_path);
            let cnf = test_common::load_optional_benchmark(&path)?;
            let oracle = run_cadical_oracle(&cnf, &format!("sat_{}", benchmark.name));
            assert_eq!(
                oracle,
                OracleResult::Sat,
                "oracle baseline changed: expected SAT for {}",
                benchmark.name
            );
            Some((*benchmark, cnf, oracle))
        })
        .collect()
}

fn load_unsat_oracle_cases() -> Vec<OracleCase> {
    ORACLE_UNSAT_BENCHMARKS
        .iter()
        .filter_map(|benchmark| {
            let path = test_common::workspace_root().join(benchmark.rel_path);
            let cnf = test_common::load_optional_benchmark(&path)?;
            let oracle = run_cadical_oracle(&cnf, &format!("unsat_{}", benchmark.name));
            assert_eq!(
                oracle,
                OracleResult::Unsat,
                "oracle baseline changed: expected UNSAT for {}",
                benchmark.name
            );
            Some((*benchmark, cnf, oracle))
        })
        .collect()
}

fn run_sat_oracle_matrix(sat_cases: &[OracleCase]) {
    for feature in GateFeature::ALL {
        for (benchmark, cnf, expected) in sat_cases {
            let label = format!("{}/{}", feature.label(), benchmark.name);
            let (result, clauses, _) = solve_feature_isolation(feature, cnf);
            let actual = sat_result_kind(&result);
            assert_eq!(
                actual, *expected,
                "SOUNDNESS GATE [{label}]: AY vs CaDiCaL mismatch on SAT benchmark"
            );
            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, &label);
            }
        }
    }
}

fn run_unsat_oracle_matrix(unsat_cases: &[OracleCase]) {
    for feature in GateFeature::ALL {
        for (benchmark, cnf, expected) in unsat_cases {
            let label = format!("{}/{}", feature.label(), benchmark.name);
            let (result, clauses, _) = solve_feature_isolation(feature, cnf);
            let actual = sat_result_kind(&result);
            assert_eq!(
                actual, *expected,
                "SOUNDNESS GATE [{label}]: AY vs CaDiCaL mismatch on UNSAT benchmark"
            );

            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, &label);
            }

            // Native DRAT verification (ay-drat-check, in-process) for
            // matrix_drat benchmarks (#7913). Uses the hermetic in-process
            // checker (no external drat-trim required). In debug builds,
            // the solver's inline forward checker also verifies every
            // derived clause is RUP-implied during the proof-mode re-solve.
            // Regression coverage for #7929 (forward checker assertion
            // failure fixed by removing BVE backward subsumption in #7917).
            if benchmark.matrix_drat
                && feature.drat_verified()
                && matches!(result, SatResult::Unsat(_))
            {
                verify_unsat_with_native_drat(feature, cnf, &format!("native_drat_{label}"));
            }
        }
    }
}

#[test]
fn gate_unsat_oracle_matrix_requires_native_drat_coverage() {
    let uncovered: Vec<_> = ORACLE_UNSAT_BENCHMARKS
        .iter()
        .filter(|benchmark| !benchmark.matrix_drat)
        .map(|benchmark| benchmark.name)
        .collect();
    assert!(
        uncovered.is_empty(),
        "SOUNDNESS GATE [native-drat-matrix-coverage]: every UNSAT oracle benchmark must be re-solved with native DRAT checking; uncovered={uncovered:?}"
    );

    let unexpected_unverified_features: Vec<_> = GateFeature::ALL
        .iter()
        .copied()
        .filter(|feature| {
            !feature.drat_verified()
                && !matches!(
                    feature,
                    GateFeature::Sweep | GateFeature::Congruence | GateFeature::Decompose
                )
        })
        .map(GateFeature::label)
        .collect();
    assert!(
        unexpected_unverified_features.is_empty(),
        "SOUNDNESS GATE [native-drat-matrix-coverage]: new non-sweep DRAT verification gaps must not be silently skipped; features={unexpected_unverified_features:?}"
    );
}

#[test]
// 14 features x 7 UNSAT benchmarks + 56 native DRAT proof-mode re-solves.
// Debug-mode forward checker makes proof solves ~5x slower. 600s needed.
#[timeout(600_000)]
fn gate_isolation_oracle_model_matrix_sat() {
    if try_cadical_binary().is_none() {
        eprintln!("SKIP: CaDiCaL binary not available for SAT oracle matrix");
        return;
    }
    let sat_cases = load_sat_oracle_cases();
    run_sat_oracle_matrix(&sat_cases);
}

// 14 features x 7 UNSAT benchmarks + 56 native DRAT proof-mode re-solves.
// Debug-mode forward checker makes proof solves ~5x slower. 600s needed.
#[test]
#[timeout(600_000)]
fn gate_isolation_oracle_model_and_drat_matrix_unsat() {
    if try_cadical_binary().is_none() {
        eprintln!("SKIP: CaDiCaL binary not available for UNSAT oracle matrix");
        return;
    }
    let unsat_cases = load_unsat_oracle_cases();
    run_unsat_oracle_matrix(&unsat_cases);
}

// ============================================================================
// Pairwise native DRAT proof verification (#7913)
// Verifies that pairwise feature combinations produce valid DRAT proofs
// using the in-process ay-drat-check (no external drat-trim required).
// Uses barrel6 (248 vars) to keep proof-mode solves within timeout.
// ============================================================================

/// Pairs of features tested by the pairwise interaction gates above.
/// Each pair is verified to produce a valid DRAT proof on barrel6.
///
/// Coverage: 9 of 91 possible pairs (14 choose 2).
/// Congruence, decompose, and sweep pairs are omitted from DRAT proof coverage
/// while proof mode clamps or skips those techniques.
const PAIRWISE_DRAT_PAIRS: &[(GateFeature, GateFeature)] = &[
    // Original pairs
    (GateFeature::Vivify, GateFeature::Subsume),
    (GateFeature::Probe, GateFeature::Transred),
    (GateFeature::Shrink, GateFeature::Probe),
    (GateFeature::Shrink, GateFeature::Vivify),
    (GateFeature::Shrink, GateFeature::Bve),
    (GateFeature::Bve, GateFeature::Bce),
    // #3479: other high-risk pairs
    (GateFeature::Bve, GateFeature::Transred),
    (GateFeature::Factor, GateFeature::Bve),
    (GateFeature::Backbone, GateFeature::Probe),
];

/// Triple combinations tested by triple interaction gates above.
/// Each triple is verified to produce a valid DRAT proof on barrel6.
const TRIPLE_DRAT_TRIPLES: &[(GateFeature, GateFeature, GateFeature)] =
    &[(GateFeature::Bve, GateFeature::Subsume, GateFeature::Vivify)];

#[test]
#[timeout(600_000)]
fn gate_pairwise_native_drat_barrel6() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    for &(feat_a, feat_b) in PAIRWISE_DRAT_PAIRS {
        let label = format!(
            "pairwise-native-drat/{}+{}/barrel6",
            feat_a.label(),
            feat_b.label()
        );
        verify_pairwise_unsat_with_native_drat(feat_a, feat_b, &content, &label);
    }
}

/// Triple DRAT proof verification (#3479).
/// Verifies that triple feature combinations produce valid DRAT proofs
/// using the in-process ay-drat-check. Uses barrel6 (248 vars).
#[test]
#[timeout(600_000)]
fn gate_triple_native_drat_barrel6() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    for &(feat_a, feat_b, feat_c) in TRIPLE_DRAT_TRIPLES {
        let label = format!(
            "triple-native-drat/{}+{}+{}/barrel6",
            feat_a.label(),
            feat_b.label(),
            feat_c.label()
        );
        verify_triple_unsat_with_native_drat(feat_a, feat_b, feat_c, &content, &label);
    }
}
