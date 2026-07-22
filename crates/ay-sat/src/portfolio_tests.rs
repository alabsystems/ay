// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::dimacs::parse_str;
use crate::features::SatFeatures;
use crate::literal::{Literal, Variable};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

#[test]
fn test_portfolio_sat_simple() {
    let cnf = "p cnf 3 2\n1 2 0\n-1 3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let portfolio = PortfolioSolver::new(2);
    let result = portfolio.solve(&formula);

    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_portfolio_unsat_simple() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let portfolio = PortfolioSolver::new(2);
    let result = portfolio.solve(&formula);

    assert!(result.is_unsat());
}

#[test]
fn test_portfolio_unsat_proof_certificate_available() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let mut portfolio = PortfolioSolver::new(2);
    portfolio.set_proof_mode(true);

    // Use solve_with_proof_bytes() to get forward DRAT proof (#8428).
    // Forward DRAT captures all derived clauses including those from
    // BCP at level 0, unlike backward reconstruction which may miss them.
    let (result, proof_bytes) = portfolio.solve_with_proof_bytes(&formula);

    assert!(result.is_unsat(), "expected UNSAT, got {result:?}");

    let bytes = proof_bytes.expect("proof_mode UNSAT should produce raw DRAT proof bytes");
    assert!(
        !bytes.is_empty(),
        "forward DRAT proof bytes from portfolio UNSAT should be non-empty"
    );

    // Verify the proof ends with the empty clause deletion marker "0\n"
    let proof_text = String::from_utf8_lossy(&bytes);
    assert!(
        proof_text.ends_with("0\n"),
        "DRAT proof should end with empty clause: {proof_text:?}"
    );
}

#[test]
fn test_clause_share_bus_filters_and_skips_origin_worker() {
    let bus = ClauseShareBus::default();
    let a = pos(0);
    let b = pos(1);

    assert!(bus.export(0, &[b, a], 2));
    assert!(!bus.export(0, &[a, b], 4), "LBD > 3 is not shared");
    assert!(
        !bus.export(0, &[a, a.negated()], 1),
        "tautological clauses are not shared"
    );

    let mut cursor = 0;
    assert!(
        bus.import_batch(0, &mut cursor).is_empty(),
        "workers must not import their own exported clauses"
    );

    assert!(bus.export(1, &[b, a], 3));
    let imported = bus.import_batch(0, &mut cursor);
    assert_eq!(imported, vec![vec![a, b]]);
}

#[test]
fn test_clause_share_bus_retention_is_bounded() {
    let bus = ClauseShareBus {
        max_stored: 2,
        ..Default::default()
    };

    assert!(bus.export(0, &[pos(0)], 1));
    assert!(bus.export(1, &[pos(1)], 1));
    assert!(bus.export(2, &[pos(2)], 1));

    let mut cursor = 0;
    let imported = bus.import_batch(9, &mut cursor);
    assert_eq!(imported, vec![vec![pos(1)], vec![pos(2)]]);
}

#[test]
fn test_portfolio_strategies() {
    let strategies = Strategy::all();
    assert_eq!(strategies.len(), 7);
    // The Equiticks arm carries the equal-effort stable-budget config plus
    // the progress gate (captures 3ef7fa06/4c3001f8 on the parallel track).
    assert!(Strategy::Equiticks.to_config().mode_equiticks);
    assert!(Strategy::Equiticks.to_config().mode_eqt_progress);
    assert!(!Strategy::VsidsLuby.to_config().mode_equiticks);
    assert!(!Strategy::VsidsLuby.to_config().mode_eqt_progress);

    // BVE is no longer part of the conservative portfolio baseline; keep it
    // confined to the BVE-focused strategy until reconstruction is sound.
    assert!(!Strategy::VsidsLuby.to_config().features.bve);
    assert!(!Strategy::VsidsGlucose.to_config().features.bve);
    assert!(!Strategy::AggressiveInprocessing.to_config().features.bve);
    assert!(Strategy::BveFocused.to_config().features.bve);
    // BVE disabled in conservative and probe-focused strategies
    assert!(!Strategy::Conservative.to_config().features.bve);
    assert!(!Strategy::ProbeFocused.to_config().features.bve);

    // Factorization enabled in general-purpose strategies (reconstruction removed, #3373 fixed)
    assert!(Strategy::VsidsLuby.to_config().features.factor);
    assert!(Strategy::VsidsGlucose.to_config().features.factor);
    assert!(Strategy::AggressiveInprocessing.to_config().features.factor);
    assert!(Strategy::BveFocused.to_config().features.factor);

    // #3900: conditioning and congruence disabled in Conservative
    let conservative = Strategy::Conservative.to_config();
    assert!(!conservative.features.condition);
    assert!(!conservative.features.congruence);
    assert!(!conservative.features.transred);
    assert!(!conservative.features.decompose);
    assert!(!conservative.features.hbr);
    // Conditioning OFF in general-purpose strategies (#8190: CaDiCaL condition=0)
    assert!(!Strategy::VsidsLuby.to_config().features.condition);
    assert!(!Strategy::VsidsGlucose.to_config().features.congruence);
    assert!(Strategy::VsidsLuby.to_config().features.transred);
    assert!(!Strategy::VsidsGlucose.to_config().features.decompose);
    assert!(
        !Strategy::AggressiveInprocessing
            .to_config()
            .features
            .condition
    );
    assert!(
        !Strategy::AggressiveInprocessing
            .to_config()
            .features
            .congruence
    );

    let probe_focused = Strategy::ProbeFocused.to_config();
    assert!(probe_focused.features.probe);
    assert!(probe_focused.features.subsume);
    assert!(probe_focused.features.hbr);
    assert!(!probe_focused.features.transred);
    assert!(!probe_focused.features.decompose);

    let bve_focused = Strategy::BveFocused.to_config();
    assert!(bve_focused.features.bve);
    assert!(bve_focused.features.gate);
    assert!(bve_focused.features.condition);
    assert!(!bve_focused.features.transred);
    assert!(!bve_focused.features.decompose);
}

#[test]
fn test_portfolio_recommended_threads() {
    // 1 thread should give 1 strategy
    let s1 = Strategy::recommended(1);
    assert_eq!(s1.len(), 1);

    // 4 threads should give 4 strategies
    let s4 = Strategy::recommended(4);
    assert_eq!(s4.len(), 4);

    // 8 threads: recommended() returns at most 7 base strategies (incl the
    // Equiticks arm). Extension to 8 threads is handled by
    // strategies_to_configs() (#8584).
    let s8 = Strategy::recommended(8);
    assert_eq!(s8.len(), 7);
}

/// Verify that strategies_to_configs generates the correct number of
/// configs for thread counts beyond the base 6 (#8584).
#[test]
fn test_portfolio_extended_configs_count() {
    let base = Strategy::all();
    let configs_8 = strategies_to_configs(base.clone(), 8);
    assert_eq!(configs_8.len(), 8, "8 threads should produce 8 configs");

    let configs_16 = strategies_to_configs(base, 16);
    assert_eq!(configs_16.len(), 16, "16 threads should produce 16 configs");

    // 4 threads, 6 base strategies: should truncate base, not extend
    // (strategies_to_configs only extends, it relies on caller to pass
    // correct number of strategies)
    let four_strats = Strategy::recommended(4);
    let configs_4 = strategies_to_configs(four_strats, 4);
    assert_eq!(configs_4.len(), 4, "4 threads should produce 4 configs");
}

/// Verify that extended configs are structurally diverse — not just
/// seed-different copies of the base strategies (#8584).
#[test]
fn test_portfolio_extended_configs_diverse() {
    let base = Strategy::all();
    let configs = strategies_to_configs(base, 16);

    // Each config should have a unique seed.
    let seeds: Vec<u64> = configs.iter().map(|c| c.seed).collect();
    for (i, s) in seeds.iter().enumerate() {
        assert_eq!(*s, i as u64, "config {i} should have seed {i}");
    }

    // Extended configs (6..16) must differ structurally from every base config.
    // Check that each extended config differs in at least one non-seed field
    // from the base config at the same index mod 6 (which was the old behavior).
    for ext_idx in 6..16 {
        let ext = &configs[ext_idx];
        let old_base_idx = ext_idx % 6;
        let base_config = &configs[old_base_idx];

        let features_differ = ext.features != base_config.features;
        let restart_differs = ext.glucose_restarts != base_config.glucose_restarts;
        let chrono_differs = ext.chrono_enabled != base_config.chrono_enabled;
        let phase_differs = ext.initial_phase != base_config.initial_phase;
        let mab_differs = ext.branch_selector_ucb1 != base_config.branch_selector_ucb1;
        let stable_differs = ext.stable_only != base_config.stable_only;
        let restart_base_differs = ext.restart_base != base_config.restart_base;
        let random_freq_differs = ext.random_var_freq != base_config.random_var_freq;
        let stable_init_differs = ext.stable_phase_init != base_config.stable_phase_init;

        let structurally_different = features_differ
            || restart_differs
            || chrono_differs
            || phase_differs
            || mab_differs
            || stable_differs
            || restart_base_differs
            || random_freq_differs
            || stable_init_differs;

        assert!(
            structurally_different,
            "extended config {ext_idx} must differ structurally from base config \
             {old_base_idx} (the old duplication target)"
        );
    }
}

/// Verify that the 9 extended templates are pairwise distinct (#8584).
#[test]
fn test_portfolio_extended_templates_pairwise_distinct() {
    let templates: Vec<SolverConfig> = (0..NUM_EXTENDED_TEMPLATES).map(extended_template).collect();

    for i in 0..templates.len() {
        for j in (i + 1)..templates.len() {
            let a = &templates[i];
            let b = &templates[j];

            // At least one structural field must differ (ignoring seed which
            // is set by the caller).
            let same = a.features == b.features
                && a.glucose_restarts == b.glucose_restarts
                && a.chrono_enabled == b.chrono_enabled
                && a.initial_phase == b.initial_phase
                && a.branch_selector_ucb1 == b.branch_selector_ucb1
                && a.stable_only == b.stable_only
                && a.restart_base == b.restart_base
                && a.random_var_freq == b.random_var_freq
                && a.stable_phase_init == b.stable_phase_init
                && a.chrono_reuse_trail == b.chrono_reuse_trail;

            assert!(
                !same,
                "extended templates {i} and {j} must be structurally distinct"
            );
        }
    }
}

#[test]
fn test_portfolio_single_thread_fallback() {
    let cnf = "p cnf 3 3\n1 2 0\n-1 2 0\n-2 3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    // Single thread should work
    let portfolio = PortfolioSolver::new(1);
    let result = portfolio.solve(&formula);

    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_portfolio_with_custom_config() {
    let cnf = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let config = SolverConfig {
        features: crate::InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: false,
            vivify: false,
            subsume: false,
            probe: false,
            bve: false,
            bce: false,
            condition: false,
            decompose: false,
            factor: false,
            sbva: false,
            transred: false,
            htr: false,
            gate: false,
            congruence: false,
            sweep: false,
            backbone: false,
            symmetry: false,
            reorder: false,
            cce: false,
        },
        glucose_restarts: false,
        chrono_enabled: false,
        initial_phase: Some(true),
        branch_selector_ucb1: false,
        seed: 42,
        ..Default::default()
    };

    let portfolio = PortfolioSolver::new(1).with_configs(vec![config]);
    let result = portfolio.solve(&formula);

    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_portfolio_worker_solver_wires_shared_interrupt_flag() {
    let terminate = Arc::new(AtomicBool::new(true));
    let config = SolverConfig::default();
    let mut solver = create_portfolio_worker_solver(2, 1, &config, false, Arc::clone(&terminate));
    solver.add_clause(vec![pos(0), pos(1)]);

    let result = solver.solve_interruptible(|| false).into_inner();

    assert!(
        matches!(result, SatResult::Unknown),
        "pre-set portfolio interrupt flag should stop before CDCL, got {result:?}"
    );
    assert_eq!(
        solver.last_unknown_reason(),
        Some(crate::solver::SatUnknownReason::Interrupted),
        "portfolio worker interrupt should use the shared solver interrupt side channel"
    );
}

/// Test: portfolio UNSAT with LRAT output verified by built-in LRAT checker (#8428).
///
/// Solves a non-trivial UNSAT formula (all 8 sign combinations of 3 variables)
/// with proof mode enabled, extracts the forward LRAT proof bytes from the
/// winning solver thread, parses them, and feeds each step to the `LratChecker`
/// to verify that every derived clause has a valid RUP chain. This is the
/// acceptance criterion for #8428: proof file output from portfolio solving.
#[test]
fn test_portfolio_proof_verified_by_lrat_checker() {
    use crate::lrat_checker::LratChecker;

    // All 8 sign combinations of 3 variables: always UNSAT.
    let cnf = "\
        p cnf 3 8\n\
        1 2 3 0\n\
        1 2 -3 0\n\
        1 -2 3 0\n\
        1 -2 -3 0\n\
        -1 2 3 0\n\
        -1 2 -3 0\n\
        -1 -2 3 0\n\
        -1 -2 -3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let mut portfolio = PortfolioSolver::new(2);
    portfolio.set_proof_mode(true);
    let (result, proof_bytes) = portfolio.solve_with_proof_bytes(&formula);

    assert!(result.is_unsat(), "expected UNSAT, got {result:?}");
    let bytes = proof_bytes.expect("proof_mode UNSAT must produce raw LRAT proof bytes");
    assert!(!bytes.is_empty(), "LRAT proof bytes must be non-empty");

    let proof_text = String::from_utf8(bytes).expect("LRAT proof must be valid UTF-8");

    // Parse LRAT and verify with LratChecker.
    let mut checker = LratChecker::new(formula.num_vars);

    // Add original clauses (1-indexed IDs matching LRAT convention).
    for (i, clause) in formula.clauses.iter().enumerate() {
        let lits: Vec<Literal> = clause.clone();
        checker.add_original((i + 1) as u64, &lits);
    }

    let mut derived_empty_clause = false;
    for line in proof_text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with("d ") {
            // Deletion line: "d <id1> <id2> ... 0"
            let tokens: Vec<&str> = line.split_whitespace().skip(1).collect();
            for tok in tokens {
                if tok == "0" {
                    break;
                }
                let id: u64 = tok.parse().expect("deletion ID must parse");
                checker.delete(id);
            }
            continue;
        }
        // Addition line: "<id> <lit1> ... 0 <hint1> ... 0"
        let tokens: Vec<&str> = line.split_whitespace().collect();
        assert!(!tokens.is_empty(), "non-empty LRAT line must have tokens");

        let clause_id: u64 = tokens[0].parse().expect("clause ID must parse");

        // Parse literals until first "0".
        let mut lits = Vec::new();
        let mut idx = 1;
        while idx < tokens.len() && tokens[idx] != "0" {
            let dimacs_lit: i32 = tokens[idx].parse().expect("literal must parse");
            let var = Variable::new(dimacs_lit.unsigned_abs() - 1);
            let lit = if dimacs_lit > 0 {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            lits.push(lit);
            idx += 1;
        }
        idx += 1; // skip the "0" terminator

        // Parse hints until second "0".
        let mut hints = Vec::new();
        while idx < tokens.len() && tokens[idx] != "0" {
            let hint: u64 = tokens[idx].parse().expect("hint must parse");
            hints.push(hint);
            idx += 1;
        }

        // Verify the derived clause via the LRAT checker.
        checker.add_derived(clause_id, &lits, &hints);

        if lits.is_empty() {
            derived_empty_clause = true;
        }
    }

    assert!(
        derived_empty_clause,
        "LRAT proof must derive the empty clause for UNSAT"
    );
    assert_eq!(
        checker.failures(),
        0,
        "LRAT checker must report zero failures"
    );
}

/// Test: portfolio proof output works with a single thread (non-parallel path).
///
/// Ensures proof mode works correctly in the `num_threads == 1` fast path
/// which bypasses thread spawning (#8428).
#[test]
fn test_portfolio_proof_single_thread_verified() {
    use crate::lrat_checker::LratChecker;

    let cnf = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let mut portfolio = PortfolioSolver::new(1);
    portfolio.set_proof_mode(true);
    let (result, proof_bytes) = portfolio.solve_with_proof_bytes(&formula);

    assert!(result.is_unsat(), "expected UNSAT, got {result:?}");
    let bytes = proof_bytes.expect("proof_mode UNSAT must produce raw LRAT proof bytes");
    let proof_text = String::from_utf8(bytes).expect("LRAT proof must be valid UTF-8");

    let mut checker = LratChecker::new(formula.num_vars);
    for (i, clause) in formula.clauses.iter().enumerate() {
        checker.add_original((i + 1) as u64, &clause.clone());
    }

    let mut derived_empty_clause = false;
    for line in proof_text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with("d ") {
            let tokens: Vec<&str> = line.split_whitespace().skip(1).collect();
            for tok in tokens {
                if tok == "0" {
                    break;
                }
                let id: u64 = tok.parse().expect("deletion ID must parse");
                checker.delete(id);
            }
            continue;
        }
        let tokens: Vec<&str> = line.split_whitespace().collect();
        let clause_id: u64 = tokens[0].parse().expect("clause ID must parse");
        let mut lits = Vec::new();
        let mut idx = 1;
        while idx < tokens.len() && tokens[idx] != "0" {
            let dimacs_lit: i32 = tokens[idx].parse().expect("literal must parse");
            let var = Variable::new(dimacs_lit.unsigned_abs() - 1);
            let lit = if dimacs_lit > 0 {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            lits.push(lit);
            idx += 1;
        }
        idx += 1;
        let mut hints = Vec::new();
        while idx < tokens.len() && tokens[idx] != "0" {
            let hint: u64 = tokens[idx].parse().expect("hint must parse");
            hints.push(hint);
            idx += 1;
        }
        checker.add_derived(clause_id, &lits, &hints);
        if lits.is_empty() {
            derived_empty_clause = true;
        }
    }

    assert!(
        derived_empty_clause,
        "LRAT proof must derive the empty clause"
    );
    assert_eq!(
        checker.failures(),
        0,
        "LRAT checker must report zero failures"
    );
}

// --- Instance-aware algorithm selection tests ---

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

#[test]
fn test_algo_select_random3sat_prioritizes_bve() {
    // Build a random-3-SAT-like feature profile.
    let num_vars = 2000;
    let clauses: Vec<Vec<Literal>> = (0..8000)
        .map(|i| {
            let v0 = (i * 3) as u32 % num_vars as u32;
            let v1 = (i * 3 + 1) as u32 % num_vars as u32;
            let v2 = (i * 3 + 2) as u32 % num_vars as u32;
            vec![pos(v0), neg(v1), pos(v2)]
        })
        .collect();
    let features = SatFeatures::extract(num_vars, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::BveFocused);
}

#[test]
fn test_algo_select_structured_prioritizes_aggressive() {
    // Mostly binary clauses -> structured instance.
    let num_vars = 2000;
    let clauses: Vec<Vec<Literal>> = (0..4000)
        .map(|i| {
            let v0 = (i * 2) as u32 % num_vars as u32;
            let v1 = (i * 2 + 1) as u32 % num_vars as u32;
            vec![pos(v0), neg(v1)]
        })
        .collect();
    let features = SatFeatures::extract(num_vars, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::AggressiveInprocessing);
}

#[test]
fn test_algo_select_industrial_prioritizes_glucose() {
    // Very large formula with heterogeneous clause sizes -> industrial classification.
    let num_vars = 100_000;
    let clauses: Vec<Vec<Literal>> = (0..300_000)
        .map(|i| {
            let base_v = (i * 5) as u32 % num_vars as u32;
            // Vary clause length: 2-8 based on index for structural heterogeneity.
            let len = 2 + (i % 7);
            (0..len)
                .map(|j| {
                    let v = (base_v + j as u32) % num_vars as u32;
                    if j % 2 == 0 {
                        pos(v)
                    } else {
                        neg(v)
                    }
                })
                .collect()
        })
        .collect();
    let features = SatFeatures::extract(num_vars, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::VsidsGlucose);
}

#[test]
fn test_algo_select_small_prioritizes_glucose() {
    // Small formula -> VsidsGlucose (fast default).
    let clauses = vec![vec![pos(0), neg(1)], vec![pos(1), neg(2)]];
    let features = SatFeatures::extract(3, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::VsidsGlucose);
}

#[test]
fn test_algo_select_thread_count_respected() {
    // Any features, verify thread count is respected.
    let clauses = vec![vec![pos(0), neg(1)]];
    let features = SatFeatures::extract(2, &clauses);

    let s1 = Strategy::recommended_for_instance(1, &features);
    assert_eq!(s1.len(), 1);

    let s4 = Strategy::recommended_for_instance(4, &features);
    assert_eq!(s4.len(), 4);

    // recommended_for_instance returns at most 7 base strategies (incl the
    // Equiticks arm). Extension to 8 configs is handled by
    // strategies_to_configs() (#8584).
    let s8 = Strategy::recommended_for_instance(8, &features);
    assert_eq!(s8.len(), 7);

    // But the full pipeline (strategies_to_configs) produces 8 configs.
    let configs = strategies_to_configs(s8, 8);
    assert_eq!(configs.len(), 8);
}

#[test]
fn test_algo_select_adaptive_portfolio_sat() {
    // Verify adaptive portfolio produces correct SAT result.
    let cnf = "p cnf 3 2\n1 2 0\n-1 3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");
    let portfolio = PortfolioSolver::new_adaptive(2, &formula);
    let result = portfolio.solve(&formula);
    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_algo_select_adaptive_portfolio_unsat() {
    // Verify adaptive portfolio produces correct UNSAT result.
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");
    let portfolio = PortfolioSolver::new_adaptive(2, &formula);
    let result = portfolio.solve(&formula);
    assert!(result.is_unsat());
}

// --- Soundness (task #14): the parallel portfolio must never emit a wrong
// UNSAT on a satisfiable instance (the `--no-proof --parallel` false-UNSAT
// regression), and its UNSAT-acceptance gate must fail closed. ---

/// Build a satisfiable, XOR-rich CNF: a planted parity system. A fixed planted
/// assignment satisfies every 3-XOR constraint, so the formula is SAT, while
/// the dense XOR structure is exactly the shape that surfaced the historical
/// `--no-proof --parallel` false-UNSAT (bit-blasted, XOR-heavy CNF). Fully
/// deterministic so the regression is reproducible.
fn planted_xor_sat_cnf(nvars: usize, nconstraints: usize, seed: u64) -> String {
    // Small deterministic LCG (no rand dependency).
    let mut state: u64 = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let mut next = |m: usize| -> usize {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 33) as usize) % m
    };

    // Planted assignment over 1-indexed variables (assign[0] unused).
    let assign: Vec<bool> = (0..=nvars)
        .map(|i| (i.wrapping_mul(2654435761) & 1) == 1)
        .collect();

    let mut clauses: Vec<[i64; 3]> = Vec::new();
    for _ in 0..nconstraints {
        // Pick three distinct variables (1-indexed).
        let a = next(nvars) + 1;
        let mut b = next(nvars) + 1;
        while b == a {
            b = next(nvars) + 1;
        }
        let mut c = next(nvars) + 1;
        while c == a || c == b {
            c = next(nvars) + 1;
        }
        let vars = [a, b, c];
        let parity = assign[a] ^ assign[b] ^ assign[c];
        // Encode XOR(vars) = parity: forbid the 4 assignments of wrong parity.
        for mask in 0..8u32 {
            let bits = [mask & 1, (mask >> 1) & 1, (mask >> 2) & 1];
            let mask_parity = (bits[0] ^ bits[1] ^ bits[2]) == 1;
            if mask_parity != parity {
                // Clause literal excludes this forbidden bit pattern.
                let mut cl = [0i64; 3];
                for i in 0..3 {
                    let v = vars[i] as i64;
                    cl[i] = if bits[i] == 1 { -v } else { v };
                }
                clauses.push(cl);
            }
        }
    }

    let mut out = format!("p cnf {} {}\n", nvars, clauses.len());
    for cl in &clauses {
        out.push_str(&format!("{} {} {} 0\n", cl[0], cl[1], cl[2]));
    }
    out
}

/// The UNSAT-acceptance gate must reject an untrusted `Unsat` (one produced
/// with cross-worker clause sharing active and no proof) while accepting every
/// trustworthy result. This is the fail-closed core of the false-UNSAT fix:
/// even if unsound sharing is ever re-enabled, a contaminated `Unsat` can never
/// win the portfolio.
#[test]
fn test_portfolio_soundness_gate_rejects_untrusted_unsat() {
    use crate::proof_certificate::ProofCertificate;
    let unsat = SatResult::Unsat(ProofCertificate::empty());
    let sat = SatResult::Sat(vec![true]);
    let unknown = SatResult::Unknown;

    // Untrusted: UNSAT from a sharing-contaminated, non-proof worker is dropped.
    assert!(
        !portfolio_result_is_trustworthy(&unsat, false, true),
        "UNSAT under active clause sharing without a proof must be rejected"
    );
    // Trusted: no sharing => independent refutation of the original formula.
    assert!(portfolio_result_is_trustworthy(&unsat, false, false));
    // Trusted: proof mode carries a machine-checkable refutation.
    assert!(portfolio_result_is_trustworthy(&unsat, true, false));
    assert!(portfolio_result_is_trustworthy(&unsat, true, true));
    // SAT and Unknown are always safe to surface.
    assert!(portfolio_result_is_trustworthy(&sat, false, true));
    assert!(portfolio_result_is_trustworthy(&unknown, false, true));
}

/// The default portfolio path (non-proof, i.e. the historical false-UNSAT mode)
/// must be OFF for unsound cross-worker clause sharing.
#[test]
fn test_portfolio_clause_sharing_disabled_for_soundness() {
    const {
        assert!(
            !PORTFOLIO_CLAUSE_SHARING_ENABLED,
            "cross-worker clause sharing must stay disabled until it is re-expressed \
             over the stable external variable namespace (task #14 soundness)"
        );
    }
}

/// Regression: the multi-threaded portfolio must NEVER report UNSAT on a
/// satisfiable XOR-rich instance, in the non-proof (`--no-proof --parallel`)
/// mode where the false-UNSAT lived. Runs many iterations to exercise the
/// worker-join race that previously surfaced the wrong answer.
#[test]
fn test_portfolio_no_false_unsat_on_xor_rich_sat() {
    let cnf = planted_xor_sat_cnf(80, 90, 0xA1CE);
    let formula = parse_str(&cnf).expect("valid DIMACS");

    for iter in 0..24 {
        // Non-proof mode (proof_mode defaults to false) with a real thread
        // count is exactly the historical false-UNSAT configuration.
        let portfolio = PortfolioSolver::new_adaptive(8, &formula);
        let result = portfolio.solve(&formula);
        assert!(
            !result.is_unsat(),
            "iteration {iter}: satisfiable XOR-rich instance must never be \
             reported UNSAT by the parallel portfolio, got {result:?}"
        );
    }
}

/// A satisfiable XOR-rich instance solves correctly (SAT with a valid model)
/// under the parallel portfolio.
#[test]
fn test_portfolio_parallel_sat_xor_rich() {
    let cnf = planted_xor_sat_cnf(60, 70, 7);
    let formula = parse_str(&cnf).expect("valid DIMACS");

    let portfolio = PortfolioSolver::new_adaptive(8, &formula);
    let result = portfolio.solve(&formula);

    let model = match result {
        SatResult::Sat(m) => m,
        other => panic!("expected SAT on planted XOR-SAT, got {other:?}"),
    };
    // The returned model must satisfy every clause of the original formula.
    for clause in &formula.clauses {
        let satisfied = clause.iter().any(|lit| {
            let idx = lit.variable().index();
            idx < model.len() && model[idx] == lit.is_positive()
        });
        assert!(satisfied, "returned model must satisfy clause {clause:?}");
    }
}

/// A non-trivial UNSAT instance is solved correctly by the multi-threaded
/// portfolio in both proof and non-proof modes (sharing disabled => every
/// worker's refutation is sound).
#[test]
fn test_portfolio_parallel_unsat_multi_worker() {
    // All 8 sign combinations of 3 variables: unsatisfiable.
    let cnf = "\
        p cnf 3 8\n\
        1 2 3 0\n\
        1 2 -3 0\n\
        1 -2 3 0\n\
        1 -2 -3 0\n\
        -1 2 3 0\n\
        -1 2 -3 0\n\
        -1 -2 3 0\n\
        -1 -2 -3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    // Non-proof mode (the sharing-capable path, now sharing-disabled).
    let portfolio = PortfolioSolver::new_adaptive(8, &formula);
    assert!(
        portfolio.solve(&formula).is_unsat(),
        "non-proof parallel portfolio must prove this UNSAT"
    );

    // Proof mode: independent proof-carrying workers.
    let mut portfolio = PortfolioSolver::new_adaptive(8, &formula);
    portfolio.set_proof_mode(true);
    assert!(
        portfolio.solve(&formula).is_unsat(),
        "proof-mode parallel portfolio must prove this UNSAT"
    );
}

// --- Completeness (#parallel-bv): a worker that gives up (`Unknown`) must not
// end the portfolio, and a global timeout/interrupt must be honoured. ---

/// Build the pigeonhole formula PHP(holes+1, holes): unsatisfiable and hard for
/// resolution, so preprocessing/lucky phases cannot dispatch it — a worker must
/// enter the CDCL loop (where the stop condition is polled).
fn pigeonhole_cnf(holes: usize) -> String {
    let pigeons = holes + 1;
    let var = |p: usize, h: usize| p * holes + h + 1; // 1-indexed
    let mut clauses: Vec<Vec<i64>> = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| var(p, h) as i64).collect());
    }
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(vec![-(var(p1, h) as i64), -(var(p2, h) as i64)]);
            }
        }
    }
    let nv = pigeons * holes;
    let mut out = format!("p cnf {} {}\n", nv, clauses.len());
    for cl in &clauses {
        for lit in cl {
            out.push_str(&format!("{lit} "));
        }
        out.push_str("0\n");
    }
    out
}

/// `portfolio_result_is_definitive` distinguishes answers (`Sat`/`Unsat`) from
/// a give-up (`Unknown`) — only definitive results may stop the portfolio.
#[test]
fn test_portfolio_result_is_definitive() {
    use crate::proof_certificate::ProofCertificate;
    assert!(portfolio_result_is_definitive(&SatResult::Sat(vec![true])));
    assert!(portfolio_result_is_definitive(&SatResult::Unsat(
        ProofCertificate::empty()
    )));
    assert!(!portfolio_result_is_definitive(&SatResult::Unknown));
}

/// The join's store/supersede rule: a definitive result fills an empty slot or
/// supersedes a stored `Unknown` fallback, an `Unknown` only fills an empty
/// slot, and a definitive result is never overwritten. This is the core of the
/// premature-give-up fix.
#[test]
fn test_portfolio_should_store_supersedes_unknown_fallback() {
    use crate::proof_certificate::ProofCertificate;
    let sat = SatResult::Sat(vec![true]);
    let unsat = SatResult::Unsat(ProofCertificate::empty());
    let unknown = SatResult::Unknown;

    // Empty slot: anything is stored.
    assert!(portfolio_should_store(None, &unknown));
    assert!(portfolio_should_store(None, &sat));
    assert!(portfolio_should_store(None, &unsat));

    // A definitive result supersedes a stored Unknown fallback.
    assert!(portfolio_should_store(Some(&unknown), &sat));
    assert!(portfolio_should_store(Some(&unknown), &unsat));

    // Another Unknown does NOT overwrite the fallback.
    assert!(!portfolio_should_store(Some(&unknown), &unknown));

    // A definitive result is never overwritten (soundness + stability).
    assert!(!portfolio_should_store(Some(&sat), &unsat));
    assert!(!portfolio_should_store(Some(&sat), &unknown));
    assert!(!portfolio_should_store(Some(&unsat), &sat));
    assert!(!portfolio_should_store(Some(&unsat), &unknown));
}

/// A pre-set external cancellation flag stops every worker, so the
/// multi-threaded portfolio returns `Unknown` promptly (honouring a global
/// timeout) instead of running to completion or hanging.
#[test]
fn test_portfolio_external_cancel_stops_all_workers() {
    let cnf = pigeonhole_cnf(8); // PHP(9,8): UNSAT, resolution-hard.
    let formula = parse_str(&cnf).expect("valid DIMACS");

    let mut portfolio = PortfolioSolver::new_adaptive(8, &formula);
    portfolio.set_external_cancel(Arc::new(AtomicBool::new(true)));

    let result = portfolio.solve(&formula);
    assert!(
        result.is_unknown(),
        "a pre-set external cancel must stop all workers before they finish, \
         got {result:?}"
    );
}
