// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-vivify-kissat`: vivification runs in every simplification round,
//! small dense formulas included, and classifies tiers by the focused glue
//! limits. `--sat-probe-round-kissat`: so do the round's other passes.

use super::*;
use crate::solver::inprocessing::VivifySkipReason;

fn small_dense_solver_mid_search() -> Solver {
    let mut solver = Solver::new(10);
    solver.set_vivify_enabled(true);
    solver.num_conflicts = 5_000;
    solver.num_original_clauses = 400;
    solver
}

#[test]
fn vivify_kissat_runs_on_small_dense_formulas() {
    let skip = |kissat: bool| {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            vivify_kissat: Some(kissat),
            ..Default::default()
        });
        let solver = small_dense_solver_mid_search();
        solver.vivify_skip_reason()
    };
    assert_eq!(skip(true), None, "Kissat has no small-dense skip");
    assert_eq!(skip(false), Some(VivifySkipReason::SmallDenseSkip));
}

#[test]
fn vivify_kissat_uses_the_focused_tier2_limit() {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        vivify_kissat: Some(true),
        ..Default::default()
    });
    let mut solver = Solver::new(8);
    let lits: Vec<_> = (0..4).map(|v| Literal::positive(Variable(v))).collect();
    let idx = solver.add_clause_db(&lits, true);
    solver.tiers.tier1_lbd = [2, 2];
    solver.tiers.tier2_lbd = [6, 9];
    solver.arena.set_lbd(idx, 8);
    assert_eq!(solver.vivify_clause_tier(idx), ClauseTier::Tier2);
    solver.arena.set_lbd(idx, 6);
    assert_eq!(solver.vivify_clause_tier(idx), ClauseTier::Tier1);
    solver.arena.set_lbd(idx, 2);
    assert_eq!(solver.vivify_clause_tier(idx), ClauseTier::Core);
}

/// `--sat-probe-round-kissat`: sweeping, transitive reduction, factoring and
/// the backbone run in every simplification round, not on their own
/// conflict intervals.
#[test]
fn probe_round_kissat_ignores_the_per_pass_intervals() {
    let skip = |kissat: bool| {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            probe_round_kissat: Some(kissat),
            // The backbone bypass needs Kissat's binary backbone alone.
            backbone_binary_kissat: Some(kissat),
            inproc_nlogn_schedule: Some(true),
            ..Default::default()
        });
        let mut solver = Solver::new(10);
        solver.set_sweep_enabled(true);
        solver.set_transred_enabled(true);
        solver.set_backbone_enabled(true);
        solver.num_conflicts = 100;
        solver.inproc_ctrl.sweep.next_conflict = 1_000_000;
        solver.inproc_ctrl.transred.next_conflict = 1_000_000;
        solver.inproc_ctrl.backbone.next_conflict = 1_000_000;
        (
            solver.should_sweep(),
            solver.should_transred(),
            solver.should_backbone(),
        )
    };
    assert_eq!(skip(true), (true, true, true));
    assert_eq!(skip(false), (false, false, false));
}

/// A random 3-CNF over `vars_count` variables with two planted (a b c) over
/// (a b d), (c -d e), (c -d -e) (under the negation of (a b c) propagation
/// conflicts without making a, b or c true first, so only the conflict path
/// can delete it) and some weakened resolvents of clashing pairs (asymmetric
/// tautologies of the formula).
fn asym_test_formula(next: &mut impl FnMut(u64) -> u64, vars_count: u32) -> Vec<Vec<Literal>> {
    let mut formula: Vec<Vec<Literal>> = Vec::new();
    while formula.len() < 24 {
        let mut vars: Vec<u32> = Vec::new();
        while vars.len() < 3 {
            let v = next(u64::from(vars_count)) as u32;
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
        let lits = vars
            .iter()
            .map(|&v| {
                if next(2) == 0 {
                    Literal::positive(Variable(v))
                } else {
                    Literal::negative(Variable(v))
                }
            })
            .collect();
        formula.push(lits);
    }
    // Two planted (a b c) over (a b d), (c -d e), (c -d -e): under the
    // negation of (a b c) propagation conflicts without making a, b or c
    // true first, so only the conflict path can delete it.
    for _ in 0..2 {
        let mut vars: Vec<u32> = Vec::new();
        while vars.len() < 5 {
            let v = next(u64::from(vars_count)) as u32;
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
        let [a, b, c, d, e] = [0, 1, 2, 3, 4].map(|i| Literal::positive(Variable(vars[i])));
        formula.push(vec![a, b, d]);
        formula.push(vec![c, d.negated(), e]);
        formula.push(vec![c, d.negated(), e.negated()]);
        formula.push(vec![a, b, c]);
    }
    // Weakened resolvents of clashing pairs: each is an asymmetric
    // tautology of the formula.
    let base = formula.len();
    for i in 0..base {
        for j in 0..base {
            let (a, b) = (&formula[i], &formula[j]);
            let Some(&pivot) = a.iter().find(|l| b.contains(&l.negated())) else {
                continue;
            };
            let mut resolvent: Vec<Literal> = a.iter().filter(|&&l| l != pivot).copied().collect();
            for &l in b.iter().filter(|&&l| l != pivot.negated()) {
                if !resolvent.contains(&l) {
                    resolvent.push(l);
                }
            }
            let tautology = resolvent.iter().any(|l| resolvent.contains(&l.negated()));
            if !tautology && resolvent.len() >= 3 && next(4) == 0 {
                formula.push(resolvent);
            }
        }
    }
    formula
}

/// `--sat-vivify-asym-kissat`: on random formulas seeded with weakened
/// resolvents (asymmetric tautologies whose probe ends in a conflict),
/// irredundant vivification deletes some of them, and with the switch on or
/// off the irredundant clauses left, with the root units, are equivalent to
/// the input formula (checked over every assignment).
#[test]
fn vivify_asym_kissat_deletes_asymmetric_tautologies_and_keeps_the_formula() {
    const VARS: u32 = 10;
    let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = move |bound: u64| {
        seed = seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (seed >> 33) % bound
    };
    let mut deleted = [0u64; 2];
    for _ in 0..40 {
        let formula = asym_test_formula(&mut next, VARS);
        for (k, on) in [false, true].into_iter().enumerate() {
            let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
                vivify_asym_kissat: Some(on),
                ..Default::default()
            });
            let mut solver = Solver::new(VARS as usize);
            for clause in &formula {
                solver.add_clause(clause.clone());
            }
            if solver.process_initial_clauses().is_some() {
                continue;
            }
            solver.initialize_watches();
            solver.set_vivify_enabled(true);
            if solver.vivify_irredundant() {
                continue;
            }
            deleted[k] += solver.inproc.vivifier.stats.asym_deleted;
            let mut kept: Vec<Vec<Literal>> = Vec::new();
            for idx in solver.arena.active_indices() {
                if !solver.arena.is_garbage_any(idx) && !solver.arena.is_learned(idx) {
                    kept.push(solver.arena.literals(idx).to_vec());
                }
            }
            for v in 0..VARS {
                let lit = Literal::positive(Variable(v));
                if let Some(value) = solver.lit_value(lit) {
                    kept.push(vec![if value { lit } else { lit.negated() }]);
                }
            }
            let holds = |clauses: &[Vec<Literal>], m: u32| {
                clauses.iter().all(|c| {
                    c.iter()
                        .any(|l| ((m >> l.variable().0) & 1 == 1) == l.is_positive())
                })
            };
            for m in 0..(1u32 << VARS) {
                assert_eq!(
                    holds(&formula, m),
                    holds(&kept, m),
                    "assignment {m:#x} (switch {on})"
                );
            }
        }
    }
    assert_eq!(
        deleted[0], 0,
        "the default never deletes on the conflict path"
    );
    assert!(deleted[1] > 0, "the switch deletes asymmetric tautologies");
}

/// `--sat-vivify-asym-kissat`: (a b c) with (a b d), (c -d e), (c -d -e).
/// Every order of the decisions -a, -b, -c ends in a conflict that needs all
/// three, and none of a, b, c is made true first, so the implied-literal path
/// never fires: the switch deletes the clause, the default keeps it.
#[test]
fn vivify_asym_kissat_deletes_a_clause_only_its_conflict_refutes() {
    for on in [false, true] {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            vivify_asym_kissat: Some(on),
            ..Default::default()
        });
        let mut solver = Solver::new(5);
        let [a, b, c, d, e] = [0, 1, 2, 3, 4].map(|v| Literal::positive(Variable(v)));
        let target = solver.arena.len();
        solver.add_clause(vec![a, b, c]);
        let support: Vec<usize> = [
            vec![a, b, d],
            vec![c, d.negated(), e],
            vec![c, d.negated(), e.negated()],
        ]
        .into_iter()
        .map(|clause| {
            let idx = solver.arena.len();
            solver.add_clause(clause);
            idx
        })
        .collect();
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        solver.set_vivify_enabled(true);
        // Generations: only the untried target is a candidate.
        solver.set_vivify_generations(true);
        for &idx in &support {
            solver.arena.set_vivify_tried(idx, true);
        }
        assert!(!solver.vivify_irredundant());
        let live = solver.arena.is_active(target) && !solver.arena.is_garbage_any(target);
        assert_eq!(
            live, !on,
            "switch {on}: the target clause is deleted only under the switch"
        );
        assert_eq!(solver.inproc.vivifier.stats.asym_deleted, u64::from(on));
        for &idx in &support {
            assert!(solver.arena.is_active(idx) && !solver.arena.is_garbage_any(idx));
        }
    }
}

/// `--sat-vivify-order-kissat`: vivification ranks literals by their plain
/// occurrence count in the live clauses of size > 2 (learned ones included;
/// binaries not counted), as Kissat does; the default keeps the
/// Jeroslow-Wang weights, which count binaries and favour short clauses.
#[test]
fn vivify_order_kissat_counts_large_clause_occurrences() {
    for on in [false, true] {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            vivify_order_kissat: Some(on),
            ..Default::default()
        });
        let mut solver = Solver::new(6);
        let [a, b, c, d, e, f] = [0, 1, 2, 3, 4, 5].map(|v| Literal::positive(Variable(v)));
        solver.add_clause(vec![a, b, c]);
        solver.add_clause(vec![a, d, e, f]);
        solver.add_clause_db(&[b, d, e], true);
        solver.add_clause(vec![b, c.negated()]);
        solver.add_clause(vec![b, d.negated()]);
        let scores = solver.vivify_literal_scores();
        let score = |lit: Literal| scores[lit.index()];
        if on {
            assert_eq!(score(a), 2, "two large clauses");
            assert_eq!(
                score(b),
                2,
                "one irredundant and one learned large clause; binaries not counted"
            );
            assert_eq!(score(d), 2);
            assert_eq!(score(c.negated()), 0, "binary only");
        } else {
            // Jeroslow-Wang: 2^(12 - len), binaries included.
            assert_eq!(score(a), (1 << 9) + (1 << 8));
            assert_eq!(score(b), (1 << 9) + (1 << 9) + 2 * (1 << 10));
            assert_eq!(score(c.negated()), 1 << 10);
        }
    }
}
