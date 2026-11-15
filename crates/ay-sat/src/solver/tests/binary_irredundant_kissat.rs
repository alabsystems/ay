// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-binary-irredundant-kissat`: learned binaries are promoted to
//! irredundant; hyper resolvents and longer learned clauses stay learned.
//! `--sat-factor-schedule-kissat`: Kissat's factor delay gate.

use super::*;

#[test]
fn learned_binaries_become_irredundant() {
    let run = |kissat: bool| {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            binary_irredundant_kissat: Some(kissat),
            ..Default::default()
        });
        let p = |v: u32| Literal::positive(Variable(v));
        let mut solver = Solver::new(6);
        let binary = solver.add_clause_db(&[p(0), p(1)], true);
        let ternary = solver.add_clause_db(&[p(2), p(3), p(4)], true);
        let hyper = solver.add_clause_db(&[p(4), p(5)], true);
        solver.arena.set_hyper(hyper, true);
        let irredundant_before = solver.arena.irredundant_count();
        solver.promote_learned_binaries_kissat();
        (
            solver.arena.is_learned(binary),
            solver.arena.is_learned(ternary),
            solver.arena.is_learned(hyper),
            solver.arena.irredundant_count() - irredundant_before,
        )
    };
    assert_eq!(run(true), (false, true, true, 1));
    assert_eq!(run(false), (true, true, true, 0));
}

/// `--sat-factor-schedule-kissat`: factoring waits until floor(log10(active))
/// <= in-search eliminations + 4, at every size (factor.c:1068-1085).
#[test]
fn factor_schedule_kissat_counts_in_search_eliminations() {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        factor_schedule_kissat: Some(true),
        ..Default::default()
    });
    let mut solver = Solver::new(200_000);
    assert!(solver.factor_delay_gate_holds(), "log10(200K) = 5 > 0 + 4");
    solver.cold.kissat_eliminations = 1;
    assert!(!solver.factor_delay_gate_holds(), "5 <= 1 + 4");
}
