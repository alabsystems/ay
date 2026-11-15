// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-preprocess-kissat`: preprocessing runs Kissat 4.0.4's
//! `probe_initially` (congruence, substitution, binary backbone, sweeping,
//! factoring) and no elimination, which first runs in search at Kissat's
//! initial limit. `--sat-subst-kissat` keeps the dense decompose guard.

use super::*;
use crate::solver::inprocessing::kissat_eliminate_interval_nlog2n;

/// Two copies of g = AND(a, b), each used by a different clause, so
/// congruence merges them and elimination has variables to remove.
fn duplicate_gates_with_every_pass_on() -> Solver {
    let v = |i: u32| Variable(i);
    let (a, b, g1, g2, c, d, e) = (v(0), v(1), v(2), v(3), v(4), v(5), v(6));
    let mut solver = Solver::new(7);
    for g in [g1, g2] {
        solver.add_clause(vec![
            Literal::negative(a),
            Literal::negative(b),
            Literal::positive(g),
        ]);
        solver.add_clause(vec![Literal::positive(a), Literal::negative(g)]);
        solver.add_clause(vec![Literal::positive(b), Literal::negative(g)]);
    }
    solver.add_clause(vec![
        Literal::positive(g1),
        Literal::positive(c),
        Literal::positive(d),
    ]);
    solver.add_clause(vec![
        Literal::negative(g2),
        Literal::positive(c),
        Literal::positive(e),
    ]);
    solver.add_clause(vec![
        Literal::negative(c),
        Literal::positive(d),
        Literal::positive(e),
    ]);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_backbone_enabled(true);
    solver.set_bve_enabled(true);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver
}

fn preprocess_with(kissat: bool) -> Solver {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        preprocess_kissat: Some(kissat),
        ..Default::default()
    });
    let mut solver = duplicate_gates_with_every_pass_on();
    assert!(!solver.preprocess(), "the formula is satisfiable");
    solver
}

#[test]
fn preprocess_kissat_substitutes_and_leaves_elimination_to_search() {
    let solver = preprocess_with(true);
    assert!(
        solver.congruence_stats().equivalences_found > 0,
        "congruence merges the duplicate gates"
    );
    assert!(solver.decompose_stats().rounds > 0, "substitution runs");
    assert_eq!(
        solver.bve_stats().vars_eliminated,
        0,
        "no elimination before search"
    );
    assert!(
        solver.inproc_ctrl.bve.enabled,
        "elimination stays armed for search"
    );
    assert_eq!(
        solver.inproc_ctrl.bve.next_conflict,
        kissat_eliminate_interval_nlog2n(solver.arena.irredundant_count() as u64, 1),
        "the first elimination waits for Kissat's initial limit"
    );
}

#[test]
fn default_preprocessing_eliminates() {
    let solver = preprocess_with(false);
    assert!(solver.bve_stats().vars_eliminated > 0);
}

/// A formula over 3 variables with 66 clauses: parsed density 22, above the
/// AUTO dense disarm's 20.
fn dense_formula_with_auto_collapse_armed() -> Solver {
    let mut solver = Solver::new(3);
    for i in 0..66u32 {
        let lit = |v: u32| {
            if (i >> v) & 1 == 0 {
                Literal::positive(Variable(v))
            } else {
                Literal::negative(Variable(v))
            }
        };
        if i % 8 != 7 {
            solver.add_clause(vec![lit(0), lit(1), lit(2)]);
        } else {
            solver.add_clause(vec![lit(0), lit(1)]);
        }
    }
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    solver.cold.subst_auto_capped = true;
    solver.cold.subst_auto_collapse = true;
    solver
}

/// The dense disarm is AY's soundness guard for decompose (#8448), so
/// `--sat-subst-kissat` keeps it (review 2026-09-29): only the collapse
/// probe's verdict is overridden.
#[test]
fn subst_kissat_keeps_the_dense_decompose_guard() {
    let armed = |kissat: bool| {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            subst_kissat: Some(kissat),
            ..Default::default()
        });
        let mut solver = dense_formula_with_auto_collapse_armed();
        solver.compute_preprocess_policy();
        (
            solver.inproc_ctrl.congruence.enabled,
            solver.inproc_ctrl.decompose.enabled,
        )
    };
    assert_eq!(armed(true), (false, false), "the dense guard stays");
    assert_eq!(armed(false), (false, false), "the AUTO dense disarm");
}
