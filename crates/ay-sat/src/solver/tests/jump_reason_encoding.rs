// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The jump rule follows only a literal-encoded binary reason. A variable
//! propagated through a binary clause while the jump gate was off carries the
//! clause's arena offset with the binary flag set; when
//! `--sat-jump-reasons-kissat` opens the gate above level 0 (at a
//! reduction), that offset must not be decoded as a literal (review of
//! 48c98a43d: it indexed an arbitrary variable, or past the end).

use super::*;

/// Decision `d` at level 1 and `a` implied by the binary clause `(a | -d)`,
/// stored as a clause reference with the binary flag, as BCP does with the
/// gate off.
fn implied_through_a_clause_reference() -> (Solver, Literal, Literal) {
    let mut solver = Solver::new(3);
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    solver.add_clause(vec![a, d.negated()]);
    let off = solver.arena.indices().next().expect("the binary clause");
    solver.decide(d);
    solver.enqueue(a, Some(ClauseRef(off as u32)));
    solver.var_data[1].flags |= VarData::FLAG_BINARY_REASON_PUB;
    assert!(solver.var_data[1].is_binary_reason());
    assert!(!is_binary_literal_reason(solver.var_data[1].reason));
    (solver, d, a)
}

#[test]
fn a_clause_reference_reason_is_not_jumped() {
    let (mut solver, _d, a) = implied_through_a_clause_reference();
    solver.cold.jump_reasons_enabled = true;
    let jumped = solver.stats.jumped_reasons;
    let b = Literal::positive(Variable(2));
    solver.enqueue_binary_reason(b, a.negated());
    assert!(matches!(solver.var_reason_kind(2), ReasonKind::BinaryLiteral(r) if r == a.negated()));
    assert_eq!(solver.stats.jumped_reasons, jumped);
}

#[test]
fn a_literal_reason_is_jumped_to_its_root() {
    let mut solver = Solver::new(3);
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    let b = Literal::positive(Variable(2));
    solver.cold.jump_reasons_enabled = true;
    solver.decide(d);
    solver.enqueue_binary_reason(a, d.negated());
    let jumped = solver.stats.jumped_reasons;
    solver.enqueue_binary_reason(b, a.negated());
    assert!(matches!(solver.var_reason_kind(2), ReasonKind::BinaryLiteral(r) if r == d.negated()));
    assert_eq!(solver.stats.jumped_reasons, jumped + 1);
}

/// `--sat-target-kissat-pop`: with a conflict pending, the saved target leaves
/// out the conflict level's assignments (Kissat pops that level first); without
/// the switch every assigned value is copied.
#[test]
fn target_kissat_pop_leaves_out_the_conflict_level() {
    let run = |pop: bool| {
        let _guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            target_kissat_pop: Some(pop),
            ..Default::default()
        });
        let mut solver = Solver::new(3);
        solver.decide(Literal::positive(Variable(0)));
        assert!(solver.propagate().is_none());
        solver.decide(Literal::negative(Variable(1)));
        // A conflict happened while propagating level 2.
        solver.no_conflict_until = 1;
        solver.target_phase.fill(0);
        solver.save_assigned_values_into(crate::solver::restart::PhaseArray::Target);
        (solver.target_phase[0], solver.target_phase[1])
    };
    assert_eq!(
        run(true),
        (1, 0),
        "level 1 saved, the conflict level left out"
    );
    assert_eq!(run(false), (1, -1), "every assigned value saved");
}

/// `--sat-restart-gate-kissat`: in focused mode with the EMA condition met, one
/// conflict after the start is enough (Kissat `restartint` 1); AY's default
/// needs more than its gate of 2.
#[test]
fn restart_gate_kissat_restarts_after_one_conflict() {
    let run = |kissat: bool| {
        let _guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            restart_gate_kissat: Some(kissat),
            ..Default::default()
        });
        let mut solver = Solver::new(4);
        solver.decide(Literal::positive(Variable(0)));
        solver.stable_mode = false;
        solver.num_conflicts = 10;
        solver.conflicts_since_restart = 1;
        solver.cold.lbd_ema_fast = 2.0;
        solver.cold.lbd_ema_slow = 1.0;
        solver.should_restart_pure()
    };
    assert!(run(true), "Kissat's gate allows the restart");
    assert!(!run(false), "the default gate needs more conflicts");
}

/// `--sat-best-stable-kissat`: a focused-mode trail never becomes the best
/// phases (Kissat updates target and best in stable mode only).
#[test]
fn best_stable_kissat_skips_focused_mode() {
    let run = |kissat: bool| {
        let _guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            best_stable_kissat: Some(kissat),
            ..Default::default()
        });
        let mut solver = Solver::new(3);
        solver.stable_mode = false;
        solver.decide(Literal::positive(Variable(0)));
        assert!(solver.propagate().is_none());
        solver.decide(Literal::negative(Variable(1)));
        solver.no_conflict_until = solver.trail.len();
        solver.best_trail_len = 0;
        solver.update_target_and_best_phases();
        solver.best_trail_len
    };
    assert_eq!(run(true), 0, "focused trail not recorded as best");
    assert_eq!(run(false), 2, "the default records it");
}

/// `--sat-randec-kissat`: a started sequence keeps deciding randomly across
/// decisions (Kissat decide.c); AY's default checks its conflict limit first,
/// which starting the sequence has just pushed ahead, so it stops after one.
#[test]
fn randec_kissat_sequences_make_several_random_decisions() {
    let run = |kissat: bool| {
        let _guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            randec_kissat: Some(kissat),
            ..Default::default()
        });
        let mut solver = Solver::new(20);
        solver.stable_mode = false;
        solver.num_conflicts = 1_200;
        // A second sequence: AY's interval n*ln(n)*500 is 0 for the first.
        solver.cold.random_decision_phases = 1;
        solver.cold.next_random_decision = 1_000;
        let first = solver.next_random_decision();
        let v = first.expect("the first call starts a sequence");
        solver.decide(Literal::positive(v));
        solver.next_random_decision().is_some()
    };
    assert!(run(true), "the Kissat sequence continues");
    assert!(!run(false), "the default makes one random decision");
}

/// `--sat-reluctant-cap-kissat`: the stable restart interval never exceeds
/// 2^20 conflicts (Kissat reluctant.c:44-49); AY's default caps v, not the
/// interval, so it doubles on to 2^21.
#[test]
fn reluctant_cap_kissat_bounds_the_interval() {
    let next = |kissat: bool| {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            reluctant_cap_kissat: Some(kissat),
            ..Default::default()
        });
        let mut solver = Solver::new(2);
        // u = 2048 (lowest bit 2048), v = 1024: the next step doubles v.
        solver.cold.reluctant_u = 2048;
        solver.cold.reluctant_v = 1024;
        solver.advance_reluctant()
    };
    assert_eq!(next(true), 1024, "2048 x 1024 > 2^20 resets to the period");
    assert_eq!(next(false), 2048 * 1024);
}

/// `--sat-reorder-weights-kissat`: a learned binary weighs 1 in the reorder,
/// so its variables move ahead of variables in no clause; AY's default skips
/// learned clauses.
#[test]
fn reorder_weights_kissat_counts_learned_binaries() {
    let ahead = |kissat: bool| {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            reorder_weights_kissat: Some(kissat),
            ..Default::default()
        });
        let mut solver = Solver::new(4);
        solver.stable_mode = false;
        solver.add_clause_db(
            &[
                Literal::positive(Variable(0)),
                Literal::positive(Variable(1)),
            ],
            true,
        );
        solver.reorder_variables();
        solver.vsids.bump_order(Variable(0)) > solver.vsids.bump_order(Variable(3))
    };
    assert!(ahead(true), "the learned binary's variable comes first");
    assert!(!ahead(false), "the default leaves index order");
}
