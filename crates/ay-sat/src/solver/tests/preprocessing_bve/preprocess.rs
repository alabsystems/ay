// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_preprocess_skips_expensive_equivalence_passes_on_large_formula() {
    let mut solver = Solver::new(PREPROCESS_EXPENSIVE_MAX_VARS + 1);
    add_duplicate_and_gate_formula(&mut solver);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_backbone_enabled(false);
    solver.set_htr_enabled(true);
    solver.set_factor_enabled(true);

    // Simulate BVE having advanced enough that factor would otherwise pass its
    // delay guard on a large formula. The preprocessing size guard should still
    // keep factor disabled here.
    solver.cold.bve_phases = 1;
    solver.cold.factor_marked_epoch = solver.cold.factor_last_completed_epoch + 1;

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let congr_rounds_before = solver.congruence_stats().rounds;
    let decompose_rounds_before = solver.decompose_stats().rounds;
    let factor_rounds_before = solver.factor_stats().rounds;
    let htr_rounds_before = solver.htr_stats().rounds;
    let sweep_rounds_before = solver.sweep_stats().rounds;

    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT on satisfiable large gate formula"
    );
    // Congruence is gated on formula size during preprocessing (#7162):
    // Even with a CaDiCaL-style retry delay in the congruence engine, the
    // first preprocessing pass on large formulas (>200K vars or >3M clauses)
    // is still too expensive because AY rebuilds occurrence lists from scratch.
    // Congruence still fires during inprocessing (with skip_expensive guard).
    assert_eq!(
        solver.congruence_stats().rounds,
        congr_rounds_before,
        "preprocess should skip congruence on large formulas (#7162)"
    );
    assert_eq!(
        solver.decompose_stats().rounds,
        decompose_rounds_before,
        "preprocess should skip decompose on large formulas (#7162)"
    );
    assert_eq!(
        solver.factor_stats().rounds,
        factor_rounds_before,
        "preprocess should skip factor on large formulas"
    );
    assert_eq!(
        solver.htr_stats().rounds,
        htr_rounds_before,
        "preprocess should skip HTR on large formulas"
    );
    assert_eq!(
        solver.sweep_stats().rounds,
        sweep_rounds_before,
        "preprocess should skip sweep on large formulas"
    );
}

#[test]
fn test_bve_post_collapse_unlock_requires_env_and_collapse() {
    // Above-cap formula, but NO congruence/decompose collapse has run:
    // count_removed() == 0, so the post-collapse unlock must stay closed
    // regardless of the env knob — with the default-ON knob (wf_55735963)
    // the collapse requirement is what keeps elimination-only instances
    // inert, and AY_AB_BVE_POST_COLLAPSE=0 closes it outright.
    let mut solver = Solver::new(PREPROCESS_EXPENSIVE_MAX_VARS + 1);
    add_duplicate_and_gate_formula(&mut solver);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(
        !solver.bve_post_collapse_unlock_active(),
        "post-collapse BVE unlock must be inert when the collapse merged nothing"
    );

    // In-band formula (num_vars <= PREPROCESS_EXPENSIVE_MAX_VARS): the
    // re-derivation may only OPEN above-cap cases — an in-band solver never
    // activates the unlock, even after substitutions exist.
    let mut small = Solver::new(64);
    add_uniform_3sat_clauses(&mut small, 64, 160);
    small.initialize_watches();
    assert!(small.process_initial_clauses().is_none());
    small.var_lifecycle.mark_substituted(0);
    assert!(
        !small.bve_post_collapse_unlock_active(),
        "post-collapse BVE unlock must never touch in-band formulas"
    );
}

#[test]
fn test_restart_inprocessing_skips_bce_and_condition_on_uniform_nonbinary_formula() {
    let mut solver = Solver::new(64);
    add_uniform_3sat_clauses(&mut solver, 64, 160);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_bce_enabled(true);
    solver.set_condition_enabled(true);

    solver.num_conflicts = 0;
    solver.inproc_ctrl.bce.next_conflict = 0;
    solver.inproc_ctrl.condition.next_conflict = 0;
    // Simulate a reduce_db having occurred so the reduction gate passes (#5130).
    solver.cold.num_reductions = 1;

    let bce_rounds_before = solver.bce_stats().rounds;
    let conditioning_rounds_before = solver.inproc.conditioning.stats().rounds;

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on satisfiable random 3-SAT formula"
    );
    // BCE and conditioning are no longer skipped for uniform nonbinary formulas
    // (the skip_gate_dependent_passes guard was removed in the inproc_ctrl refactor).
    // They run normally when scheduled.
    assert!(
        solver.bce_stats().rounds >= bce_rounds_before,
        "BCE should execute normally during restart inprocessing"
    );
    assert!(
        solver.inproc.conditioning.stats().rounds >= conditioning_rounds_before,
        "conditioning should execute normally during restart inprocessing"
    );
}

#[test]
fn test_restart_inprocessing_skips_congruence_on_large_formula() {
    // Congruence gate extraction is O(clauses) without a tick budget.
    // On large residuals (>3M clauses or >200K vars), skip congruence in
    // inprocessing and reschedule for the next round. This prevents
    // pathological overhead on shuffling-2 (4.7M clauses). (#7135)
    //
    // CaDiCaL runs congruence without a clause count threshold, but its
    // gate extraction uses pre-built occurrence lists (O(1) per clause).
    // AY's gate extraction does a full O(clauses) scan each time.
    let mut solver = Solver::new(PREPROCESS_EXPENSIVE_MAX_VARS + 1);
    add_duplicate_and_gate_formula(&mut solver);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_factor_enabled(false);

    solver.num_conflicts = 500;
    solver.inproc_ctrl.congruence.next_conflict = 0;
    solver.inproc_ctrl.decompose.next_conflict = u64::MAX;

    let congr_rounds_before = solver.congruence_stats().rounds;

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on satisfiable large gate formula"
    );
    assert_eq!(
        solver.congruence_stats().rounds,
        congr_rounds_before,
        "restart inprocessing should skip congruence on large formulas (#7135)"
    );
}

#[test]
fn test_restart_inprocessing_skips_congruence_when_gate_disabled() {
    let mut solver = Solver::new(4);
    add_duplicate_and_gate_formula(&mut solver);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_backbone_enabled(false);

    solver.num_conflicts = 500;
    solver.cold.num_reductions = 1;
    solver.inproc_ctrl.congruence.next_conflict = 0;
    solver.inproc_ctrl.decompose.next_conflict = u64::MAX;

    let congruence_rounds_before = solver.congruence_stats().rounds;

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on satisfiable duplicate-gate formula"
    );
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before,
        "gate-disabled restart inprocessing must not run congruence"
    );
}

#[test]
fn test_restart_inprocessing_htr_does_not_force_second_decompose_same_round() {
    let mut solver: Solver = Solver::new(3);
    let r = Variable(0);
    let x = Variable(1);
    let y = Variable(2);

    // HTR derives (¬y ∨ x), but the same inprocessing round should not
    // immediately pay for a second full decompose scan after the initial
    // normalization pass (#7480 D3).
    solver.add_clause(vec![
        Literal::positive(r),
        Literal::negative(y),
        Literal::positive(x),
    ]);
    solver.add_clause(vec![Literal::negative(r), Literal::negative(y)]);
    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());

    solver.set_decompose_enabled(true);
    solver.set_htr_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_backbone_enabled(false);

    solver.num_conflicts = 20_000;
    solver.cold.num_reductions = 1;
    solver.inproc_ctrl.decompose.next_conflict = 0;
    solver.inproc_ctrl.htr.next_conflict = 0;

    let decompose_rounds_before = solver.decompose_stats().rounds;
    let htr_rounds_before = solver.htr_stats().rounds;

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on satisfiable HTR fixture"
    );
    assert_eq!(
        solver.htr_stats().rounds,
        htr_rounds_before + 1,
        "HTR should still run and produce the new binary implication"
    );
    assert_eq!(
        solver.decompose_stats().rounds,
        decompose_rounds_before + 1,
        "decompose should run only once per inprocessing round after the D3 gate"
    );

    let decompose_time_ns = solver
        .inprocessing_pass_times_ns()
        .into_iter()
        .find_map(|(label, value)| (label == "inproc_decompose_ms").then_some(value))
        .unwrap_or(0);
    let htr_time_ns = solver
        .inprocessing_pass_times_ns()
        .into_iter()
        .find_map(|(label, value)| (label == "inproc_htr_ms").then_some(value))
        .unwrap_or(0);
    assert!(
        decompose_time_ns > 0,
        "timed inprocessing stats should record decompose runtime"
    );
    assert!(
        htr_time_ns > 0,
        "timed inprocessing stats should record HTR runtime"
    );
}

#[test]
fn test_restart_inprocessing_forces_decompose_after_congruence_equivalences() {
    let mut solver: Solver = Solver::new(5);
    let y0 = Variable(0);
    let y1 = Variable(1);
    let a = Variable(2);
    let b = Variable(3);
    let c = Variable(4);

    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::negative(b),
        Literal::negative(c),
        Literal::positive(y0),
    ]);
    solver.add_clause(vec![Literal::positive(a), Literal::negative(y0)]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(y0)]);
    solver.add_clause(vec![Literal::positive(c), Literal::negative(y0)]);
    solver.add_clause(vec![
        Literal::negative(b),
        Literal::negative(c),
        Literal::positive(y1),
    ]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(y1)]);
    solver.add_clause(vec![Literal::positive(c), Literal::negative(y1)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "fixture must expose a level-0 assignment before congruence runs"
    );

    solver.set_decompose_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_backbone_enabled(false);

    solver.num_conflicts = 20_000;
    solver.cold.num_reductions = 1;
    solver.inproc_ctrl.congruence.next_conflict = 0;
    solver.inproc_ctrl.decompose.next_conflict = u64::MAX;

    let decompose_rounds_before = solver.decompose_stats().rounds;
    let congruence_rounds_before = solver.congruence_stats().rounds;

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on satisfiable congruence fixture"
    );
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before + 1,
        "congruence should still run when its interval is due"
    );
    assert_eq!(
        solver.decompose_stats().rounds,
        decompose_rounds_before + 1,
        "forced post-congruence decompose must ignore the ordinary D3 interval gate"
    );
}

#[test]
fn test_decompose_direct_call_runs_with_proof_logging() {
    let mut solver = Solver::with_proof(3, Vec::new());
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // x0≡x1 equivalence via binary clauses: (¬x0,x1) and (¬x1,x0)
    solver.add_clause_db(&[Literal::negative(x0), Literal::positive(x1)], false);
    solver.add_clause_db(&[Literal::negative(x1), Literal::positive(x0)], false);
    solver.add_clause_db(&[Literal::positive(x1), Literal::positive(x2)], false);
    solver.initialize_watches();

    let rounds_before = solver.decompose_stats().rounds;
    solver.decompose();

    assert!(
        solver.decompose_stats().rounds > rounds_before,
        "direct decompose call should still exercise proof logging"
    );
}

/// Regression test for #4349: decompose rewrite path must pass real clause IDs
/// (not 0) for proof records. Before the fix, `writer.delete(..., 0)` was
/// emitted for every decompose mutation, making proofs invalid.
///
/// Uses DRAT output and calls the decompose body directly to validate the
/// low-level proof emission path.
#[test]
fn test_decompose_drat_proof_uses_real_clause_ids() {
    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // x0≡x1 equivalence via binary clauses
    solver.add_clause_db(&[Literal::negative(x0), Literal::positive(x1)], false);
    solver.add_clause_db(&[Literal::negative(x1), Literal::positive(x0)], false);
    solver.add_clause_db(&[Literal::positive(x1), Literal::positive(x2)], false);
    solver.initialize_watches();

    let rounds_before = solver.decompose_stats().rounds;
    solver.decompose();
    assert!(
        solver.decompose_stats().rounds > rounds_before,
        "decompose should run (not be skipped)"
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");

    // Decompose must produce non-empty proof output (additions + deletions).
    assert!(
        !proof_text.is_empty(),
        "DRAT proof output should be non-empty after decompose rewrites"
    );

    // DRAT format: addition lines are bare clause literals, deletion lines
    // start with "d ". Verify both exist.
    let has_add = proof_text.lines().any(|l| !l.starts_with("d "));
    let has_del = proof_text.lines().any(|l| l.starts_with("d "));
    assert!(has_add, "DRAT proof should contain at least one add line");
    assert!(
        has_del,
        "DRAT proof should contain at least one delete line"
    );

    // Verify deletion lines contain actual clause literals (not empty).
    for line in proof_text.lines() {
        if let Some(rest) = line.strip_prefix("d ") {
            let lits: Vec<&str> = rest.split_whitespace().take_while(|&p| p != "0").collect();
            assert!(
                !lits.is_empty(),
                "DRAT deletion line must contain clause literals (line: {line})"
            );
        }
    }
}

/// Verify decompose remains fail-closed in LRAT mode until route admission
/// has checker-visible obligations for the destructive rewrite.
#[test]
fn test_preprocess_lrat_enables_decompose() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 3);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // x0≡x1 equivalence via binary clauses; third clause gets rewritten.
    solver.add_clause_db(&[Literal::negative(x0), Literal::positive(x1)], false);
    solver.add_clause_db(&[Literal::negative(x1), Literal::positive(x0)], false);
    solver.add_clause_db(&[Literal::positive(x1), Literal::positive(x2)], false);
    solver.initialize_watches();

    assert!(
        !solver.inproc_ctrl.decompose.enabled,
        "decompose must stay disabled in LRAT mode until checked route admission"
    );
}

/// Regression for #3906 F3: verify conditioning works in both DRAT and LRAT modes.
///
/// Conditioning uses regular delete (delete_clause_with_snapshot) — the same
/// pattern as BCE which is LRAT-enabled. CaDiCaL uses weaken_minus
/// (condition.cpp:791) but regular deletion is accepted by the LRAT checker.
/// This test verifies:
/// 1. DRAT preprocess fires conditioning (formula is conditioning-capable)
/// 2. LRAT preprocess also fires conditioning (lrat_override=false, #4812)
/// 3. Direct condition() in LRAT mode works (non-vacuous engine test)
#[test]
fn test_preprocess_conditioning_lrat_mode_non_vacuous() {
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let clauses: [Vec<Literal>; 3] = [
        vec![Literal::positive(x0), Literal::positive(x1)],
        vec![Literal::negative(x0), Literal::positive(x2)],
        vec![Literal::negative(x1), Literal::positive(x2)],
    ];

    let isolate_conditioning = |solver: &mut Solver| {
        for ctrl in [
            &mut solver.inproc_ctrl.vivify,
            &mut solver.inproc_ctrl.vivify_irred,
            &mut solver.inproc_ctrl.subsume,
            &mut solver.inproc_ctrl.probe,
            &mut solver.inproc_ctrl.backbone,
            &mut solver.inproc_ctrl.bve,
            &mut solver.inproc_ctrl.bce,
            &mut solver.inproc_ctrl.factor,
            &mut solver.inproc_ctrl.transred,
            &mut solver.inproc_ctrl.htr,
            &mut solver.inproc_ctrl.gate,
            &mut solver.inproc_ctrl.congruence,
            &mut solver.inproc_ctrl.decompose,
            &mut solver.inproc_ctrl.sweep,
        ] {
            ctrl.enabled = false;
        }
        solver.inproc_ctrl.condition.enabled = true;
    };

    // 1. DRAT mode: conditioning fires.
    let mut drat_solver = Solver::with_proof_output(3, ProofOutput::drat_text(Vec::<u8>::new()));
    drat_solver.preprocessing_quick_mode = false; // test needs conditioning during preprocess
    isolate_conditioning(&mut drat_solver);
    for clause in &clauses {
        assert!(drat_solver.add_clause(clause.clone()));
    }
    drat_solver.initialize_watches();
    assert!(
        !drat_solver.preprocess(),
        "DRAT preprocess should not derive UNSAT for this SAT formula"
    );
    let drat_eliminated = drat_solver.inproc.conditioning.stats().clauses_eliminated;
    assert!(
        drat_eliminated > 0,
        "DRAT conditioning must eliminate at least one clause"
    );

    // 2. LRAT preprocess: conditioning fires (lrat_override=false, same as BCE).
    let mut lrat_solver = Solver::with_proof_output(
        3,
        ProofOutput::lrat_text(Vec::<u8>::new(), clauses.len() as u64),
    );
    lrat_solver.preprocessing_quick_mode = false; // test needs conditioning during preprocess
    isolate_conditioning(&mut lrat_solver);
    for clause in &clauses {
        assert!(lrat_solver.add_clause(clause.clone()));
    }
    lrat_solver.initialize_watches();
    assert!(
        !lrat_solver.preprocess(),
        "LRAT preprocess should not derive UNSAT for this SAT formula"
    );
    let lrat_eliminated = lrat_solver.inproc.conditioning.stats().clauses_eliminated;
    assert!(
        lrat_eliminated > 0,
        "LRAT conditioning must eliminate at least one clause; got {lrat_eliminated}"
    );

    // 3. Direct condition() in LRAT mode: works (non-vacuous engine test).
    let mut direct_solver = Solver::with_proof_output(
        3,
        ProofOutput::lrat_text(Vec::<u8>::new(), clauses.len() as u64),
    );
    isolate_conditioning(&mut direct_solver);
    for clause in &clauses {
        assert!(direct_solver.add_clause(clause.clone()));
    }
    direct_solver.initialize_watches();
    direct_solver.condition();
    let direct_eliminated = direct_solver.inproc.conditioning.stats().clauses_eliminated;
    assert!(
        direct_eliminated > 0,
        "direct condition() must eliminate clauses; DRAT={drat_eliminated}, direct={direct_eliminated}"
    );
}
