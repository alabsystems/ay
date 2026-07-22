// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::add_duplicate_and_gate_formula;
use super::*;

#[test]
fn test_preprocess_congruence_htr_binaries_feed_decompose_without_gate_equivalences() {
    // Clauses:
    //  (r ∨ ¬y ∨ x), (¬r ∨ ¬y), (¬x ∨ y)
    //
    // Hyper-ternary in congruence derives (¬y ∨ x). Together with (¬x ∨ y),
    // this forms x ↔ y and decompose should substitute at least one variable.
    // There are no duplicated gates here, so this exercises the "new binary
    // clauses but no congruence equivalence" path.
    let mut solver: Solver = Solver::new(3);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);
    let r = Variable(0);
    let x = Variable(1);
    let y = Variable(2);

    solver.add_clause(vec![
        Literal::positive(r),
        Literal::negative(y),
        Literal::positive(x),
    ]);
    solver.add_clause(vec![Literal::negative(r), Literal::negative(y)]);
    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT on this satisfiable formula"
    );

    // With find_equivalences(), congruence now discovers binary implication
    // equivalences (x ≡ y from HTR-derived (¬y,x) + existing (¬x,y)).
    // The original test expected 0 gate equivalences + decompose SCC discovery.
    // Now congruence finds the equivalence directly OR decompose finds it via SCC.
    let cong_equivs = solver.congruence_stats().equivalences_found;
    let decompose_subs = solver.decompose_stats().substituted;
    assert!(
        cong_equivs > 0 || decompose_subs > 0,
        "x↔y equivalence should be found by congruence find_equivalences or decompose SCC \
         (cong_equivs={cong_equivs}, decompose_subs={decompose_subs})"
    );
}

#[test]
fn test_congruence_uses_level0_vals_to_collapse_duplicate_and_gates() {
    let mut solver: Solver = Solver::new(5);
    let y0 = Variable(0);
    let y1 = Variable(1);
    let a = Variable(2);
    let b = Variable(3);
    let c = Variable(4);

    // Root unit assignment a=true. Without passing solver.vals into the
    // congruence engine, y0 stays AND(a,b,c) and cannot collide with y1.
    solver.add_clause(vec![Literal::positive(a)]);

    // y0 = AND(a, b, c)
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::negative(b),
        Literal::negative(c),
        Literal::positive(y0),
    ]);
    solver.add_clause(vec![Literal::positive(a), Literal::negative(y0)]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(y0)]);
    solver.add_clause(vec![Literal::positive(c), Literal::negative(y0)]);

    // y1 = AND(b, c)
    solver.add_clause(vec![
        Literal::negative(b),
        Literal::negative(c),
        Literal::positive(y1),
    ]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(y1)]);
    solver.add_clause(vec![Literal::positive(c), Literal::negative(y1)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "fixture must expose a level-0 assignment before congruence runs"
    );

    assert!(
        solver.congruence(),
        "level-0 vals should reduce y0 to AND(b,c) so congruence can discover y0 ≡ y1"
    );
    assert!(
        solver.congruence_stats().equivalences_found > 0,
        "expected congruence equivalences after vals-aware gate rewriting"
    );
}

#[test]
fn test_preprocess_congruence_does_not_force_decompose_when_disabled() {
    let mut solver: Solver = Solver::new(4);
    add_duplicate_and_gate_formula(&mut solver);

    solver.set_decompose_enabled(false);
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

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // Drain initial unit propagations so qhead == trail.len() before preprocess.
    assert!(solver.propagate().is_none());

    let decompose_rounds_before = solver.decompose_stats().rounds;
    let congruence_rounds_before = solver.congruence_stats().rounds;

    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT on satisfiable duplicate-gate formula"
    );
    // #5752: congruence MUST NOT run when decompose is disabled. Without
    // decompose, congruence binary clauses remain unsubstituted and BVE may
    // eliminate variables with active equivalence binaries, causing
    // reconstruction to produce invalid models.
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before,
        "congruence must not run when decompose_enabled=false (#5752)"
    );
    assert_eq!(
        solver.decompose_stats().rounds,
        decompose_rounds_before,
        "decompose must not run when decompose_enabled=false"
    );
}

#[test]
fn test_preprocess_skips_congruence_when_congruence_disabled() {
    let mut solver: Solver = Solver::new(4);
    add_duplicate_and_gate_formula(&mut solver);

    solver.set_decompose_enabled(false);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(false);
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

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // Drain initial unit propagations so qhead == trail.len() before preprocess.
    assert!(solver.propagate().is_none());

    let congruence_rounds_before = solver.congruence_stats().rounds;
    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT on satisfiable duplicate-gate formula"
    );
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before,
        "congruence must stay skipped when congruence_enabled=false"
    );
}

#[test]
fn test_restart_inprocessing_congruence_does_not_force_decompose_when_disabled() {
    let mut solver: Solver = Solver::new(4);
    add_duplicate_and_gate_formula(&mut solver);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // Drain initial unit propagations so qhead == trail.len() before inprocessing.
    assert!(solver.propagate().is_none());

    solver.set_decompose_enabled(false);
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

    solver.num_conflicts = solver.inproc_ctrl.congruence.next_conflict;
    // Simulate a reduce_db having occurred so the reduction gate passes (#5130).
    solver.cold.num_reductions = 1;

    let decompose_rounds_before = solver.decompose_stats().rounds;
    let congruence_rounds_before = solver.congruence_stats().rounds;

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on satisfiable duplicate-gate formula"
    );
    // #5752: congruence MUST NOT run when decompose is disabled. Without
    // decompose, congruence binary clauses remain unsubstituted and BVE may
    // eliminate variables with active equivalence binaries, causing
    // reconstruction to produce invalid models.
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before,
        "congruence must not run when decompose_enabled=false (#5752)"
    );
    assert_eq!(
        solver.decompose_stats().rounds,
        decompose_rounds_before,
        "decompose must not run when decompose_enabled=false"
    );
}

#[test]
fn test_xor_ladder_rungs_are_watched_as_long_clauses_under_drat() {
    // Regression pin for the f0bafebd collapse-DRAT emission defect
    // (wf_0c7d84e9, fixed in proof_ladder.rs insert_ladder_rung).
    //
    // Two identical 2-input XOR gates t1 = a^b and t2 = a^b give the
    // congruence closure an XorMatch edge t1 == t2 whose equivalence
    // binaries are NOT directly RUP (assuming t1, -t2 propagates nothing),
    // so the DRAT route must emit the XOR-matching ladder rungs
    // [(-)t1, (+)t2, +-b] -- 3-literal clauses -- before the edge binaries.
    //
    // insert_ladder_rung used to attach those >=3-lit rungs with
    // is_binary=true. A long clause watched with BINARY_FLAG propagates its
    // blocker while IGNORING its remaining literals, skips the BCP liveness
    // check, and survives deletion as a stale watch; on f0bafebd this
    // manufactured a proof-less level-0 unit through a deleted-rung husk and
    // dpr-trim rejected the emitted proof ("RAT check on proof pivot
    // failed"). The debug_assert in attach_clause_watches (clause_add.rs)
    // aborts this test if any rung is ever again attached with a binary
    // watch; the stats assertion below guarantees the rung path actually
    // ran (xor_ladders_emitted counts edges whose rung set was inserted).
    use crate::ProofOutput;

    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver: Solver = Solver::with_proof_output(4, proof);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);

    let a = Variable(0);
    let b = Variable(1);
    let t1 = Variable(2);
    let t2 = Variable(3);
    // t1 = a XOR b
    solver.add_clause(vec![
        Literal::negative(t1),
        Literal::positive(a),
        Literal::positive(b),
    ]);
    solver.add_clause(vec![
        Literal::negative(t1),
        Literal::negative(a),
        Literal::negative(b),
    ]);
    solver.add_clause(vec![
        Literal::positive(t1),
        Literal::positive(a),
        Literal::negative(b),
    ]);
    solver.add_clause(vec![
        Literal::positive(t1),
        Literal::negative(a),
        Literal::positive(b),
    ]);
    // t2 = a XOR b (duplicate gate; no direct binary link t1 <-> t2, so the
    // closure edge needs the ladder for RUP justification).
    solver.add_clause(vec![
        Literal::negative(t2),
        Literal::positive(a),
        Literal::positive(b),
    ]);
    solver.add_clause(vec![
        Literal::negative(t2),
        Literal::negative(a),
        Literal::negative(b),
    ]);
    solver.add_clause(vec![
        Literal::positive(t2),
        Literal::positive(a),
        Literal::negative(b),
    ]);
    solver.add_clause(vec![
        Literal::positive(t2),
        Literal::negative(a),
        Literal::positive(b),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(
        !solver.preprocess(),
        "preprocess must not derive UNSAT on this satisfiable formula"
    );

    let stats = solver.congruence_stats();
    assert!(
        stats.xor_ladders_emitted >= 1,
        "XOR-matching ladder must fire on the duplicate XOR gates so the \
         rung watch-attachment path stays covered (xor_ladders_emitted={}, \
         equivalences_found={}, non_rup_equivalences={})",
        stats.xor_ladders_emitted,
        stats.equivalences_found,
        stats.non_rup_equivalences,
    );
}
