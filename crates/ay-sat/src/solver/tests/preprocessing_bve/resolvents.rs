// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// BVE resolvent and preprocessing tests (extracted from tests.rs, Part of #5142)
// ========================================================================

/// Test for #1495: BVE resolvents must be properly watched when literals
/// are already assigned at level 0.
///
/// This test creates a scenario where:
/// 1. Variable x0 is eliminated at level 0
/// 2. The resolvent has literals that are already assigned
/// 3. The resolvent must be reordered so unassigned literals are watched
#[test]
fn test_bve_resolvent_reordering_when_assigned_at_level_0() {
    let mut solver = Solver::new(4);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);

    // Force x1 = true, x2 = true via unit clauses
    solver.add_clause(vec![Literal::positive(x1)]); // x1 = true
    solver.add_clause(vec![Literal::positive(x2)]); // x2 = true

    // Clauses for BVE that will produce resolvent with -x1, -x2
    // (x0 ∨ -x1 ∨ x3)
    // (-x0 ∨ -x2)
    // Resolution: (-x1 ∨ x3 ∨ -x2)
    // With x1=true, x2=true: -x1=false, -x2=false, x3=unassigned
    // The fix ensures x3 is watched first
    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::negative(x1),
        Literal::positive(x3),
    ]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x2)]);

    // Process initial clauses (does unit propagation at level 0)
    assert!(solver.process_initial_clauses().is_none());

    assert_eq!(
        solver.lit_value(Literal::positive(x1)),
        Some(true),
        "x1 should be true"
    );
    assert_eq!(
        solver.lit_value(Literal::positive(x2)),
        Some(true),
        "x2 should be true"
    );

    // Run BVE - this should not panic and should correctly handle the resolvent
    let derived_unsat = solver.bve();
    assert!(
        !derived_unsat,
        "BVE should not derive UNSAT for this SAT formula"
    );

    assert!(
        solver.inproc.bve.is_eliminated(x0),
        "x0 should be eliminated by BVE"
    );

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Formula should be SAT but got {result:?}"
    );
}

/// Test for #1495: BVE binary resolvent where both literals are false
/// should derive UNSAT.
#[test]
fn test_bve_binary_resolvent_both_false_derives_unsat() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    solver.add_clause(vec![Literal::positive(x1)]); // x1 = true
    solver.add_clause(vec![Literal::positive(x2)]); // x2 = true

    // Resolution on x0: (-x1 ∨ -x2), both false → conflict
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x2)]);

    assert!(solver.process_initial_clauses().is_none());

    let derived_unsat = solver.bve();
    assert!(
        derived_unsat,
        "BVE should derive UNSAT when resolvent is binary conflict"
    );

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT but got {result:?}"
    );
}

/// BVE must fire during preprocessing (#4209).
#[test]
fn test_bve_fires_during_preprocessing() {
    let mut solver = Solver::new(3);
    solver.set_preprocess_enabled(true);
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.bve.enabled = true;

    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);

    assert!(solver.process_initial_clauses().is_none());
    assert!(
        !solver.preprocess(),
        "preprocessing BVE should not derive UNSAT for this SAT formula"
    );
    assert!(
        solver.bve_stats().vars_eliminated > 0,
        "BVE must eliminate x0 during preprocessing (was blocked by #4209)"
    );
}

/// Regression for #7432: preprocessing fastelim must NOT run the post-round
/// instantiation hook until #7437 ports CaDiCaL's isolated watch-state model.
///
/// The fixture forces one unrelated elimination on `x`, making the disabled
/// hook reachable. Variable `g` has >100 negative occurrences per polarity,
/// so fastelim skips ordinary elimination via the FASTELIM_OCC_LIMIT guard.
/// The candidate ternary clause `(g v b v c)` must remain intact.
///
/// Extra variables (5..106) are frozen to prevent BVE from eliminating them
/// as pure literals, which would cascade g's negative occ count below the
/// FASTELIM_OCC_LIMIT threshold.
#[test]
fn test_bve_fastelim_keeps_instantiation_candidate_clause_intact() {
    let mut solver = Solver::new(106);
    let x = Variable(0);
    let y = Variable(1);
    let g = Variable(2);
    let b = Variable(3);
    let c = Variable(4);

    solver.freeze(y);
    solver.freeze(b);
    solver.freeze(c);

    // Unrelated elimination so the post-BVE instantiation hook would run.
    solver.add_clause_db(&[Literal::positive(x), Literal::positive(y)], false);
    solver.add_clause_db(&[Literal::negative(x), Literal::positive(y)], false);

    let candidate_idx = solver.add_clause_db(
        &[
            Literal::positive(g),
            Literal::positive(b),
            Literal::positive(c),
        ],
        false,
    );

    // Give `g` 101 negative occurrences total so preprocessing fastelim skips
    // elimination on `g` (FASTELIM_OCC_LIMIT=100, guard is `> 100`).
    // Each extra variable is frozen to prevent pure-literal elimination from
    // cascading g's occurrence count below the threshold.
    for extra_var in 5..106 {
        solver.freeze(Variable(extra_var as u32));
        solver.add_clause_db(
            &[
                Literal::negative(g),
                Literal::positive(Variable(extra_var as u32)),
            ],
            false,
        );
    }

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    // Match preprocessing fastelim mode: enable the 100-occurrence guard.
    solver.inproc.bve.set_growth_bound(8);

    let derived_unsat = solver.bve();
    assert!(
        !derived_unsat,
        "fixture should stay satisfiable; this only checks the disabled instantiation hook"
    );
    assert!(
        solver.inproc.bve.is_eliminated(x),
        "BVE must eliminate x so the post-round instantiation hook becomes reachable"
    );
    assert!(
        !solver.var_lifecycle.is_removed(g.index()),
        "g must stay active; fastelim should skip it on the >100-occurrence side"
    );
    assert!(
        solver.arena.is_active(candidate_idx),
        "candidate clause must remain active when instantiation is disabled"
    );

    let candidate_lits = solver.arena.literals(candidate_idx);
    assert_eq!(
        candidate_lits.len(),
        3,
        "disabled instantiation must not strengthen the ternary candidate"
    );
    assert!(
        candidate_lits.contains(&Literal::positive(g)),
        "candidate clause must still contain g when the instantiation hook is disabled"
    );
}

/// #8922: LRAT-enabled BVE must not enter the post-BVE instantiation path.
///
/// This mirrors the reachable-hook fixture above, but with proof output enabled
/// and a direct BVE call. If instantiation runs, it marks the ternary candidate
/// clause as instantiated and temporarily reconnects watches.
#[test]
fn test_bve_lrat_skips_post_bve_instantiation_hook() {
    use crate::proof::ProofOutput;

    let mut solver = Solver::with_proof_output(107, ProofOutput::lrat_text(Vec::new(), 104));
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);
    let g = Variable(3);
    let b = Variable(4);
    let c = Variable(5);

    solver.freeze(y);
    solver.freeze(z);
    solver.freeze(b);
    solver.freeze(c);

    assert!(solver.add_clause(vec![Literal::positive(x), Literal::positive(y)]));
    assert!(solver.add_clause(vec![Literal::negative(x), Literal::positive(z)]));

    let candidate_lits = [
        Literal::positive(g),
        Literal::positive(b),
        Literal::positive(c),
    ];
    assert!(solver.add_clause(candidate_lits.to_vec()));
    let candidate_idx = solver
        .arena
        .active_indices()
        .find(|&idx| solver.arena.literals(idx) == candidate_lits)
        .expect("candidate clause should be active");

    for extra_var in 6..107 {
        solver.freeze(Variable(extra_var as u32));
        assert!(solver.add_clause(vec![
            Literal::negative(g),
            Literal::positive(Variable(extra_var as u32)),
        ]));
    }

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver.inproc.bve.set_growth_bound(8);

    let derived_unsat = solver.bve();
    assert!(!derived_unsat, "fixture should stay satisfiable");
    assert!(
        solver.inproc.bve.is_eliminated(x),
        "BVE must eliminate x so the post-round instantiation hook is reachable"
    );
    assert!(
        !solver.var_lifecycle.is_removed(g.index()),
        "g must stay active as a post-BVE instantiation candidate"
    );
    assert!(
        solver.arena.is_active(candidate_idx),
        "candidate clause must remain active"
    );
    assert!(
        !solver.arena.is_instantiated(candidate_idx),
        "LRAT BVE must not execute post-BVE instantiation"
    );
    assert!(
        !solver.cold.instantiate_rebuilt_watches,
        "LRAT BVE must not reconnect watches through instantiation"
    );
}

/// Per-variable backward subsumption (#7998) is safe because extension
/// stack entries are populated before backward subsumption runs.
#[test]
fn test_bve_resolvent_backward_subsumes_after_elimination_completes() {
    let mut solver = Solver::new(4);
    let x = Variable(0);
    let a = Variable(1);
    let b = Variable(2);
    let c = Variable(3);

    solver.freeze(a);
    solver.freeze(b);
    solver.freeze(c);

    let subsumed_idx = solver.add_clause_db(
        &[
            Literal::positive(a),
            Literal::positive(b),
            Literal::positive(c),
        ],
        false,
    );
    solver.add_clause_db(&[Literal::positive(x), Literal::positive(a)], false);
    solver.add_clause_db(&[Literal::negative(x), Literal::positive(b)], false);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let derived_unsat = solver.bve();
    assert!(
        !derived_unsat,
        "fixture should remain satisfiable after eliminating the pivot"
    );
    assert!(
        solver.inproc.bve.is_eliminated(x),
        "BVE must eliminate the pivot and add the (a v b) resolvent"
    );
    // (#8397) Backward subsumption IDENTIFIES (a v b v c) as subsumed by
    // (a v b), but does NOT delete it. Deleting subsumed clauses during BVE
    // breaks the reconstruction resolution guarantee when the subsumer
    // resolvent is later eliminated. The subsumed clause is kept alive and
    // will be cleaned up by subsumption passes between BVE rounds.
    assert!(
        !solver.arena.is_dead(subsumed_idx),
        "(#8397) backward subsumption no longer deletes during BVE; (a v b v c) is kept alive"
    );
    assert_eq!(
        solver.arena.active_clause_count(),
        2,
        "resolvent (a v b) and subsumed (a v b v c) both remain after BVE (#8397)",
    );
}

#[test]
fn test_preprocess_quick_mode_runs_subsume_before_bve() {
    let mut solver = Solver::new(5);
    solver.disable_all_inprocessing();
    solver.set_bve_enabled(true);
    solver.set_subsume_enabled(true);
    solver.preprocessing_quick_mode = true;

    for idx in 0..5 {
        solver.freeze(Variable(idx));
    }

    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    let subsumed_idx = solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
            Literal::positive(Variable(2)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::positive(Variable(3)),
            Literal::positive(Variable(4)),
        ],
        false,
    );
    solver.initialize_watches();

    assert!(
        !solver.preprocess(),
        "simple subsumption setup should remain satisfiable",
    );
    assert!(
        !solver.arena.is_active(subsumed_idx),
        "quick-mode preprocessing must subsume the ternary clause before BVE (#7178)",
    );
    assert!(
        solver.subsume_stats().forward_subsumed > 0,
        "pre-BVE quick-mode subsumption should report forward progress",
    );
}

// ========================================================================
// GPU BVE dispatch classification (#8349 parity fixes)
// ========================================================================

/// A clause containing both pivot polarities appears in BOTH occurrence
/// lists. The old GPU path resolved it against itself, producing a spurious
/// EMPTY resolvent (false UNSAT). Classification must exclude it from
/// resolution entirely; with no remaining pairs the elimination is trivially
/// bounded with zero resolvents. This regression test needs no GPU: the
/// classification runs CPU-side before any dispatch.
#[cfg(feature = "gpu")]
#[test]
fn test_gpu_bve_dispatch_pivot_tautology_no_false_unsat() {
    let mut solver = Solver::new(10);
    let x0 = Variable(0);

    // {x0, ~x0, x2}: tautological in the pivot, lives in both occ lists.
    let taut_idx = solver.arena.add(
        &[
            Literal::positive(x0),
            Literal::negative(x0),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    let result = solver.gpu_bve_resolve_and_check(x0, &[taut_idx], &[taut_idx], u64::MAX);
    let (can_eliminate, resolvents, strengthened, satisfied, attempts) =
        result.expect("classification-only path must not require a GPU");
    assert!(can_eliminate);
    assert!(
        resolvents.is_empty(),
        "pivot-tautological self-resolution must produce NO resolvents \
         (an empty resolvent here is a false UNSAT)"
    );
    assert!(strengthened.is_empty());
    assert!(satisfied.is_empty());
    assert_eq!(attempts, 0);
}

/// Stale (dead / out-of-range) occurrence entries and root-satisfied
/// parents must be filtered before GPU resolution, matching the CPU path.
#[cfg(feature = "gpu")]
#[test]
fn test_gpu_bve_dispatch_filters_stale_and_satisfied_parents() {
    let mut solver = Solver::new(10);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x3 = Variable(3);
    let x4 = Variable(4);

    let pos_idx = solver
        .arena
        .add(&[Literal::positive(x0), Literal::positive(x1)], false);
    let sat_idx = solver
        .arena
        .add(&[Literal::positive(x0), Literal::positive(x3)], false);
    let neg_idx = solver
        .arena
        .add(&[Literal::negative(x0), Literal::positive(x4)], false);

    // Make x3 root-true so sat_idx is a satisfied parent.
    solver.vals[Literal::positive(x3).index()] = 1;
    solver.vals[Literal::negative(x3).index()] = -1;

    let oob_idx = solver.arena.len() + 100;

    let result =
        solver.gpu_bve_resolve_and_check(x0, &[pos_idx, sat_idx, oob_idx], &[neg_idx], u64::MAX);
    let Some((can_eliminate, resolvents, _strengthened, satisfied, _attempts)) = result else {
        // Only one real pair remains; reaching the dispatch stage without a
        // GPU adapter returns None. Classification was still exercised.
        return;
    };
    assert!(can_eliminate);
    assert_eq!(
        satisfied,
        vec![sat_idx],
        "root-satisfied parent must be reported so it is never witnessed (#8397)"
    );
    assert_eq!(resolvents.len(), 1, "only (pos_idx, neg_idx) resolves");
    let lits = &resolvents[0].0;
    assert_eq!(lits.len(), 2);
    assert!(lits.contains(&Literal::positive(x1)));
    assert!(lits.contains(&Literal::positive(x4)));
}

include!("resolvents/gpu_occ_limit.rs");
